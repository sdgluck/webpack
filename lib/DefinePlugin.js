/*
	MIT License http://www.opensource.org/licenses/mit-license.php
	Author Tobias Koppers @sokra
*/

"use strict";

// import {cloneDeep} from "lodash";
// import mergeData from "lodash-es/_mergeData";

const RuntimeGlobals = require("./RuntimeGlobals");
const ConstDependency = require("./dependencies/ConstDependency");
const BasicEvaluatedExpression = require("./javascript/BasicEvaluatedExpression");
const {
	approve,
	evaluateToString,
	toConstantDependency
} = require("./javascript/JavascriptParserHelpers");
const path = require("path");
const JavascriptParser = require("./javascript/JavascriptParser");

/** @typedef {import("estree").Expression} Expression */
/** @typedef {import("./Compiler")} Compiler */
/** @typedef {import("./NormalModule")} NormalModule */
/** @typedef {import("./RuntimeTemplate")} RuntimeTemplate */

/** @typedef {null|undefined|RegExp|Function|string|number|boolean|bigint|undefined} CodeValuePrimitive */
/** @typedef {RecursiveArrayOrRecord<CodeValuePrimitive|RuntimeValue>} CodeValue */

class RuntimeValue {
	constructor(fn, fileDependencies) {
		this.fn = fn;
		this.fileDependencies = fileDependencies || [];
	}

	exec(parser) {
		const buildInfo = parser.state.module.buildInfo;
		if (this.fileDependencies === true) {
			buildInfo.cacheable = false;
		} else {
			for (const fileDependency of this.fileDependencies) {
				buildInfo.fileDependencies.add(fileDependency);
			}
		}

		return this.fn({ module: parser.state.module });
	}
}

/**
 * @param {any[]|{[k: string]: any}} obj obj
 * @param {JavascriptParser} parser Parser
 * @param {RuntimeTemplate} runtimeTemplate the runtime template
 * @param {boolean|undefined|null=} asiSafe asi safe (undefined: unknown, null: unneeded)
 * @returns {string} code converted to string that evaluates
 */
const stringifyObj = (obj, parser, runtimeTemplate, asiSafe) => {
	let code;
	let arr = Array.isArray(obj);
	if (arr) {
		code = `[${obj
			.map(code => toCode(code, parser, runtimeTemplate, null))
			.join(",")}]`;
	} else {
		code = `{${Object.keys(obj)
			.map(key => {
				const code = obj[key];
				return (
					JSON.stringify(key) +
					":" +
					toCode(code, parser, runtimeTemplate, null)
				);
			})
			.join(",")}}`;
	}

	switch (asiSafe) {
		case null:
			return code;
		case true:
			return arr ? code : `(${code})`;
		case false:
			return arr ? `;${code}` : `;(${code})`;
		default:
			return `Object(${code})`;
	}
};

/**
 * Convert code to a string that evaluates
 * @param {CodeValue} code Code to evaluate
 * @param {JavascriptParser} parser Parser
 * @param {RuntimeTemplate} runtimeTemplate the runtime template
 * @param {boolean|undefined|null=} asiSafe asi safe (undefined: unknown, null: unneeded)
 * @returns {string} code converted to string that evaluates
 */
const toCode = (code, parser, runtimeTemplate, asiSafe) => {
	if (code === null) {
		return "null";
	}
	if (code === undefined) {
		return "undefined";
	}
	if (Object.is(code, -0)) {
		return "-0";
	}
	if (code instanceof RuntimeValue) {
		return toCode(code.exec(parser), parser, runtimeTemplate, asiSafe);
	}
	if (code instanceof RegExp && code.toString) {
		return code.toString();
	}
	if (typeof code === "function" && code.toString) {
		return "(" + code.toString() + ")";
	}
	if (typeof code === "object") {
		return stringifyObj(code, parser, runtimeTemplate, asiSafe);
	}
	if (typeof code === "bigint") {
		return runtimeTemplate.supportsBigIntLiteral()
			? `${code}n`
			: `BigInt("${code}")`;
	}
	return code + "";
};

const state = {
	values: {},
	modulesUsingKey: {}
};

let didAfterCompileHookRun = false;
let didCodeGeneration = false;
const invalidModulePaths = new Set();
let cacheEmpty = false;
let resolverHookCalled = false;

class DefinePlugin {
	/**
	 * Create a new define plugin
	 * @param {Record<string, CodeValue>} definitions A map of global object definitions
	 */
	constructor(definitions) {
		this.definitions = definitions;
	}

	static runtimeValue(fn, fileDependencies) {
		return new RuntimeValue(fn, fileDependencies);
	}

	/**
	 * Apply the plugin
	 * @param {Compiler} compiler the compiler instance
	 * @returns {void}
	 */
	apply(compiler) {
		const definitions = this.definitions;

		const definePluginCache = compiler.getCache("DefinePlugin");
		const definePluginCacheKey = "state";

		let resolveReconcile,
			rejectReconcile,
			reconcilePromise = new Promise((resolve, reject) => {
				resolveReconcile = resolve;
				rejectReconcile = reject;
			});

		compiler.hooks.compilation.tap(
			"DefinePlugin",
			(compilation, { normalModuleFactory }) => {
				compilation.dependencyTemplates.set(
					ConstDependency,
					new ConstDependency.Template()
				);

				definePluginCache.get(
					definePluginCacheKey,
					null,
					/**
					 * @param {Error|null} err error
					 * @param {string} rawCacheValue cache value as string
					 */
					(err, rawCacheValue) => {
						if (err) {
							rejectReconcile(err);
							return;
						}

						// console.log(rawCacheValue)

						if (!rawCacheValue) {
							// console.log("DEFINE PLUGIN no cache value");
							cacheEmpty = true;
							resolveReconcile();
							return;
						}

						const cache = JSON.parse(rawCacheValue);

						// console.log("DEFINE PLUGIN state", cache);

						function run(obj, prefix) {
							Object.keys(obj).forEach(key => {
								if (
									typeof obj[key] === "object" &&
									!(obj[key] instanceof RuntimeValue) &&
									!(obj[key] instanceof RegExp)
								) {
									run(obj[key], prefix ? prefix + "." + key : key);
									return;
								}
								const codeStr = toCode(
									obj[key],
									new JavascriptParser("auto"),
									runtimeTemplate,
									null
								);
								if (!codeStr) {
									return;
								}
								const fullKey = prefix ? prefix + "." + key : key;
								if (
									fullKey in cache.values &&
									cache.values[fullKey].length > 0 &&
									codeStr !== cache.values[fullKey]
								) {
									cache.modulesUsingKey[fullKey].forEach(modulePath => {
										invalidModulePaths.add(modulePath);
									});
								}
							});
						}

						run(definitions);

						console.log(
							"DEFINE PLUGIN invalid module paths",
							invalidModulePaths
						);

						resolveReconcile();
					}
				);

				compiler.resolverFactory.hooks.resolver.intercept({
					factory(type, hook) {
						hook.tap("ResolverCachePlugin", resolver => {
							resolver.hooks.resolve.intercept({
								register: tapInfo => {
									if (tapInfo.name !== "ResolverCachePlugin") {
										return tapInfo;
									}
									const originalTapFn = tapInfo.fn;
									/**
									 * @param {object} request request object
									 * @param {any} resolveContext resolve context
									 * @param {function} callback callback function
									 */
									tapInfo.fn = (request, resolveContext, callback) => {
										reconcilePromise
											.then(() => {
												if (cacheEmpty) {
													originalTapFn(request, resolveContext, callback);
													return;
												}
												const modulePath = path.resolve(
													path.dirname(request.context.issuer),
													request.request
												);
												if (invalidModulePaths.has(modulePath)) {
													console.log(
														"DEFINE PLUGIN invalid module",
														modulePath
													);
													request._forceRealResolve = true
													invalidModulePaths.delete(modulePath)
												}
												originalTapFn(request, resolveContext, callback);
											})
											.catch(err => {
												console.log("err", err);
												originalTapFn(request, resolveContext, callback);
											});
									};
									return tapInfo;
								}
							});
						});
						return hook;
					}
				});

				compiler.hooks.afterCompile.tapAsync(
					"DefinePlugin",
					(compilation, callback) => {
						if (didAfterCompileHookRun) {
							callback();
							return;
						}
						if (!didCodeGeneration) {
							// console.log("DEFINE PLUGIN skipping cache store");
							callback();
							return;
						}
						didAfterCompileHookRun = true;
						// console.log("DEFINE PLUGIN store", state);
						definePluginCache.store(
							definePluginCacheKey,
							null,
							JSON.stringify(state),
							callback
						);
					}
				);

				const { runtimeTemplate } = compilation;

				/**
				 * Handler
				 * @param {JavascriptParser} parser Parser
				 * @returns {void}
				 */
				const handler = parser => {
					/**
					 * @template T
					 * @template R
					 * @param {string} key definition key
					 * @param {function(T): [string, R]} callback hook callback
					 * @returns {function(T, NormalModule): R} wrapped hook callback
					 */
					const hookCallback = (key, callback) => (expr, module) => {
						const [strCode, result] = callback(expr) || [];
						if (!result) {
							// TODO correct?
							return result;
						}
						didCodeGeneration = true;
						state.values[key] = strCode;
						state.modulesUsingKey = {
							...state.modulesUsingKey,
							[key]: [...(state.modulesUsingKey[key] || []), module.request]
						};
						return result;
					};

					/**
					 * Walk definitions
					 * @param {Object} definitions Definitions map
					 * @param {string} prefix Prefix string
					 * @returns {void}
					 */
					const walkDefinitions = (definitions, prefix) => {
						Object.keys(definitions).forEach(key => {
							const code = definitions[key];
							if (
								code &&
								typeof code === "object" &&
								!(code instanceof RuntimeValue) &&
								!(code instanceof RegExp)
							) {
								walkDefinitions(code, prefix + key + ".");
								applyObjectDefine(prefix + key, code);
								return;
							}
							applyDefineKey(prefix, key);
							applyDefine(prefix + key, code);
						});
					};

					/**
					 * Apply define key
					 * @param {string} prefix Prefix
					 * @param {string} key Key
					 * @returns {void}
					 */
					const applyDefineKey = (prefix, key) => {
						const splittedKey = key.split(".");
						splittedKey.slice(1).forEach((_, i) => {
							const fullKey = prefix + splittedKey.slice(0, i + 1).join(".");
							parser.hooks.canRename.for(fullKey).tap("DefinePlugin", approve);
						});
					};

					/**
					 * Apply Code
					 * @param {string} key Key
					 * @param {CodeValue} code Code
					 * @returns {void}
					 */
					const applyDefine = (key, code) => {
						const isTypeof = /^typeof\s+/.test(key);
						if (isTypeof) key = key.replace(/^typeof\s+/, "");
						let recurse = false;
						let recurseTypeof = false;
						if (!isTypeof) {
							parser.hooks.canRename.for(key).tap("DefinePlugin", approve);
							parser.hooks.evaluateIdentifier.for(key).tap(
								"DefinePlugin",
								hookCallback(key, expr => {
									/**
									 * this is needed in case there is a recursion in the DefinePlugin
									 * to prevent an endless recursion
									 * e.g.: new DefinePlugin({
									 * "a": "b",
									 * "b": "a"
									 * });
									 */
									if (recurse) return;
									recurse = true;
									const strCode = toCode(code, parser, runtimeTemplate, null);
									const res = parser.evaluate(strCode);
									recurse = false;
									res.setRange(expr.range);
									return [strCode, res];
								})
							);
							parser.hooks.expression.for(key).tap(
								"DefinePlugin",
								hookCallback(key, expr => {
									const strCode = toCode(
										code,
										parser,
										runtimeTemplate,
										!parser.isAsiPosition(expr.range[0])
									);
									let res;
									if (/__webpack_require__\s*(!?\.)/.test(strCode)) {
										res = toConstantDependency(parser, strCode, [
											RuntimeGlobals.require
										])(expr);
									} else if (/__webpack_require__/.test(strCode)) {
										res = toConstantDependency(parser, strCode, [
											RuntimeGlobals.requireScope
										])(expr);
									} else {
										res = toConstantDependency(parser, strCode)(expr);
									}
									return [strCode, res];
								})
							);
						}
						parser.hooks.evaluateTypeof.for(key).tap(
							"DefinePlugin",
							hookCallback(key, expr => {
								/**
								 * this is needed in case there is a recursion in the DefinePlugin
								 * to prevent an endless recursion
								 * e.g.: new DefinePlugin({
								 * "typeof a": "typeof b",
								 * "typeof b": "typeof a"
								 * });
								 */
								if (recurseTypeof) return;
								recurseTypeof = true;
								const strCode = toCode(code, parser, runtimeTemplate, null);
								const typeofCode = isTypeof
									? strCode
									: "typeof (" + strCode + ")";
								const res = parser.evaluate(typeofCode);
								recurseTypeof = false;
								res.setRange(expr.range);
								return [strCode, res];
							})
						);
						parser.hooks.typeof.for(key).tap(
							"DefinePlugin",
							hookCallback(key, expr => {
								const strCode = toCode(code, parser, runtimeTemplate, null);
								const typeofCode = isTypeof
									? strCode
									: "typeof (" + strCode + ")";
								const res = parser.evaluate(typeofCode);
								if (!res.isString()) return;
								return [
									strCode,
									toConstantDependency(parser, JSON.stringify(res.string)).bind(
										parser
									)(expr)
								];
							})
						);
					};

					/**
					 * Apply Object
					 * @param {string} key Key
					 * @param {Object} obj Object
					 * @returns {void}
					 */
					const applyObjectDefine = (key, obj) => {
						parser.hooks.canRename.for(key).tap("DefinePlugin", approve);
						parser.hooks.evaluateIdentifier.for(key).tap(
							"DefinePlugin",
							hookCallback(key, expr => {
								const res = new BasicEvaluatedExpression()
									.setTruthy()
									.setSideEffects(false)
									.setRange(expr.range);
								const strCode = res.asString();
								return [strCode, res];
							})
						);
						parser.hooks.evaluateTypeof.for(key).tap(
							"DefinePlugin",
							hookCallback(key, expr => {
								const res = evaluateToString("object")(expr);
								return [res.asString(), res];
							})
						);
						parser.hooks.expression.for(key).tap(
							"DefinePlugin",
							hookCallback(key, expr => {
								const strCode = stringifyObj(
									obj,
									parser,
									runtimeTemplate,
									!parser.isAsiPosition(expr.range[0])
								);
								let res;
								if (/__webpack_require__\s*(!?\.)/.test(strCode)) {
									res = toConstantDependency(parser, strCode, [
										RuntimeGlobals.require
									])(expr);
								} else if (/__webpack_require__/.test(strCode)) {
									res = toConstantDependency(parser, strCode, [
										RuntimeGlobals.requireScope
									])(expr);
								} else {
									res = toConstantDependency(parser, strCode)(expr);
								}
								return [strCode, res];
							})
						);
						parser.hooks.typeof.for(key).tap(
							"DefinePlugin",
							hookCallback(key, expr => {
								const res = toConstantDependency(
									parser,
									JSON.stringify("object")
								)(expr);
								return [res.asString(), res];
							})
						);
					};

					walkDefinitions(definitions, "");
				};

				normalModuleFactory.hooks.parser
					.for("javascript/auto")
					.tap("DefinePlugin", handler);
				normalModuleFactory.hooks.parser
					.for("javascript/dynamic")
					.tap("DefinePlugin", handler);
				normalModuleFactory.hooks.parser
					.for("javascript/esm")
					.tap("DefinePlugin", handler);
			}
		);
	}
}
module.exports = DefinePlugin;
