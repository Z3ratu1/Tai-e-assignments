/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.util.AnalysisException;

import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        result.getCSCallGraph().edges().forEach(edge -> {
            config.getSinks().forEach(sink -> {
                if (sink.method() == edge.getCallee().getMethod()) {
                    Var var = edge.getCallSite().getCallSite().getInvokeExp().getArg(sink.index());
                    CSVar csVar = csManager.getCSVar(edge.getCallSite().getContext(), var);
                    csVar.getPointsToSet().forEach(csObj -> {
                        if (manager.isTaint(csObj.getObject())) {
                            taintFlows.add(new TaintFlow((Invoke) csObj.getObject().getAllocation(), edge.getCallSite().getCallSite(), sink.index()));
                        }
                    });
                }
            });
        });
        return taintFlows;
    }

    public void checkSource(Invoke invoke, Context callerContext) {
        // 假定污点的产生一定是方法的返回值
        Var v = invoke.getResult();
        if (v != null) {
            // 理论上来说JMethod里面包含了返回值，不是很懂为什么这里需要对返回值再判断一次?并且java是不支持返回值重载的，只能参数重载
            Source s = new Source(invoke.getMethodRef().resolve(), invoke.getMethodRef().getReturnType());
            if (config.getSources().contains(s)) {
                // 污点对象使用空上下文
                CSObj taint = csManager.getCSObj(emptyContext, manager.makeTaint(invoke, s.type()));
                // 为了确保这个taint能够在分析中传递，应当添加到worklist中，而不是直接赋值给返回值的PointToSet
                solver.addWorkListEntry(csManager.getCSVar(callerContext, v), PointsToSetFactory.make(taint));
            }
        }
    }

    public void checkTaintStep(Invoke invoke, Context callerContext) {
        final int BASE = -1;
        final int RESULT = -2;
        Var base = invoke.getInvokeExp() instanceof InvokeInstanceExp ? ((InvokeInstanceExp) invoke.getInvokeExp()).getBase() : null;
        CSVar csBase = base != null ? csManager.getCSVar(callerContext, base) : null;
        // 这里是对每一个taintStep单独分析，就算一个语句同时将污点传递到base和result也能分开分析完成
        config.getTransfers().forEach(taintTransfer -> {
            if (invoke.getMethodRef().resolve() == taintTransfer.method()) {
                int from = taintTransfer.from();
                int to = taintTransfer.to();

                // 先做一个合法判断
                if (invoke.isStatic() && (from == BASE || to == BASE)) {
                    throw new AnalysisException("invalid taint step");
                }

                if (to == RESULT) {
                    Var resultVar = invoke.getResult();
                    CSVar csResult = csManager.getCSVar(callerContext, resultVar);
                    if (resultVar != null) {
                        if (invoke.getMethodRef().getReturnType() == taintTransfer.type()) {
                            // from是参数
                            if (from > BASE) {
                                Var arg = invoke.getInvokeExp().getArg(from);
                                CSVar csArg = csManager.getCSVar(callerContext, arg);
                                taintStep(csArg, csResult);
                            } else if (from == BASE) {
                                // 已经做过了static下不允许from和to为base的校验了，所以这里是不可能为null的
                                // 终究是idea智力不够了
                                taintStep(csBase, csResult);
                            } else {
                                throw new AnalysisException("invalid taint step");
                            }
                        }
                    }
                } else if (to == BASE) {
                    if (from > BASE) {
                        if (csBase.getType() == taintTransfer.type()) {
                            Var arg = invoke.getInvokeExp().getArg(from);
                            CSVar csArg = csManager.getCSVar(callerContext, arg);
                            taintStep(csArg, csBase);
                        }
                    } else {
                        throw new AnalysisException("invalid taint step");

                    }
                } else {
                    throw new AnalysisException("invalid taint step");

                }
                // 需要根据to的位置来判断应该用哪个type去比较
                // 当污点传播的方法对上之后，只需要检查from是否是污点并传播即可
//                if (from == BASE && to == RESULT && invoke.getMethodRef().getReturnType() == taintTransfer.type()) {
//                    Var resultVar = invoke.getResult();
//                    if (resultVar != null) {
//                        solver.getResult().getPointsToSet(base).forEach(csObj -> {
//                            if (manager.isTaint(csObj.getObject())) {
//                                CSVar csResultVar = csManager.getCSVar(callerContext, resultVar);
//                                // 污点传递的时候应该是创建一个新的污点对象进行传递，这里是将taintStep中的方法作为一个黑盒去分析的（大概）
//                                Obj taint = manager.makeTaint(invoke, invoke.getMethodRef().getReturnType());
//                                CSObj csTaint = csManager.getCSObj(csObj.getContext(), taint);
//                                solver.addWorkListEntry(csResultVar, PointsToSetFactory.make(csTaint));
//                            }
//                        });
//                    }
//                } else if (from > BASE) {
//                    CSVar csArg = csManager.getCSVar(callerContext, invoke.getInvokeExp().getArg(from));
//                    solver.getResult().getPointsToSet(csArg).forEach(csObj -> {
//                        if (manager.isTaint(csObj.getObject())) {
//                            if (to == BASE && base.getType() == taintTransfer.type()) {
//                                Obj taint = manager.makeTaint(invoke, base.getType());
//                                CSObj csTaint = csManager.getCSObj(csObj.getContext(), taint);
//                                solver.addWorkListEntry(base, PointsToSetFactory.make(csTaint));
//                            } else if (to == RESULT && invoke.getMethodRef().getReturnType() == taintTransfer.type()) {
//                                Var resultVar = invoke.getResult();
//                                if (resultVar != null) {
//                                    CSVar resVar = csManager.getCSVar(callerContext, resultVar);
//                                    Obj taint = manager.makeTaint(invoke, invoke.getMethodRef().getReturnType());
//                                    CSObj csTaint = csManager.getCSObj(csObj.getContext(), taint);
//                                    solver.addWorkListEntry(resVar, PointsToSetFactory.make(csTaint));
//                                }
//                            } else {
//                                // 根据题目定义，不可能出现参数与参数间流动
//                                throw new AnalysisException("invalid taint step");
//                            }
//                        }
//                    });
//                } else {
//                    throw new AnalysisException("invalid taint step");
//                }
            }
        });
    }

    private void taintStep(CSVar from, CSVar to) {
        from.getPointsToSet().forEach(csObj -> {
            if (manager.isTaint(csObj.getObject())) {
                // 从题目给的算法来看，新的taintObj是继承之前的allocation site的?
                Obj taint = manager.makeTaint((Invoke) csObj.getObject().getAllocation(), to.getType());
                CSObj csTaint = csManager.getCSObj(emptyContext, taint);
                solver.addWorkListEntry(to, PointsToSetFactory.make(csTaint));
            }
        });
    }

    public boolean isTaint(CSObj csObj) {
        return manager.isTaint(csObj.getObject());
    }

}
