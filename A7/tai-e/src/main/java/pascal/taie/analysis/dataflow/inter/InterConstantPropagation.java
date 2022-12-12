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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private MultiMap<Var, Var> alias;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        // 抄rmb作业用mutilMap存别名关系
        alias = initializeAlias(pta);
    }

    private MultiMap<Var, Var> initializeAlias(PointerAnalysisResult pta) {
        MultiMap<Var, Var> alias = Maps.newMultiMap();
        MultiMap<Obj, Var> objToVars = Maps.newMultiMap();

        pta.getVars().forEach(var -> {
            pta.getPointsToSet(var).forEach(obj -> {
                objToVars.put(obj, var);
            });
        });

        objToVars.forEachSet(((obj, vars) -> {
            vars.forEach(var -> {
                // 包含自己
                alias.putAll(var, vars);
            });
        }));
        return alias;
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 调用应该不用我去管吧
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 需要最先把老方法调用起来。。。不然重复的部分很难办，要么就得改这个方法
        if (!(stmt instanceof LoadArray) && !(stmt instanceof LoadField) &&
                !(stmt instanceof StoreArray) && !(stmt instanceof StoreField)) {
            return cp.transferNode(stmt, in, out);
        }
        // 感觉应该是这里需要处理别名?
        CPFact origin = out.copy();
        // 这里复制之后再调用cp.transferNode会有潜在的bug，进cp.transferNode之后out和in因为之前的复制就一开始就是相同的了
        in.forEach(out::update);
        // 且只处理有左值的语句
        Optional<LValue> def = stmt.getDef();
        if (def.isPresent()) {
            LValue lValue = def.get();
            if (lValue instanceof Var var && ConstantPropagation.canHoldInt(var)) {
                if (stmt instanceof LoadArray loadArray) {
                    out.update(loadArray.getLValue(), cp.meetValue(solver.getInFact(stmt).get(var), getArrayIndexAliasValue(loadArray)));
                } else if (stmt instanceof LoadField loadField) {
                    // stmt instance of LoadField
                    FieldAccess fieldAccess = loadField.getFieldAccess();
                    if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) {
                        // 不要忘记左值可能有初始值
                        out.update(var, cp.meetValue(solver.getInFact(stmt).get(var), getInstanceFieldAliasValue(instanceFieldAccess)));
                    } else if (fieldAccess instanceof StaticFieldAccess staticFieldAccess) {
                        out.update(var, cp.meetValue(solver.getInFact(stmt).get(var), getStaticFieldAliasValue(staticFieldAccess)));
                    } else {
                        throw new AnalysisException("unknown field access");
                    }
                } else {
                    throw new AnalysisException("unknown load");
                }
            } else if (stmt instanceof StoreArray storeArray && ConstantPropagation.canHoldInt(storeArray.getRValue())) {
                // 题目有一个预先假定，**假设所有程序中的字段和数组都在被 load 之前通过 store 语句显式地初始化了**
                // 所以理论上来说应该不需要对store语句做处理，load的时候去找store就行了
                // 然而在InterProcedural2里出了问题，如果先分析getter再分析setter，会导致getter拿到的值为空，所以需要setter更新时更新所有别名
                // 感觉静态字段和数组也可能出现因为在方法中修改与方法分析顺序导致的值缺失，都加上去
                // a[i] = x
                // 感觉是store之后如果值有变化把所有相关节点的load语句加入worklist?
                if (!origin.equals(out)) {
                    setArrayIndexAliasValue(storeArray);
                }
            } else if (stmt instanceof StoreField storeField && ConstantPropagation.canHoldInt(storeField.getRValue())) {
                // o.f = x
                // 感觉不用比较RValue的值是否变化，因为in不变肯定就整个都没变
                if (!origin.equals(out)) {
                    setFieldAliasValue(storeField);
                }
            }
        }
        return !origin.equals(out);
    }

    // 你在实现 transfer*Edge() 方法的时候，不应该修改第二个参数，也就是该边的源节点的 OUT fact。
    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Stmt stmt = edge.getSource();
        CPFact returnOut = out.copy();
        Var result = ((Invoke) stmt).getResult();
        returnOut.remove(result);
        return returnOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Stmt source = edge.getSource();
        CPFact out = new CPFact();
        if (source instanceof Invoke) {
            InvokeExp exp = ((Invoke) source).getInvokeExp();
            int argCnt = exp.getArgCount();
            IR ir = edge.getCallee().getIR();
            int paramCnt = ir.getParams().size();
            for (int i = 0; i < argCnt && i < paramCnt; i++) {
                Var arg = exp.getArg(i);
                Var param = ir.getParam(i);
                out.update(param, callSiteOut.get(arg));
            }
        } else {
            throw new AnalysisException("invalid CallToReturn edge");
        }
        return out;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact out = new CPFact();
        Stmt invoke = edge.getCallSite();
        if (invoke instanceof Invoke) {
            Var result = ((Invoke) invoke).getResult();
            if (result == null) {
                return out;
            } else {
                Value value = Value.getUndef();
                for (Var v : edge.getReturnVars()) {
                    value = cp.meetValue(value, returnOut.get(v));
                }
                out.update(result, value);
            }
        } else {
            throw new AnalysisException("invalid call site");
        }
        return out;
    }

    private void setFieldAliasValue(StoreField storeField) {
        // 只处理对象字段
        if (storeField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
            alias.get(instanceFieldAccess.getBase()).forEach(var -> {
                for (LoadField loadField : var.getLoadFields()) {
                    // 简陋的字段比较手段...
                    if (Objects.equals(storeField.getFieldRef().resolve().getName(), loadField.getFieldRef().resolve().getName())) {
                        // 这里添加之后还是靠再次触发load语句找到store时更新的值
                        solver.AddWorkList(loadField);
                    }
                }
            });
        } else {
            // static字段
            assert storeField.getFieldAccess() instanceof StaticFieldAccess;
            for (Stmt stmt : icfg.getNodes()) {
                if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                    if (Objects.equals(loadField.getFieldRef().resolve().getName(), storeField.getFieldRef().resolve().getName())) {
                        solver.AddWorkList(stmt);
                    }
                }
            }
        }
    }


    private Value getInstanceFieldAliasValue(InstanceFieldAccess instanceFieldAccess) {
        Value value = Value.getUndef();
        for (Var var : alias.get(instanceFieldAccess.getBase())) {
            // o.f = x
            // var.getStoreFields()是获取所有var.f=x语句
            for (StoreField storeField : var.getStoreFields()) {
                // 检查字段名字一致，只要两个变量能指向同一个对象，那么就认为只要名字相同就应该是同一个字段(大概)
                if (Objects.equals(storeField.getFieldRef().resolve().getName(), instanceFieldAccess.getFieldRef().resolve().getName())) {
                    // 从infact中拿到被store进去的值
                    CPFact fact = solver.getInFact(storeField);
                    value = cp.meetValue(value, fact.get(storeField.getRValue()));
                }
            }
        }

        return value;
    }

    private Value getStaticFieldAliasValue(StaticFieldAccess staticFieldAccess) {
        // 忽略静态变量的初始化语句
        // 直接遍历全节点吗?
        Value value = Value.getUndef();
        for (Stmt stmt : icfg.getNodes()) {
            // T.f = x
            if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                // 静态字段的话应该还要对比一下类的名字之类的8，这个toString应该是都带上了?
                if (Objects.equals(storeField.getFieldRef().toString(), staticFieldAccess.getFieldRef().toString())) {
                    value = cp.meetValue(value, solver.getInFact(stmt).get(storeField.getRValue()));
                }
            }
        }
        return value;
    }


    private void setArrayIndexAliasValue(StoreArray storeArray) {
        for (Var var : alias.get(storeArray.getArrayAccess().getBase())) {
            // var.getLoadArrays()是获取所有x=var[i]的语句
            for (LoadArray loadArray : var.getLoadArrays()) {
                if (isAlias(storeArray, loadArray)) {
                    solver.AddWorkList(loadArray);
                }
            }
        }
    }

    private Value getArrayIndexAliasValue(LoadArray loadArray) {
        Value value = Value.getUndef();
        for (Var var : alias.get(loadArray.getArrayAccess().getBase()))
            // a[i] = x
            for (StoreArray storeArray : var.getStoreArrays()) {
                if (isAlias(storeArray, loadArray)) {
                    // 不能在lambda表达式里面修改外部值，只能用for了捏
                    value = cp.meetValue(value, solver.getInFact(storeArray).get(storeArray.getRValue()));
                }
            }
        return value;
    }

    // source的值传递到target中
    private boolean isAlias(StoreArray srcStmt, LoadArray tgtStmt) {
        // 进这个函数的array base已经互为别名了，只需要检查下标即可
        Var sourceIndex = srcStmt.getArrayAccess().getIndex();
        Var targetIndex = tgtStmt.getArrayAccess().getIndex();
        Value sourceIndexValue = solver.getInFact(srcStmt).get(sourceIndex);
        Value targetIndexValue = solver.getInFact(tgtStmt).get(targetIndex);
        if (sourceIndexValue.isUndef()) {
            return false;
        } else if (sourceIndexValue.isConstant()) {
            if (targetIndexValue.isUndef()) {
                return false;
            } else if (targetIndexValue.isConstant()) {
                return targetIndexValue.getConstant() == sourceIndexValue.getConstant();
            } else if (targetIndexValue.isNAC()) {
                return true;
            }
        } else if (sourceIndexValue.isNAC()) {
            if (targetIndexValue.isUndef()) {
                return false;
            } else if (targetIndexValue.isConstant() || targetIndexValue.isNAC()) {
                return true;
            }
        }
        throw new AnalysisException("invalid value type");
    }
}
