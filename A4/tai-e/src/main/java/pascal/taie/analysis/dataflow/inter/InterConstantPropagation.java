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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Return;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
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
        if(stmt instanceof Invoke){
            // 调用时似乎不修改返回值，返回值是在call2ret edge上被kill掉，再通过ret edge恢复
            // 直接深拷贝in到out里
            return out.copyFrom(in);
        }else {
            throw new AnalysisException("transfer not invoke stmt in transferCallNode");
        }
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 抄之前的
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // 题图1->2的边
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // 题图2->3的边，需要kill掉返回值
        // 你在实现 transfer*Edge() 方法的时候，不应该修改第二个参数，也就是该边的源节点的 OUT fact。
        Stmt stmt = edge.getSource();
        CPFact returnOut = out.copy();
        if(stmt instanceof Invoke){
            Var result = ((Invoke) stmt).getResult();
            returnOut.remove(result);
        }else {
            throw new AnalysisException("invalid CallToReturn edge");
        }
        return returnOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        // 题图2->4，需要传递参数
        Stmt source = edge.getSource();
        CPFact out = new CPFact();
        if(source instanceof Invoke){
            InvokeExp exp = ((Invoke) source).getInvokeExp();
            int argCnt = exp.getArgCount();
            IR ir = edge.getCallee().getIR();
            int paramCnt = ir.getParams().size();
            // 我们在第二次作业中介绍过，你可以从 IR 类中获取方法的参数，且可以使用 API JMethod.getIR() 来获取一个方法的 IR。
            // 应该和之前的合并逻辑不一样，每次调用都是独立的，应该单独计算一次inFact
            for (int i = 0; i < argCnt && i < paramCnt; i++) {
                Var arg = exp.getArg(i);
                Var param = ir.getParam(i);
                out.update(param, callSiteOut.get(arg));
            }
        }else {
            throw new AnalysisException("invalid CallToReturn edge");
        }
        return out;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        // 题图6->3，需要传递返回值
        CPFact out = new CPFact();
        Stmt invoke = edge.getCallSite();
        if(invoke instanceof Invoke){
            Var result = ((Invoke) invoke).getResult();
            if(result == null){
                return out;
            }else {
                // 实在想不通去抄了rmb的作业
                // 原来不需要考虑控制流啊，有多个返回值就直接合并结果。。。
                Value value = Value.getUndef();
                for (Var v:edge.getReturnVars()) {
                    value = cp.meetValue(value, returnOut.get(v));
                }
                out.update(result, value);
            }
        }else {
            throw new AnalysisException("invalid call site");
        }
        return out;
    }
}
