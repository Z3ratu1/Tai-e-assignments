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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.AnalysisException;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me

        Set<Stmt> liveCode = new HashSet<>();
        Queue<Stmt> liveStmts = new LinkedList<>();

        // always add entry and exit
        // 有时候死循环的时候exit不会被遍历到，但是还是得加进来
        liveStmts.add(cfg.getEntry());
        liveStmts.add(cfg.getExit());
        while (!liveStmts.isEmpty()) {
            boolean addAll = true;
            Stmt stmt = liveStmts.poll();
            if (liveCode.contains(stmt)) {
                continue;
            } else {
                liveCode.add(stmt);
            }
            if (stmt instanceof AssignStmt<?, ?>) {
                LValue lValue = ((AssignStmt<?, ?>) stmt).getLValue();
                RValue rValue = ((AssignStmt<?, ?>) stmt).getRValue();
                SetFact<Var> varSetFact = liveVars.getOutFact(stmt);
                if (lValue instanceof Var && !varSetFact.contains((Var) lValue) && hasNoSideEffect(rValue)) {
                    deadCode.add(stmt);
                }
            } else if (stmt instanceof If) {
                ConditionExp condition = ((If) stmt).getCondition();
                if (ConstantPropagation.canHoldInt(condition.getOperand1()) && ConstantPropagation.canHoldInt(condition.getOperand2())) {
                    Value v = ConstantPropagation.evaluate(condition, constants.getInFact(stmt));
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        switch (edge.getKind()) {
                            case IF_TRUE -> {
                                if (v.isConstant() && v.getConstant() != 0) {
                                    // 如果记录无效后继，然后在遍历时剔除，会导致do{}while(false)这种能执行一次的整个block也被视为deadcode
                                    liveStmts.add(edge.getTarget());
                                    addAll = false;
                                }
                            }
                            case IF_FALSE -> {
                                if (v.isConstant() && v.getConstant() == 0) {
                                    liveStmts.add(edge.getTarget());
                                    addAll = false;
                                }
                            }
                            default -> throw new AnalysisException("unknown Kind");
                        }
                    }
                }
            } else if (stmt instanceof SwitchStmt) {
                Var var = ((SwitchStmt) stmt).getVar();
                if (ConstantPropagation.canHoldInt(var)) {
                    CPFact cpFact = constants.getInFact(stmt);
                    Value value = cpFact.get(var);
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        switch (edge.getKind()) {
                            // 有一个结果是恒真的，那么剩下的结果就是恒假，添加这一个然后剩下的全部排出
                            case SWITCH_CASE -> {
                                if (value.isConstant() && value.getConstant() == edge.getCaseValue()) {
                                    liveStmts.add(edge.getTarget());
                                    addAll = false;
                                }
                            }
                            case SWITCH_DEFAULT -> {
                                List<Integer> caseValues = ((SwitchStmt) stmt).getCaseValues();
                                if (value.isConstant() && !caseValues.contains(value.getConstant())) {
                                    liveStmts.add(edge.getTarget());
                                    addAll = false;
                                }
                            }
                            default -> throw new AnalysisException("unknown Kind");
                        }
                    }
                }
            }
            if(addAll){
                liveStmts.addAll(cfg.getSuccsOf(stmt));
            }
        }
        for (Stmt stmt : cfg.getNodes()) {
            if (!liveCode.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
