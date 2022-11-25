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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Optional;

import static pascal.taie.ir.exp.ArithmeticExp.Op.*;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // get params from cfg
        CPFact cpFact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            // don't forget to check
            if(canHoldInt(param)) {
                cpFact.update(param, Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var, value) -> {
            if (target.keySet().contains(var)) {
                target.update(var, meetValue(value, target.get(var)));
            } else {
                target.update(var, value);
            }
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() && v2.isConstant()) {
            return Value.makeConstant(v2.getConstant());
        } else if (v1.isConstant() && v2.isUndef()) {
            return Value.makeConstant(v1.getConstant());
        } else if (v1.isUndef() && v2.isUndef()) {  // not sure
            return Value.getUndef();
        } else if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                return Value.makeConstant(v1.getConstant());
            } else {
                return Value.getNAC();
            }
        }
        throw new AnalysisException("unreachable code");
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact origin = out.copy();
        // copy from rmb, extremely elegant
        in.forEach(out::update);
        // should be a defStmt first
        if (stmt instanceof DefinitionStmt<?, ?>) {
            // invokeStmt is DefStmt, and it doesn't have LValue
            Optional<LValue> def = stmt.getDef();
            if (def.isPresent()) {
                LValue lValue = def.get();
                if (lValue instanceof Var && canHoldInt((Var) lValue)) {
                    // if there is `z=x+y`,rvalue will be [x,y,binaryexp]? seems exp will be the last rvalue
                    // `y=x+1` will be changed to `tmp=1;y=x+tmp`
                    List<RValue> rValueList = stmt.getUses();
                    // should consider the order of rValue
                    for (RValue rValue : rValueList) {
                        if (rValue instanceof BinaryExp) {
                            // check operand is number
                            Var left = ((BinaryExp) rValue).getOperand1();
                            Var right = ((BinaryExp) rValue).getOperand2();
                            if (canHoldInt(left) && canHoldInt(right)) {
                                // no need to meet value here.
                                out.update((Var) lValue, evaluate(rValue, in));
                            }
                            // maybe put a break here would better
                            break;
                        } else if (rValue instanceof Var && canHoldInt((Var) rValue)) {
                            out.update((Var) lValue, in.get((Var) rValue));
                        } else if (rValue instanceof IntLiteral) {
                            out.update((Var) lValue, Value.makeConstant(((IntLiteral) rValue).getValue()));
                        } else {
                            // handle other condition? like x=o.f/x=arr[index]?
                            out.update((Var) lValue, Value.getNAC());
                        }
                    }
                }
            }
        }
        return !origin.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // only evaluate binary op?
        // TODO - finish me
        if (exp instanceof BinaryExp) {
            Var v1 = ((BinaryExp) exp).getOperand1();
            Var v2 = ((BinaryExp) exp).getOperand2();
            Value value1 = in.get(v1);
            Value value2 = in.get(v2);
            // consider *0 and /0
            if (exp instanceof ArithmeticExp) {
                switch (((ArithmeticExp) exp).getOperator()) {
                    case ADD -> {
                        if (value1.isConstant() && value2.isConstant()) {
                            return Value.makeConstant(value1.getConstant() + value2.getConstant());
                        }
                    }
                    case SUB -> {
                        if (value1.isConstant() && value2.isConstant()) {
                            return Value.makeConstant(value1.getConstant() - value2.getConstant());
                        }
                    }
                    case MUL -> {
                        // I set 0*NAC=0 then it judge me wrong. I think it is wrong
//                        if (value1.isConstant() && value1.getConstant() == 0) {
//                            return Value.makeConstant(0);
//                        }
//                        if (value2.isConstant() && value2.getConstant() == 0) {
//                            return Value.makeConstant(0);
//                        }
                        if (value1.isConstant() && value2.isConstant()) {
                            return Value.makeConstant(value1.getConstant() * value2.getConstant());
                        }
                    }
                    case DIV -> {
                        // tutorial said it should be undef
                        if (value2.isConstant() && value2.getConstant() == 0) {
                            return Value.getUndef();
                        }
                        // 0 div everything is 0
//                        if (value1.isConstant() && value1.getConstant() == 0) {
//                            return Value.makeConstant(0);
//                        }
                        if (value1.isConstant() && value2.isConstant()) {
                            return Value.makeConstant(value1.getConstant() / value2.getConstant());
                        }
                    }
                    case REM -> {
                        // rem is same as div
                        if (value2.isConstant() && value2.getConstant() == 0) {
                            return Value.getUndef();
                        }
//                        if (value1.isConstant() && value1.getConstant() == 0) {
//                            return Value.makeConstant(0);
//                        }
                        if (value1.isConstant() && value2.isConstant()) {
                            return Value.makeConstant(value1.getConstant() % value2.getConstant());
                        }
                    }
                    default -> throw new AnalysisException("unknown op");
                }
            } else if (exp instanceof ConditionExp) {
                if (value1.isConstant() && value2.isConstant()) {
                    switch (((ConditionExp) exp).getOperator()) {
                        case EQ -> {
                            if (value1.getConstant() == value2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case GE -> {
                            if (value1.getConstant() >= value2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case GT -> {
                            if (value1.getConstant() > value2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case LE -> {
                            if (value1.getConstant() <= value2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case LT -> {
                            if (value1.getConstant() < value2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        case NE -> {
                            if (value1.getConstant() != value2.getConstant()) {
                                return Value.makeConstant(1);
                            } else {
                                return Value.makeConstant(0);
                            }
                        }
                        default -> throw new AnalysisException("unknown op");
                    }
                }
            } else if (exp instanceof ShiftExp) {
                if (value1.isConstant() && value2.isConstant()) {
                    switch (((ShiftExp) exp).getOperator()) {
                        case SHL -> {
                            return Value.makeConstant(value1.getConstant() << value2.getConstant());
                        }
                        case SHR -> {
                            return Value.makeConstant(value1.getConstant() >> value2.getConstant());
                        }
                        case USHR -> {
                            return Value.makeConstant(value1.getConstant() >>> value2.getConstant());
                        }
                        default -> throw new AnalysisException("unknown op");
                    }
                }
            } else if (exp instanceof BitwiseExp) {
                if(value1.isConstant() && value2.isConstant()){
                    switch (((BitwiseExp) exp).getOperator()){
                        case OR -> {
                            return Value.makeConstant(value1.getConstant() | value2.getConstant());
                        }
                        case AND -> {
                            return Value.makeConstant(value1.getConstant() & value2.getConstant());
                        }
                        case XOR -> {
                            return Value.makeConstant(value1.getConstant() ^ value2.getConstant());
                        }
                        default -> throw new AnalysisException("unknown op");
                    }
                }
            }
            if (value1.isNAC() || value2.isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }
        throw new AnalysisException("exp is not binary exp");
    }
}
