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

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // generate empty set
        return new SetFact<>();
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // generate empty set
        return new SetFact<>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // just union
        target.union(fact);
    }

    // if in(out) changed, return true, else false
    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // record previous in
        SetFact<Var> origin = in.copy();
        // OUT[B]. but already exist item in "in" would not be removed, so use union is also ok
        in.set(out);
        // -def_B
//        if(stmt.getDef().isPresent()){
//            LValue def = stmt.getDef().orElse(null);
//            if(def instanceof Var){
//                in.remove((Var) def);
//            }
//        }
        // more elegant version from rmb
        stmt.getDef().ifPresent(def -> {
            if(def instanceof Var){
                in.remove((Var) def);
            }
        });
        // +use_B
//        if(stmt.getUses().size() > 0){
//            List<RValue> uses = stmt.getUses();
//            for (RValue use: uses) {
//                if (use instanceof Var) {
//                    in.add((Var) use);
//                }
//            }
//        }
        stmt.getUses().forEach(use ->{
            if (use instanceof Var) {
                    in.add((Var) use);
                }
        });
        return !origin.equals(in);
    }
}
