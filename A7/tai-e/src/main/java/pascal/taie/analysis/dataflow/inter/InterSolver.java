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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.AnalysisException;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        workList = new LinkedList<>();
        for (Node node: icfg.getNodes()) {
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
        // 怎么拿到整个的入口？虽然我感觉应该第一个就是。。。
        List<Method> entryMethod = icfg.entryMethods().toList();
        if(entryMethod.size() != 1){
            throw new AnalysisException("error entry method number");
        }
        Node entry = icfg.getEntryOf(entryMethod.get(0));
        // 后向分析应该只需要初始化out?
        result.setOutFact(entry, analysis.newBoundaryFact(entry));
    }

    private void doSolve() {
        // TODO - finish me
        // 感觉上都是照着原来的抄就行了?
        workList.addAll(icfg.getNodes());
        while (!workList.isEmpty()){
            Node node = workList.poll();
            Fact inFact = result.getInFact(node);
            Fact outFact = result.getOutFact(node);
            // 先merge出当前节点的inFact
            for (ICFGEdge<Node> edge:icfg.getInEdgesOf(node)) {
                Node prev = edge.getSource();
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(prev)), inFact);
            }
            // transfer之后有变化
            if(analysis.transferNode(node, inFact, outFact)){
                // 对于get set方法而言，如果先处理get方法再处理set方法就会出问题，
                workList.addAll(icfg.getSuccsOf(node));
            }
        }
    }

    public Fact getInFact(Node node){
        return result.getInFact(node);
    }
    public void AddWorkList(Node node){
        workList.add(node);
    }
}
