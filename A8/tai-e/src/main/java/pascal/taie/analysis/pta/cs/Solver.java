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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import static pascal.taie.analysis.graph.callgraph.CallGraphs.getCallKind;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            csMethod.getMethod().getIR().getStmts().forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            Var var = stmt.getLValue();
            // 对于new语句来说，还需要考虑堆抽象，上课的时候讲过，然后我一开始写这里的时候全忘了...
            // 但是这里提到的是对于k层context selector，堆抽象的层数是k-1，和课上的例子并不一致
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            // 之前从pfg中获取的节点现在需要从csManager中获取
            CSObj csObj = csManager.getCSObj(heapContext, obj);
            CSVar csVar = csManager.getCSVar(context, var);
            // 这里应该创建一个新的PTS，而不是修改csVar的PTS
            PointsToSet pointsToSet = PointsToSetFactory.make(csObj);
            workList.addEntry(csVar, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar target = csManager.getCSVar(context, stmt.getLValue());
            CSVar source = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(source, target);
            return null;
        }

        // 静态变量有一点全局的感觉，所以是不考虑context的
        @Override
        public Void visit(StoreField stmt) {
            // T.f = y
            if (stmt.isStatic()) {
                CSVar source = csManager.getCSVar(context, stmt.getRValue());
                StaticField target = csManager.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // y = T.f
            if (stmt.isStatic()) {
                CSVar target = csManager.getCSVar(context, stmt.getLValue());
                StaticField source = csManager.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                // this.context就是caller context
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context calleeContext = contextSelector.selectContext(csCallSite, method);
                CSMethod csMethod = csManager.getCSMethod(calleeContext, method);
                // checkTaintStep由于污点变量的传递是单独的，如果放在addEdge中可能导致该边之前被迭代过而被放弃
                taintAnalysis.checkTaintStep(stmt, context);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csMethod))) {
                    taintAnalysis.checkSource(stmt, context);
                    addReachable(csMethod);
                    for (int i = 0; i < stmt.getInvokeExp().getArgCount(); i++) {
                        Var arg = stmt.getInvokeExp().getArg(i);
                        Var param = method.getIR().getParam(i);
                        CSVar csArg = csManager.getCSVar(context, arg);
                        CSVar csParam = csManager.getCSVar(calleeContext, param);
                        addPFGEdge(csArg, csParam);
                    }
                    Var retVar = stmt.getResult();
                    if (retVar != null) {
                        CSVar target = csManager.getCSVar(context, retVar);
                        method.getIR().getReturnVars().forEach(var -> {
                            CSVar source = csManager.getCSVar(calleeContext, var);
                            addPFGEdge(source, target);
                        });
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = entry.pointsToSet();
            PointsToSet diffObjs = propagate(pointer, pointsToSet);
            if (pointer instanceof CSVar) {
                Context context = ((CSVar) pointer).getContext();
                for (CSObj obj : diffObjs) {
                    Var var = ((CSVar) pointer).getVar();
                    // x.f = y
                    var.getStoreFields().forEach(storeField -> {
                        CSVar source = csManager.getCSVar(context, storeField.getRValue());
                        InstanceField target = csManager.getInstanceField(obj, storeField.getFieldAccess().getFieldRef().resolve());
                        addPFGEdge(source, target);
                    });
                    // y = x.f
                    var.getLoadFields().forEach(loadField -> {
                        CSVar target = csManager.getCSVar(context, loadField.getLValue());
                        InstanceField source = csManager.getInstanceField(obj, loadField.getFieldAccess().getFieldRef().resolve());
                        addPFGEdge(source, target);
                    });
                    // x[i] = y
                    var.getStoreArrays().forEach(storeArray -> {
                        ArrayIndex target = csManager.getArrayIndex(obj);
                        CSVar source = csManager.getCSVar(context, storeArray.getRValue());
                        addPFGEdge(source, target);
                    });
                    // y = x[i]
                    var.getLoadArrays().forEach(loadArray -> {
                        CSVar target = csManager.getCSVar(context, loadArray.getLValue());
                        ArrayIndex source = csManager.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    });
                    diffObjs.forEach(csObj -> {
                        if(taintAnalysis.isTaint(csObj)){
                            // 对将这个变量作为参数的调用也要进行污点传递
                            callGraph.edges().forEach(edge ->{
                                Invoke invoke = edge.getCallSite().getCallSite();
                                if(invoke.getInvokeExp().getArgs().contains(var)){
                                    taintAnalysis.checkTaintStep(invoke,edge.getCallSite().getContext());
                                }
                            });
                        }
                    });

                    // processCall里面将该变量作为recvObj的调用进行了污点传递
                    processCall((CSVar) pointer, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet diffObjs = PointsToSetFactory.make();
        PointsToSet originObjs = pointer.getPointsToSet();
        pointsToSet.forEach(csObj -> {
            if (originObjs.addObject(csObj)) {
                diffObjs.addObject(csObj);
            }
        });
        if (!diffObjs.isEmpty()) {
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, diffObjs));
        }
        return diffObjs;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Var recvVar = recv.getVar();
        // 直接取当前变量所在的context作为callerContext
        // 应当是只有在方法调用时才会创建context，所以在这里和static invoke处着重注意context的创建和分配即可
        Context callerContext = recv.getContext();
        recvVar.getInvokes().forEach(invoke -> {
            InvokeExp invokeExp = invoke.getInvokeExp();
            CSCallSite csCallSite = csManager.getCSCallSite(callerContext, invoke);
            JMethod method = resolveCallee(recvObj, invoke);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, method);
            CSMethod csMethod = csManager.getCSMethod(calleeContext, method);
            // 添加m_this，差点忘了
            CSVar csThis = csManager.getCSVar(calleeContext, method.getIR().getThis());
            workList.addEntry(csThis, PointsToSetFactory.make(recvObj));
            // 一旦obj有变就应当检查污点传播，如果放在addEdge里面可能导致先分析该调用再传播污点，从worklist取出污点时addEdge进不去
            // 根源在于用taintObj调用这个方法的时候这个边并不是一条新边?按道理来说如果是object sensitive的上下文应该是能区别的
            taintAnalysis.checkTaintStep(invoke, callerContext);
            if (callGraph.addEdge(new Edge<>(getCallKind(invokeExp), csCallSite, csMethod))) {
                // source的生成就第一次调用的时候触发一次，可以放里面降低工作量
                taintAnalysis.checkSource(invoke, callerContext);
                addReachable(csMethod);
                for (int i = 0; i < invokeExp.getArgCount(); i++) {
                    Var arg = invokeExp.getArg(i);
                    Var param = method.getIR().getParam(i);
                    CSVar csArg = csManager.getCSVar(callerContext, arg);
                    CSVar csParam = csManager.getCSVar(calleeContext, param);
                    addPFGEdge(csArg, csParam);
                }

                Var retVar = invoke.getResult();
                if (retVar != null) {
                    CSVar target = csManager.getCSVar(callerContext, retVar);
                    method.getIR().getReturnVars().forEach(var -> {
                        CSVar source = csManager.getCSVar(calleeContext, var);
                        addPFGEdge(source, target);
                    });
                }
            }
        });
    }


    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }

    public void addWorkListEntry(Pointer pointer, PointsToSet pointsToSet) {
        workList.addEntry(pointer, pointsToSet);
    }
}
