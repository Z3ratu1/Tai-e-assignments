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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(callGraph.addReachableMethod(method)){
            Collection<Stmt> stmts = method.getIR().getStmts();
            // 突然发现ReachableStmts好像用不上...?
            for (Stmt stmt:stmts) {
                // 访问者模式，会利用多态调用到stmtProcessor的不同类型的方法
                stmt.accept(stmtProcessor);
            }

        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        // 并不需要一个专门存reachable stmt的地方，在addReachable中直接把所有reachable stmt遍历即可

        @Override
        public Void visit(New stmt) {
            // x = new A();
            Var var = stmt.getLValue();
            Obj newObj = heapModel.getObj(stmt);
            // 虽然这里x是新对象，但是也可以直接去问PFG要，因为getVarPtr的实现就是如果不存在则创建一个新的，并更新到PFG中
            // 由后续代码合并，并触发更新后的store和load等操作
            Pointer varPtr = pointerFlowGraph.getVarPtr(var);
            PointsToSet set = new PointsToSet(newObj);
            workList.addEntry(varPtr, set);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y;
            Var source = stmt.getRValue();
            Var target = stmt.getLValue();
            Pointer sourcePtr = pointerFlowGraph.getVarPtr(source);
            Pointer targetPtr = pointerFlowGraph.getVarPtr(target);
            // source为空在addEdge中检查，同上，无需考虑是否需要新建，该方法不存在则新建
            addPFGEdge(sourcePtr, targetPtr);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // y = x.f
            // y = T.f
            // 只处理静态类型的LoadField，感觉静态类型的这个赋值其实更倾向于Copy类型的stmt
            // 对于形如y=x.f类型的load语句不能在addreachable的原因是f需要x确定的前提，而静态字段则无所谓
            if(stmt.isStatic()){
                Pointer staticField = pointerFlowGraph.getStaticField(stmt.getRValue().getFieldRef().resolve());
                Pointer target = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(staticField, target);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // y.f = x
            // T.f = x
            // 同上只处理static field
            if(stmt.isStatic()){
                Pointer source = pointerFlowGraph.getVarPtr(stmt.getRValue());
                Pointer staticField = pointerFlowGraph.getStaticField(stmt.getLValue().getFieldRef().resolve());
                addPFGEdge(source, staticField);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            // 处理静态调用
            InvokeExp invokeExp = stmt.getInvokeExp();
            if(getCallKind(invokeExp) == CallKind.STATIC) {
                // null 用于解析静态方法和special方法
                JMethod method = resolveCallee(null, stmt);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, method))) {
                    addReachable(method);
                    for (int i = 0; i < invokeExp.getArgCount(); i++) {
                        Pointer source = pointerFlowGraph.getVarPtr(invokeExp.getArg(i));
                        Pointer target = pointerFlowGraph.getVarPtr(method.getIR().getParam(i));
                        addPFGEdge(source, target);
                    }
                    Var retVar = stmt.getResult();
                    if (retVar != null) {
                        for (Var ret : method.getIR().getReturnVars()) {
                            Pointer retSource = pointerFlowGraph.getVarPtr(ret);
                            addPFGEdge(retSource, pointerFlowGraph.getVarPtr(retVar));
                        }
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
        if(pointerFlowGraph.addEdge(source, target)){
            // 应当保证算法中source是一个已经存在的节点，target是一个空的节点
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        List<JMethod> entryList = callGraph.entryMethods().toList();
        if(entryList.size() != 1){
            throw new AnalysisException("more than one entry method");
        }
        addReachable(entryList.get(0));
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet objs = entry.pointsToSet();

            PointsToSet diffObjs = propagate(pointer, objs);
            if (pointer instanceof VarPtr) {
                Var var = ((VarPtr) pointer).getVar();
                // 对于Δ做store和load的同步
                for (Obj obj : diffObjs) {
                    // y = x.f; LoadField继承stmt
                    var.getLoadFields().forEach(loadField-> {
                        FieldAccess fieldAccess = loadField.getFieldAccess();
                        Pointer instanceField = pointerFlowGraph.getInstanceField(obj, fieldAccess.getFieldRef().resolve());
                        addPFGEdge(instanceField, pointerFlowGraph.getVarPtr(loadField.getLValue()));
                    });
                    // x.f = y;
                    var.getStoreFields().forEach(storeField-> {
                        FieldAccess fieldAccess = storeField.getFieldAccess();
                        Pointer instanceField = pointerFlowGraph.getInstanceField(obj, fieldAccess.getFieldRef().resolve());
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()), instanceField);
                    });
                    // Var有loadarr和storearr方法...白瞎半天
                    // y = x[i]
                    var.getLoadArrays().forEach(loadArray -> {
                        // 没有必要取base，这里的var本身就是base
                        Pointer target = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        // 同时obj即为var中的新增obj
                        Pointer source = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    });
                    // x[i] = y
                    var.getStoreArrays().forEach(storeArray -> {
                        Pointer source = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        Pointer target = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    });
                    processCall(((VarPtr) pointer).getVar(), obj);
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
        PointsToSet originObjs;
        PointsToSet diffObjs = new PointsToSet();
        if(pointer instanceof VarPtr){
            // 从图中获取原来的obj set，套了好几层。。。需要用Ptr获取Var作为键查PFG，然后得到的是一个新的Ptr，然后从Ptr里拿到obj set
            originObjs = pointerFlowGraph.getVarPtr(((VarPtr) pointer).getVar()).getPointsToSet();
        } else if (pointer instanceof StaticField) {
            originObjs = pointerFlowGraph.getStaticField(((StaticField) pointer).getField()).getPointsToSet();
        } else if (pointer instanceof InstanceField) {
            originObjs = pointerFlowGraph.getInstanceField(((InstanceField) pointer).getBase(), ((InstanceField) pointer).getField()).getPointsToSet();
        } else if (pointer instanceof ArrayIndex) {
            originObjs = pointerFlowGraph.getArrayIndex(((ArrayIndex) pointer).getArray()).getPointsToSet();
        }else {
            throw new AnalysisException("invalid pointer type");
        }
        for (Obj obj:pointsToSet) {
            // 进行合并，并把新增项找出来
            if(originObjs.addObject(obj)){
                diffObjs.addObject(obj);
            }
        }
        // 把所有后继添加进worklist等待更新
        if(!diffObjs.isEmpty()){
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, diffObjs));
        }
        return diffObjs;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        var.getInvokes().forEach(invoke -> {
            JMethod method = resolveCallee(recv, invoke);
            IR ir = method.getIR();
            InvokeExp invokeExp = invoke.getInvokeExp();
            workList.addEntry(pointerFlowGraph.getVarPtr(ir.getThis()), new PointsToSet(recv));
            if(callGraph.addEdge(new Edge<>(getCallKind(invokeExp), invoke, method))) {
                addReachable(method);
                for (int i = 0; i < invokeExp.getArgCount(); i++) {
                    Pointer source = pointerFlowGraph.getVarPtr(invokeExp.getArg(i));
                    Pointer target = pointerFlowGraph.getVarPtr(ir.getParam(i));
                    addPFGEdge(source, target);
                }
                Var retVal = invoke.getResult();
                if (retVal != null) {
                    ir.getReturnVars().forEach(ret -> {
                        // 应该是把调用返回值对应的变量关联上去，这里一开始关联了recvObj...
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(retVal));
                    });
                }
            }
        });
    }


    public static CallKind getCallKind(InvokeExp invokeExp) {
        if (invokeExp instanceof InvokeVirtual) {
            return CallKind.VIRTUAL;
        } else if (invokeExp instanceof InvokeInterface) {
            return CallKind.INTERFACE;
        } else if (invokeExp instanceof InvokeSpecial) {
            return CallKind.SPECIAL;
        } else if (invokeExp instanceof InvokeStatic) {
            return CallKind.STATIC;
        } else if (invokeExp instanceof InvokeDynamic) {
            return CallKind.DYNAMIC;
        } else {
            throw new AnalysisException("Cannot handle InvokeExp: " + invokeExp);
        }
    }
    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
