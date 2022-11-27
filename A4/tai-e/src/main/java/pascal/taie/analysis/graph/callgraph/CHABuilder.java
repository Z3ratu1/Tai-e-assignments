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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.IR;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.*;
import pascal.taie.util.AnalysisException;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
//        Set<JMethod> reachableMethod = new HashSet<>();
        LinkedList<JMethod> worklist = new LinkedList<>();
        worklist.add(entry);
        while (!worklist.isEmpty()){
            JMethod method = worklist.poll();
            if(callGraph.addReachableMethod(method)){
                IR ir = method.getIR();
                for(Stmt stmt: ir.getStmts()){
                    if(stmt instanceof Invoke){
                        for (JMethod jMethod: resolve((Invoke) stmt)){
                            worklist.add(jMethod);
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind((Invoke) stmt), (Invoke) stmt, jMethod));
                        }
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> jMethods = new HashSet<>();
        switch (CallGraphs.getCallKind(callSite)){
            // 主要是好像也没有其他办法能拿到static的JMethod
            case STATIC, SPECIAL -> {
                JMethod jMethod = dispatch(callSite.getMethodRef().getDeclaringClass(), callSite.getMethodRef().getSubsignature());
                if (jMethod != null){
                    jMethods.add(jMethod);
                }else {
                    throw new AnalysisException("can't find method in STATIC/SPECIAL call");
                }
            }
            case VIRTUAL, INTERFACE -> {
                JClass jClass = callSite.getMethodRef().getDeclaringClass();
                Subsignature subsignature = callSite.getMethodRef().getSubsignature();
                // 继承应该不会出现环吧...就一个worklist应该就够了吧
                LinkedList<JClass> workList  = new LinkedList<>();
                workList.add(jClass);
                // java原来可以MyInter inter = new MyInterImpl()然后直接用实例化的接口对象调用方法啊...
                while (!workList.isEmpty()){
                    JClass clazz = workList.poll();
                    if(clazz.isInterface()) {
                        workList.addAll(hierarchy.getDirectSubinterfacesOf(clazz));
                        workList.addAll(hierarchy.getDirectImplementorsOf(clazz));
                    }else {
                        workList.addAll(hierarchy.getDirectSubclassesOf(clazz));
                    }
                    JMethod jMethod = dispatch(clazz, subsignature);
                    // 在给定一个接口类进行调用的时候，dispatch可能直接拿到接口类中声明的abstract方法，该方法是无法分析的
                    // 所以dispatch会丢弃这个方法，返回一个null，故此处接受返回值为null
                    if(jMethod != null){
                        jMethods.add(jMethod);
                    }
                }
            }
            default -> throw new AnalysisException("unknown call type");
        }
        return jMethods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        while (jclass != null){
            JMethod jMethod = jclass.getDeclaredMethod(subsignature);
            if(jMethod != null) {
                // 抽象方法不可被调用，但向上搜索时有可能找到抽象方法
                if(jMethod.isAbstract()){
                    return null;
                }else {
                    return jclass.getDeclaredMethod(subsignature);
                }
            }
            // 应该是传值不影响吧。。。
            jclass = jclass.getSuperClass();
        }
        return null;
    }
}
