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
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;
import java.util.stream.Collectors;

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

        ArrayDeque<JMethod> workList = new ArrayDeque<>();
        workList.offer(entry);

        while(!workList.isEmpty()){
            JMethod curr = workList.poll();

            if(callGraph.contains(curr)){
                continue;
            }

            callGraph.addReachableMethod(curr);
            List<Stmt> invokes = curr.getIR().getStmts().stream().filter(stmt -> stmt instanceof Invoke).toList();
            for (Stmt stmt : invokes) {
                if(stmt instanceof Invoke invoke){
                    Set<JMethod> t = resolve(invoke);
                    for (JMethod target : t) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, target));
                        workList.offer(target);
                    }
                }else{
                    throw new IllegalStateException();
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
        Set<JMethod> res = new HashSet<>();

        CallKind callKind = CallGraphs.getCallKind(callSite);
        final JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();

        switch (callKind){
            case STATIC, SPECIAL -> res.add(dispatch(declaringClass, subsignature));

            default -> {
                Queue<JClass> queue = new ArrayDeque<>();
                queue.offer(declaringClass);

                while(!queue.isEmpty()){
                    JClass jClass = queue.poll();
                    JMethod dispatch = dispatch(jClass, subsignature);

                    if(dispatch != null){
                        res.add(dispatch);
                    }

                    if(jClass.isInterface()){
                        queue.addAll(hierarchy.getDirectImplementorsOf(jClass));
                        queue.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                    }else{
                        queue.addAll(hierarchy.getDirectSubclassesOf(jClass));
                    }
                }
            }
        }
        return res;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if(jclass == null) return null;

        System.out.println(jclass + " --> " + subsignature);
        JMethod declaredMethod = jclass.getDeclaredMethod(subsignature);
        if(declaredMethod != null && !declaredMethod.isAbstract()){
            return declaredMethod;
        }else{
            return dispatch(jclass.getSuperClass(), subsignature);
        }
    }
}
