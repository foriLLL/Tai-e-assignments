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
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import soot.util.StationaryArrayList;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
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
        if (callGraph.addReachableMethod(csMethod)) { // do changed
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
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
            Obj obj = heapModel.getObj(stmt);
            CSObj csObj = csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj);
            CSVar varPtr = csManager.getCSVar(context, stmt.getLValue());
            workList.addEntry(varPtr, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Pointer s = csManager.getCSVar(context, stmt.getRValue());
            Pointer t = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(s, t);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {    // 静态 store
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Var y = stmt.getRValue();
                addPFGEdge(csManager.getCSVar(context, y), csManager.getStaticField(field));
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {     // 静态 load
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Var y = stmt.getLValue();
                addPFGEdge(csManager.getStaticField(field), csManager.getCSVar(context, y));
            }
            return null;
        }

        @Override
        public Void visit(Invoke invokeStmt) {   // 静态调用
            if (invokeStmt.isStatic()) {
                JMethod staticMethod = resolveCallee(null, invokeStmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, invokeStmt);   // 当前context下的callsite
                Context ct = contextSelector.selectContext(csCallSite, staticMethod);   // 获取静态调用的context

                paramNreturn(invokeStmt, staticMethod, context, csCallSite, ct);
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
            PointsToSet delta = propagate(pointer, pointsToSet);

            if (pointer instanceof CSVar csVar) {
                Var var = csVar.getVar();
                Context context = csVar.getContext();

                for (CSObj csObj : delta) {
                    for (StoreField storeField : var.getStoreFields()) {
                        addPFGEdge(csManager.getCSVar(context, storeField.getRValue()),
                                csManager.getInstanceField(csObj, storeField.getFieldRef().resolve()));
                    }
                    for (LoadField loadField : var.getLoadFields()) {
                        addPFGEdge(csManager.getInstanceField(csObj, loadField.getFieldRef().resolve()),
                                csManager.getCSVar(context, loadField.getLValue()));
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        addPFGEdge(csManager.getCSVar(context, storeArray.getRValue()),
                                csManager.getArrayIndex(csObj));
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        addPFGEdge(csManager.getArrayIndex(csObj),
                                csManager.getCSVar(context, loadArray.getLValue()));
                    }
                    processCall(csVar, csObj);
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
        PointsToSet delta = PointsToSetFactory.make();
        for (CSObj newObj : pointsToSet) {
            if (pointer.getPointsToSet().addObject(newObj)) {
                delta.addObject(newObj);
            }
        }
        if (!delta.isEmpty()) {
            for (Pointer success : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(success, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (Invoke invoke : recv.getVar().getInvokes()) {
            JMethod m = resolveCallee(recvObj, invoke);
            Context context = recv.getContext();
            CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
            Context ct = contextSelector.selectContext(csCallSite, recvObj, m);
            workList.addEntry(csManager.getCSVar(ct, m.getIR().getThis()), PointsToSetFactory.make(recvObj));

            paramNreturn(invoke, m, context, csCallSite, ct);
        }
    }

    private void paramNreturn(Invoke invoke, JMethod m, Context context, CSCallSite csCallSite, Context ct) {
        CSMethod csMethod = csManager.getCSMethod(ct, m);
        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csMethod))) {
            addReachable(csMethod);
            for (int i = 0; i < m.getParamCount(); i++) {
                Var param = m.getIR().getParam(i);
                Var arg = csCallSite.getCallSite().getInvokeExp().getArg(i);// c: ai
                CSVar source = csManager.getCSVar(context, arg);
                CSVar target = csManager.getCSVar(ct, param);
                addPFGEdge(source, target);
            }
        }
        // return edge
        if (invoke.getLValue() != null) {
            for (Var returnVar : m.getIR().getReturnVars()) {
                CSVar source = csManager.getCSVar(ct, returnVar);
                CSVar target = csManager.getCSVar(context, invoke.getLValue());
                addPFGEdge(source, target);
            }
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
