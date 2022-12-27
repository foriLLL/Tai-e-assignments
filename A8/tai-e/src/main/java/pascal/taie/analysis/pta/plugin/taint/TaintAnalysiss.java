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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;


    public boolean containsSource(JMethod jMethod, Type type){
        return config.getSources().stream().anyMatch(source -> source.method().equals(jMethod) &&
                source.type().equals(type));
    }

    public boolean containsSink(JMethod jMethod, int index){
        return config.getSinks().stream().anyMatch(sink-> sink.method().equals(jMethod) &&
                sink.index() == index);
    }

    public boolean containsTransfer(JMethod jMethod, int from, int to, Type type) {
        return config.getTransfers().stream().anyMatch(taintTransfer -> taintTransfer.method().equals(jMethod) &&
                taintTransfer.from() == from &&
                taintTransfer.to() == to &&
                taintTransfer.type().equals(type));
    }

    public void transfer(CSCallSite csCallSite, CSVar recv) {
        Invoke callSite = csCallSite.getCallSite();
        Context context = csCallSite.getContext();

        JMethod method = callSite.getMethodRef().resolve();
        Type type = method.getReturnType();


        if (!method.isStatic()) {
            // base-to-result
            if (callSite.getLValue() != null) {
                Set<CSObj> basePointsToSet = solver.getResult().getPointsToSet(recv);
                if (containsTransfer(method, TaintTransfer.BASE, TaintTransfer.RESULT, type)) {
                    for (CSObj csObj : basePointsToSet) {
                        if (manager.isTaint(csObj.getObject())) {
                            Obj resultTaintObj = makeTaint(manager.getSourceCall(csObj.getObject()), callSite.getLValue().getType());
                            solver.addToList(csManager.getCSVar(context, callSite.getLValue()), PointsToSetFactory.make(csManager.getCSObj(context, resultTaintObj)));
                        }
                    }
                }
            }

            // arg-to-base
            for (int i = 0; i< method.getParamCount(); i++) {
                Set<CSObj> argIPointsToSet = solver.getResult().getPointsToSet(csManager.getCSVar(context, callSite.getInvokeExp().getArg(i)));
                for (CSObj csObj : argIPointsToSet) {
                    if (manager.isTaint(csObj.getObject()) && containsTransfer(method, i, TaintTransfer.BASE, type)) {
                        Obj baseTaintObj = makeTaint(manager.getSourceCall(csObj.getObject()), recv.getType());
                        solver.addToList(recv, PointsToSetFactory.make(csManager.getCSObj(context, baseTaintObj)));
                    }
                }
            }
        }


        // arg-to-result
        if (callSite.getLValue() != null) {
            for (int i = 0; i < method.getParamCount(); i++) {
                Set<CSObj> argIPointToSet = solver.getResult()
                        .getPointsToSet(csManager.getCSVar(context, callSite.getInvokeExp().getArg(i)));
                for (CSObj csObj : argIPointToSet) {
                    if (manager.isTaint(csObj.getObject()) && containsTransfer(method, i, TaintTransfer.RESULT, type)) {
                        Obj resultTaintObj = makeTaint(manager.getSourceCall(csObj.getObject()), callSite.getLValue().getType());
                        solver.addToList(csManager.getCSVar(context, callSite.getLValue()), PointsToSetFactory.make(csManager.getCSObj(context, resultTaintObj)));
                    }
                }
            }
        }
    }

    public Obj makeTaint(Invoke source, Type type) {
        return manager.makeTaint(source, type);
    }

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        CallGraph<Invoke, JMethod> callGraph = result.getCallGraph();
        callGraph.reachableMethods().forEach(method -> {
            for (Invoke callSite : callGraph.getCallSitesIn(method)) {
                JMethod callMethod = callSite.getMethodRef().resolve();
                for (int i = 0; i < callMethod.getParamCount(); i++) {
                    if (containsSink(callMethod, i)) {
                        for (Obj obj : result.getPointsToSet(callSite.getInvokeExp().getArg(i))) {
                            if (manager.isTaint(obj)) {
                                System.out.println("-".repeat(20));
                                System.out.println(manager.getSourceCall(obj));
                                System.out.println(callSite);
                                System.out.println(i);
                                System.out.println("-".repeat(20));
                                taintFlows.add(new TaintFlow(manager.getSourceCall(obj), callSite, i));
                            }
                        }
                    }
                }
            }
        });

        return taintFlows;
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }
}
