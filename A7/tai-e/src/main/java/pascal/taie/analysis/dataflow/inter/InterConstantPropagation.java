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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import javax.swing.*;
import java.rmi.UnexpectedException;
import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    // ********
    private Map<JField, Set<StoreField>> staticFieldWithMetStoreFields;
    private Map<Var, Set<Var>> aliases;
    private PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        this.pta = pta;
        this.staticFieldWithMetStoreFields = new HashMap<>();
        this.aliases = new HashMap<>();

        // establish aliases
        // 注意 a和b是别名，a和c是别名，b和c不一定是别名 所以不能用聚类并查集什么的，简单的解决方案是每一个变量维护一个别名
        Collection<Var> vars = pta.getVars();
        for (Var var : vars) {
            for (Obj obj : pta.getPointsToSet(var)) {
                for (Var var2check : vars) {
                    if (pta.getPointsToSet(var2check).contains(obj)) {    //有交集
                        putAlias(var, var2check);
                        putAlias(var2check, var);
                    }
                }
            }
        }

        // establish staticFieldWithMetStoreFields
        for (Stmt stmt : icfg) {
            if (stmt instanceof StoreField storeFieldStmt && storeFieldStmt.isStatic()) {
                //static field store
                JField staticField = storeFieldStmt.getFieldRef().resolve();
                if (staticFieldWithMetStoreFields.containsKey(staticField)) {
                    staticFieldWithMetStoreFields.get(staticField).add(storeFieldStmt);
                } else {
                    staticFieldWithMetStoreFields.put(staticField, new HashSet<>(Set.of(storeFieldStmt)));
                }

            }
        }

    }

    public boolean isAlias(Var a, Var b) {
        for (Obj obj : pta.getPointsToSet(a)) {
            if (pta.getPointsToSet(b).contains(obj)) {
                return true;
            }
        }
        return false;
    }

    private void putAlias(Var self, Var alias) {
        if (aliases.containsKey(self)) {
            aliases.get(self).add(alias);
        } else {
            aliases.put(self, new HashSet<>(Set.of(alias)));
        }
    }


    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean change = false;
        for (Var var : in.keySet()) {
            change |= out.update(var, in.get(var));
        }
        return change;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean change = false;

        for (Var key : in.keySet()) { // transfer in to out
            change |= out.update(key, in.get(key));
        }

        if (stmt instanceof LoadField loadFieldStmt) {
            if (loadFieldStmt.isStatic()) {     // static, x = T.f
                Var lVar = loadFieldStmt.getLValue();
                JField field = loadFieldStmt.getFieldRef().resolve();
                Value metValue = staticFieldWithMetStoreFields.get(field).stream()
                        .map(relatedStoreStmt -> {
//                            System.out.println("*********" + solver.getStmtInFact(relatedStoreStmt).get(relatedStoreStmt.getRValue()));
                            solver.add2worklist(relatedStoreStmt);
                            return solver.getStmtInFact(relatedStoreStmt).get(relatedStoreStmt.getRValue());
                        })
                        .reduce(cp::meetValue)
                        .orElseGet(Value::getUndef);
                return out.update(lVar, metValue) || change;
            } else {    // instance     x = a.f
                InstanceFieldAccess instanceFieldAccess = (InstanceFieldAccess) loadFieldStmt.getFieldAccess();
                Var baseVar = instanceFieldAccess.getBase();
                if (!aliases.containsKey(baseVar)) {
                    throw new RuntimeException("找不到base变量");
                }

                Value lValue = Value.getUndef();

                for (Var alias : aliases.get(baseVar)) {
                    for (StoreField storeField : alias.getStoreFields()) {
                        // 判断是不是同一个field
                        if (storeField.getFieldRef().resolve().equals(loadFieldStmt.getFieldRef().resolve())) {  // bug：可以这么判断吗？
                            // 是，拿到右值 因为分析的是IR，所以不用考虑 a.f = T.f' 的情况
                            Value valueFromAlias = in.get(storeField.getRValue());
                            lValue = cp.meetValue(valueFromAlias, lValue);
                        }
                        if (lValue == Value.getNAC()) break;
                    }
                    if (lValue == Value.getNAC()) break;
                }
                return out.update(loadFieldStmt.getLValue(), lValue) || change;
            }
        } else if (stmt instanceof LoadArray loadArrayStmt) {     // x = a[i]
            ArrayAccess arrayAccess = loadArrayStmt.getArrayAccess();

            Var baseVar = arrayAccess.getBase();
            if (!aliases.containsKey(baseVar)) {
                throw new RuntimeException("找不到base变量");
            }

            Var i = arrayAccess.getIndex();
            Value lValue = Value.getUndef();
            for (Var alias : aliases.get(baseVar)) {
                for (StoreArray storeArray : alias.getStoreArrays()) {  // b[j] = y
                    Var j = storeArray.getArrayAccess().getIndex();
                    if (checkIndexIfAlias(i, j, in)) {
                        Value valueFromAlias = in.get(storeArray.getRValue());
                        lValue = cp.meetValue(valueFromAlias, lValue);
                    }
                    if (lValue == Value.getNAC()) break;
                }
                if (lValue == Value.getNAC()) break;
            }
            return out.update(loadArrayStmt.getLValue(), lValue) || change;
        } else {
            return cp.transferNode(stmt, in, out);  // 这里其实不用 || change
        }
    }

    private boolean checkIndexIfAlias(Var i, Var j, CPFact in) {
        Value iVal = in.get(i);
        Value jVal = in.get(j);
        if (iVal == Value.getUndef() || jVal == Value.getUndef()) {
            return false;
        }
        if (iVal == Value.getNAC() || jVal == Value.getNAC()) {
            return true;
        }
        return iVal.equals(jVal);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact copy = out.copy();
        LValue callSiteDef = edge.getSource().getDef().orElse(null);
        if (callSiteDef instanceof Var lVar) {
            copy.remove(lVar);
        }
        return copy;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact newFact = new CPFact();

        if (edge.getSource() instanceof Invoke invoke) {
            List<Var> params2Fill = edge.getCallee().getIR().getParams();
            List<Var> actualArgs = invoke.getInvokeExp().getArgs();

            assert params2Fill.size() == actualArgs.size();

            for (int i = 0; i < params2Fill.size(); i++) {
                if (ConstantPropagation.canHoldInt(params2Fill.get(i))) {
                    newFact.update(params2Fill.get(i), callSiteOut.get(actualArgs.get(i)));
                }
            }
        }
        return newFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact newFact = new CPFact();
        LValue callSiteDef = edge.getCallSite().getDef().orElse(null);

        if (callSiteDef instanceof Var var) {
            for (Var returnVar : edge.getReturnVars()) {
                if (ConstantPropagation.canHoldInt(returnVar)) {
                    newFact.update(var, cp.meetValue(newFact.get(var), returnOut.get(returnVar)));
                }
            }
        }
        return newFact;
    }
}
