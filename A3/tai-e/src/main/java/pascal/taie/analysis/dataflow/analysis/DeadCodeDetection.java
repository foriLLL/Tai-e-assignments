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

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me

        Queue<Stmt> queue = new ArrayDeque<>(); // BFS
        queue.offer(cfg.getEntry());

        deadCode.addAll(cfg.getNodes());     // 先假设都不可达
        deadCode.remove(cfg.getExit());
        while(!queue.isEmpty()){
            Stmt stmt = queue.poll();
            if(!deadCode.contains(stmt)){
                continue;
            }

            if(stmt instanceof If ifStmt){
                deadCode.remove(ifStmt);
                Value condition = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt));
                if(condition.isConstant()) {
                    int conditionRes = condition.getConstant();
                    Edge.Kind edge2go = conditionRes == 1 ? Edge.Kind.IF_TRUE : Edge.Kind.IF_FALSE;

                    // 将要走的分支加入queue 并从 dead 中删除
                    cfg.getOutEdgesOf(ifStmt)
                            .stream().filter(e -> e.getKind() == edge2go)
                            .findFirst().ifPresent(edge -> {
                                Stmt edgeTarget = edge.getTarget();
                                queue.offer(edgeTarget);
                            });
                    continue;
                }
            }else if(stmt instanceof SwitchStmt switchStmt){
                deadCode.remove(switchStmt);
                Value condition = constants.getInFact(switchStmt).get(switchStmt.getVar());
                if(condition.isConstant()){
                    // 是常数，从edges找对应，找不到就是default
                    int conditionValue = condition.getConstant();
                    Stmt target;
                    Optional<Edge<Stmt>> optionalEdge = cfg.getOutEdgesOf(switchStmt).stream()
                            .filter(Edge::isSwitchCase)
                            .filter(e -> e.getCaseValue() == conditionValue)
                            .findFirst();
                    if(optionalEdge.isPresent()){
                        target = optionalEdge.get().getTarget();
                    }else{
                        // default
                        target = switchStmt.getDefaultTarget();
                    }
                    queue.offer(target);
                    continue;
                }
            }else if(stmt instanceof AssignStmt<?, ?> assignStmt){
                if(hasNoSideEffect(assignStmt.getRValue())
                        && assignStmt.getLValue() instanceof Var lVar
                        && !liveVars.getOutFact(assignStmt).contains(lVar)){
                    // 没有副作用 且 不被需要
                    queue.addAll(cfg.getSuccsOf(stmt));
                    continue;
                }
            }
            deadCode.remove(stmt);
            queue.addAll(cfg.getSuccsOf(stmt));
        }

        System.out.println(deadCode);

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
