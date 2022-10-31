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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact cpFact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if(canHoldInt(param))
                cpFact.update(param, Value.getNAC());
        }
        return cpFact;
    }


    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.entries().forEach(varValueEntry -> {
            Var key = varValueEntry.getKey();
            Value value = varValueEntry.getValue();
            Value targetValue = target.get(key);    // UNDEF is absent
            target.update(key, meetValue(value, targetValue));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {// equals 重写为 kind 相同且 值相同
                return v1;
            } else {
                return Value.getNAC();
            }
        }


        if (v1.isConstant() || v2.isConstant()) {
            if (v1.isConstant()) return v1;
            return v2;
        }

        return Value.getUndef();

    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean change = false;

        for(Var key : in.keySet()){
            change |= out.update(key, in.get(key));
        }

        if(stmt instanceof DefinitionStmt<?, ?> def){
            LValue left = def.getLValue();
            if(left instanceof Var x){
                if(canHoldInt(x)){
                    Value res = evaluate(def.getRValue(), in);
                    change |= out.update(x, res);
                }
            }
        }
        return change;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var v) {
            return in.get(v);
        }

        if (exp instanceof IntLiteral i) {
            return Value.makeConstant(i.getValue());
        }

        if (!(exp instanceof BinaryExp b)){
            return Value.getNAC();
        }

        Value operand1 = in.get(b.getOperand1());
        Value operand2 = in.get(b.getOperand2());
        String operator = b.getOperator().toString();

        if(operand2.isConstant()
                &&
                operand2.getConstant() == 0
                &&
                ( operator.equals("/") || operator.equals("%") )
        ){
            return Value.getUndef();
        }

        if (operand1.isNAC() || operand2.isNAC()) {
            return Value.getNAC();
        }

        if (operand1.isConstant() && operand2.isConstant()) {
            int i1 = operand1.getConstant(), i2 = operand2.getConstant();
            int intValue = switch (operator) {
                case "+" -> i1 + i2;
                case "-" -> i1 - i2;
                case "*" -> i1 * i2;
                case "/" -> i1 / i2;
                case "%" -> i1 % i2;
                case "==" -> bool2int(i1 == i2);
                case "!=" -> bool2int(i1 != i2);
                case "<" -> bool2int(i1 < i2);
                case ">" -> bool2int(i1 > i2);
                case "<=" -> bool2int(i1 <= i2);
                case ">=" -> bool2int(i1 >= i2);

                case "<<" -> i1 << i2;
                case ">>" -> i1 >> i2;
                case ">>>" -> i1 >>> i2;

                case "|" -> i1 | i2;
                case "&" -> i1 & i2;
                case "^" -> i1 ^ i2;
                default -> throw new IllegalStateException("非法操作符");
            };
            return Value.makeConstant(intValue);
        } else {
            return Value.getUndef();
        }
    }

    private static int bool2int(boolean b) {
        return b ? 1 : 0;
    }
}
