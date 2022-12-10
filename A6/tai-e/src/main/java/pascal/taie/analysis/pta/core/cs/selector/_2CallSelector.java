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

package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;

/**
 * Implementation of 2-call-site sensitivity.
 */
public class _2CallSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // TODO - finish me
        // call site本身就不考虑recv obj,照抄
        return selectContext(callSite, null, callee);
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // TODO - finish me
        // 这里输入的应该是之前调用的上下文，需要把第一个上下文pop出去然后append一个这个callsite上去
        // 也不对，还得判断一下长度，没到两层就直接append上去就可以了，get方法如果超过下标会throw error
        Invoke invoke = callSite.getCallSite();
        Context callerContext = callSite.getContext();
        // IDEA的超级优化语法，真高级啊
        return switch (callerContext.getLength()) {
            case 0 -> ListContext.make(invoke);
            case 1 -> ListContext.make(callerContext.getElementAt(0), invoke);
            case 2 -> ListContext.make(callerContext.getElementAt(1), invoke);
            default -> throw new AnalysisException("invalid context lenght");
        };
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // TODO - finish me
        // 一层的堆上下文，这里的method直接是callee context，和上面两个方法不一样
        // 因为上面两个方法本身是一层调用，需要添加被调函数上下文，这里是在被调函数中使用new，把被调函数的这一层context拿出来就行
        Context calleeContext = method.getContext();
        return switch (calleeContext.getLength()) {
            case 0 -> calleeContext;
            case 1 -> ListContext.make(calleeContext.getElementAt(0));
            case 2 -> ListContext.make(calleeContext.getElementAt(1));
            default -> throw new AnalysisException("invalid context lenght");
        };
    }
}
