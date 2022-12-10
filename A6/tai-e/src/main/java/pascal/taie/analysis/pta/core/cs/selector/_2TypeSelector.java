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
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

/**
 * Implementation of 2-type sensitivity.
 */
public class _2TypeSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // TODO - finish me
        return callSite.getContext();
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // TODO - finish me
        Context callerContext = recv.getContext();
        // 上课的时候没认真听这段。。。type是用recvObj声明时所在的类作为type，而不是recvObj本身的type，怪
        Type type = recv.getObject().getContainerType();
        return switch (callerContext.getLength()) {
            case 0 -> ListContext.make(type);
            case 1 -> ListContext.make(callerContext.getElementAt(0), type);
            case 2 -> ListContext.make(callerContext.getElementAt(1), type);
            default -> throw new AnalysisException("invalid context lenght");
        };
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // TODO - finish me
        Context calleeContext = method.getContext();
        return switch (calleeContext.getLength()) {
            case 0 -> calleeContext;
            case 1 -> ListContext.make(calleeContext.getElementAt(0));
            case 2 -> ListContext.make(calleeContext.getElementAt(1));
            default -> throw new AnalysisException("invalid context lenght");
        };
    }
}
