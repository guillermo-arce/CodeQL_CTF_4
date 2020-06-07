import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.FlowSources


/* 

--------------------- Step 1.1: Source ---------------------

The sources of tainted data are the bean properties that go through constraint validation. In the code, 
these can be found as the first parameter of ConstraintValidator.isValid(...).

Write a CodeQL predicate that identifies these call arguments: */

predicate isSource_defined(DataFlow::Node source) { 
    exists(Method method |
        method instanceof IsValidMethod
        and source.asParameter() = method.getParameter(0)
    )
}

/**
 * Class containing isValid methods implemented from ConstraintValidator interface
 */
class IsValidMethod extends Method{
IsValidMethod(){
        this.getName() = "isValid" 
        and this.getDeclaringType().getASourceSupertype() instanceof ConstraintValidatorInterface
        and this.getAnAnnotation() instanceof OverrideAnnotation
    }
}

/**
 * Class representing ConstraintValidator
 */
class ConstraintValidatorInterface extends RefType {
ConstraintValidatorInterface(){ 
        this.hasQualifiedName("javax.validation", "ConstraintValidator") 
    }
}


/* 
--------------------- Step 1.2: Sink ---------------------

The injection sinks we are considering occur as the first argument of a call to 
ConstraintValidatorContext.buildConstraintViolationWithTemplate(...).

Write a CodeQL predicate to identify these sinks. */

predicate isSink_defined(DataFlow::Node sink) {
    exists(MethodAccess call |
        call instanceof BuildConstraintViolationWithTemplateCall
        and sink.asExpr() = call.getArgument(0)
    )
}

/**
 * Class containing buildConstraintViolationWithTemplate calls from ConstraintValidatorContext object
 */
class BuildConstraintViolationWithTemplateCall extends MethodAccess{
BuildConstraintViolationWithTemplateCall(){
        this.getMethod().getName() = "buildConstraintViolationWithTemplate" 
        and this.getMethod().getDeclaringType() instanceof ConstraintValidatorContext
    }
}

/**
 * Class representing ConstraintValidatorContext 
 */
class ConstraintValidatorContext extends RefType {
ConstraintValidatorContext(){ 
        this.hasQualifiedName("javax.validation", "ConstraintValidatorContext") 
    }
}


/* 
--------------------- Step 1.3: TaintTracking configuration ---------------------

You'll need to create a taint tracking configuration as explained in the CodeQL documentation. 

Fill in the template below with your definitions of isSource and isSink, and a nicer name. 
The predicate hasFlowPath will hold for any path through which data can flow from your sources to your sinks. 
As you checked that your predicates give you the correct sources and sinks, we'll get our vulnerability. */

import semmle.code.java.dataflow.TaintTracking
//import DataFlow::PathGraph //Conflict with PartialPathGraph

class TaintTracking_ConstraintValidator extends TaintTracking::Configuration {
    TaintTracking_ConstraintValidator() { this = "TaintTracking_ConstraintValidator" }

    override predicate isSource(DataFlow::Node source) { 
        isSource_defined(source)
    }

    override predicate isSink(DataFlow::Node sink) { 
        isSink_defined(sink)
    }
}


// from TaintTracking_ConstraintValidator cfg, DataFlow::PathNode source, DataFlow::PathNode sink
// where cfg.hasFlowPath(source, sink) 
// select source, sink, "Custom constraint error message contains unsanitized user data"


/* 
--------------------- Step 1.4: Partial Flow to the rescue ---------------------

You'll need to create a taint tracking configuration as explained in the CodeQL documentation. 

Fill in the template below with your definitions of isSource and isSink, and a nicer name. 
The predicate hasFlowPath will hold for any path through which data can flow from your sources to your sinks. 
As you checked that your predicates give you the correct sources and sinks, we'll get our vulnerability. */

import DataFlow::PartialPathGraph

class TaintTracking_ConstraintValidator_Debug extends TaintTracking::Configuration {
TaintTracking_ConstraintValidator_Debug() { this = "TaintTracking_ConstraintValidator_Debug" }

    override predicate isSource(DataFlow::Node source) { 
        isSource_defined(source)
    }

    override predicate isSink(DataFlow::Node sink) { 
        isSink_defined(sink)
    }

    override int explorationLimit() { result =  10}

}

class NodeToDebug extends DataFlow::Node{
    NodeToDebug(){
        isSource_defined(this)
        and this.getLocation().toString() = "SchedulingConstraintValidator:72"
        //SpELClassValidator:64
        //CollectionValidator:40
        //SchedulingConstraintValidator:72
        //SchedulingConstraintSetValidator:56
    }
}

// from TaintTracking_ConstraintValidator_Debug cfg, DataFlow::PartialPathNode source, DataFlow::PartialPathNode sink
// where
//   cfg.hasPartialFlow(source, sink, _) 
//   and source.getNode() instanceof  NodeToDebug
// select source, sink, "Partial flow from unsanitized user data"



/* 
--------------------- Step 1.5: Identifying a missing taint step ---------------------

You must have found that CodeQL does not propagate taint through getters like container.getHardConstraints and 
container.getSoftConstraints. Can you guess why this default behaviour was implemented?

---> -------------------------------

*/


/* 
--------------------- Step 1.6: Adding additional taint steps ---------------------

*/

class AddingTaintSteps extends TaintTracking::AdditionalTaintStep{
    override predicate step(DataFlow::Node src, DataFlow::Node sink){
        exists(MethodAccess ma |
            (ma.getMethod().getName()="getSoftConstraints" or 
                ma.getMethod().getName()="getHardConstraints"
                or ma.getMethod().getName()="keySet"
                    or ma.getMethod().getName()="stream"
                        or ma.getMethod().getName()="map"
                            or ma.getMethod().getName()="collect")
            and src.asExpr() = ma.getQualifier()
            and sink.asExpr() = ma  
        )
    }
}

class AddingTaintSteps_HashSet extends TaintTracking::AdditionalTaintStep {
override predicate step(DataFlow::Node src, DataFlow::Node sink) {
        exists(ConstructorCall cs |
            cs.getConstructedType().getCompilationUnit().getName()="HashSet"
            and src.asExpr() = cs.getAnArgument() 
            and sink.asExpr() = cs 
        )
    }
}

/* class AddingTaintSteps_TryCatch extends TaintTracking::AdditionalTaintStep {
override predicate step(DataFlow::Node src, DataFlow::Node sink) {
        exists(TryStmt ts, MethodAccess ma1, MethodAccess ma2|
            ma1.get
            and ma.getMethod().getName() = "getMessage"
            and ma.getBasicBlock() = ts.getACatchClause().getBasicBlock()
            and sink.asExpr() = ma
        )
    }
} */



/* from CatchClause cc, MethodAccess ma
where ma.getMethod().getName()="getMessage" and ma.getBasicBlock() = cc.getBasicBlock()
select ma,cc,ma.getBasicBlock(),cc.getBasicBlock()
 */