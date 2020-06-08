/**
* Hi, my name is Guillermo Arce
* Welcome to my CodeQL solution to CTF 4 - CodeAndChill
*/

import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph //Conflict with PartialPathGraph


// --------------------- SOURCE --------------------- 

/** Definition of source */
predicate isSource_definition(DataFlow::Node source) { 
    exists(Method method |
        method instanceof IsValidMethod
        and source.asParameter() = method.getParameter(0)
    )
}

/** Auxiliar class containing isValid methods implemented from ConstraintValidator interface */
class IsValidMethod extends Method{
    IsValidMethod(){
        this.getName() = "isValid" 
        and this.getDeclaringType().getASourceSupertype() instanceof ConstraintValidatorInterface
        and this.getAnAnnotation() instanceof OverrideAnnotation
    }
}

/** Auxiliar class representing ConstraintValidator interface */
class ConstraintValidatorInterface extends RefType {
ConstraintValidatorInterface(){ 
        this.hasQualifiedName("javax.validation", "ConstraintValidator") 
    }
}


// --------------------- SINK ---------------------  

/** Definition of sink */
predicate isSink_definition(DataFlow::Node sink) {
    exists(MethodAccess call |
        call instanceof BuildConstraintViolationWithTemplateCall
        and sink.asExpr() = call.getArgument(0)
    )
}

/** Auxiliar class containing buildConstraintViolationWithTemplate calls from ConstraintValidatorContext object */
class BuildConstraintViolationWithTemplateCall extends MethodAccess{
    BuildConstraintViolationWithTemplateCall(){
        this.getMethod().getName() = "buildConstraintViolationWithTemplate" 
        and this.getMethod().getDeclaringType() instanceof ConstraintValidatorContext
    }
}

/** Auxiliar class representing ConstraintValidatorContext */
class ConstraintValidatorContext extends RefType {
ConstraintValidatorContext(){ 
        this.hasQualifiedName("javax.validation", "ConstraintValidatorContext") 
    }
}


// --------------------- TAINT TRACKING CONFIG ---------------------

import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph //Conflict with PartialPathGraph

class ConstraintValidator_Config extends TaintTracking::Configuration {
    ConstraintValidator_Config() { this = "ConstraintValidator_Config" }
    
    override predicate isSource(DataFlow::Node source) { 
        isSource_definition(source)
    }
    override predicate isSink(DataFlow::Node sink) { 
        isSink_definition(sink)
    }
}

from ConstraintValidator_Config cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "Custom constraint error message contains unsanitized user data"


// --------------------- ADDITIONAL TAINT STEPS ---------------------

/** Step for methods that were interfering the taint path and shouldn't */
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
/** Step for constructor of HashSet */
class AddingTaintSteps_HashSet extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node src, DataFlow::Node sink) {
        exists(ConstructorCall cs |
            cs.getConstructedType().getCompilationUnit().getName()="HashSet"
            and src.asExpr() = cs.getAnArgument() 
            and sink.asExpr() = cs 
        )
    }
}
/** Step for try catch */
class AddingTaintSteps_TryCatch extends TaintTracking::AdditionalTaintStep {
override predicate step(DataFlow::Node src, DataFlow::Node sink) {
    exists(TryStmt ts, MethodAccess ma1, MethodAccess ma2|
    
        ts.getEnclosingCallable() = ma1.getEnclosingCallable()
        and ts.getAChild().getAChild() = ma1.getEnclosingStmt()
        and src.asExpr() = ma1.getAnArgument() 

        and ts.getACatchClause().getEnclosingCallable() = ma2.getEnclosingCallable()
        and ts.getACatchClause().getAChild().getAChild() = ma2.getEnclosingStmt()
        and ma2.getQualifier().getType() instanceof LoggerClass
        and ma2.getMethod().getName() = "error"
        and sink.asExpr() = ma2.getAnArgument() //Intuitivelly I would say it is sink.asExpr() = ma2 in order to show the call as a taint,
                                                //but I am getting 0 results when I do it.
    )
    }
}

/** Auxiliary class for getting the Logger class */
class LoggerClass extends RefType {
LoggerClass(){ 
    this.hasQualifiedName("org.slf4j", "Logger") 
}
}


/* Query for Try Catch step study

from TryStmt ts, MethodAccess ma1, MethodAccess ma2, DataFlow::Node src, DataFlow::Node sink
where 
ts.getEnclosingCallable() = ma1.getEnclosingCallable()
and ts.getAChild().getAChild() = ma1.getEnclosingStmt()
and src.asExpr() = ma1 
and ts.getACatchClause().getEnclosingCallable() = ma2.getEnclosingCallable()
and ts.getACatchClause().getAChild().getAChild() = ma2.getEnclosingStmt()
and ma2.getQualifier().getType() instanceof LoggerClass
and ma2.getMethod().getName() = "error"
and sink.asExpr() = ma2.getAnArgument()
select ts,src,sink */


// --------------------- PARTIAL TAINT TRACKING  ---------------------

/* Commented due to conflict with DataFlow::PathGraph

import DataFlow::PartialPathGraph

class ConstraintValidator_Config_Debug extends TaintTracking::Configuration {
    ConstraintValidator_Config_Debug() { this = "ConstraintValidator_Config_Debug" }

    override predicate isSource(DataFlow::Node source) { 
        isSource_definition(source)(source)
    }

    override predicate isSink(DataFlow::Node sink) { 
        isSink_definition(sink)
    }

    override int explorationLimit() { result =  10}

} */

/** Auxiliar class used to restrict to a specified source */
class NodeToDebug extends DataFlow::Node{
    NodeToDebug(){
        isSource_definition(this)
        and this.getLocation().toString() = "SchedulingConstraintValidator:72"
    }
}

/* from ConstraintValidator_Config_Debug cfg, DataFlow::PartialPathNode source, DataFlow::PartialPathNode sink
where
  cfg.hasPartialFlow(source, sink, _) 
  and source.getNode() instanceof  NodeToDebug
select sink, source, sink, "Partial flow from unsanitized user data" */

