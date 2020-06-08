# CodeQL-CTF4
Hunt for a recently identified vulnerability in a popular container management platform. 
This vulnerability enabled attackers to inject arbitrary Java EL expressions, leading to a pre-auth Remote Code Execution (RCE) 
vulnerability.  Using CodeQL to track tainted data from a user-controlled bean property to a custom error message, you'll learn to 
fill in any gaps in the taint tracking to carve a full data flow path to the vulnerability.

## My solution to the CTF
Hi, my name is Guillermo Arce and I am a software engineering student from Spain.
My solution to the CTF is presented below:
### Step 1: Data flow and taint tracking analysis
As the base of the taint tracking analysis, we are going to define **source** and **sink** of the desired vulnerability.
#### Source
In order to define the source as clear as possible, two auxiliary classes have been defined:
```
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
```
Now we can directly define our source with the following predicate:
```
/** Definition of source */
predicate isSource_definition(DataFlow::Node source) { 
    exists(Method method |
        method instanceof IsValidMethod
        and source.asParameter() = method.getParameter(0)
    )
}
```
#### Sink
Following the same procedure as for the source, we define the sink with the support of other two auxiliary classes:
```
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
```
Now, we can also get our sinks with the following predicate:
```
/** Definition of sink */
predicate isSink_definition(DataFlow::Node sink) {
    exists(MethodAccess call |
        call instanceof BuildConstraintViolationWithTemplateCall
        and sink.asExpr() = call.getArgument(0)
    )
}
```
#### TaintTracking configuration
Following the typical procedure, we arrive to the point in which we define the TaintTracking configuration in order to get
the path from the source nodes to the sink ones. For that purpose, after adding the correspondent imports, 
we create a class extending TaintTracking::Configuration as the following:
```
class ConstraintValidator_Config extends TaintTracking::Configuration {
    ConstraintValidator_Config() { this = "ConstraintValidator_Config" }
    
    override predicate isSource(DataFlow::Node source) { 
        isSource_definition(source)
    }
    override predicate isSink(DataFlow::Node sink) { 
        isSink_definition(sink)
    }
}

```
Now, we can write the query that will report the vulnerable path:
```
from ConstraintValidator_Config cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink) 
select sink, source, sink, "Custom constraint error message contains unsanitized user data"
```
#### Partial Flow to the rescue
We have set everything that we need in order to report the vulnerability. However, if we execute our query we won't get the expected
results. The reason is that CodeQL analysis tries not to give you extra flow that may lead to false positives and we need to specify
that tainted data can be propagated by certain code patterns.

In order to analyse these situations, we can define partial data flow debugging mechanisms. First, we are defining the taint tracking configuration:
```
class ConstraintValidator_Config_Debug extends TaintTracking::Configuration {
    ConstraintValidator_Config_Debug() { this = "ConstraintValidator_Config_Debug" }

    override predicate isSource(DataFlow::Node source) { 
        isSource_definition(source)(source)
    }

    override predicate isSink(DataFlow::Node sink) { 
        isSink_definition(sink)
    }

    override int explorationLimit() { result =  10}

}
```
Now, we can use a query in order to analyse where is our taint been blocked.
```
from ConstraintValidator_Config_Debug cfg, DataFlow::PartialPathNode source, DataFlow::PartialPathNode sink
where
  cfg.hasPartialFlow(source, sink, _) 
  and source.getNode() instanceof  NodeToDebug
select sink, source, sink, "Partial flow from unsanitized user data"
```
In the previous case, a class (NodeToDebug) has been created in order to restrict the source node for which we want to make the partial 
taint analysis.
```
/** Auxiliar class used to restrict to a specified source */
class NodeToDebug extends DataFlow::Node{
    NodeToDebug(){
        isSource_definition(this)
        and this.getLocation().toString() = "SchedulingConstraintValidator:72"
    }
}
```
#### Adding additional taint steps
After making some analysis using the previous technique, we know that we need some additional taint steps in order to go through
some barriers that block our taint propagation (as explained before).

For that, we need to create a class, extend TaintTracking::AdditionalTaintStep and override step (in which we define the source and
sink for which we want to create an additional step).
In this particular project, two main steps have been created. One for all the methods that interrupt the taint tracking:
```
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
```
And another one for the constructor of HashSet, which also interrupted the taint propagation:
```
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
```
### Step 2: Second issue
From what we have done until the moment, we have detected two different paths in which the source propagates the taint into the sink.
One belongs to SchedulingConstraintSetValidator.java and the other to SchedulingConstraintValidator.java classes. Both are detected with the
previous steps and configuration.

To sum up, we can say that we have succesfully found and demostrated (with the use of CodeQL) a vulnerability on input validation.
### Step 3: Errors and Exceptions
Since the sink of this vulnerability is associated with generating error messages, there are many cases where they will be generated 
from an exception message. For that, as an extra consideration on our procedure, we create a step that considers this case:
```
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
```
However, I am not very confident with this query.
### Step 4: Exploit and remediation
>In my case, the interesting part of the CTF was to improve my skills and learn more about CodeQL. For that purpose, I was not interested into
in taking the time to find an exploit for the vulnerability.

Finally we can check that the vulnerability was patched, by executing the query into the database of the following versions of Netflix Titus.
When we execute it, we get no results:

[Result](auxImg.JPG)

Thank you for your time, have a nice day!

## Author

#### Guillermo Arce - arceguillermo@outlook.es

 


