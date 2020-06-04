import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.FlowSources

// The sources of tainted data are the bean properties that go through constraint validation. In the code, 
// these can be found as the first parameter of ConstraintValidator.isValid(...).
// Write a CodeQL predicate that identifies these call arguments:
predicate isSource(DataFlow::Node source) { 
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
class ConstraintValidatorInterface extends GenericInterface {
ConstraintValidatorInterface(){ 
        this.hasQualifiedName("javax.validation", "ConstraintValidator") 
    }
}

from Method m
select m