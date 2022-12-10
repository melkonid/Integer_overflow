//package io.joern.integer_overflows
import scala.collection.mutable.ListBuffer;

class integerOperation
{

    //Lists containing all int types from short - long
    val ushort_types : List[String] = List("unsigned short","unsigned short int") 
    val short_types : List[String] = List("short","short int","signed short","signed short int")
    val uint_types : List[String] = List("unsigned","unsigned int")
    val int_types : List[String] = List("int","signed","signed int")
    //Lists to contain assignments
    val ushort_variables = new ListBuffer[String]()
    val short_variables = new ListBuffer[String]()
    val uint_variables = new ListBuffer[String]()
    val int_variables = new ListBuffer[String]()

    val vulnerable_ids = new ListBuffer[String]()

    var positive_counter = 0
    var negative_counter = 0


    def isNumber(str : String) : Boolean = 
    {
        var counter = 1
        for(c <- str)
        {
            if(!c.isDigit)
            {
                if(counter == 1 && (c.equals('+') || c.equals('-')))
                {
                    //skip the 1st if its a sign
                }
                else{return false}
            }
            counter = counter + 1
        }
        negative_counter = negative_counter + 1
        return true
    }

    def removeLiteralAssignments(assignments : overflowdb.traversal.Traversal[io.shiftleft.semanticcpg.language.operatorextension.opnodes.Assignment]) : ListBuffer[operatorextension.opnodes.Assignment] = 
    {
        val return_list = new ListBuffer[operatorextension.opnodes.Assignment]()
        for(assignment <- assignments)
        {
            val right_hand_side = assignment.code.split("=")(1)

            if(!isNumber(right_hand_side.replaceAll("\\s","")))
            {
                return_list += assignment
            }
        }
        return return_list
    }

    def checkMalloc(assignment : operatorextension.opnodes.Assignment) : Unit = 
    {
        val string_max = "UINT_MAX"
        val num_max = "4294967295"
        var flag = false
        val malloc_operation = assignment.astChildren.astChildren.code.l(0).replaceAll("\\s", "") 
        //println(malloc_operation)
        val condition = assignment.astParent.astParent.code.replaceAll("\\s", "")
        if(condition.contains(malloc_operation)  && condition.substring(0, Math.min(condition.length(), 2)) == "if")
        {
            if(condition.contains("<=" + string_max) || condition.contains("<" + string_max) || condition.contains(string_max + ">") || condition.contains( string_max + ">="))
                flag = true
            if(condition.contains("<" + num_max) || condition.contains("<=" + num_max) || condition.contains(num_max + ">") || condition.contains(num_max + ">="))
                flag = true
        }

        if(!flag)
        {
            println("No check if malloc could overflow       | " + assignment.lineNumber + " | " + assignment.code)
            positive_counter = positive_counter + 1
        }
        else {
            negative_counter = negative_counter + 1
        }
        
    }
    def checkMinMax(assignment : operatorextension.opnodes.Assignment, num_type : String) : Boolean = 
    {
        var string_max = " "
        var string_min = " "
        var num_max = " "
        var num_min = " "
        if(num_type.equals("int"))
        {
            string_max = "INT_MAX"
            string_min = "INT_MIN"
            num_max  = "2147483647"
            num_min = "-2147483648"
        }
        else if(num_type.equals("short"))
        {
            string_max = "SHRT_MAX"
            string_min = "SHRT_MIN"
            num_max  = "32767"
            num_min = "-32768"
        }
        else if(num_type.equals("uint"))
        {
            string_max = "UINT_MAX"
            string_min = "0"
            num_max  = "4294967295"
            num_min = "0"
        }
        else if(num_type.equals("ushort"))
        {
            string_max = "USHRT_MAX"
            string_min = "0"
            num_max  = "65535"
            num_min = "0"
        }
        var pass = true
        val value_assigned = assignment.code.replaceAll("\\s", "").split("=")(1)
        val condition = assignment.astParent.astParent.code.replaceAll("\\s", "") 
        if(condition.contains(value_assigned) && condition.substring(0, Math.min(condition.length(), 2)) == "if")
        {
            //println("True for  " + condition)
            if(condition.contains("<") && condition.contains(string_max) && condition.indexOf("<") < condition.indexOfSlice(string_max))
                return true // < INT_MAX
            if(condition.contains(">") && condition.contains(string_max) && condition.indexOf(">") > condition.indexOfSlice(string_max))
                return true // INT_MAX > 
            if(condition.contains("<") && condition.contains(string_min) && condition.indexOf("<") > condition.indexOfSlice(string_min))
                return true // INT_MIN < 
            if(condition.contains(">") && condition.contains(string_min) && condition.indexOf(">") < condition.indexOfSlice(string_min))
                return true //  > INT_MIN 

            if(condition.contains("<") && condition.contains(num_max) && condition.indexOf("<") < condition.indexOfSlice(num_max))
                return true // < NUM_MAX
            if(condition.contains(">") && condition.contains(num_max) && condition.indexOf(">") > condition.indexOfSlice(num_max))
                return true // NUM_MAX > 
            if(condition.contains("<") && condition.contains(num_min) && condition.indexOf("<") > condition.indexOfSlice(num_min))
                return true // NUM_MIN < 
            if(condition.contains(">") && condition.contains(num_min) && condition.indexOf(">") < condition.indexOfSlice(num_min))
                return true //  > INT_MIN                  
        }
        return false

    }  

    def checkTypeChange(assignment : operatorextension.opnodes.Assignment) : Boolean = 
    {
        var flag = true
        val typeFullName = assignment.ast.filter(_.isInstanceOf[Identifier]).asInstanceOf[Traversal[Identifier]].typeFullName.l(0)
        //println(assignment.code + " : " + typeFullName)
        val ushort_unsafe = int_types ++ uint_types ++ short_types
        val short_unsafe = int_types ++ uint_types ++ ushort_types
        val uint_unsafe = short_types ++ int_types
        val int_unsafe = uint_types

        var unsafe_types : List[String] = List()

        if(ushort_types.contains(typeFullName)){unsafe_types = ushort_unsafe}
        else if(short_types.contains(typeFullName)){unsafe_types = short_unsafe}
        else if(uint_types.contains(typeFullName)){unsafe_types = uint_unsafe}
        else if(int_types.contains(typeFullName)){unsafe_types = int_unsafe}
        else{println("Error unknown type " + typeFullName)}

        for(identifier <- assignment.ast.filter(_.isInstanceOf[Identifier]).asInstanceOf[Traversal[Identifier]])
        {
            if(unsafe_types.contains(identifier.typeFullName))
            {
                println("Possbile Wrap Around                    | " + assignment.lineNumber + " | " + assignment.code + "       | " + identifier.typeFullName + " to " + typeFullName)
                flag =  false
            }
        }

        val methods_in_assignment = assignment.ast.filter(_.isInstanceOf[io.shiftleft.codepropertygraph.generated.nodes.Call]).asInstanceOf[Traversal[io.shiftleft.codepropertygraph.generated.nodes.Call]].filter(node => cpg.method.internal.name.l.contains(node.name)).l
        //methods_in_assignment = methods_in_assignment 
        for(method <- methods_in_assignment)
        {
            val method_return_type = cpg.method.filter(_.name == method.name).methodReturn.code.l(0)
            if(unsafe_types.contains(method_return_type))
            {
                println("Possbile Wrap Around                    | " + assignment.lineNumber + " | " + assignment.code + "       | " + method_return_type + " to " + typeFullName)
                flag =  false
            }
        }

        return flag

    }  

    def checkInteger(assignment : operatorextension.opnodes.Assignment, num_type : String) : Unit = 
    {
        val check1 = checkMinMax(assignment,num_type)
        val check2 = checkTypeChange(assignment)
        if(!check1)
        {
           println("No check if variable can hold result    | " + assignment.lineNumber + " | " + assignment.code)
        }
        if(!check1 || !check2)
        {
            positive_counter = positive_counter + 1
        }
        else{
            negative_counter = negative_counter + 1
        }
    }    

    def getAllInt() : Unit = 
    {

        
        // Get all integer identifiers
        for(variable <- cpg.identifier)
        {
            if(ushort_types.contains(variable.typeFullName)){ushort_variables += variable.name}

            if(short_types.contains(variable.typeFullName)){short_variables += variable.name}

            if(uint_types.contains(variable.typeFullName)){uint_variables += variable.name}

            if(int_types.contains(variable.typeFullName)){int_variables += variable.name}

        }
        // Find their assignments
        val all_assignments = cpg.assignment

        val assignments = removeLiteralAssignments(all_assignments)

        val ushort_assignments = new ListBuffer[operatorextension.opnodes.Assignment]()
        val short_assignments = new ListBuffer[operatorextension.opnodes.Assignment]()
        val uinteger_assignments = new ListBuffer[operatorextension.opnodes.Assignment]()
        val integer_assignments = new ListBuffer[operatorextension.opnodes.Assignment]()

        val malloc_assignments = new ListBuffer[operatorextension.opnodes.Assignment]()

        for(assignment <- assignments)
        {
            if(assignment.code.contains("malloc")){malloc_assignments += assignment}
            else
            {
                if(int_variables.contains(assignment.code.split(" +")(0))){integer_assignments += assignment}

                if(uint_variables.contains(assignment.code.split(" +")(0))){uinteger_assignments += assignment}
                
                if(short_variables.contains(assignment.code.split(" +")(0))){short_assignments += assignment}
                
                if(ushort_variables.contains(assignment.code.split(" +")(0))){ushort_assignments += assignment}
            }
        }


        println("Reason                                  | Line    | Code               | Comment    |")
        println("-------------------------------------------------------------------------------------")
        
        for(assignment <- integer_assignments)
        {
            checkInteger(assignment,"int")
        }
        //println("-------------------------------------------------------------------------------------")

        for(assignment <- uinteger_assignments)
        {
            checkInteger(assignment,"uint")
        }
        //println("-------------------------------------------------------------------------------------")
        for(assignment <- short_assignments)
        {
            checkInteger(assignment,"short")
        }
        //println("-------------------------------------------------------------------------------------")
        for(assignment <- ushort_assignments)
        {
            checkInteger(assignment,"ushort")
        }
        //println("-------------------------------------------------------------------------------------")
        for(assignment <- malloc_assignments)
        {
            checkMalloc(assignment)
        }
        println("-------------------------------------------------------------------------------------")


        println("Final Number of Positives : " + positive_counter)
        println("Final Number of Negatives : " + negative_counter)
        
    }
}
