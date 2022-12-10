//package io.joern.integer_overflows

import $file.integerOperation, integerOperation._

@main def exec(cpgFile: String = ""): Unit = {

    val t1 = System.nanoTime
    if (cpgFile != "") {
        importCode(cpgFile)
        println("===================================================================================================================")
        val integers = new integerOperation()
        integers.getAllInt()
        val duration = (System.nanoTime - t1) / 1e9d
        println("Time of Execution: " + duration + "s")
        println("===================================================================================================================")
    }

    //val dnsq = new DNSVulnCodeSmells()
    //dnsq.printBanner()
    //dnsq.invalidCompressionChecks()
    //dnsq.unsafeCompressionPointerOperations()
}
