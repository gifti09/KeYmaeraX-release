import java.io.{BufferedWriter, File, FileWriter}
import java.util.concurrent.TimeUnit

import edu.cmu.cs.ls.keymaerax.btactics.{ArithmeticSimplification, Simplifier, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{Lemma, Provable}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXExtendedLemmaParser

/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

/**
  * Created by nfulton on 5/30/16.
  */
class QETests extends TacticTestBase {
  case class Result(modelName: String, qeFile: String, qeRuntime: Long, smartRuntime: Long, simplifyTime: Long, simplifyWithoutHide: Long) {
    override def toString = s""""${modelName}", "${qeFile}", ${qeRuntime}, ${smartRuntime}, ${simplifyTime}, ${simplifyWithoutHide}"""
  }

  //Note: before running this disable recordQE.
  "QE results" should "prove" in withMathematica { implicit qeTool =>
    val caseStudiesDirectory = new java.io.File("/home/nfulton/dev/papers/lslab/tactics/data/QE")
    val caseStudies = caseStudiesDirectory.getAbsoluteFile.list().tail.tail //note: remove this to run PassiveSafety. Excluded here because that was my test run.
    println(s"case studies: ${caseStudies.mkString(", ")}")

    val results = caseStudies.toList.flatMap(caseStudy => {
      val caseStudyDirectory = new File(caseStudiesDirectory.getAbsolutePath + File.separator + caseStudy)
      println(s"Gathering results for ${caseStudy} in ${caseStudyDirectory.getAbsolutePath}");
      caseStudyDirectory.list().toList.sorted.map(qeFile => {
        println(s"Loading ${qeFile} in ${caseStudy} for analysis")

        val provable = toLemma(caseStudyDirectory.getAbsolutePath + File.separator + qeFile).fact

        var qeTime:Long = -1
        var smartHideTime:Long = -1
        var simplifyTime:Long = -1
        var simplifyWithoutHide:Long = -1
        try {
          qeTime = timedProof(proveBy(provable, TactixLibrary.QE))
        } catch {case e : Throwable => println(s"problem in qe: ${e.getMessage}")}
        try {
          smartHideTime = timedProof(proveBy(provable, ArithmeticSimplification.smartHide & TactixLibrary.QE))
        } catch {case e : Throwable => println(s"Problem in smartHide: ${e.getMessage}")}
        try {
          simplifyTime = timedProof(proveBy(provable, Simplifier.simp()('R) & ArithmeticSimplification.smartHide & TactixLibrary.QE))
        } catch {case e : Throwable => println(s"Problem in simplify: ${e.getMessage}")}
        try {
          simplifyWithoutHide = timedProof(proveBy(provable, Simplifier.simp()('R) & TactixLibrary.QE))
        } catch {case e : Throwable => println(s"Problem in simplify: ${e.getMessage}")}


        val result = Result(caseStudy, qeFile, qeTime, smartHideTime, simplifyTime, simplifyWithoutHide)
        appendReport(result) //add to report file.
        result
      })
    })

    printReport(results) //also print entire report to stdout.
  }

  private def toLemma(fileName: String): Lemma = try {
    val contents = scala.io.Source.fromFile(new File(fileName)).getLines().mkString("\n")
    Lemma.fromString(contents)
  } catch {
    case e: Throwable => {println(s"ERROR: Failed to parse ${fileName} into a lemma."); throw e}
  }

  private def timedProof(block: => Provable): Long = {
    val t0 = System.nanoTime()
    val result = block    // call-by-name
    val t1 = System.nanoTime()
    assert(block.isProved)
    println("Elapsed time: " + (t1 - t0) + "ns")
    TimeUnit.MILLISECONDS.convert(t1- t0, TimeUnit.NANOSECONDS)
  }

  private def printReport(results: List[Result]) = {
    val report =
      results.map(_.toString)
        .mkString("\n")
    println(report)
  }

  private def appendReport(result: Result) = {
    val reportFile = new File("/tmp/report.csv")
    new BufferedWriter(new FileWriter(reportFile, true)) {
      append(result.toString + "\n");
      close
    }

  }
}
