Component-based deductive verification with KeYmaera X
======================================================
KeYmarea X is a theorem prover for cyber-physical systems. This goal of this fork is, to introduce component-based verificatin techniques into KeYmaera X, without changing the prover core.

The package keymaerax-webui/src/test/scala/cbcps/ contains all code related to the component-based approach.

(Note that due to an update of KeYmaera X, the component-based approach is currently not fully functional. We are currently working on fixing these issues.)

Case Studies
============
The file PerformanceTest.scala in the above package contains a collection of case studies, which compare the performance of the component-based approach with a monolithic approach. All provided models and tactics were develped by Stefan Mitsch.

Details regarding all case studies can be found in the doctoral thesis of Andreas Müller, available at the Johannes Kepler University Linz: http://epub.jku.at/urn:nbn:at:at-ubl:1-19087

Currently, the following examples are available:
* Running Example 1 - Traffic Control (incomplete): The first case study if from the field of control, but was not yet successfully verified using KeYmaera X.
* Running  Example 2a - Automated Robot Cruise Control: A cruise control system using an automated speed suggestion.
* Running Example 2b - Guided Robot Cruise Control: A cruise control system, allowing user input for speed suggestions.
* Running Example 3 - Robot Obstacle Avoidance: A very simple tele-operated robot collision avoidance system.
* Case Study 1 - ETCS: European train control system
* Case Study 2 - Robix: 2 dimesional robot collision avoidance
* Case Study 3 - Local Lane Control: Adaptive cruise control system


STTT Journal - FASE long version
--------------------------------
For the STTT journal version of the FASE paper 

  Müller, A., Mitsch, S., Retschitzegger, W., Schwinger, W., Platzer, A.: Change and delay contracts for hybrid system component verification. In: Huisman, M., Rubin, J. (eds.) FASE. LNCS, vol. 10202, pp. 134-151. Springer (2017).
  
we presented the results of this performance tests. The examples considered there are:
* RC Robot - corresponts to "Running Example 3"
* ETCS - corresponds to "Case Study 1 - ETCS"
* Robix - corresponds to " Case Study 2 - Robix"
* LLC - corresponds to "Case Study 3 - Local Lane Control"


The detailed models, interfaces, contracts and tactics can be found in the scala code.

Contact
=======
This fork was created and is maintained by
Andreas Müller
Research Fellow
Department of Cooperative Information Systems
andreas.mueller@jku.at
