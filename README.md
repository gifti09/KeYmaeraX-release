Component-based deductive verification with KeYmaera X
======================================================
KeYmarea X is a theorem prover for cyber-physical systems. This goal of this fork is, to introduce component-based verificatin techniques into KeYmaera X, without changing the prover core.

The package keymaerax-webui/src/test/scala/cbcps/ contains all code related to the component-based approach.

(Note that due to an update of KeYmaera X, the component-based approach is currently not fully functional. We are currently working on fixing these issues.)

Case Studies
============
The easiest way to run KeYmaera X is to download binaries 
[keymaerax.jar](http://keymaerax.org/keymaerax.jar) and start from command line

    java -jar keymaerax.jar

First ensure that the following software is installed
- [Java Development Kit JDK](https://java.com/download)
  (version 1.8+ recommended. Mathematica 9.0 is only compatible with Java 1.6 and 1.7. Mathematica 10.0+ are also compatible with Java 1.8)
- [Wolfram Mathematica](https://www.wolfram.com/mathematica/)
  (version 10+ recommended. Other versions may work.
  The Mathematica J/Link library that comes with Mathematica is needed during compilation. Mathematica needs to be activated to use it also at runtime.
  Otherwise the [Z3 Solver](https://github.com/Z3Prover/z3) is automatically used for real arithmetic.)

#### FAQ: Run Problems

If running `java -jar keymaerax.jar` results in the error `Invalid or corrupt jarfile` then update to Java 1.8 and to Mathematica 10+.
If you need to use an earlier version of Java or Mathematica, you can also run KeYmaera X via

    java -Xss20M -cp keymaerax.jar KeYmaeraX

If KeYmaera X acts weird after an update, clean your local cache of lemmas by removing (or renaming) the directory `~/.keymaerax/cache`.
You could also try renaming the model and proof database `~/.keymaerax/keymaerax.sqlite` (if this file has become corrupt, it may prevent KeYmaera X from working properly).

Errors related to `com.wolfram.jlink` or `JLinkNativeLibrary` are caused by incompatibilities of Java 1.8 in combination with Mathematica 9. It is recommended to use Mathematica 10. Or they may be caused by some operating system configuration issues.

#### Configuration
KeYmaera X requires a decision procedure for real arithmetic to finalize proofs. It is tested best with Mathematica.
After starting KeYmaera X you can configure arithmetic tools in the _Help->Tool Configuration_ menu.

Depending on the operating system, Mathematica is installed in different locations. 
Alternatively, you can also specify which arithmetic tools to use from command line with
parameters `-mathkernel` and `-jlink`. Parameters that are appropriate when
Mathematica is installed in the default location are provided below.

#### Default Configuration Parameters per Operating System
Mac OS, 64bit, Mathematica 10.4+
* `-mathkernel /Applications/Mathematica.app/Contents/MacOS/MathKernel`
* `-jlink /Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64`

Linux, 64bit, Mathematica 10.4+
* `-mathkernel /usr/local/Wolfram/Mathematica/10.4/Executables/MathKernel`
* `-jlink /usr/local/Wolfram/Mathematica/10.4/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64`

Windows, 64bit, Mathematica 10.4+
* `-mathkernel "C:\Program Files\Wolfram Research\Mathematica\10.4\MathKernel.exe"`
* `-jlink "C:\Program Files\Wolfram Research\Mathematica\10.4\SystemFiles\Links\JLink\SystemFiles\Libraries\Windows-x86-64"`

Building
========
To compile KeYmaera X from source code, see [Building Instructions](https://github.com/LS-Lab/KeYmaeraX-release/wiki/Building-Instructions).
In a nutshell, run the following after installing the right software:

    sbt clean assembly


Publications
============

KeYmaera X implements the uniform substitution calculus for differential dynamic logic in order to enable soundness assurance by way of a small trusted LCF-style kernel while still being amenable to automatic theorem proving.

http://www.ls.cs.cmu.edu/publications.html

1. André Platzer. 
[A complete uniform substitution calculus for differential dynamic logic](http://dx.doi.org/10.1007/s10817-016-9385-1). 
Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.

2. André Platzer.
[Logics of dynamical systems](http://dx.doi.org/10.1109/LICS.2012.13).
ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012.

Details regarding all case studies can be found in the doctoral thesis of Andreas Müller, available at the Johannes Kepler University Linz: http://epub.jku.at/urn:nbn:at:at-ubl:1-19087

Currently, the following examples are available:
* Running Example 1 - Traffic Control (incomplete): The first case study if from the field of control, but was not yet successfully verified using KeYmaera X.
* Running  Example 2a - Automated Robot Cruise Control: A cruise control system using an automated speed suggestion.
* Running Example 2b - Guided Robot Cruise Control: A cruise control system, allowing user input for speed suggestions.
* Running Example 3 - Robot Obstacle Avoidance: A very simple tele-operated robot collision avoidance system.
* Case Study 1 - ETCS: European train control system
* Case Study 2 - Robix: 2 dimesional robot collision avoidance
* Case Study 3 - Local Lane Control: Adaptive cruise control system

5. André Platzer.
[Logical Foundations of Cyber-Physical Systems](http://lfcps.org/lfcps/).
Springer, 2018.

STTT Journal - FASE long version
--------------------------------
For the STTT journal version of the FASE paper 

  Müller, A., Mitsch, S., Retschitzegger, W., Schwinger, W., Platzer, A.: Change and delay contracts for hybrid system component verification. In: Huisman, M., Rubin, J. (eds.) FASE. LNCS, vol. 10202, pp. 134-151. Springer (2017).
  
we presented the results of this performance tests. The examples considered there are:
* RC Robot - corresponts to "Running Example 3"
* ETCS - corresponds to "Case Study 1 - ETCS"
* Robix - corresponds to " Case Study 2 - Robix"
* LLC - corresponds to "Case Study 3 - Local Lane Control"

A secondary goal of KeYmaera X is to also make it possible to implement extensions of differential dynamic logic, such as differential game logic for hybrid games as well as quantified differential dynamic logic for distributed hybrid systems:

7. André Platzer. 
[Differential game logic](http://dx.doi.org/10.1145/2817824). 
ACM Trans. Comput. Log., 17(1), 2015.

8. André Platzer. 
[Differential hybrid games](http://dx.doi.org/10.1145/3091123). 
ACM Trans. Comput. Log., 18(3), 2017.

9. André Platzer.
[A complete axiomatization of quantified differential dynamic logic for distributed hybrid systems](http://dx.doi.org/10.2168/LMCS-8(4:17)2012).
Logical Methods in Computer Science, 8(4), pages 1-44, 2012.

Copyright and Licenses
======================

Copyright (C) 2014-2018 Carnegie Mellon University. See COPYRIGHT.txt for details.
Developed by Andre Platzer, Stefan Mitsch, Nathan Fulton, Brandon Bohrer, Jan-David Quesel, Yong Kiam Tan, Marcus Voelp, Ran Ji.

See LICENSE.txt for the conditions of using this software.

The KeYmaera X distribution contains external tools. A list of tools and their licenses can be found in

    keymaerax-webui/src/main/resources/license/tools_licenses

Contact
=======
This fork was created and is maintained by
Andreas Müller
Research Fellow
Department of Cooperative Information Systems
andreas.mueller@jku.at
