package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

import scala.collection.immutable.{Map, _}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, RenUSubst, _}

/**
  * Created by yongkiat on 11/27/16.
  */
object PolynomialArith {

  /**
    * Normalised polynomial arithmetic
    *
    * A normalised monomial has the following shape in KeYmaeraX's term grammar (n is a natural number > 0):
    *
    * mono:= 1 | mono * (Var)^n
    *
    * Variables in the first half of * must be lexicographically > than the variable in the second by Scala string cmp
    *
    * Similarly, a normalised polynomial has the following shape (const is non-zero):
    *
    * poly:= 0 | poly + const * mono
    *
    * monomials in the second half of + must be smaller than the first half by monomial ordering
    *
    * The units are included for now to get a nicer definition??
    *
    * todo: Add ability to turn off proof generation everywhere
    */

  //Sanity check that a term representing a monomial satisfies the monomial normalisation requirement
  def checkMono(t:Term,maxs:String = ""): Boolean = {
    t match {
      case n:Number => n.value == 1
      case Times(l,Power(s:Variable,n:Number)) =>
        n.value.isValidInt && n.value.toInt > 0 && s.name > maxs && checkMono(l,s.name)
      case _ => false
    }
  }

  //Monomial order
  def ordMono(t:Term) : Integer = {
    //assert(checkMono(t))
    t match {
      case Times(l,Power(s:Variable,n:Number)) => n.value.toInt + ordMono(l)
      case _ => 0
    }
  }

  //Lexicographical < comparison of monomials
  def lexMono(l:Term,r:Term) :Boolean = {
    (l,r) match {
      case(n:Number,m:Number) => false
      case (Times(l,Power(sl:Variable,nl:Number)),Times(r,Power(sr:Variable,nr:Number))) =>
        if(sl.name > sr.name) true
        else if(sl.name == sr.name) {
          if (nl.value < nr.value) true
          else if(nl.value == nr.value) lexMono(l,r)
          else false
        }
        else false
    }
  }

  //Strict monomial comparison l < r?
  def cmpMono(l:Term,r:Term) : Boolean = {
    val or = ordMono(r)
    val ol = ordMono(l)
    if (or > ol) {
      true
    }
    else if(or == ol) {
      lexMono(l,r)
    }
    else false
  }

  //Sanity check that a term representing a polynomial satisfies the normalisation requirement
  def checkPoly(t:Term,maxm:Option[Term] = None): Boolean = {
    t match {
      case n:Number => n.value == 0
      case Plus(l,Times(c:Number,m)) =>
        (c.value != 0) && checkMono(m) &&
          (maxm match {
          case None => checkPoly(l,Some(m))
          case Some(n) => cmpMono(m,n) && checkPoly(l,Some(n))
          })
      case _ => false
    }
  }

  //List of reassociations needed -- avoids QE inside the actual proof (QE should get everything right)
  private val plusAssoc1 = proveBy("(F_() + G_()) + (A_() + B_()) = ((F_()+G_())+A_())+B_()".asFormula,QE)
  private val plusAssoc2 = proveBy("(F_() + K_()*M_()) + (A_() + L_()*M_()) = (F_()+A_())+(K_()+L_())*M_()".asFormula,QE)

  private val plusCoeff1 = proveBy("K_() = 0 -> (F_() + K_()*M_() = F_())".asFormula,QE)
  private val plusCoeff2 = proveBy("K_() = L_() -> (F_() + K_()*M_() = F_() + L_()*M_())".asFormula,
    byUS("const congruence"))

  //This seems like it might be a bad idea ...
  private def getProver(skip_proofs:Boolean) :(Formula,BelleExpr)=>ProvableSig =
    if (skip_proofs) ( (f:Formula,b:BelleExpr) => DerivedAxioms.equivReflexiveAxiom.fact ) else proveBy

  //Takes and returns normalised polynomials
  //The returned provable is just reflexivity if no proof is required
  def addPoly(l:Term,r:Term,skip_proofs:Boolean = false): (Term,ProvableSig) = {
    val lhs = Plus(l,r)
    val prover = getProver(skip_proofs)
    val res = (l,r) match {
      case (n:Number,_) => //Left unit for addition
        (r,prover(Equal(lhs,r), byUS("0+")))
      case (_,n:Number) => //Right unit for addition
        (l,prover(Equal(lhs,l), byUS("+0")))
      case (Plus(nl,Times(cl:Number,ml)),Plus(nr,Times(cr:Number,mr))) => {
        if(cmpMono(ml,mr)) {
          val (rec,pr) = addPoly(l,nr,skip_proofs)
          val res = Plus(rec,Times(cr:Number,mr))
          (res,prover(Equal(lhs,res), useAt(plusAssoc1)(SuccPosition(1,0::Nil))
            & useAt(pr)(SuccPosition(1,0::0::Nil)) & byUS("= reflexive")))
        }
        else if (ml == mr) {
          val (rec,pr) = addPoly(nl,nr,skip_proofs)
          val cnew = cl.value + cr.value
          if(cnew == 0) //Canceling out the 0
            (rec, prover(Equal(lhs,rec), useAt(plusAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(plusCoeff1,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & TactixLibrary.RCF))
          else {
            val res = Plus(rec,Times(Number(cl.value+cr.value),ml))
            (res, prover(Equal(lhs,res), useAt(plusAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(plusCoeff2,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & RCF))
          }
        }
        else {
          val (rec,pr) = addPoly(r,l,skip_proofs)
          //Flip the +
          (rec,if (skip_proofs) DerivedAxioms.equivReflexiveAxiom.fact else useFor("+ commute")(SuccPosition(1,0::Nil))(pr))
        }
      }
      case _ => ???
    }
    res
  }

  //One of these is missing in DerivedAxioms
  private val onetimes = proveBy("1*F_() = F_()".asFormula,QE)
  private val timesone = proveBy("F_()*1 = F_()".asFormula,QE)

  private val timesAssoc1 = proveBy("(F_() * G_()) * (A_() * B_()) = ((F_()*G_())*A_())*B_()".asFormula,QE)
  private val timesAssoc2 = proveBy("(F_() * M_()^K_()) * (A_() * M_()^L_()) = (F_()*A_())*M_()^(K_()+L_())".asFormula,QE)

  //QE has interesting ideas about X^0
  private val timesCoeff1Lem = proveBy("F_() = F_() * M_() ^ 0".asFormula,QE)
  private val timesCoeff1 = proveBy("K_() = 0 -> (F_() * M_()^K_() = F_() )".asFormula,
    useAt(timesCoeff1Lem)(SuccPosition(1,1::1::Nil)) & byUS("const congruence"))

  private val timesCoeff2 = proveBy("K_() = L_() -> (F_() * M_()^K_() = F_() * M_()^L_())".asFormula,
    byUS("const congruence"))

  //Multiplies and returns normalised monomials (this is basically the same as the implementation for adding polynomials)
  def mulMono(l:Term,r:Term,skip_proofs:Boolean = false): (Term,ProvableSig) = {
    val lhs = Times(l,r)
    val prover = getProver(skip_proofs)
    (l,r) match {
      case(n:Number,_) => (r,prover(Equal(lhs,r),byUS(onetimes)))  //Unit
      case (_,n:Number) => (l,prover(Equal(lhs,l),byUS(timesone))) //Unit
      case (Times(nl,Power(sl:Variable,ml:Number)),Times(nr,Power(sr:Variable,mr:Number))) =>
        if(sl.name > sr.name)
        {
          val(rec,pr) = mulMono(l,nr,skip_proofs)
          val res = Times(rec,Power(sr:Variable,mr:Number))
          (res,prover(Equal(lhs,res), useAt(timesAssoc1)(SuccPosition(1,0::Nil))
            & useAt(pr)(SuccPosition(1,0::0::Nil)) & byUS("= reflexive")))
        }
        else if(sl.name == sr.name) {
          val(rec,pr) = mulMono(nl,nr,skip_proofs)
          val mnew = ml.value + mr.value
          if(mnew == 0) //Canceling out the 0
            (rec, prover(Equal(lhs,rec), useAt(timesAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(timesCoeff1,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & RCF))
          else {
            val res = Times(rec,Power(sl,Number(ml.value+mr.value)))
            (res, prover(Equal(lhs,res), useAt(timesAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(timesCoeff2,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & RCF))
          }
        }
        else {
          val (rec,pr) = mulMono(r,l,skip_proofs)
          //Flip the *
          (rec,if (skip_proofs) DerivedAxioms.equivReflexiveAxiom.fact else useFor("* commute")(SuccPosition(1,0::Nil))(pr))
        }
      case _ => ???
    }
  }

  private val timesAssoc3 = proveBy(("(P_() + C_() * M_()) * (D_() * N_()) = " +
    "P_() * (D_() * N_()) + (C_() * D_()) * (M_() * N_())").asFormula,QE)

  //Multiplies a normalized polynomial by a constant and a normalized monomial
  def mulPolyMono(l:Term,c:Number,r:Term,skip_proofs:Boolean = false): (Term,ProvableSig) = {
    val lhs = Times(l,Times(c,r))
    val prover = getProver(skip_proofs)
    l match {
      case n:Number => (n,prover(Equal(lhs,n),byUS("0*"))) // Multiplication by 0 poly
      case Plus(nl,Times(cl:Number,ml)) =>
        val (rec1,pr1) = mulPolyMono(nl,c,r,skip_proofs)
        val (rec2,pr2) = mulMono(ml,r,skip_proofs)
        val res =  Plus(rec1,Times(Number(cl.value*c.value),rec2) )

        (res,prover(Equal(lhs,res),useAt(timesAssoc3)(SuccPosition(1,0::Nil))
          & useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::1::Nil))
          & useAt(plusCoeff2,PosInExpr(1::Nil))(1)
          //Should only be simple arithmetic
          & RCF))

      case _ => ???
    }
  }

  //Multiplies and returns normalised polynomials
  def mulPoly(l:Term,r:Term,skip_proofs:Boolean = false): (Term,ProvableSig) = {
    val lhs = Times(l,r)
    val prover = getProver(skip_proofs)
    r match {
      case n:Number => (n,prover(Equal(lhs,n),byUS("*0"))) //Multiplication by 0 poly
      case Plus(nr,Times(cr:Number,mr)) =>
        val (rec1,pr1) = mulPoly(l,nr,skip_proofs)
        val (rec2,pr2) = mulPolyMono(l,cr,mr,skip_proofs)
        val (res,pr3) = addPoly(rec1,rec2,skip_proofs)
        (res,prover(Equal(lhs,res),useAt("distributive")(SuccPosition(1,0::Nil))
          & useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3)
        ))

      case _ => ???
    }
  }

  private val powLem1 = proveBy("F_()^0 = 1".asFormula,QE)
  private val powLem2 = proveBy("F_()^1 = F_()".asFormula,QE)
  private val powLem3 = proveBy("(F_()^K_())^2 = F_()^(2*K_())".asFormula,QE)
  private val powLem4 = proveBy("(F_()^K_())^2 * F_() = F_()^(2*K_()+1)".asFormula,QE)
  private val powLem5 = proveBy("K_() = L_() -> (M_()^K_() = M_()^L_())".asFormula,
    byUS("const congruence"))

  //Reduces t^n to iterated squares
  def iterSquare(l:Term,p:Int,skip_proofs:Boolean = false) : (Term,ProvableSig) = {
    val lhs = Power(l,Number(p))
    val prover = getProver(skip_proofs)
    if (p == 0) (Number(1),prover(Equal(lhs,Number(1)),byUS(powLem1)))
    else if (p == 1) (l,prover(Equal(lhs,l),byUS(powLem2)))
    else if (p % 2 == 0)
    {
      val (rec,pr) = iterSquare(l,p/2,skip_proofs)
      val rhs = Power(rec,Number(2))
      (rhs,prover(Equal(lhs,rhs),
        useAt(pr,PosInExpr(1::Nil))(SuccPosition(1,1::0::Nil)) &
        useAt(powLem3)(SuccPosition(1,1::Nil)) &
        useAt(powLem5,PosInExpr(1::Nil))(1) & RCF))
    }
    else
    {
      val (rec,pr) = iterSquare(l,p/2,skip_proofs)
      val rhs = Times(Power(rec,Number(2)),l)
      (rhs,prover(Equal(lhs,rhs),
        useAt(pr,PosInExpr(1::Nil))(SuccPosition(1,1::0::0::Nil)) &
        useAt(powLem4)(SuccPosition(1,1::Nil)) &
        useAt(powLem5,PosInExpr(1::Nil))(1) & RCF))
    }
  }

  private val negNormalise = proveBy("-P_() = P_() * (-1 * 1)".asFormula,QE)
  private val minusNormalise = proveBy("P_()-Q_() = P_() + -(Q_())".asFormula,QE)
  private val powNormalise = proveBy("P_()^2 = P_() * P_()".asFormula,QE)

  //Normalizes an otherwise un-normalized term
  def normalise(l:Term,skip_proofs:Boolean = false) : (Term,ProvableSig) = {
    val prover = getProver(skip_proofs)
    val res = l match {
      case n:Number =>
        //0 + 1 * n (unless n = 0)
        val res = if (n.value == 0) n else Plus(Number(0), Times(n,Number(1)))
        (res,prover(Equal(l,res), RCF ))
      case v:Variable =>
        //0 + 1 * (1 * v^1)
        val res = Plus(Number(0),Times(Number(1), Times(Number(1),Power(v,Number(1))) ))
        (res,prover(Equal(l,res), RCF ))
      case Plus(ln,rn) =>
        val (rec1,pr1) = normalise(ln,skip_proofs)
        val (rec2,pr2) = normalise(rn,skip_proofs)
        val (res,pr3) = addPoly(rec1,rec2,skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3)))
      case Times(ln,rn) =>
        val (rec1,pr1) = normalise(ln,skip_proofs)
        val (rec2,pr2) = normalise(rn,skip_proofs)
        val (res,pr3) = mulPoly(rec1,rec2,skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3)))
      case Power(_:Variable,_:Number) =>
        //0 + 1 * (1 * v^n)
        val res = Plus(Number(0),Times(Number(1), Times(Number(1),l) ))
        (res,prover(Equal(l,res),RCF))
      case Power(ln,n:Number) if n.value == 2 =>
        val (rec1,pr1) = normalise(ln,skip_proofs)
        //Square the polynomial by hand
        val (res,pr2) = mulPoly(rec1,rec1,skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(powNormalise)(SuccPosition(1,0::Nil))
          & by(pr2)))
      case Power(ln,n:Number) if n.value.isValidInt =>
        val(rec1,pr1) = iterSquare(ln,n.value.intValue(),skip_proofs)
        val(res,pr2) = normalise(rec1,skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::Nil))
          & by(pr2)))
      case Neg(ln) =>
        //Negation ~= multiply by -1 monomial
        val (rec1,pr1) = normalise(ln,skip_proofs)
        val (res,pr2) = mulPolyMono(rec1,Number(-1),Number(1),skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(negNormalise)(SuccPosition(1,0::Nil)) & by(pr2) ))
      case Minus(ln,rn) =>
        //Minus ~= move - into negation
        val (rec1,pr1) = normalise(ln,skip_proofs)
        val (rec2,pr2) = normalise(Neg(rn),skip_proofs)
        val (res,pr3) = addPoly(rec1,rec2,skip_proofs)
        (res,prover(Equal(l,res), useAt(minusNormalise)(SuccPosition(1,0::Nil))
          & useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3) ))
      case _ => ???
    }
    res
  }

  val normaliseAt:DependentPositionTactic = new DependentPositionTactic("normalise at"){
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        sequent.sub(pos) match
        {
          case Some(t:Term) =>
            val(tt,pr) = normalise(t,false)
            //println(tt,pr)
            CEat(useFor("= commute")(SuccPos(0))(pr))(pos)
          case _ => ident
        }
      }
    }
  }

  //Polynomial division: no proof needed, although the polynomials need to be pre-normalised
  //todo: Might this be implemented in terms of mulMono with -ve power? (probably not because ordering gets messed up)

  //Monomial division l/r : returns the normalised quotient monomial q * r = l only if it is truly divisible
  def divMono(l:Term,r:Term): Option[Term] = {
    val lhs = Times(l,r)
    (l,r) match {
      case (_,n:Number) => Some(l) //Divide by 1
      case(n:Number,_) => None //Dividing 1 by something not 1
      case (Times(nl,Power(sl:Variable,ml:Number)),Times(nr,Power(sr:Variable,mr:Number))) =>
        if(sl.name > sr.name) None
        else if(sl.name == sr.name) {
          val mnew = ml.value - mr.value
          if (mnew < 0) None
          divMono(nl, nr) match {
            case None => None
            case Some(q) =>
              Some (if (mnew == 0) q else Times(q, Power(sr, Number(mnew))))
          }
        }
        else {
          divMono(nl,r) match
          {
            case None => None
            case Some(q) => Some(Times(q,Power(sl,ml)))
          }
        }
      case _ => ???
    }
  }

  //Polynomial division on head monomials (no proofs)

  //Find the first non-zero monomial in l that r divides if it exists & returns the quotient along with its coefficient
  def divPolyMono(l:Term,r:Term) : Option[(Number,Term)] = {
    l match {
      case n: Number => None //We want non-zero monomials only
      case Plus(nl, Times(cl: Number, ml)) =>
        divMono(ml, r) match {
          case None => divPolyMono(nl, r)
          case Some(q) => Some(Number(cl.value), q)
        }
    }
  }

  //Returns the divisor and quotient (if one exists)
  def divPoly(l:Term,r:Term): Option[(Term,Term)] = {
    r match {
      case n:Number => None //Division by 0
      case Plus(nr,Times(cr:Number,mr)) =>
        divPolyMono(l,mr) match {
          case None => None //No monomial in l divisible by r
          case Some((c,q)) => //The monomial c*(q*mr) was in l
            //The actual coefficient we need to return for the reduction:
            val divisor = Times(Number(-1 * c.value / (cr.value)),q)
            //For division, we need to use the normalized version internally
            val quotient = addPoly(l, mulPolyMono(r, Number(-1 * c.value / (cr.value)), q,true)._1,true)._1
            Some(divisor,quotient)
        }
    }
  }

  //Don't know how to do this in Scala neatly
  def firstDivisor(l:List[Term],i:Int,r:Term) : Option[(Int,Term,Term)] ={
    l match {
      case Nil => None
      case (x::xs) =>
        divPoly(r,x) match {
          case None => firstDivisor(xs,i+1,r)
          case Some((d,q)) => Some(i,d,q)
        }
    }
  }

  //Repeated division of normalized things
  //Returns the sequence of reduction steps, each a pair of the index and divisor of the dividing polynomial
  def reduction(l:List[Term],r:Term): List[(Int,Term)] ={
    firstDivisor(l,0,r) match {
      case None => Nil
      case Some((i,d,q)) =>
        (i,d)::reduction(l,q)
    }
  }

  //This lemma should be in DerivedAxioms together with 1>0 and f_()^2 >= 0
  private val plusGtMono: ProvableSig = proveBy("(f_() > k_() & g_() >= 0) -> f_() + g_() > k_()".asFormula,QE)

  //Doesn't use QE, but the DerivedAxioms used do
  val notZeroGt: ProvableSig = proveBy("!(0>0)".asFormula,
    notR(1) & useAt(">2!=")(-1) & useAt("! =",PosInExpr(1::Nil))(-1) & notL(-1) & byUS("= reflexive"))

  //Generate a proof for |- !(1 + s_1^2 + ... + s_n^2 = 0) (without QE)
  def assertWitness(l:List[Term]) : (Term,ProvableSig) =
  {
    l match {
      case Nil => (Number(1),DerivedAxioms.oneGreaterZero.fact)
      case (x::xs) =>
        val (rec,pr) = assertWitness(xs) //1 + foo > 0
        val res = Plus(rec,Power(x,Number(2)))
        (res,proveBy(Greater(res,Number(0)), // (1+ foo) + x^2 >0
          useAt(plusGtMono,PosInExpr(1::Nil))(1) & andR(1) <( by(pr), byUS("nonnegative squares") ) ))
    }
  }

  //todo: more convenient to cut in, can be derived without QE from something else
  private val gtNotZero: ProvableSig = proveBy("f_() > 0 -> !(f_() = 0)".asFormula,QE)

  // Given a list representing a (hopefully Groebner) basis g_1, ... g_k, a witness, and
  // an optional list of instructions (detailing the coefficients) and a list of witnesses s_i ^2
  // Proves the contradiction g_1 = 0 ; ... g_k = 0 |-
  // Nothing needs to be normalized?

  //Copy of implyRi that keeps the anteposition around
  def implyRiKeep(antePos: AntePos = AntePos(0), succPos: SuccPos = SuccPos(0)): DependentTactic = new SingleGoalDependentTactic("inverse imply right") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.length > antePos.getIndex && sequent.succ.length > succPos.getIndex,
        "Ante position " + antePos + " or succ position " + succPos + " is out of bounds; provable has ante size " +
          sequent.ante.length + " and succ size " + sequent.succ.length)
      val left = sequent.ante(antePos.getIndex)
      val right = sequent.succ(succPos.getIndex)
      val cutUsePos = AntePos(sequent.ante.length)
      cut(Imply(left, right)) <(
        /* use */ implyL(cutUsePos) & OnAll(TactixLibrary.close),
        /* show */ (assertE(right, "")(succPos) & hideR(succPos) & assertE(left, "")(antePos) ) partial /* This is the result. */)
    }
  }

  private val axMov: ProvableSig = proveBy("f_() + a_() * g_() = k_() -> (a_() = 0 -> f_() = k_())".asFormula,QE)

  def proveWithWitness(ctx:List[Term], witness:List[Term], instopt:Option[List[(Int,Term)]] = None) : ProvableSig = {
    val antes = ctx.map( t => Equal(t,Number(0)))
    val (wit,pfi) = assertWitness(witness)
    val pf = useFor(gtNotZero,PosInExpr(0::Nil))(SuccPosition(1))(pfi)
    //assert(pf.isProved)
    //Generate our own reduction instructions if not available
    //Proofs skipped
    val inst = instopt.getOrElse({
      val wit_norm = normalise(wit,true)._1
      val ctx_norm = ctx.map( t=> normalise(t,true)._1)
      reduction(ctx_norm,wit_norm)
    })
    proveBy(Sequent(antes.toIndexedSeq,IndexedSeq()),
      //1+s_i^2 > 0
      cut(pf.conclusion.succ.head) <(
        notL('Llast) &
        //Run the instructions
        inst.foldRight(ident)(
          (h,tac) =>
          implyRiKeep(AntePos(h._1),SuccPos(0))
          & useAt("ANON", axMov,PosInExpr(1::Nil),(us:Option[Subst])=>us.get++RenUSubst(("g_()".asTerm,h._2)::Nil))(1)
          & tac) &
        normaliseAt(SuccPosition(1,0::Nil)) &
        ?(cohideR(1) & byUS("= reflexive"))
        ,
        cohideR(1) & by(pf)
        ))
  }
}