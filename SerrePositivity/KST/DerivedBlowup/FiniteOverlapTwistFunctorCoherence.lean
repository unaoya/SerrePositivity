module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeInverse
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistGauge

/-!
概要：KST §3.1 の整数捻りの加法と逆を大域係数 dg 関手の等式へ移す。
方針：局所 scalar 自己同型の整数冪公式と gauge の外延性を使う。
規約：対象写像と全次数 Hom 写像の等式として保持する。
使われ方：O(m) の捻り作用の合成と逆の大域整合性。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：零捻りの指定 gauge は恒等 gauge。
方針：全ての包含で scalar 自己同型の零指数公式を使う。
規約：KST §3.1。使われ方：零捻りの作用の単位条件。 -/
theorem finiteOverlapTwistGauge_zero (a : I → R) :
    finiteOverlapTwistGauge R a 0 =
      diagramHomGaugeIdentity (finiteOverlapDGAlgebraDiagram R a) := by
  apply DiagramHomGauge.ext
  intro T U h
  exact finiteOverlapTwistScalar_zero R a h

/-- 概要：整数捻りの和は指定 gauge の合成に一致する。
方針：全ての包含で scalar 自己同型の加法公式を使う。
規約：KST §3.1。使われ方：捻り作用の加法整合性。 -/
theorem finiteOverlapTwistGauge_add (a : I → R) (m n : ℤ) :
    finiteOverlapTwistGauge R a (m + n) =
      DiagramHomGauge.comp (finiteOverlapDGAlgebraDiagram R a)
        (finiteOverlapTwistGauge R a m) (finiteOverlapTwistGauge R a n) := by
  apply DiagramHomGauge.ext
  intro T U h
  exact finiteOverlapTwistScalar_add R a h m n

/-- 概要：負の整数捻りの gauge は指定逆 gauge。
方針：全ての包含で scalar 自己同型の負指数公式を使う。
規約：KST §3.1。使われ方：捻り作用の指定逆。 -/
theorem finiteOverlapTwistGauge_neg (a : I → R) (m : ℤ) :
    finiteOverlapTwistGauge R a (-m) =
      DiagramHomGauge.inverse (finiteOverlapDGAlgebraDiagram R a)
        (finiteOverlapTwistGauge R a m) := by
  apply DiagramHomGauge.ext
  intro T U h
  exact finiteOverlapTwistScalar_neg R a h m

/-- 概要：零捻りの係数 dg 自己関手は恒等。
方針：零 gauge の同定を一般の恒等関手公式へ渡す。
規約：KST §3.1。使われ方：構造加群との大域比較。 -/
theorem finiteOverlapTwistDGFunctor_zero (a : I → R) :
    finiteOverlapTwistDGFunctor R a 0 =
      DGFunctor.id (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a)) := by
  unfold finiteOverlapTwistDGFunctor
  rw [finiteOverlapTwistGauge_zero, diagramGaugeDGFunctor_identity]

/-- 概要：指定整数捻りの dg 関手は指数の和を合成へ送る。
方針：一般の gauge 合成保存と具体的整数冪の加法公式を使う。
規約：KST §3.1。使われ方：捻り作用の大域的な結合整合性。 -/
theorem finiteOverlapTwistDGFunctor_add (a : I → R) (m n : ℤ) :
    (finiteOverlapTwistDGFunctor R a m).comp (finiteOverlapTwistDGFunctor R a n) =
      finiteOverlapTwistDGFunctor R a (m + n) := by
  unfold finiteOverlapTwistDGFunctor
  rw [diagramGaugeDGFunctor_comp, ← finiteOverlapTwistGauge_add]

/-- 概要：整数捻りに逆指数の捻りを続けると恒等 dg 関手。
方針：指数の加法公式と零捻りを使う。
規約：KST §3.1。使われ方：大域の捻り作用の逆。 -/
theorem finiteOverlapTwistDGFunctor_neg_comp (a : I → R) (m : ℤ) :
    (finiteOverlapTwistDGFunctor R a m).comp (finiteOverlapTwistDGFunctor R a (-m)) =
      DGFunctor.id (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a)) := by
  rw [finiteOverlapTwistDGFunctor_add, add_neg_cancel, finiteOverlapTwistDGFunctor_zero]

/-- 概要：逆指数の捻りに元の捻りを続けても恒等 dg 関手。
方針：指数の加法公式と零捻りを使う。
規約：KST §3.1。使われ方：大域の捻り作用の両側逆。 -/
theorem finiteOverlapTwistDGFunctor_comp_neg (a : I → R) (m : ℤ) :
    (finiteOverlapTwistDGFunctor R a (-m)).comp (finiteOverlapTwistDGFunctor R a m) =
      DGFunctor.id (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a)) := by
  rw [finiteOverlapTwistDGFunctor_add, neg_add_cancel, finiteOverlapTwistDGFunctor_zero]

end SerrePositivity.KST.DerivedBlowup
