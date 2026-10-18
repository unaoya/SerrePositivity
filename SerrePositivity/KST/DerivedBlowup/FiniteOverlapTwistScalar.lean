module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistUnits
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGAlgebraDiagram
public import SerrePositivity.KST.DerivedBlowup.RestrictedScalarIso

/-!
概要：KST §3.1 の O(m) の推移単元を有限重なりの Hom 複体の自己同型にする。
方針：局所係数環上の scalar 自己同型を共通基底環へ制限する。
規約：単元の向きは共変な frame の遷移、指数は全整数。
使われ方：係数 dg 圏の Hom の重み付けと実際の捻り加群。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：包含に沿う O(m) の推移単元による Hom 複体の指定自己同型。
方針：局所 Koszul 自己 Hom の scalar 倍を基底環へ制限する。
規約：KST §3.1。使われ方：捻りの Hom gauge の具体的な成分。 -/
def finiteOverlapTwistScalar (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) (m : ℤ) :
    ((finiteOverlapDGAlgebraDiagram R a).obj U).X ≅
      ((finiteOverlapDGAlgebraDiagram R a).obj U).X :=
  restrictedScalarUnitIso R (FiniteOverlapVertexRing R U)
    (homObject (FiniteOverlapVertexRing R U)
      (FiniteOverlapKoszulObject R a (finiteOverlapIndexPivot U) U.val) .point .point)
    (finiteOverlapTwistUnit R h m)

/-- 概要：捻り自己同型の順射は各次数で指定局所単元の scalar 倍。
方針：係数制限した scalar 自己同型の成分を読む。
規約：KST §3.1。使われ方：Hom の重み付けと合成の整合計算。 -/
theorem finiteOverlapTwistScalar_hom_apply (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) (m q : ℤ)
    (z : (homObject (FiniteOverlapVertexRing R U)
      (FiniteOverlapKoszulObject R a (finiteOverlapIndexPivot U) U.val) .point .point).X q) :
    ((finiteOverlapTwistScalar R a h m).hom.f q) z =
      (finiteOverlapTwistUnit R h m : FiniteOverlapVertexRing R U) • z := rfl

/-- 概要：恒等包含の捻り自己同型は恒等。
方針：推移単元の恒等律を scalar 自己同型の恒等律へ送る。
規約：KST §3.1。使われ方：Hom gauge の対角条件。 -/
theorem finiteOverlapTwistScalar_id (a : I → R) (T : FiniteOverlapIndex I) (m : ℤ) :
    finiteOverlapTwistScalar R a (le_refl T) m = Iso.refl _ := by
  unfold finiteOverlapTwistScalar
  rw [finiteOverlapTwistUnit_id, restrictedScalarUnitIso_one]
  rfl

/-- 概要：零捻りの Hom 自己同型は恒等。
方針：零乗の単元を scalar 自己同型へ送る。
規約：KST §3.1。使われ方：O(0) と構造加群の比較。 -/
theorem finiteOverlapTwistScalar_zero (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) : finiteOverlapTwistScalar R a h 0 = Iso.refl _ := by
  unfold finiteOverlapTwistScalar
  rw [finiteOverlapTwistUnit_zero, restrictedScalarUnitIso_one]
  rfl

/-- 概要：捻り指数の和は指定自己同型の合成に対応する。
方針：推移単元の加法則と scalar 自己同型の積公式を合成する。
規約：KST §3.1。使われ方：捻り自己関手の加法則。 -/
theorem finiteOverlapTwistScalar_add (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) (m n : ℤ) :
    finiteOverlapTwistScalar R a h (m + n) =
      finiteOverlapTwistScalar R a h m ≪≫ finiteOverlapTwistScalar R a h n := by
  unfold finiteOverlapTwistScalar
  rw [finiteOverlapTwistUnit_add, restrictedScalarUnitIso_mul]

/-- 概要：逆捻りの指定自己同型は逆同型。
方針：推移単元の負冪と scalar 自己同型の逆公式を使う。
規約：KST §3.1。使われ方：捻り自己関手の逆。 -/
theorem finiteOverlapTwistScalar_neg (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) (m : ℤ) :
    finiteOverlapTwistScalar R a h (-m) = (finiteOverlapTwistScalar R a h m).symm := by
  unfold finiteOverlapTwistScalar
  rw [finiteOverlapTwistUnit_neg, restrictedScalarUnitIso_inv]

end SerrePositivity.KST.DerivedBlowup
