module

public import SerrePositivity.KST.DerivedBlowup.BaseRestrictionDGFunctor
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTransitionComponents

/-!
概要：KST §3.1 の全有限重なりのチャート dg 遷移を共通基底環上で扱う。
方針：局所係数環から基底環へ制限し、実際の代数射に沿う dg 遷移を基底制限する。
規約：共通基底環上の図式であり、加群の厳密な貼り合わせは要求しない。
使われ方：dg 代数図式とその上の coherent な降下模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：有限重なりの局所 Koszul dg 模型を共通基底環に制限した対象型。
方針：局所係数環の構造射に沿う既存の dg 係数制限を使う。
規約：KST §3.1。使われ方：共通基底環上の dg 図式の対象。 -/
abbrev FiniteOverlapBaseKoszulObject (a : I → R) (i : I) (T : Finset I) :=
  DGRestriction (algebraMap R (FiniteOverlapRing R i T)) (FiniteOverlapKoszulObject R a i T)

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環の複体のモノイダル構造を照合するために必要。
/-- 概要：共通基底環上の有限重なり dg 遷移。
方針：局所化環の代数射と実際の半線形 dg 遷移を基底制限する。
規約：KST §3.1。使われ方：全有限重なりの共通係数 dg 図式の射。 -/
def finiteOverlapBaseDGTransition (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) :
    DGFunctor R (FiniteOverlapBaseKoszulObject R a i T) (FiniteOverlapBaseKoszulObject R a k U) :=
  baseRestrictionDGFunctor (finiteOverlapChartMap R i k h hi)
    (finiteOverlapDGTransition R a i k h hi)

set_option maxHeartbeats 2000000 in
-- 局所化環の元の dg 遷移と基底制限後の Hom を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環の複体のモノイダル構造を照合するために必要。
/-- 概要：基底制限後の有限重なり dg 遷移は各次数で元の像を保つ。
方針：外積模型を行先とする基底制限 dg 関手の成分公式を使う。
規約：KST §3.1。使われ方：共通基底環上の恒等・合成律。 -/
theorem finiteOverlapBaseDGTransition_apply (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) (v w : FiniteOverlapKoszulObject R a i T) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R i T) (FiniteOverlapKoszulObject R a i T) v w).X q) :
    (((finiteOverlapBaseDGTransition R a i k h hi).map v w).f q) z =
      (((finiteOverlapDGTransition R a i k h hi).map v w).f q) z := by
  exact baseRestrictionDGFunctor_exterior_apply (finiteOverlapChartMap R i k h hi)
    _ (finiteOverlapDGTransition R a i k h hi) v w q z

set_option maxHeartbeats 2000000 in
-- 局所化環の元の対象と基底制限後の対象を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環の複体のモノイダル構造を照合するために必要。
/-- 概要：共通基底環への制限は遷移の対象の像を保つ。
方針：基底制限 dg 関手の対象公式を使う。
規約：KST §3.1。使われ方：共通基底環上の遷移の合成で対象をそろえる。 -/
theorem finiteOverlapBaseDGTransition_obj (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) (v : FiniteOverlapKoszulObject R a i T) :
    (finiteOverlapBaseDGTransition R a i k h hi).obj v =
      (finiteOverlapDGTransition R a i k h hi).obj v :=
  baseRestrictionDGFunctor_obj _ _ v

end SerrePositivity.KST.DerivedBlowup
