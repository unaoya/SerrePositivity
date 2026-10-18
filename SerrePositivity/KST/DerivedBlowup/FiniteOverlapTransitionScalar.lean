module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapBaseDGTransition

/-!
概要：KST §3.1 の共通基底環上のチャート遷移の局所係数半線形性。
方針：基底制限後の成分を元の半線形 dg 遷移の線形写像へ戻す。
規約：始点の scalar は実際のチャート環射で行先へ送る。
使われ方：O(m) の推移単元と係数 dg 圏の合成の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 局所係数環と基底環の Hom の成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
/-- 概要：共通基底環に制限したチャート遷移は局所係数 scalar を環射で送る。
方針：元の dg 遷移の線形性を係数制限した行先の scalar 作用として読む。
規約：KST §3.1。使われ方：捻りの二つの重みを同じ係数環に集める。 -/
theorem finiteOverlapBaseDGTransition_smul (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) (q : ℤ)
    (b : FiniteOverlapRing R i T)
    (z : (homObject (FiniteOverlapRing R i T)
      (FiniteOverlapKoszulObject R a i T) .point .point).X q) :
    (((finiteOverlapBaseDGTransition R a i k h hi).map .point .point).f q) (b • z) =
      finiteOverlapChartMap R i k h hi b •
        (show (homObject (FiniteOverlapRing R k U)
          (FiniteOverlapKoszulObject R a k U) .point .point).X q from
          (((finiteOverlapBaseDGTransition R a i k h hi).map .point .point).f q) z) := by
  rw [finiteOverlapBaseDGTransition_apply, finiteOverlapBaseDGTransition_apply]
  exact (((finiteOverlapDGTransition R a i k h hi).map .point .point).f q).hom.map_smul b z

end SerrePositivity.KST.DerivedBlowup
