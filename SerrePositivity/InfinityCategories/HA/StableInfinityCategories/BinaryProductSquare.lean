module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductSquare

/-! # 二つの指定頂点を持つ零終点の引き戻し

概要：安定 ∞ 圏の任意の二頂点に対し、それらから零終点へ向かう引き戻し四角形がある。
方針：反対圏の零始点の押し出しを双対化して元の値域へ戻す。
規約：二つの入力頂点を厳密に指定する。使われ方：h C の二項積の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：任意の二頂点を右下・左上に持つ零終点の引き戻し四角形が存在する。
方針：反対圏で二頂点を指定した零始点の押し出しを双対化する。
規約：値域は安定な quasicategory。使われ方：二点図式の極限と双積の存在。 -/
lemma exists_zeroTargetPullbackSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (x y : X _⦋0⦌) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 1 1) ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 1 0 = x ∧
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 1 = y ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare R := by
  obtain ⟨R, hz, hRx, hRy, hR⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_zeroSourcePushoutSquare (X := X.op)
    (SSet.opObjEquiv.symm x) (SSet.opObjEquiv.symm y)
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.dualSquare R ≫ q, ?_, ?_, ?_, ?_⟩
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := X) (SSet.opObjEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0))
    exact hz.unop
  · change SSet.opObjEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 1 0) = x
    exact (congrArg SSet.opObjEquiv hRx).trans (SSet.opObjEquiv.apply_symm_apply x)
  · change SSet.opObjEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 1) = y
    exact (congrArg SSet.opObjEquiv hRy).trans (SSet.opObjEquiv.apply_symm_apply y)
  · exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_postcomp_isIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.dualSquare R) q).1
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_dualSquare R).1 hR)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
