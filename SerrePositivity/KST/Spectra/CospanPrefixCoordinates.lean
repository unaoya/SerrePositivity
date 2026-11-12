module

public import SerrePositivity.KST.Spectra.CospanBousfieldKanWeight
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PrefixOverWeight

/-!
概要：元の cospan の各射の初区間の BK 重みを、元のホーンの左右の辺へ厳密同定する。
方針：中央 over 圏の忘却で初区間の二頂点を読み、既存のホーン重み同型を用いる。
規約：元の cospan の左・右の射を保持。使われ方：元の解像切断の二つの三単体の指定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CospanShape

/-- 元の小さい cospan の左の一射の列。 -/
abbrev leftArrow : ComposableArrows (AsSmall.{u} WalkingCospan) 1 :=
  ComposableArrows.mk₁ (AsSmall.up.map WalkingCospan.Hom.inl)

/-- 元の小さい cospan の右の一射の列。 -/
abbrev rightArrow : ComposableArrows (AsSmall.{u} WalkingCospan) 1 :=
  ComposableArrows.mk₁ (AsSmall.up.map WalkingCospan.Hom.inr)

/-- 左射の元の初区間をホーン重みへ送ると、元の左辺に厳密一致する。 -/
lemma leftPrefix_horn :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight leftArrow.{u}).app (1 : Fin 2) ≫
      cospanBKWeightIso.hom.app (AsSmall.up.obj .one) = horn₂₂.ι₀₂ := by
  apply SSet.yonedaEquiv.injective
  change (cospanNerveHornIso.hom).app (Opposite.op ⦋1⦌)
    ((nerveMap (Over.forget
      (AsSmall.up.obj WalkingCospan.one : AsSmall.{u} WalkingCospan))).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain leftArrow (1 : Fin 2))) = _
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 右射の元の初区間をホーン重みへ送ると、元の右辺に厳密一致する。 -/
lemma rightPrefix_horn :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight rightArrow.{u}).app (1 : Fin 2) ≫
      cospanBKWeightIso.hom.app (AsSmall.up.obj .one) = horn₂₂.ι₁₂ := by
  apply SSet.yonedaEquiv.injective
  change (cospanNerveHornIso.hom).app (Opposite.op ⦋1⦌)
    ((nerveMap (Over.forget
      (AsSmall.up.obj WalkingCospan.one : AsSmall.{u} WalkingCospan))).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain rightArrow (1 : Fin 2))) = _
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 二つの元の初区間の終点は、同じ中央の恒等射の over 頂点を保持する。 -/
lemma prefix_target_common :
    stdSimplex.δ (0 : Fin 2) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight leftArrow.{u}).app (1 : Fin 2) =
      stdSimplex.δ (0 : Fin 2) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight rightArrow).app (1 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  change SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫
    (SSet.yonedaEquiv (X := nerve (Over
      (AsSmall.up.obj WalkingCospan.one : AsSmall.{u} WalkingCospan))) (n := ⦋1⦌)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain leftArrow.{u} (1 : Fin 2))) =
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫
        (SSet.yonedaEquiv (X := nerve (Over
        (AsSmall.up.obj WalkingCospan.one : AsSmall.{u} WalkingCospan))) (n := ⦋1⦌)).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain rightArrow.{u} (1 : Fin 2)))
  simp only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · fin_cases i
    rfl
  · intro i j f
    exact Subsingleton.elim _ _

end SerrePositivity.KST.Spectra.CospanShape
