module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.StrictSpanPointHomEnd

/-!
概要：持ち上げた通常の span のホーン表示の二辺を、元の指定構造射へ同定する。
方針：元の nerve とホーンの同型の辺の法則を、同じ宇宙の同型で引く。
規約：二辺の像を対象ごとに選ばず、区間からの射の等式とする。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、S8 の押し出し四角形の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 持ち上げた span のホーン表示の左辺は、元の左構造射の同じ辺。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、形状同型の評価の法則。 -/
lemma strictSpanHornIso_inv_left_edge :
    horn₂₀.ι₀₁ ≫ (strictSpanHornIso.{u, v}).inv =
      (SSet.yonedaEquiv.symm
        (ULift.up (nerve.edgeMk (AsSmall.up.map WalkingSpan.Hom.fst)).edge) :
        (Δ[1] : SSet.{max u v}) ⟶
          (SSet.uliftFunctor.{v, u}).obj (nerve (AsSmall.{u} WalkingSpan))) := by
  change horn₂₀.ι₀₁ ≫
    (hornToSpanNerve ≫ (liftedAsSmallNerveIso.{u, v} WalkingSpan).inv) = _
  rw [← Category.assoc, hornToSpanNerve_left_edge]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  simp only [_root_.Equiv.apply_symm_apply]
  apply ULift.ext
  refine ComposableArrows.ext₁ rfl rfl ?_
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- 持ち上げた span のホーン表示の右辺は、元の右構造射の同じ辺。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、形状同型の評価の法則。 -/
lemma strictSpanHornIso_inv_right_edge :
    horn₂₀.ι₀₂ ≫ (strictSpanHornIso.{u, v}).inv =
      (SSet.yonedaEquiv.symm
        (ULift.up (nerve.edgeMk (AsSmall.up.map WalkingSpan.Hom.snd)).edge) :
        (Δ[1] : SSet.{max u v}) ⟶
          (SSet.uliftFunctor.{v, u}).obj (nerve (AsSmall.{u} WalkingSpan))) := by
  change horn₂₀.ι₀₂ ≫
    (hornToSpanNerve ≫ (liftedAsSmallNerveIso.{u, v} WalkingSpan).inv) = _
  rw [← Category.assoc, hornToSpanNerve_right_edge]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  simp only [_root_.Equiv.apply_symm_apply]
  apply ULift.ext
  refine ComposableArrows.ext₁ rfl rfl ?_
  apply ULift.ext
  exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
