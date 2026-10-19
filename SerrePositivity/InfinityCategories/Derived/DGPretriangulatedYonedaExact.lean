module
public import SerrePositivity.InfinityCategories.Derived.DGRepleteYonedaStability
public import SerrePositivity.InfinityCategories.Derived.DGModulePropertyExactInclusion

/-! # 前三角 dg 圏の実 Yoneda の完全性と押し出しの反映

概要：共通宇宙の Yoneda は完全であり、実押し出し四角形を反映する。
方針：ホモトピー表現可能部分への同値と全加群への充満包含を使う。
規約：実余極限性を反映する。使われ方：dg 関手の完全性の加群模型による判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v)
  [DGCategory A D] [Small.{u} D] [IsDGPretriangulated A D]

/-- 共通宇宙の前三角 dg 圏から全加群への実 Yoneda は完全。 -/
theorem dgPretriangulatedYoneda_isExactFunctor :
    IsExactFunctor (dgNerve.map
      ((dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp (dgYoneda A D))) := by
  let := dgRepleteYonedaNerve_isExactFunctor A D
  let := dgRepleteRepresentablesInclusion_isExactFunctor A D
  have h : IsExactFunctor (dgNerve.map (dgRepleteYoneda A D) ≫
      dgNerve.map (dgFullSubcategoryInclusion A (RightModule A D)
        (dgHomotopyRepresentable A D))) := inferInstance
  rwa [← dgNerve.map_comp, dgRepleteYoneda_inclusion] at h

/-- 前三角 dg 圏の共通宇宙の実 Yoneda は、全四角形の押し出し性を反映する。 -/
lemma dgPretriangulatedYoneda_reflectsPushoutSquare
    (L : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) ⟶
      dgNerve A (DGUniverseLift.{v, max (u + 1) v} D))
    (h : IsPushoutSquare (L ≫ dgNerve.map
      ((dgUniverseLiftDown A D).comp (dgYoneda A D)))) : IsPushoutSquare L := by
  let := dgUniverseLiftNerve_isStable A D
  let : IsStable (dgNerve A (DGRepleteRepresentables A D)) :=
    dgHomotopyRepresentableNerve_isStable A D
  let R := dgNerve.map (dgRepleteYoneda A D)
  let I := dgNerve.map (dgFullSubcategoryInclusion A (RightModule A D)
    (dgHomotopyRepresentable A D))
  have he : R ≫ I = dgNerve.map ((dgUniverseLiftDown A D).comp (dgYoneda A D)) := by
    rw [← dgNerve.map_comp, dgRepleteYoneda_inclusion]
  have hr : IsPushoutSquare (L ≫ R) := by
    apply isColimitCone_of_fullInclusion A (RightModule A D)
      (dgHomotopyRepresentable A D) (pushoutCocone _)
    change IsPushoutSquare ((L ≫ R) ≫ I)
    rwa [Category.assoc, he]
  have hp := IsStable.pullback_of_pushout_square (L ≫ R) hr
  have hl : IsPullbackSquare L := by
    apply ((dgRepleteYonedaNerveEquivalence A D).isLimitCone_iff (pullbackCone L)).mpr
    simpa only [IsPullbackSquare, pullbackCone, pullbackCospan, mapJoinCone,
      Category.assoc, dgRepleteYonedaNerveEquivalence_hom] using hp
  exact IsStable.pushout_of_pullback_square L hl

end SerrePositivity.InfinityCategories
