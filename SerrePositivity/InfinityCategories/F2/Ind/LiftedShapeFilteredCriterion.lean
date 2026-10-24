module

public import SerrePositivity.InfinityCategories.F2.Compact.FilteredUniverse
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeCocone
/-!
概要：小さい κ-small 試験形状の余錐から、大きい全空間の filtered 性を得る。
方針：任意の有限形状を小さい有限形状へ縮小し、同じ元の図式への余錐を戻す。
規約：大きい全空間の小ささを仮定しない。
使われ方：Ind の評価の under comma の filtered 性と cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：小さい試験形状の全余錐が存在すれば、大きい全空間も filtered。
方針：有限形状の宇宙を縮小する。規約：元の図式を保持。使われ方：Quillen A の入力。 -/
lemma isFilteredInfinity_of_liftedShape_cocones {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (X : SSet.{u + 1}) [Quasicategory X]
    (h : ∀ {A : SSet.{u}}, IsKappaSmall κ A →
      ∀ q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ X, Nonempty (JoinCocone q)) :
    IsFilteredInfinity X := by
  constructor
  intro K hK f
  have (n : SimplexCategoryᵒᵖ) : Small.{u} (K.obj n) := inferInstance
  let A := smallSimplicialSet.{u, u + 1} K
  let e := smallSimplicialSetIso.{u, u + 1} K
  have : A.Finite := Compact.finite_smallSimplicialSet K
  obtain ⟨c⟩ := h (isKappaSmall_of_finite hκ.aleph0_le A) (e.hom ≫ f)
  exact ⟨(e.inv_hom_id_assoc f) ▸ c.restrict e.inv⟩
end SerrePositivity.InfinityCategories.F2.Ind
