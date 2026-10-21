module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeCompositionSections

/-!
概要：同じ section の底変換結合同型は、底の全ての射に対して厳密に自然。
方針：両方の pullback の section 同型の前合成自然性を同じ section 空間で比較する。
規約：元の比較成分の結合同型を変更しない。
使われ方：底全体の比較と元の分類 Hom の Segal 制限の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  {E : SSet.{u}} (p : E ⟶ nerve C) [CocartesianFibration p] (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ結合同型を元の section へ戻すと、二重底変換の元の section 同型になる。 -/
lemma cocartesianBaseChangeAssociativityComponent_iso (a : A) :
    (cocartesianBaseChangeAssociativityComponent p l k a).hom ≫
      (cocartesianSectionsPullbackIso (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip
        (nerveMap (Under.forget a)) (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) rfl).hom =
      (cocartesianBaseChangeCompositeSectionsIso p l k a).hom := by
  simp only [cocartesianBaseChangeAssociativityComponent, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 同じ底変換結合同型は、底の元の strict transport の射に対して自然。 -/
lemma cocartesianBaseChangeAssociativityComponent_naturality {a b : A} (f : a ⟶ b) :
    kanCocartesianStrictTransportMap
        (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) f ≫
      (cocartesianBaseChangeAssociativityComponent p l k b).hom =
    (cocartesianBaseChangeAssociativityComponent p l k a).hom ≫
      kanCocartesianStrictTransportMap (pullback.fst (nerveMap (l ⋙ k)) p) f := by
  let u : Over.mk (nerveMap (Under.forget b)) ⟶
      Over.mk (nerveMap (Under.forget a)) :=
    Over.homMk (kanCocartesianUnderMap f) (kanCocartesianUnderMap_projection f)
  have h₁ := cocartesianSectionsPullbackIso_pre
    (cocartesianBaseChangeComposite_isPullback p l k) u
  have h₂ := cocartesianSectionsPullbackIso_pre
    (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip u
  apply (cancel_mono (cocartesianSectionsPullbackIso
    (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip
    (nerveMap (Under.forget b)) (nerveMap (Under.forget b) ≫ nerveMap (l ⋙ k)) rfl).hom).mp
  rw [Category.assoc, cocartesianBaseChangeAssociativityComponent_iso, Category.assoc]
  change kanCocartesianSectionsPre _ u ≫
      (cocartesianSectionsPullbackIso _ _ _ _).hom =
    (cocartesianBaseChangeAssociativityComponent p l k a).hom ≫
      kanCocartesianSectionsPre _ u ≫ (cocartesianSectionsPullbackIso _ _ _ _).hom
  refine h₁.trans ?_
  have he := congrArg
    (fun z ↦ z ≫ kanCocartesianSectionsPre p ((Over.map (nerveMap (l ⋙ k))).map u))
    (cocartesianBaseChangeAssociativityComponent_iso p l k a).symm
  have hh := congrArg (fun z ↦
    (cocartesianBaseChangeAssociativityComponent p l k a).hom ≫ z) h₂.symm
  exact he.trans ((Category.assoc _ _ _).trans hh)

end SerrePositivity.InfinityCategories
