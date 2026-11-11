module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeCompositionSections

/-!
概要：同じ section の底変換結合同型は、底の全ての射に対して厳密に自然。
方針：両方の pullback の section 同型の前合成自然性を同じ section 空間で比較する。
規約：元の比較成分の結合同型を変更しない。
使われ方：底全体の比較と元の分類 Hom の Segal 制限の整合性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  {E : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ結合同型を元の section へ戻すと、二重底変換の元の section 同型になる。 -/
lemma cocartesianBaseChangeAssociativityComponent_iso (a : A) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p l k a).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip
        (nerveMap (Under.forget a)) (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) rfl).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeCompositeSectionsIso p l k a).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 同じ底変換結合同型は、底の元の strict transport の射に対して自然。 -/
lemma cocartesianBaseChangeAssociativityComponent_naturality {a b : A} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap
        (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) f ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p l k b).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p l k a).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap (pullback.fst (nerveMap (l ⋙ k)) p) f := by
  let u : Over.mk (nerveMap (Under.forget b)) ⟶
      Over.mk (nerveMap (Under.forget a)) :=
    Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso_pre
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeComposite_isPullback p l k) u
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso_pre
    (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip u
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso
    (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip
    (nerveMap (Under.forget b)) (nerveMap (Under.forget b) ≫ nerveMap (l ⋙ k)) rfl).hom).mp
  rw [Category.assoc, cocartesianBaseChangeAssociativityComponent_iso, Category.assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre _ u ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso _ _ _ _).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p l k a).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre _ u ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso _ _ _ _).hom
  refine h₁.trans ?_
  have he := congrArg
    (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p ((Over.map (nerveMap (l ⋙ k))).map u))
    (cocartesianBaseChangeAssociativityComponent_iso p l k a).symm
  have hh := congrArg (fun z ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p l k a).hom ≫ z) h₂.symm
  exact he.trans ((Category.assoc _ _ _).trans hh)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
