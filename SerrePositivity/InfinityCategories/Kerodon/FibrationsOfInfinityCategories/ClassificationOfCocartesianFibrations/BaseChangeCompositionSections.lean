module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeCompositionProjection

/-!
概要：底変換の比較の合成を、同じ元の section 空間への厳密な等式として表す。
方針：二重の pullback の同じ射影を使い、全相対族の等式から section の等式を回収する。
規約：独立な同値の代表を選ばず、元の pullback と元の比較成分を使う。
使われ方：分類 Hom の底変換比較の合成の整合性。

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
  {E : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
  (l : A ⥤ D) (k : D ⥤ C) (a : A)

/-- 二回の元の pullback の射影は、合成した底変換の実際の pullback 正方形。 -/
lemma cocartesianBaseChangeComposite_isPullback :
    IsPullback
      (pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p) ≫ pullback.snd (nerveMap k) p)
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) p (nerveMap (l ⋙ k)) :=
  (IsPullback.of_hasPullback (nerveMap l) (pullback.fst (nerveMap k) p)).flip.paste_horiz
    (IsPullback.of_hasPullback (nerveMap k) p).flip

/-- 二回底変換した同じ section を、元の全空間への section と同定する。 -/
def cocartesianBaseChangeCompositeSectionsIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) a ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso (cocartesianBaseChangeComposite_isPullback p l k)
    (nerveMap (Under.forget a)) (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) rfl

/-- 元の比較成分の二回の合成は、同じ section 表示では合成した底変換の比較そのもの。 -/
lemma cocartesianStrictTransportBaseChangeComponent_comp_sections :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p k (l.obj a) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent (pullback.fst (nerveMap k) p) l a) ≫
        (cocartesianBaseChangeCompositeSectionsIso p l k a).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p (l ⋙ k) a ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip
          (nerveMap (Under.forget a)) (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) rfl).hom := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p
    (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)))).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
  rw [cocartesianBaseChangeCompositeSectionsIso,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso_hom_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso_hom_uncurry]
  simpa only [Category.id_comp, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent_comp_uncurry_snd p l k a
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport p (k.obj (l.obj a))))

/-- 二重底変換と直接の底変換の strict transport の、同じ section による同型。 -/
def cocartesianBaseChangeAssociativityComponent :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) a ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport (pullback.fst (nerveMap (l ⋙ k)) p) a :=
  cocartesianBaseChangeCompositeSectionsIso p l k a ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip
      (nerveMap (Under.forget a)) (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) rfl).symm

/-- 同じ結合同型を通すと、二回の元の比較は直接の元の比較に厳密に一致する。 -/
lemma cocartesianStrictTransportBaseChangeComponent_comp :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p k (l.obj a) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent (pullback.fst (nerveMap k) p) l a) ≫
        (cocartesianBaseChangeAssociativityComponent p l k a).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p (l ⋙ k) a := by
  dsimp only [cocartesianBaseChangeAssociativityComponent, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, cocartesianStrictTransportBaseChangeComponent_comp_sections,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
