module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
概要：前合成の同値条件の直積による保存。
方針：内部 currying の同型を通じて、前合成を内部 Hom の後合成に移す。
規約：単体集合の始域に quasicategory 性を要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join 比較の直積との両立。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単体集合の同型は quasicategory の同値を与える。
方針：厳密な逆射の等式から関手単体集合の同型を作る。
規約：両対象は quasicategory。
使われ方：Kerodon §4.5.1（Tag 01DQ） の厳密な模型の変更。 -/
noncomputable def qCatEquivalenceOfIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : X ≅ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y where
  hom := e.hom
  inv := e.inv
  homInvIso := eqToIso (congrArg (fun f : X ⟶ X ↦
    SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) e.hom_inv_id)
  invHomIso := eqToIso (congrArg (fun f : Y ⟶ Y ↦
    SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) e.inv_hom_id)

/-- 概要：内部 currying は最初の変数での前合成に自然。
方針：二回 uncurry し、評価の自然性と結合子の自然性を使う。
規約：任意の単体集合と射に対する厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の直積による同値条件の保存。 -/
lemma ihomCurry_pre_whiskerRight {A B : SSet.{u}} (f : A ⟶ B) (K X : SSet.{u}) :
    (pre (f ▷ K)).app X ≫ (ihomCurryIso A K X).hom =
      (ihomCurryIso B K X).hom ≫ (ihom K).map ((pre f).app X) := by
  change (pre (f ▷ K)).app X ≫ ihomCurry A K X =
    ihomCurry B K X ≫ (ihom K).map ((pre f).app X)
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right, uncurry_ihomCurry]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_ihomCurry,
    uncurry_curry]
  simp only [← Category.assoc]
  rw [associator_inv_naturality_right]
  simp only [Category.assoc, id_tensor_pre_app_comp_ev]
  rw [← Category.assoc, ← associator_inv_naturality_left]
  simp only [uncurry_curry, Category.assoc]

/-- 概要：前合成の同値条件は任意の右直積で保存される。
方針：内部 currying による同型の共役と、同値の内部 Hom による保存を使う。
規約：A、B、K に quasicategory 性を要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join 比較のセルへの還元。 -/
lemma IsPrecompositionEquivalence.whiskerRight {A B : SSet.{u}} {f : A ⟶ B}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (f ▷ K) := by
  intro X hX
  have h := (qCatEquivalenceOfIso (ihomCurryIso B K X)).isQCatEquivalence.comp
    ((hf X).postcompose K)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((ihomCurryIso B K X).hom ≫
    (ihom K).map ((pre f).app X)) at h
  rw [← ihomCurry_pre_whiskerRight] at h
  exact (qCatEquivalenceOfIso (ihomCurryIso A K X)).isQCatEquivalence.cancel_right h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsPrecompositionEquivalence (whiskerRight)


/-- 概要：単体集合の同型は前合成の同値条件を満たす。
方針：前合成による厳密な逆同型を構成する。
規約：元の対象の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の直積の対称性による移送。 -/
lemma isPrecompositionEquivalence_of_iso {A B : SSet.{u}} (e : A ≅ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence e.hom := by
  intro X hX
  let i : (ihom B).obj X ≅ (ihom A).obj X :=
    { hom := (pre e.hom).app X
      inv := (pre e.inv).app X
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id, NatTrans.id_app]
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← pre_map, e.hom_inv_id, pre_id, NatTrans.id_app] }
  exact (qCatEquivalenceOfIso i).isQCatEquivalence

/-- 概要：前合成の同値条件は任意の左直積で保存される。
方針：対称性の同型で右直積の場合に移す。
規約：元の三つの単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join 比較のセルへの還元。 -/
lemma IsPrecompositionEquivalence.whiskerLeft {A B : SSet.{u}} {f : A ⟶ B}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (K ◁ f) := by
  have h := ((isPrecompositionEquivalence_of_iso (β_ K A)).comp
    (hf.whiskerRight K)).comp (isPrecompositionEquivalence_of_iso (β_ B K))
  have heq : ((β_ K A).hom ≫ f ▷ K) ≫ (β_ B K).hom = K ◁ f := by
    rw [Category.assoc, ← BraidedCategory.braiding_naturality_right_assoc,
      SymmetricCategory.symmetry, Category.comp_id]
  rw [heq] at h
  exact h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsPrecompositionEquivalence (whiskerLeft)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
