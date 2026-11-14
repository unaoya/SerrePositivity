module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomotopyStrictBaseSquare
/-!
概要：厳密基底上での指定恒等と augmentation 正方形を、同じ入力制限へ移す。
方針：前後合成の交換と恒等同型の保存を用いて指定値を型付きで保つ。
規約：新しい入力同型を選ばない。使われ方：元の入力 Up に沿う実 augmentation 正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
private lemma refl_heq_of_map_eq {X Y : SSet.{u}} {f g : X ⟶ Y} (h : f = g) :
    HEq (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)))
      (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))) := by cases h; rfl
/-- 厳密基底の指定恒等は、同じ入力制限の後にも指定された恒等の値を保持する。 -/
lemma functorIso_strictBase_precomp_heq {W X Y B : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : Y ⟶ B) (h : X ⟶ B)
    (hf : f ≫ p = h) (hg : g ≫ p = h)
    (he : HEq (e.postcomp p) (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h))))
    (a : W ⟶ X) :
    HEq ((e.precomp a).postcomp p)
      (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((a ≫ f) ≫ p)))) := by
  let b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso h h := Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h))
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq b (e.postcomp p) hf.symm hg.symm he a
  have hid : b.precomp a = Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ h))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
    exact CategoryTheory.Functor.mapIso_refl _ _
  have hm : a ≫ h = (a ≫ f) ≫ p := by rw [Category.assoc, hf]
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp e a p)).trans
    (hp.trans ((heq_of_eq hid).trans (refl_heq_of_map_eq hm)))
/-- 同じ厳密基底上の augmentation 正方形は、任意の指定入力で制限しても保たれる。 -/
lemma strictBaseHomotopySquare_precomp_heq {W X Y B Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z]
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : Y ⟶ B) (t : B ⟶ Z)
    (r : Y ⟶ Z) (H : SSet.Homotopy r (p ≫ t)) (h : X ⟶ B)
    (hf : f ≫ p = h) (hg : g ≫ p = h)
    (he : HEq (e.postcomp p) (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h))))
    (a : W ⟶ X) :
    HEq (((e.precomp a).postcomp r).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (a ≫ g))))
      (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (a ≫ f)))) := by
  have hpre : (a ≫ g) ≫ p = (a ≫ f) ≫ p := by
    simp only [Category.assoc, hg, hf]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictBaseHomotopySquare_heq (e.precomp a) p t r H hpre
    (functorIso_strictBase_precomp_heq e p h hf hg he a)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
