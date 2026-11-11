module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionsEnrichedEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianSectionsPrecomposition

/-!
概要：section の定義域の制限と元の cocartesian 関手の高次作用との整合性。
方針：相対前合成と同じ section 作用を全入力で比較し、curry して混合作用を作る。
規約：自然性は全相対 Hom のパラメーターの射の等式で述べる。
使われ方：通常の底と cocartesian fibration 全体を同時に動かす Cat∞ 値分類写像。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- section の同じ全相対作用は、定義域を制限する前合成と厳密に可換。 -/
lemma cocartesianSectionsAction_overPre {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p q : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsAction b p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre q.hom f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p.hom f ▷ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsAction a p q := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, h⟩
  apply Subtype.ext
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- curry した同じ section の作用も、定義域の制限と全高次パラメーターで可換。 -/
lemma cocartesianSectionsPostHom_overPre {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p q : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom b p q ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p.hom b.hom)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre q.hom f) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom a p q ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p.hom f)).app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections q.hom a.hom) := by
  apply uncurry_injective
  rw [uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom, uncurry_curry, uncurry_pre_app,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom, uncurry_curry]
  exact cocartesianSectionsAction_overPre f p q

/-- 定義域の制限と cocartesian 関手の元の相対作用を同時に作用させる。 -/
def cocartesianSectionsMixedHom {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) (p q : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p.hom q.hom ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p.hom b.hom)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections q.hom a.hom) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom b p q ≫
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p.hom b.hom)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre q.hom f)

/-- 同じ混合作用は、両側の恒等射を内部 Hom の豊穣単位に写す。 -/
lemma cocartesianSectionsMixedHom_id {B : SSet.{u}} (a p : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorIdentity p ≫ cocartesianSectionsMixedHom (𝟙 a) p p =
      MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p.hom a.hom) := by
  rw [cocartesianSectionsMixedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre_id,
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p.hom a.hom)).map_id, Category.comp_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom_id]

/-- 二つの元の cocartesian 関手と定義域の二つの制限の混合作用は、同じ豊穣合成を保つ。 -/
lemma cocartesianSectionsMixedHom_comp {B : SSet.{u}} {a b c : Over B}
    (f : b ⟶ a) (g : c ⟶ b) (p q r : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorComposition p q r ≫ cocartesianSectionsMixedHom (g ≫ f) p r =
      (cocartesianSectionsMixedHom f p q ⊗ₘ cocartesianSectionsMixedHom g q r) ≫
        MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p.hom a.hom)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections q.hom b.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections r.hom c.hom) := by
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, h, k⟩
  apply Subtype.ext
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
