module

public import SerrePositivity.InfinityCategories.F1.CocartesianSectionsEnrichedEvaluation
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianSectionsPrecomposition

/-!
概要：section の定義域の制限と元の cocartesian 関手の高次作用との整合性。
方針：相対前合成と同じ section 作用を全入力で比較し、curry して混合作用を作る。
規約：自然性は全相対 Hom のパラメーターの射の等式で述べる。
使われ方：通常の底と cocartesian fibration 全体を同時に動かす Cat∞ 値分類写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- section の同じ全相対作用は、定義域を制限する前合成と厳密に可換。 -/
lemma cocartesianSectionsAction_overPre {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p q : Over B) :
    cocartesianSectionsAction b p q ≫ kanCocartesianSectionsPre q.hom f =
      kanCocartesianSectionsPre p.hom f ▷ _ ≫ cocartesianSectionsAction a p q := by
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
    cocartesianSectionsPostHom b p q ≫
      (ihom (kanCocartesianSections p.hom b.hom)).map (kanCocartesianSectionsPre q.hom f) =
    cocartesianSectionsPostHom a p q ≫
      (pre (kanCocartesianSectionsPre p.hom f)).app (kanCocartesianSections q.hom a.hom) := by
  apply uncurry_injective
  rw [uncurry_natural_right, cocartesianSectionsPostHom, uncurry_curry, uncurry_pre_app,
    cocartesianSectionsPostHom, uncurry_curry]
  exact cocartesianSectionsAction_overPre f p q

/-- 定義域の制限と cocartesian 関手の元の相対作用を同時に作用させる。 -/
def cocartesianSectionsMixedHom {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) (p q : Over B) :
    cocartesianRelativeFunctorSpace p.hom q.hom ⟶
      (ihom (kanCocartesianSections p.hom b.hom)).obj (kanCocartesianSections q.hom a.hom) :=
  cocartesianSectionsPostHom b p q ≫
    (ihom (kanCocartesianSections p.hom b.hom)).map (kanCocartesianSectionsPre q.hom f)

/-- 同じ混合作用は、両側の恒等射を内部 Hom の豊穣単位に写す。 -/
lemma cocartesianSectionsMixedHom_id {B : SSet.{u}} (a p : Over B) :
    cocartesianRelativeFunctorIdentity p ≫ cocartesianSectionsMixedHom (𝟙 a) p p =
      MonoidalClosed.id (kanCocartesianSections p.hom a.hom) := by
  rw [cocartesianSectionsMixedHom, kanCocartesianSectionsPre_id,
    (ihom (kanCocartesianSections p.hom a.hom)).map_id, Category.comp_id,
    cocartesianSectionsPostHom_id]

/-- 二つの元の cocartesian 関手と定義域の二つの制限の混合作用は、同じ豊穣合成を保つ。 -/
lemma cocartesianSectionsMixedHom_comp {B : SSet.{u}} {a b c : Over B}
    (f : b ⟶ a) (g : c ⟶ b) (p q r : Over B) :
    cocartesianRelativeFunctorComposition p q r ≫ cocartesianSectionsMixedHom (g ≫ f) p r =
      (cocartesianSectionsMixedHom f p q ⊗ₘ cocartesianSectionsMixedHom g q r) ≫
        MonoidalClosed.comp (kanCocartesianSections p.hom a.hom)
          (kanCocartesianSections q.hom b.hom) (kanCocartesianSections r.hom c.hom) := by
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

end SerrePositivity.InfinityCategories
