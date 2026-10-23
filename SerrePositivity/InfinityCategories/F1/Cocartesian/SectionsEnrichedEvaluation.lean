module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionsAction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.FibrationInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.QCatSimplicial
public import SerrePositivity.InfinityCategories.F1.Categories.CoreEnrichedFunctor
public import SerrePositivity.InfinityCategories.F1.Coherent.NervePostcomposition

/-!
概要：元の cocartesian section への全相対作用を、QCat 値の豊穣評価へ束ねる。
方針：同じ section 作用を curry し、単位・合成則を移してから両側の Hom の core を取る。
規約：追加の instance 仮定や独立な写像空間の同値による置き換えは用いない。
使われ方：Cat∞ 値 strict transport の fibration 全体にわたる coherent な関手性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ cocartesian section の作用を、相対 Hom から内部 Hom への作用に curry する。 -/
def cocartesianSectionsPostHom {B : SSet.{u}} (a p q : Over B) :
    cocartesianRelativeFunctorSpace p.hom q.hom ⟶
      (ihom (kanCocartesianSections p.hom a.hom)).obj (kanCocartesianSections q.hom a.hom) :=
  curry (cocartesianSectionsAction a p q)

/-- 同じ section の豊穣後合成は、元の cocartesian 恒等射を内部 Hom の単位に写す。 -/
lemma cocartesianSectionsPostHom_id {B : SSet.{u}} (a p : Over B) :
    cocartesianRelativeFunctorIdentity p ≫ cocartesianSectionsPostHom a p p =
      MonoidalClosed.id (kanCocartesianSections p.hom a.hom) := by
  apply uncurry_injective
  rw [cocartesianSectionsPostHom, uncurry_natural_left, uncurry_curry,
    MonoidalClosed.id_eq, uncurry_curry]
  apply (cancel_epi (ρ_ (kanCocartesianSections p.hom a.hom)).inv).1
  rw [cocartesianSectionsAction_id, Iso.inv_hom_id]

/-- 二段階の豊穣後合成を展開すると、同じ section の二段階の元の作用になる。 -/
lemma cocartesianSectionsPostHom_comp_uncurry {B : SSet.{u}} (a p q r : Over B) :
    uncurry ((cocartesianSectionsPostHom a p q ⊗ₘ cocartesianSectionsPostHom a q r) ≫
      MonoidalClosed.comp (kanCocartesianSections p.hom a.hom)
        (kanCocartesianSections q.hom a.hom) (kanCocartesianSections r.hom a.hom)) =
    (α_ (kanCocartesianSections p.hom a.hom)
      (cocartesianRelativeFunctorSpace p.hom q.hom)
      (cocartesianRelativeFunctorSpace q.hom r.hom)).inv ≫
      cocartesianSectionsAction a p q ▷ _ ≫ cocartesianSectionsAction a q r := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, f, g⟩
  apply Subtype.ext
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro y
  rfl

/-- 元の相対作用の豊穣後合成は、同じ cocartesian 相対合成を保つ。 -/
lemma cocartesianSectionsPostHom_comp {B : SSet.{u}} (a p q r : Over B) :
    cocartesianRelativeFunctorComposition p q r ≫ cocartesianSectionsPostHom a p r =
    (cocartesianSectionsPostHom a p q ⊗ₘ cocartesianSectionsPostHom a q r) ≫
      MonoidalClosed.comp (kanCocartesianSections p.hom a.hom)
        (kanCocartesianSections q.hom a.hom) (kanCocartesianSections r.hom a.hom) := by
  apply uncurry_injective
  rw [cocartesianSectionsPostHom, uncurry_natural_left, uncurry_curry,
    cocartesianSectionsPostHom_comp_uncurry]
  exact (cocartesianSectionsAction_assoc a p q r).symm

/-- 元の section への作用を、core 移送前の quasicategory 値豊穣評価に束ねる。 -/
def cocartesianSectionsEnrichedEvaluation {B : SSet.{u}} (a : Over B) :
    EnrichedFunctor SSet.{u} (CocartesianFibrationObject B) QuasicategoryObject.{u} where
  obj p := ⟨kanCocartesianSections p.val.hom a.hom, inferInstance⟩
  map p q := cocartesianSectionsPostHom a p.val q.val
  map_id p := cocartesianSectionsPostHom_id a p.val
  map_comp p q r := cocartesianSectionsPostHom_comp a p.val q.val r.val

/-- 元の全相対作用の core により、同じ cocartesian section の QCat 値豊穣評価を得る。 -/
def cocartesianSectionsCoreEnrichedEvaluation {B : SSet.{u}} (a : Over B) :
    EnrichedFunctor SSet.{u} (CocartesianFibrationCategory B) QCat.{u} :=
  quasicategoryCoreEnrichedFunctor (cocartesianSectionsEnrichedEvaluation a)

/-- 同じ底上の cocartesian fibrations の全体から、section の Cat∞ 値評価への実際の ∞ 関手。 -/
def cocartesianSectionsInfinityEvaluation {B : SSet.{u}} (a : Over B) :
    CocartesianFibrationInfinity B ⟶ CatInfinity.{u} :=
  coherentNerveMap (cocartesianSectionsCoreEnrichedEvaluation a)

end SerrePositivity.InfinityCategories
