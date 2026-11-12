module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.EdgewiseEnrichedComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition

/-!
概要：通常の圏の射を、共通 Hom 解像の定値な射へ標準的に持ち上げる。
方針：重み全体を豊穣単位へ写してから元の通常の射を適用する。
規約：元の高次 Hom からの豊穣な切断は主張しない。
使われ方：strict な Kan 図式を共通 Hom 解像上へ移し、左右の全空間比較に入力する。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の対象を共通 Hom 解像の同じ対象へ持ち上げる。 -/
def edgewiseOrdinaryObject (X : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C := ⟨X, trivial⟩

/-- 通常の射を重みの全体で定値にした、共通 Hom 解像の通常の射。 -/
def edgewiseOrdinaryHom {X Y : C} (f : X ⟶ Y) :
    edgewiseOrdinaryObject X ⟶ edgewiseOrdinaryObject Y :=
  ForgetEnrichment.homOf SSet (X := edgewiseOrdinaryObject X) (Y := edgewiseOrdinaryObject Y)
    { app := fun d => ↾fun _ => toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj d.unop) ≫ eHomEquiv SSet f
      naturality := by
        intro d e α
        apply ConcreteCategory.hom_ext
        intro a
        change toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj e.unop) ≫ eHomEquiv SSet f =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ (toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj d.unop) ≫ eHomEquiv SSet f)
        rw [← Category.assoc, comp_toUnit] }

/-- 通常の射の標準持ち上げは恒等射を保つ。 -/
lemma edgewiseOrdinaryHom_id (X : C) : edgewiseOrdinaryHom (𝟙 X) = 𝟙 _ := by
  apply (eHomEquiv SSet).injective
  rw [eHomEquiv_id]
  change edgewiseOrdinaryHom (𝟙 X) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.edgewiseEnrichedIdentity X
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  change toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj d.unop) ≫ eHomEquiv SSet (𝟙 X) =
    toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj d.unop) ≫ eId SSet X
  rw [eHomEquiv_id]

/-- 通常の射の標準持ち上げは元の合成を保つ。 -/
lemma edgewiseOrdinaryHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    edgewiseOrdinaryHom (f ≫ g) = edgewiseOrdinaryHom f ≫ edgewiseOrdinaryHom g := by
  apply (eHomEquiv SSet).injective
  rw [eHomEquiv_comp]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  exact congrArg (fun k => k.app n PUnit.unit) (eHomEquiv_comp (V := SSet) f g)

/-- 元の通常の圏から、共通 Hom 解像の underlying category への標準持ち上げ。 -/
def edgewiseOrdinaryLift (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C where
  obj X := edgewiseOrdinaryObject X
  map f := edgewiseOrdinaryHom f
  map_id := edgewiseOrdinaryHom_id
  map_comp := edgewiseOrdinaryHom_comp

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
