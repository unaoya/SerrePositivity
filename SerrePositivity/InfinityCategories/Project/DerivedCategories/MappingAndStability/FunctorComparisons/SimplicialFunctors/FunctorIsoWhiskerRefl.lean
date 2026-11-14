module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
/-!
概要：指定同型の恒等性を、同じ前後合成の恒等性へ移す。
方針：抽象的な実関手空間で同型の恒等保存を先に証明する。
規約：具体的な kernel の定義を展開しない。使われ方：対角 kernel の自然性四角形。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
/-- 指定同型が恒等なら、その実前合成も同じ恒等同型。 -/
lemma functorIso_precomp_of_refl {X Y Z : SSet.{u}} {g : Y ⟶ Z}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g g) (he : e = Iso.refl _) (f : X ⟶ Y) :
    e.precomp f = Iso.refl _ := by
  rw [he, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso, CategoryTheory.Functor.mapIso_refl]
  rfl
/-- 指定同型が恒等なら、その実後合成も同じ恒等同型。 -/
lemma functorIso_postcomp_of_refl {X Y Z : SSet.{u}} {f : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f) (he : e = Iso.refl _) (g : Y ⟶ Z) :
    e.postcomp g = Iso.refl _ := by
  rw [he, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso, CategoryTheory.Functor.mapIso_refl]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
