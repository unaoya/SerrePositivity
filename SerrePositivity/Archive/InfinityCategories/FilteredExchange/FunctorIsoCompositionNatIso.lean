module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：指定された単体的関手同型の合成標的を、ホモトピー圏上の通常の合成関手へ移す。
方針：hoFunctor の合成則で標的を表示変更し、各成分で元の指定値を保持する。
規約：元の同型を再選択しない。使われ方：四面の比較を通常の圏の相殺補題へ渡す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定された合成への関手同型を、通常のホモトピー圏の合成関手への自然同型として保持。 -/
def functorIsoCompositionNatIso {X Y Z : SSet.{u}} {f : X ⟶ Z} {g : X ⟶ Y} {h : Y ⟶ Z}
    (e : FunctorIso f (g ≫ h)) :
    (hoFunctor.map f).toFunctor ≅ (hoFunctor.map g).toFunctor ⋙ (hoFunctor.map h).toFunctor :=
  e.toNatIso ≪≫ eqToIso (by rw [Functor.map_comp, Cat.Hom.comp_toFunctor])

/-- 通常の合成関手への表示変更後も、元の指定同型の各点成分を厳密に保持する。 -/
lemma functorIsoCompositionNatIso_app {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Z]
    {f : X ⟶ Z} {g : X ⟶ Y} {h : Y ⟶ Z} (e : FunctorIso f (g ≫ h)) (x : X _⦋0⦌) :
    (functorIsoCompositionNatIso e).app (SSet.HomotopyCategory.mk x) = e.app x := by
  have hr {A D : Type u} [Category A] [Category D] {F G G' : A ⥤ D}
      (a : F ≅ G) (ha : G = G') (v : A) : HEq ((a ≪≫ eqToIso ha).app v) (a.app v) := by
    subst G'
    simp only [eqToIso_refl, Iso.trans_refl]
    rfl
  exact eq_of_heq (hr e.toNatIso _ (SSet.HomotopyCategory.mk x))

end SerrePositivity.InfinityCategories.F2
