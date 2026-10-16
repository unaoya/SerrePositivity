module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-! # The simplicial choice-category diagram with a fixed whole parameter -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

def diagram : SimplicialObject Cat.{max u v, u} where
  obj n := Cat.of (OrdinaryBarChoiceCategory.Object (C := C) hcof hfib
    (P ⊗ SSet.stdSimplex.obj n.unop))
  map θ := (OrdinaryBarChoiceCategory.reindex hcof hfib
    (P ◁ SSet.stdSimplex.map θ.unop)).toCatHom
  map_id n := by
    apply Cat.Hom.ext
    change OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.map (𝟙 n.unop)) = _
    rw [CategoryTheory.Functor.map_id, whiskerLeft_id, OrdinaryBarChoiceCategory.reindex_id]
    rfl
  map_comp f g := by
    apply Cat.Hom.ext
    change OrdinaryBarChoiceCategory.reindex hcof hfib
      (P ◁ SSet.stdSimplex.map (g.unop ≫ f.unop)) = _
    rw [CategoryTheory.Functor.map_comp, whiskerLeft_comp, OrdinaryBarChoiceCategory.reindex_comp]
    rfl

lemma diagram_face {n : ℕ} (i : Fin (n + 2)) : (diagram (C := C) hcof hfib P).δ i =
    (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i)).toCatHom := rfl

lemma diagram_degeneracy {n : ℕ} (i : Fin (n + 1)) : (diagram (C := C) hcof hfib P).σ i =
    (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.σ i)).toCatHom := rfl

def baseProjection (n : SimplexCategoryᵒᵖ) : (diagram (C := C) hcof hfib P).obj n ⥤
    ULiftHom.{u} (Cᵒᵖ × C) :=
  OrdinaryBarChoiceCategory.projection hcof hfib (P ⊗ SSet.stdSimplex.obj n.unop) ⋙
    ULiftHom.up.{v, u, u}

def projection : diagram (C := C) hcof hfib P ⟶
    (Functor.const _).obj (FreePathResolutionPresentation.base (Cᵒᵖ × C)) where
  app n := (baseProjection hcof hfib P n).toCatHom
  naturality n m θ := by
    apply Cat.Hom.ext
    change OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.map θ.unop) ⋙
        (OrdinaryBarChoiceCategory.projection hcof hfib (P ⊗ SSet.stdSimplex.obj m.unop) ⋙
          ULiftHom.up.{v, u, u}) =
      (OrdinaryBarChoiceCategory.projection hcof hfib (P ⊗ SSet.stdSimplex.obj n.unop) ⋙
          ULiftHom.up.{v, u, u}) ⋙ 𝟭 _
    rw [← CategoryTheory.Functor.assoc, OrdinaryBarChoiceCategory.reindex_projection,
      CategoryTheory.Functor.comp_id]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory
