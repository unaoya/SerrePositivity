module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTwoHornLift
public import SerrePositivity.HomotopicalAlgebra.Simplicial.CurriedHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-! # Actual homotopies representing equality of Kan-valued homotopy classes

An outer two-horn in the mapping space supplies right differences of
homotopies. Hence actual homotopies are symmetric and transitive for Kan
targets, and every equality in the generated quotient has a single interval.
No model structure is assumed on the value universe.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanActualHomotopy

private lemma vertex_zero :
    SSet.stdSimplex.δ.{v} (1 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (1 : Fin 3) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

private lemma vertex_one :
    SSet.stdSimplex.δ.{v} (0 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

variable {X K : SSet.{v}} (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  {f g h : X ⟶ K}

def refl (f : X ⟶ K) : SSet.Homotopy f f :=
  SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm f)

include hK in
lemma right_difference (Hfg : SSet.Homotopy f g) (Hhg : SSet.Homotopy h g) :
    Nonempty (SSet.Homotopy f h) := by
  have : Fibration (terminal.from K) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr hK
  have : SSet.KanComplex K := (isFibrant_iff K).mpr inferInstance
  have hp : SSet.modelCategoryQuillen.J.rlp (terminal.from ((ihom X).obj K)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  have hc : SSet.stdSimplex.δ (0 : Fin 2) ≫ curry Hhg.h =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ curry Hfg.h :=
    (LargeParameterSquare.edge_one Hhg).trans (LargeParameterSquare.edge_one Hfg).symm
  obtain ⟨t, ht₀, ht₁, _⟩ := KanTwoHornLift.exists_triangle _ hp
    (curry Hhg.h) (curry Hfg.h) (terminal.from _) hc
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  have hz : SSet.stdSimplex.δ (1 : Fin 2) ≫ (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) =
      LargeParameterSquare.point f := by
    rw [← Category.assoc, vertex_zero, Category.assoc, ht₁]
    exact LargeParameterSquare.edge_zero Hfg
  have ho : SSet.stdSimplex.δ (0 : Fin 2) ≫ (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) =
      LargeParameterSquare.point h := by
    rw [← Category.assoc, vertex_one, Category.assoc, ht₀]
    exact LargeParameterSquare.edge_zero Hhg
  exact ⟨CurriedHomotopy.ofEdge _ hz ho⟩

include hK in
lemma reverse (H : SSet.Homotopy f g) : Nonempty (SSet.Homotopy g f) :=
  right_difference hK (refl g) H

include hK in
lemma concatenate (Hfg : SSet.Homotopy f g) (Hgh : SSet.Homotopy g h) :
    Nonempty (SSet.Homotopy f h) := by
  obtain ⟨Hhg⟩ := reverse hK Hgh
  exact right_difference hK Hfg Hhg

include hK in
lemma relation_equivalence : Equivalence (fun (f g : X ⟶ K) =>
    Nonempty (SSet.Homotopy f g)) :=
  ⟨fun f => ⟨refl f⟩, fun ⟨H⟩ => reverse hK H,
    fun ⟨Hfg⟩ ⟨Hgh⟩ => concatenate hK Hfg Hgh⟩

include hK in
lemma of_class_eq (heq : HomotopyClasses.mk f = HomotopyClasses.mk g) :
    Nonempty (SSet.Homotopy f g) :=
  (relation_equivalence hK).eqvGen_iff.mp (Quot.eqvGen_exact heq)

include hK in
lemma class_eq_iff : HomotopyClasses.mk f = HomotopyClasses.mk g ↔
    Nonempty (SSet.Homotopy f g) :=
  ⟨of_class_eq hK, fun ⟨H⟩ => HomotopyClasses.sound H⟩

end SerrePositivity.SimplicialModel.KanActualHomotopy
