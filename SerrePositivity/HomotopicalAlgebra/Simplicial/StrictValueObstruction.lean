module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-! # Weakly equivalent Kan values can obstruct a strict functor on those fixed values

A cofibration/trivial-fibration factorization supplies a contractible Kan
complex with two distinct vertices. Thus it is not isomorphic to a point.
This obstructs preserving independently selected values when strictifying
a diagram over an isomorphism. It does not obstruct replacing its values.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.StrictValueObstruction
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev point : SSet.{v} := SSet.stdSimplex.obj (SimplexCategory.mk 0)
abbrev interval : SSet.{v} := SSet.stdSimplex.obj (SimplexCategory.mk 1)
abbrev factorization := MorphismProperty.factorizationData
  (cofibrations SSet.{v}) (trivialFibrations SSet.{v})
  (SSet.stdSimplex.isTerminalObj₀.from interval)
abbrev complex : SSet.{v} := factorization.Z
abbrev toPoint : complex ⟶ point := factorization.p
abbrev fromInterval : interval ⟶ complex := factorization.i

include hcof in
lemma fromInterval_mono : Mono (fromInterval.{v}) := by
  exact (congrArg (fun W : MorphismProperty SSet.{v} => W fromInterval) hcof).mp
    factorization.hi

lemma toPoint_trivialFibration : trivialFibrations SSet.{v} toPoint := factorization.hp

omit [ModelCategory SSet.{v}] in
lemma point_kanComplex : SSet.KanComplex (point.{v}) := by
  have : IsIso (terminal.from (point.{v})) :=
    isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ terminalIsTerminal _
  infer_instance

include hfib in
lemma complex_kanComplex : SSet.KanComplex (complex.{v}) := by
  have : Fibration toPoint.{v} := ⟨toPoint_trivialFibration.1⟩
  have : IsFibrant complex.{v} :=
    (isFibrant_iff_of_isTerminal toPoint SSet.stdSimplex.isTerminalObj₀).mpr inferInstance
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  rw [← hfib]
  exact mem_fibrations (terminal.from complex.{v})

include hcof in
lemma complex_not_subsingleton_vertices :
    ¬ Subsingleton ((complex.{v}).obj (Opposite.op (SimplexCategory.mk 0))) := by
  intro h
  have : Mono (fromInterval.{v}) := fromInterval_mono hcof
  have hinj := (CategoryTheory.mono_iff_injective
    ((fromInterval.{v}).app (Opposite.op (SimplexCategory.mk 0)))).mp inferInstance
  have he := hinj (h.elim
    ((fromInterval.{v}).app _ (SSet.stdSimplex.obj₀Equiv.symm 0))
    ((fromInterval.{v}).app _ (SSet.stdSimplex.obj₀Equiv.symm 1)))
  have : (0 : Fin 2) = 1 := congrArg SSet.stdSimplex.obj₀Equiv he
  exact Fin.zero_ne_one this

include hcof in
lemma not_iso_point : ¬ Nonempty (complex.{v} ≅ point) := by
  rintro ⟨e⟩
  apply complex_not_subsingleton_vertices hcof
  constructor
  intro x y
  apply (CategoryTheory.mono_iff_injective (e.hom.app _)).mp inferInstance
  apply SSet.stdSimplex.obj₀Equiv.injective
  apply Fin.ext
  omega

end SerrePositivity.SimplicialModel.StrictValueObstruction
