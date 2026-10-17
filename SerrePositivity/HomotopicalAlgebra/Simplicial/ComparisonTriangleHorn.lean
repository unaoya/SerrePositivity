module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanComparisonTriangle
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # The specified two comparison edges glue to their actual outer horn -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.KanComparisonTriangle
variable {T K : SSet.{v}} {f g z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)

abbrev hornFaces : ∀ (j : Fin 3) (_ : j ≠ 2),
    SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶ (ihom T).obj K :=
  fun j _ => if j = 0 then curry G.h else curry F.h

lemma hornCompatible : SSet.horn.IsCompatible (hornFaces F G) := by
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> first
  | exact (hj rfl).elim
  | exact (hk rfl).elim
  | exact ((not_lt_of_ge (by decide)) hjk).elim
  | exact (LargeParameterSquare.edge_one G).trans (LargeParameterSquare.edge_one F).symm

abbrev hornMap : (SSet.horn.{v} 2 2).toSSet ⟶ (ihom T).obj K := (hornCompatible F G).desc

lemma hornMap_zero : SSet.horn.ι (2 : Fin 3) 0 (by decide) ≫ hornMap F G = curry G.h :=
  (hornCompatible F G).ι_desc 0 (by decide)

lemma hornMap_one : SSet.horn.ι (2 : Fin 3) 1 (by decide) ≫ hornMap F G = curry F.h :=
  (hornCompatible F G).ι_desc 1 (by decide)

lemma Data.horn_restriction (d : Data F G) : (SSet.horn 2 2).ι ≫ d.triangle = hornMap F G := by
  apply SSet.horn.hom_ext'
  intro j hj
  rw [← Category.assoc, SSet.horn.ι_ι]
  fin_cases j
  · exact d.face_zero.trans (hornMap_zero F G).symm
  · exact d.face_one.trans (hornMap_one F G).symm
  · exact (hj rfl).elim

end SerrePositivity.SimplicialModel.KanComparisonTriangle
