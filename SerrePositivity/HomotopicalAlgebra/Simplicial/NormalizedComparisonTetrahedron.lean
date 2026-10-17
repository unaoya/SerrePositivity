module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NormalizedHornFilling
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction

/-! # A normalized comparison tetrahedron strictly natural in its source parameter

All three input cone triangles are retained as whole faces. The choice
uses one operation in the original K and hence commutes strictly with
restriction of all source data. Earlier independently chosen tetrahedra
are compared while fixing their entire specified horn.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NormalizedComparisonTetrahedron
open KanComparisonTriangle
variable {T K : SSet.{v}} {f g h z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSet.Homotopy h z)
  (a : Data F G) (b : Data F H) (c : Data G H)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

abbrev tetrahedron : SSet.stdSimplex.obj (SimplexCategory.mk 3) ⟶ (ihom T).obj K :=
  NormalizedHornFilling.fill K 3 hK (KanComparisonTetrahedron.hornMap F G H a b c)

lemma horn_restriction : (SSet.horn 3 3).ι ≫ tetrahedron F G H a b c hK =
    KanComparisonTetrahedron.hornMap F G H a b c :=
  NormalizedHornFilling.fill_restriction K 3 hK (KanComparisonTetrahedron.hornMap F G H a b c)

def build : KanComparisonTetrahedron.Filler F G H a b c where
  tetrahedron := tetrahedron F G H a b c hK
  face_zero := by
    rw [← SSet.horn.ι_ι (3 : Fin 4) 0 (by decide), Category.assoc,
      horn_restriction, KanComparisonTetrahedron.hornMap_zero]
  face_one := by
    rw [← SSet.horn.ι_ι (3 : Fin 4) 1 (by decide), Category.assoc,
      horn_restriction, KanComparisonTetrahedron.hornMap_one]
  face_two := by
    rw [← SSet.horn.ι_ι (3 : Fin 4) 2 (by decide), Category.assoc,
      horn_restriction, KanComparisonTetrahedron.hornMap_two]

variable {U : SSet.{v}} (i : U ⟶ T)
local notation "F'" => HomotopyClasses.preHomotopy i F
local notation "G'" => HomotopyClasses.preHomotopy i G
local notation "H'" => HomotopyClasses.preHomotopy i H
local notation "ta" => ComparisonCoherenceRestriction.triangle i F G a
local notation "tb" => ComparisonCoherenceRestriction.triangle i F H b
local notation "tc" => ComparisonCoherenceRestriction.triangle i G H c

private lemma hornMap_reindex : KanComparisonTetrahedron.hornMap F G H a b c ≫ (pre i).app K =
    KanComparisonTetrahedron.hornMap F' G' H' ta tb tc := by
  apply SSet.horn.hom_ext'
  intro j hj
  rw [← Category.assoc]
  fin_cases j
  · exact (congrArg (fun q => q ≫ (pre i).app K)
      (KanComparisonTetrahedron.hornMap_zero F G H a b c)).trans
        (KanComparisonTetrahedron.hornMap_zero F' G' H' ta tb tc).symm
  · exact (congrArg (fun q => q ≫ (pre i).app K)
      (KanComparisonTetrahedron.hornMap_one F G H a b c)).trans
        (KanComparisonTetrahedron.hornMap_one F' G' H' ta tb tc).symm
  · exact (congrArg (fun q => q ≫ (pre i).app K)
      (KanComparisonTetrahedron.hornMap_two F G H a b c)).trans
        (KanComparisonTetrahedron.hornMap_two F' G' H' ta tb tc).symm
  · exact (hj rfl).elim

lemma tetrahedron_reindex : tetrahedron F' G' H' ta tb tc hK =
    tetrahedron F G H a b c hK ≫ (pre i).app K := by
  rw [tetrahedron, ← hornMap_reindex]
  exact NormalizedHornFilling.fill_reindex K 3 hK (KanComparisonTetrahedron.hornMap F G H a b c) i

lemma family_reindex : uncurry (tetrahedron F' G' H' ta tb tc hK) =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 3) ≫ uncurry (tetrahedron F G H a b c hK) := by
  rw [tetrahedron_reindex]
  exact uncurry_pre_app K (tetrahedron F G H a b c hK) i

lemma coherence_reindex : KanComparisonTetrahedron.coherence F' G' H' ta tb tc
    (build F' G' H' ta tb tc hK) =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
      KanComparisonTetrahedron.coherence F G H a b c (build F G H a b c hK) := by
  change uncurry (SSet.stdSimplex.δ (3 : Fin 4) ≫ tetrahedron F' G' H' ta tb tc hK) = _
  rw [tetrahedron_reindex, ← Category.assoc]
  exact uncurry_pre_app K
    (SSet.stdSimplex.δ (3 : Fin 4) ≫ tetrahedron F G H a b c hK) i

variable (d : KanComparisonTetrahedron.Filler F G H a b c)

lemma original_horn : (SSet.horn 3 3).ι ≫ d.tetrahedron =
    KanComparisonTetrahedron.hornMap F G H a b c := by
  apply SSet.horn.hom_ext'
  intro j hj
  rw [← Category.assoc, SSet.horn.ι_ι]
  fin_cases j
  · exact d.face_zero.trans (KanComparisonTetrahedron.hornMap_zero F G H a b c).symm
  · exact d.face_one.trans (KanComparisonTetrahedron.hornMap_one F G H a b c).symm
  · exact d.face_two.trans (KanComparisonTetrahedron.hornMap_two F G H a b c).symm
  · exact (hj rfl).elim

def compare : RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn 3 3).ι
    (KanComparisonTetrahedron.hornMap F G H a b c) d.tetrahedron
    (tetrahedron F G H a b c hK) :=
  NormalizedHornFilling.compare K 3 hK (KanComparisonTetrahedron.hornMap F G H a b c)
    d.tetrahedron (original_horn F G H a b c d)

lemma degenerate (j : Fin 3)
    (e : SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom T).obj K)
    (he : KanComparisonTetrahedron.hornMap F G H a b c =
      (SSet.horn 3 3).ι ≫ SSet.stdSimplex.σ j ≫ e) :
    tetrahedron F G H a b c hK = SSet.stdSimplex.σ j ≫ e := by
  rw [tetrahedron, he]
  exact NormalizedHornFilling.fill_degenerate K 3 hK j e

end SerrePositivity.SimplicialModel.NormalizedComparisonTetrahedron
