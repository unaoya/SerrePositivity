module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProHomology

/-!
概要：非正次数源からの cover lift の自然性と、保持される全次数の群同型。
方針：元の lift の一意性と smart 切断包含の次数別準同型性を使う。
規約：元の代数が connective であるとは仮定しない。使われ方：対角模型の非正次数化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C D : Mon (Complex R)}
  [A.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0]

lemma connectiveCoverLift_naturality (f : A ⟶ B) (g : C ⟶ D)
    (a : A ⟶ C) (b : B ⟶ D) (h : a ≫ g = f ≫ b) :
    a ≫ connectiveCoverLift R g = connectiveCoverLift R f ≫ connectiveCoverMap R b := by
  have hl : a ≫ connectiveCoverLift R g = connectiveCoverLift R (a ≫ g) :=
    connectiveCoverLift_unique R _ _ (by rw [Category.assoc, connectiveCoverLift_inclusion])
  have hb : connectiveCoverMap R b ≫ connectiveCoverInclusion R D =
      connectiveCoverInclusion R B ≫ b := (connectiveCoverCounit R).naturality b
  have hr : connectiveCoverLift R f ≫ connectiveCoverMap R b = connectiveCoverLift R (a ≫ g) :=
    connectiveCoverLift_unique R _ _ (by
      rw [Category.assoc, hb,
        ← Category.assoc, connectiveCoverLift_inclusion]
      exact h.symm)
  exact hl.trans hr.symm

lemma connectiveCoverInclusion_groups_isIso (E : Mon (Complex R)) (j : ℤ) (hj : 0 ≤ j) :
    IsIso ((groups R j).map (connectiveCoverInclusion R E)) := by
  apply groups_map_isIso_of_quasiIsoAt
  change QuasiIsoAt (E.X.ιTruncLE 0) (-j)
  exact CochainComplex.quasiIsoAt_ιTruncLE E.X 0 (-j) (by omega)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
