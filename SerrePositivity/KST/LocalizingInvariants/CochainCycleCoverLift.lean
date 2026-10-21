module

public import SerrePositivity.KST.LocalizingInvariants.CochainSurjectiveQuasiIsoLifts

/-!
概要：全 cycle の自由複体被覆を、全射準同型を通る実 chain map へ持ち上げる。
方針：cycle を厳密に持ち上げ、その sphere 射を元の coproduct の普遍性でまとめる。
規約：増大の厳密な合成式を保持。使われ方：dg 代数 cell 分解の初期段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L : Complex R} (p : K ⟶ L)
  (hs : ∀ n : ℤ, Function.Surjective (p.f n)) (hq : QuasiIso p)

def liftedCoverCycle (j : ComplexCycleIndex R L) : complexCycles R K j.1 :=
  (cochain_cycle_lift_of_surjective_quasiIso p hs hq j.1 j.2).choose

lemma liftedCoverCycle_map (j : ComplexCycleIndex R L) :
    complexMapCycle R p j.1 (liftedCoverCycle p hs hq j) = j.2 := by
  apply Subtype.ext
  exact (cochain_cycle_lift_of_surjective_quasiIso p hs hq j.1 j.2).choose_spec

def cycleCoverLift : complexCycleCover R L ⟶ K :=
  Sigma.desc (fun j ↦ complexSphereMap R j.1 (liftedCoverCycle p hs hq j))

lemma cycleCoverLift_projection : cycleCoverLift p hs hq ≫ p = complexCycleCoverπ R L := by
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc]
  change (Sigma.ι (fun j : ComplexCycleIndex R L ↦ complexSphere R j.1) j ≫
    Sigma.desc (fun j ↦ complexSphereMap R j.1 (liftedCoverCycle p hs hq j))) ≫ p = _
  rw [Sigma.ι_comp_desc, complexCycleCoverι_π, complexSphereMap_mapCycle, liftedCoverCycle_map]

end SerrePositivity.KST.LocalizingInvariants
