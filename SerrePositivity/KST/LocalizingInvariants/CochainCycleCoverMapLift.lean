module

public import SerrePositivity.KST.LocalizingInvariants.CochainCycleCoverLift

/-!
概要：cycle 自由被覆からの任意の射を全射擬同型に沿って持ち上げる。
方針：各 sphere 生成射の像の cycle を持ち上げ、余積でまとめる。
規約：増大への射に限定せず、元の指定射との厳密な合成を保つ。
使われ方：dg 代数の cell 源の任意の写像に対する持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L M : Complex R} (p : K ⟶ L)
  (hs : ∀ n : ℤ, Function.Surjective (p.f n)) (hq : QuasiIso p)
  (f : complexCycleCover R M ⟶ L)

def liftedCoverMapCycle (j : ComplexCycleIndex R M) : complexCycles R K j.1 :=
  (cochain_cycle_lift_of_surjective_quasiIso p hs hq j.1
    (complexSphereCycle R j.1
      (Sigma.ι (fun j : ComplexCycleIndex R M => complexSphere R j.1) j ≫ f))).choose

lemma liftedCoverMapCycle_map (j : ComplexCycleIndex R M) :
    complexMapCycle R p j.1 (liftedCoverMapCycle p hs hq f j) =
      complexSphereCycle R j.1
        (Sigma.ι (fun j : ComplexCycleIndex R M => complexSphere R j.1) j ≫ f) := by
  apply Subtype.ext
  exact (cochain_cycle_lift_of_surjective_quasiIso p hs hq j.1
    (complexSphereCycle R j.1
      (Sigma.ι (fun j : ComplexCycleIndex R M => complexSphere R j.1) j ≫ f))).choose_spec

def cycleCoverMapLift : complexCycleCover R M ⟶ K :=
  Sigma.desc (fun j => complexSphereMap R j.1 (liftedCoverMapCycle p hs hq f j))

lemma cycleCoverMapLift_projection : cycleCoverMapLift p hs hq f ≫ p = f := by
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc]
  change (Sigma.ι (fun j : ComplexCycleIndex R M => complexSphere R j.1) j ≫
    Sigma.desc (fun j => complexSphereMap R j.1 (liftedCoverMapCycle p hs hq f j))) ≫ p = _
  rw [Sigma.ι_comp_desc, complexSphereMap_mapCycle, liftedCoverMapCycle_map]
  exact (complexSphereHomEquiv R L j.1).symm_apply_apply _

end SerrePositivity.KST.LocalizingInvariants
