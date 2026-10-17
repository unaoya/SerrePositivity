module
public import SerrePositivity.DifferentialGraded.Perfect.RingRetractTopHomology
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # 有限生成ホモロジーの有限自由singleによる被覆

有限自由加群からホモロジーへの全射をcyclesへ持ち上げ、実際のchain mapを構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

def ringSingleMapOfCycles (P : Complex A) (n : ℤ) {F : ModuleCat.{u} A}
    (q : F ⟶ P.cycles n) : (single (ModuleCat.{u} A) (.up ℤ) n).obj F ⟶ P :=
  mkHomFromSingle (q ≫ P.iCycles n) (fun k _ => by
    rw [Category.assoc, P.iCycles_d, comp_zero])

lemma ringSingleMapOfCycles_cycles (P : Complex A) (n : ℤ) {F : ModuleCat.{u} A}
    (q : F ⟶ P.cycles n) :
    (singleObjCyclesSelfIso (.up ℤ) n F).inv ≫
      cyclesMap (ringSingleMapOfCycles A P n q) n = q := by
  apply (cancel_mono (P.iCycles n)).1
  rw [Category.assoc, cyclesMap_i, ← Category.assoc, singleObjCyclesSelfIso_inv_iCycles,
    ringSingleMapOfCycles, mkHomFromSingle_f]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma ringSingleMapOfCycles_homology_epi (P : Complex A) (n : ℤ) {F : ModuleCat.{u} A}
    (q : F ⟶ P.cycles n) [Epi (q ≫ P.homologyπ n)] :
    Epi (homologyMap (ringSingleMapOfCycles A P n q) n) := by
  let S := (single (ModuleCat.{u} A) (.up ℤ) n).obj F
  let k := (singleObjCyclesSelfIso (.up ℤ) n F).inv ≫ S.homologyπ n
  have h : k ≫ homologyMap (ringSingleMapOfCycles A P n q) n = q ≫ P.homologyπ n := by
    dsimp only [k]
    rw [Category.assoc, homologyπ_naturality, ← Category.assoc,
      ringSingleMapOfCycles_cycles A P n q]
  have : Epi (k ≫ homologyMap (ringSingleMapOfCycles A P n q) n) := by
    rw [h]
    infer_instance
  exact epi_of_epi k _

lemma ringComplex_exists_finiteFree_homologyCover (P : Complex A) (n : ℤ)
    [Module.Finite A (P.homology n)] :
    ∃ (m : ℕ) (f : (single (ModuleCat.{u} A) (.up ℤ) n).obj
        (ModuleCat.of A (Fin m → A)) ⟶ P), Epi (homologyMap f n) := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin' A (P.homology n)
  let F := ModuleCat.of A (Fin m → A)
  let g' : F ⟶ P.homology n := ModuleCat.ofHom g
  have : Epi g' := (ModuleCat.epi_iff_surjective g').2 hg
  let q := Projective.factorThru g' (P.homologyπ n)
  have : Epi (q ≫ P.homologyπ n) := by
    change Epi (Projective.factorThru g' (P.homologyπ n) ≫ P.homologyπ n)
    rw [Projective.factorThru_comp]
    infer_instance
  exact ⟨m, ringSingleMapOfCycles A P n q, ringSingleMapOfCycles_homology_epi A P n q⟩

end SerrePositivity.DifferentialGraded
