module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCandidateBaseValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoofValue

/-!
概要：実次段切断候補と元の f の合成を τₙ へ射影すると、元の両遷移に一致する。
方針：候補の底の式と元の τₙ 逆 roof の左右三角形を、元の切断自然性で結ぶ。
規約：次段切断全体の逆三角形は未主張。使われ方：残る πₙ₊₁ の作用の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L)

lemma candidateRoof_value_left_base :
    (L.map (postnikovMap R (f.app d.layerInverse.zero.stage).hom (n + 1)) ≫
      SurjectiveRoof.value R L hL (d.candidateRoof R)) ≫
        L.map (postnikovTransition R (A.obj j).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) =
    L.map (postnikovMap R (A.transition (d.target_le.trans
      (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom (n + 1)) ≫
        L.map (postnikovTransition R (A.obj j).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) := by
  let k := d.layerInverse.zero.stage
  let h : j ≤ k := d.target_le.trans
    (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)
  have hl : L.map (postnikovMap R (f.app k).hom n) ≫
      SurjectiveRoof.value R L hL (d.lowerBaseInverse R).roof =
        L.map (postnikovMap R (A.transition h).hom n) :=
    ((d.lowerBaseInverse R).value_triangles R L hL).1
  calc
    _ = L.map (postnikovMap R (f.app k).hom (n + 1)) ≫
        (SurjectiveRoof.value R L hL (d.candidateRoof R) ≫
          L.map (postnikovTransition R (A.obj j).obj (n + 1) n (postnikovSuccessor_cutoff_le n))) := Category.assoc _ _ _
    _ = L.map (postnikovMap R (f.app k).hom (n + 1)) ≫
        (L.map (postnikovTransition R (B.obj k).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) ≫
          SurjectiveRoof.value R L hL (d.lowerBaseInverse R).roof) := by
      rw [d.candidateRoof_value_base R L hL]
    _ = (L.map (postnikovTransition R (A.obj k).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) ≫
        L.map (postnikovMap R (f.app k).hom n)) ≫
          SurjectiveRoof.value R L hL (d.lowerBaseInverse R).roof := by
      rw [← Category.assoc, ← L.map_comp, postnikovTransition_naturality, L.map_comp]
    _ = L.map (postnikovTransition R (A.obj k).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) ≫
        L.map (postnikovMap R (A.transition h).hom n) := by rw [Category.assoc, hl]
    _ = _ := by rw [← L.map_comp, ← postnikovTransition_naturality, L.map_comp]

lemma candidateRoof_value_right_base :
    (SurjectiveRoof.value R L hL (d.candidateRoof R) ≫ L.map (postnikovMap R (f.app j).hom (n + 1))) ≫
      L.map (postnikovTransition R (B.obj j).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) =
    L.map (postnikovMap R (B.transition (d.target_le.trans
      (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom (n + 1)) ≫
        L.map (postnikovTransition R (B.obj j).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) := by
  let k := d.layerInverse.zero.stage
  let h : j ≤ k := d.target_le.trans
    (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)
  have hr : SurjectiveRoof.value R L hL (d.lowerBaseInverse R).roof ≫
      L.map (postnikovMap R (f.app j).hom n) = L.map (postnikovMap R (B.transition h).hom n) :=
    ((d.lowerBaseInverse R).value_triangles R L hL).2
  calc
    _ = SurjectiveRoof.value R L hL (d.candidateRoof R) ≫
        (L.map (postnikovTransition R (A.obj j).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) ≫
          L.map (postnikovMap R (f.app j).hom n)) := by
      rw [Category.assoc, ← L.map_comp, postnikovTransition_naturality, L.map_comp]
    _ = (L.map (postnikovTransition R (B.obj k).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) ≫
        SurjectiveRoof.value R L hL (d.lowerBaseInverse R).roof) ≫
          L.map (postnikovMap R (f.app j).hom n) := by
      rw [← Category.assoc, d.candidateRoof_value_base R L hL]
    _ = L.map (postnikovTransition R (B.obj k).obj (n + 1) n (postnikovSuccessor_cutoff_le n)) ≫
        L.map (postnikovMap R (B.transition h).hom n) := by rw [Category.assoc, hr]
    _ = _ := by rw [← L.map_comp, ← postnikovTransition_naturality, L.map_comp]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
