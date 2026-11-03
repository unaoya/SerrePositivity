module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarDifferential
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
/-!
概要：coherent bar の頂点 summand を通る二乗項は消える。
方針：元の包含を全次数合成の中間で移し、頂点での元の列が零であることを使う。
規約：元の図式・直和・全次数係数を保持する。
使われ方：bar の MC 方程式の頂点の場合と、正次元列の終端項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarTheta_comp_vertex {M : ModuleCategory R D} (s : I _⦋0⦌) (p : ℤ)
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨0, s⟩))).X p) :
    compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarTheta R D F)
      ((eHomWhiskerLeft (Complex R) M (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)).f p f)
      rfl = 0 := by
  rw [moduleHomClosedInsertion R D
    (S := M) (M := dgCoherentBarFamily R D F ⟨0, s⟩)
    (N := dgCoherentBarGraded R D F) (P := dgCoherentBarGraded R D F),
    dgCoherentBarTheta_restrict R D F ⟨0, s⟩]
  change compose R (x := ForgetEnrichment.to (Complex R) M)
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨0, s⟩))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) 0 f rfl = 0
  exact DGNerve.zero_compose (A := R) (D := RightModule R D)
    (x := ForgetEnrichment.to (Complex R) M)
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨0, s⟩))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) f rfl

lemma dgCoherentBarColumn_maurerCartan_zero (s : I _⦋0⦌) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨0, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
        (dgCoherentBarColumn R D F ⟨0, s⟩) +
      compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨0, s⟩))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarColumn R D F ⟨0, s⟩)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  simp only [dgCoherentBarColumn, map_zero,
    DGNerve.compose_zero, add_zero]

end SerrePositivity.InfinityCategories
