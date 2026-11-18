module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# 非輪状 kernel を持つ全射の擬同型性

概要：複体の全射の kernel が非輪状なら元の射は擬同型。
方針：同じ短完全列の長完全列の二つの隣接項で単射・全射を示す。
規約：元の射と kernel を使う。
使われ方：内部 Hom の実 trivial fibration 保存。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma quasiIso_of_epi_acyclicKernel {X Y : Complex A} (p : X ⟶ Y) [Epi p]
    (hk : (kernel p).Acyclic) : QuasiIso p := by
  have hs : (ShortComplex.mk _ _ (kernel.condition p)).ShortExact :=
    { exact := ShortComplex.exact_kernel p }
  have hz (n : ℤ) : IsZero ((kernel p).homology n) :=
    (exactAt_iff_isZero_homology _ _).mp (hk n)
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap p n) := (hs.homology_exact₂ n).mono_g ((hz n).eq_of_src _ _)
  have : Epi (homologyMap p n) :=
    (hs.homology_exact₃ n (n + 1) (by simp)).epi_f ((hz (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end SerrePositivity.ComplexLimits
