module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomDegrees
/-!
概要：正規化 graded bar を標的とする斉次射を、同じ MC 微分の実正規化 bar へ移す。
方針：全評価成分と符号付き加群自然性を保持する。
規約：移送だけで閉性は主張しない。微分には正規化 theta の後合成項が加わる。
使われ方：native 余錐の全単体に対する最上成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (M : RightModule R D)

def dgCoherentBarNormalizedTargetRebase (q : ℤ)
    (z : (moduleHom R D M
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).X q) :
    (moduleHom R D M (dgCoherentBarNormalizedModule R D F hMC)).X q :=
  moduleHomElementMk R D q
    (fun x => Cochain.mk (fun i j hij =>
      ((moduleHomπ R D M
        (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F)) x.unop).f
        q z).v i j hij)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij)
      (moduleHomElement_naturality R D (M := M)
        (N := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
        q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [Cochain.mk_v, dgCoherentBarNormalizedModule_map_v] using h)

lemma dgCoherentBarNormalizedTargetRebase_π (q : ℤ)
    (z : (moduleHom R D M
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).X q)
    (x : D) (i j : ℤ) (hij : i + q = j) :
    ((moduleHomπ R D M (dgCoherentBarNormalizedModule R D F hMC) x).f q
      (dgCoherentBarNormalizedTargetRebase R D F hMC M q z)).v i j hij =
    ((moduleHomπ R D M
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F)) x).f q z).v
      i j hij := by
  rw [dgCoherentBarNormalizedTargetRebase, moduleHomElementMk_π]
  rfl

lemma dgCoherentBarNormalizedTargetRebase_zero (q : ℤ) :
    dgCoherentBarNormalizedTargetRebase R D F hMC M q 0 = 0 := by
  apply moduleHomElement_ext R D
    (M := M) (N := dgCoherentBarNormalizedModule R D F hMC)
  intro x
  rw [map_zero]
  apply Cochain.ext
  intro i j hij
  rw [dgCoherentBarNormalizedTargetRebase_π, map_zero]
  rfl

lemma dgCoherentBarNormalizedTargetRebase_d (q : ℤ)
    (z : (moduleHom R D M
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).X q) :
    (moduleHom R D M (dgCoherentBarNormalizedModule R D F hMC)).d q (q + 1)
      (dgCoherentBarNormalizedTargetRebase R D F hMC M q z) =
    dgCoherentBarNormalizedTargetRebase R D F hMC M (q + 1)
      ((moduleHom R D M
        (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).d q (q + 1) z +
      compose R (x := M)
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
        (dgCoherentBarNormalizedTheta R D F) z rfl) := by
  apply moduleHomElement_ext R D
    (M := M) (N := dgCoherentBarNormalizedModule R D F hMC)
  intro x
  rw [moduleHomElement_d_π]
  apply Cochain.ext
  intro i j hij
  obtain rfl : j = i + q + 1 := by omega
  rw [dgCoherentBarNormalizedTargetRebase_π]
  rw [δ_v (F := M.obj (Opposite.op x))
    (G := (dgCoherentBarNormalizedModule R D F hMC).obj (Opposite.op x))
    q (q + 1) rfl _ i (i + q + 1) hij (i + q) (i + 1) (by omega) rfl,
    dgCoherentBarNormalizedModule_d]
  rw [map_add, Cochain.add_v, moduleHomElement_d_π, moduleHomCompose_π,
    δ_v q (q + 1) rfl _ i (i + q + 1) hij (i + q) (i + 1) (by omega) rfl,
    Cochain.comp_v _ _ _ i (i + q) (i + q + 1) rfl (by omega)]
  simp only [dgCoherentBarNormalizedTargetRebase_π, Preadditive.comp_add,
    Units.smul_def]
  abel

end SerrePositivity.InfinityCategories
