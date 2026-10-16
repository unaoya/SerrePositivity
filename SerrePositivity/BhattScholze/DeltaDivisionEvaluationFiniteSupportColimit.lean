module

public import SerrePositivity.BhattScholze.DeltaDivisionEvaluationFiniteSupport
public import SerrePositivity.BhattScholze.DeltaDivisionSourceAlgebras
public import SerrePositivity.BhattScholze.DeltaDivisionUnitDenominator
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # 任意根族の実評価環は有限座標商の加群余極限 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "β" => deltaDivisionSourceEval D a
local notation "K" => deltaDivisionEvaluationFiniteSupportIdeal D a

/-- 有限座標の包含による、同じ源環の標準商加群射。 -/
def deltaDivisionFiniteSupportTransition {S T : Finset (σ × ℕ)} (h : S ⊆ T) :
    (L ⧸ K S) →ₗ[L] L ⧸ K T :=
  Submodule.mapQ (K S) (K T) LinearMap.id
    (by exact deltaDivisionEvaluationFiniteSupportIdeal_mono D a h)

/-- 標準遷移射は元の源環の商元を保つ。 -/
theorem deltaDivisionFiniteSupportTransition_mk {S T : Finset (σ × ℕ)} (h : S ⊆ T)
    (r : L) :
    deltaDivisionFiniteSupportTransition D a h (Ideal.Quotient.mk (K S) r) =
      Ideal.Quotient.mk (K T) r := rfl

/-- 任意根族の有限座標商の実加群図式。 -/
def deltaDivisionFiniteSupportModuleDiagram : Finset (σ × ℕ) ⥤ ModuleCat.{u} L where
  obj S := ModuleCat.of L (L ⧸ K S)
  map h := ModuleCat.ofHom (deltaDivisionFiniteSupportTransition D a (leOfHom h))
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

private theorem finite_le_ker (S : Finset (σ × ℕ)) : K S ≤ RingHom.ker β := by
  rw [deltaDivisionEvaluation_ker_eq_iSup_finiteSupport D a]
  exact le_iSup K S

/-- 各有限座標商から、元のβ作用を持つ評価環への標準線形射。 -/
def deltaDivisionFiniteSupportEval (S : Finset (σ × ℕ)) :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    (L ⧸ K S) →ₗ[L] A := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  exact Submodule.liftQ (K S) (Algebra.linearMap L A) (by exact finite_le_ker D a S)

/-- 有限座標商の評価射は、元の評価射βの実値を与える。 -/
theorem deltaDivisionFiniteSupportEval_mk (S : Finset (σ × ℕ)) (r : L) :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    deltaDivisionFiniteSupportEval D a S (Ideal.Quotient.mk (K S) r) = β r := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  rfl

/-- 元のβ評価環を頂点とする、有限座標商図式の標準余錐。 -/
def deltaDivisionFiniteSupportEvalCocone :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    Cocone (deltaDivisionFiniteSupportModuleDiagram D a) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  exact
    { pt := ModuleCat.of L A
      ι :=
        { app := fun S => ModuleCat.ofHom (deltaDivisionFiniteSupportEval D a S)
          naturality := by
            intro S T h
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
            rfl } }

private theorem cocone_mk_independent
    (c : Cocone (deltaDivisionFiniteSupportModuleDiagram D a))
    (S : Finset (σ × ℕ)) (r : L) :
    (c.ι.app S).hom (Ideal.Quotient.mk (K S) r) =
      (c.ι.app ∅).hom (Ideal.Quotient.mk (K ∅) r) := by
  have h := congrArg (fun f => f.hom (Ideal.Quotient.mk (K ∅) r))
    (c.w (homOfLE (show (∅ : Finset (σ × ℕ)) ⊆ S from Finset.empty_subset S)))
  exact h

private theorem cocone_base_ker
    (c : Cocone (deltaDivisionFiniteSupportModuleDiagram D a)) :
    RingHom.ker β ≤ LinearMap.ker ((c.ι.app ∅).hom.comp (Submodule.mkQ (K ∅))) := by
  rw [deltaDivisionEvaluation_ker_eq_iSup_finiteSupport D a]
  apply iSup_le
  intro S r hr
  change (c.ι.app ∅).hom (Ideal.Quotient.mk (K ∅) r) = 0
  rw [← cocone_mk_independent D a c S r, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- 元の評価環は、任意根族の有限座標商図式の実加群余極限である。 -/
def deltaDivisionFiniteSupportEvalIsColimit :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    IsColimit (deltaDivisionFiniteSupportEvalCocone D a) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  let b : L →ₗ[L] A := Algebra.linearMap L A
  let e := LinearMap.quotKerEquivOfSurjective b (deltaDivisionSourceEval_surjective D a)
  let desc (c : Cocone (deltaDivisionFiniteSupportModuleDiagram D a)) : A →ₗ[L] c.pt :=
    (Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app ∅).hom.comp (Submodule.mkQ (K ∅))) (by exact cocone_base_ker D a c)).comp
        e.symm.toLinearMap
  have hdesc (c : Cocone (deltaDivisionFiniteSupportModuleDiagram D a)) (r : L) :
      desc c (β r) = (c.ι.app ∅).hom (Ideal.Quotient.mk (K ∅) r) := by
    change Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app ∅).hom.comp (Submodule.mkQ (K ∅)))
        (by exact cocone_base_ker D a c) (e.symm (b r)) = _
    dsimp only [e]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  exact
    { desc := fun c => ModuleCat.ofHom (desc c)
      fac := by
        intro c S
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        change desc c (deltaDivisionFiniteSupportEval D a S (Ideal.Quotient.mk (K S) r)) = _
        rw [deltaDivisionFiniteSupportEval_mk, hdesc]
        exact (cocone_mk_independent D a c S r).symm
      uniq := by
        intro c f hf
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        obtain ⟨r, rfl⟩ := deltaDivisionSourceEval_surjective D a x
        have h := congrArg (fun g => g.hom (Ideal.Quotient.mk (K ∅) r)) (hf ∅)
        change f.hom (deltaDivisionFiniteSupportEval D a ∅ (Ideal.Quotient.mk (K ∅) r)) = _ at h
        rw [deltaDivisionFiniteSupportEval_mk] at h
        exact h.trans (hdesc c r).symm }

/-- 実圏論的余極限と、元のβ作用を持つ評価環との標準比較同型。 -/
def deltaDivisionFiniteSupportColimitEvalIso :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    colimit (deltaDivisionFiniteSupportModuleDiagram D a) ≅ ModuleCat.of L A := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (deltaDivisionFiniteSupportEvalIsColimit D a)

/-- 同じ余極限比較は、すべての有限座標商の標準β評価射を保つ。 -/
theorem deltaDivisionFiniteSupportColimitEvalIso_ι (S : Finset (σ × ℕ)) :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    colimit.ι (deltaDivisionFiniteSupportModuleDiagram D a) S ≫
      (deltaDivisionFiniteSupportColimitEvalIso D a).hom =
        ModuleCat.ofHom (deltaDivisionFiniteSupportEval D a S) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (deltaDivisionFiniteSupportEvalIsColimit D a) S

end SerrePositivity.BhattScholze
