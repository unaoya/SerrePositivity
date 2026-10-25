module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaDivisionEvaluationFiniteSupport
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSourceAlgebras
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionUnitDenominator
public import SerrePositivity.HomologicalAlgebra.FiniteSupQuotientColimit

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

/-- 元の評価環は、任意根族の有限座標商図式の実加群余極限である。 -/
def deltaDivisionFiniteSupportEvalIsColimit :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    IsColimit (deltaDivisionFiniteSupportEvalCocone D a) := by
  classical
  letI := deltaDivisionSourceEvaluationAlgebra D a
  let J : σ × ℕ → Ideal L := fun z => Ideal.span {deltaDivisionSourceGraphRelation D a z}
  have hK (S : Finset (σ × ℕ)) : K S = S.sup J := by
    induction S using Finset.induction_on with
    | empty => simp [deltaDivisionEvaluationFiniteSupportIdeal]
    | @insert z S hz ih =>
      simpa only [deltaDivisionEvaluationFiniteSupportIdeal, Finset.coe_insert,
        Set.image_insert_eq, Ideal.span_insert, Finset.sup_insert] using
          congrArg (fun I => J z ⊔ I) ih
  let eF : deltaDivisionFiniteSupportModuleDiagram D a ≅ finiteSupQuotientDiagram J :=
    NatIso.ofComponents
      (fun S => (Submodule.quotEquivOfEq _ _ (hK S)).toModuleIso) (by
        intro S T h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
        rfl)
  let b : L →ₗ[L] A := Algebra.linearMap L A
  have hker : (⨆ z, J z) = LinearMap.ker b := by
    change (⨆ z, J z) = RingHom.ker β
    rw [deltaDivisionSourceEval_ker, Ideal.span_range_eq_iSup]
    rfl
  let eA := ((Submodule.quotEquivOfEq _ _ hker).trans
    (LinearMap.quotKerEquivOfSurjective b (deltaDivisionSourceEval_surjective D a))).toModuleIso
  let hc := (IsColimit.precomposeHomEquiv eF (finiteSupQuotientCocone J)).symm
    (finiteSupQuotient_isColimit J)
  refine hc.ofIsoColimit (Cocone.ext eA ?_)
  intro S
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

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
