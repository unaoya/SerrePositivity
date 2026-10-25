module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourceQuotientDerived
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootAdjoinDivisionResidue

/-! # 実商還元のH0の元の係数商上の忠実平坦性

通常(p,d)商への実導来基底変更を扱う。一般のKoszul還元と同一視しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "k₀" => Ideal.span {(p : A), d}
local notation "κ₀" => Ideal.Quotient.mk k₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀

/-- 元の係数商から実源商への、二重係数包含の標準降下。 -/
def deltaRootSourceQuotientCoefficientMap : A ⧸ k₀ →+* Q₀ :=
  Ideal.Quotient.lift k₀ ((q₀).comp
    ((MvPolynomial.C : P₀ →+* L₀).comp (MvPolynomial.C : A →+* P₀))) (by
      change k₀ ≤ RingHom.ker _
      apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · subst x
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_insert _ _))
      · have hx := Set.mem_singleton_iff.mp hx
        subst x
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

omit [Fact p.Prime] [Unique σ] in
/-- 係数商代表元は、実源の二重係数包含の標準商像に送られる。 -/
theorem deltaRootSourceQuotientCoefficientMap_mk (a : A) :
    deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d (κ₀ a) =
      q₀ (MvPolynomial.C (MvPolynomial.C a)) := rfl

omit [Unique σ] in
/-- 実商環を経由する係数射は、既存raw残余商への標準係数射そのもの。 -/
theorem deltaRootSourceQuotientCoefficientMap_comp_residue
    (hpP : Function.Injective (fun x : P₀ => (p : P₀) * x))
    (hpL : Function.Injective (fun x : L₀ => (p : L₀) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (deltaRootSourceQuotientResidueMap D d b).comp
        (deltaRootSourceQuotientCoefficientMap (σ := σ) d) =
      deltaRootAdjoinDivisionResidueBaseMap D d b hpP hpL hg v hv := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro a
  change deltaRootSourceQuotientResidueMap D d b
    (deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) =
    deltaRootAdjoinDivisionResidueBaseMap D d b hpP hpL hg v hv (κ₀ a)
  rw [deltaRootSourceQuotientCoefficientMap_mk, deltaRootSourceQuotientResidueMap_mk,
    deltaDivisionSourceEval_C, deltaRootAdjoinDivisionResidueBaseMap_mk]

set_option maxHeartbeats 800000 in
-- 実商環上のホモロジーと複数の商作用を同時に照合するため。
/-- G7交換入力の下、実導来商還元のH0は元のA/(p,d)上忠実平坦。 -/
theorem deltaRootSourceQuotientDerivedH0_faithfullyFlat_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat (A ⧸ k₀)
      ((ModuleCat.restrictScalars (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (DeltaRootSourceQuotientDerived D d b).obj)) := by
  have hpP : Function.Injective (fun x : P₀ => (p : P₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₀)
    have h' : IsSMulRegular P₀ (p : P₀) := by simpa only [map_natCast] using h
    exact h'
  have hpL : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
    have h := (show IsSMulRegular P₀ (p : P₀) from hpP).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    exact h'
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  let := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpP hpL hg v hv
  let H := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
    (DeltaRootSourceQuotientDerived D d b).obj
  let M := (ModuleCat.restrictScalars
    (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj H
  let eQ := deltaRootSourceQuotientDerivedH0Iso_of_preservesColimit D d b hpA hg v hv hpres
  let e : M ≃ₗ[A ⧸ k₀] Res₀ :=
    { toFun := eQ.hom.hom
      invFun := eQ.inv.hom
      left_inv := fun x => congrArg (fun f => f.hom x) eQ.hom_inv_id
      right_inv := fun x => congrArg (fun f => f.hom x) eQ.inv_hom_id
      map_add' := eQ.hom.hom.map_add
      map_smul' := by
        intro s x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
        change H at x
        have h := eQ.hom.hom.map_smul
          (deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) x
        change eQ.hom.hom ((deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) • x) =
          deltaRootSourceQuotientResidueMap D d b
            (deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) * eQ.hom.hom x at h
        rw [deltaRootSourceQuotientCoefficientMap_mk,
          deltaRootSourceQuotientResidueMap_mk, deltaDivisionSourceEval_C] at h
        change eQ.hom.hom ((deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) • x) =
          deltaRootAdjoinDivisionResidueBaseMap D d b hpP hpL hg v hv (κ₀ a) * eQ.hom.hom x
        rw [deltaRootSourceQuotientCoefficientMap_mk,
          deltaRootAdjoinDivisionResidueBaseMap_mk]
        exact h }
  have := deltaRootAdjoinDivisionResidue_moduleFaithfullyFlat D d b hpP hpL hg v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e

end SerrePositivity.BhattScholze
