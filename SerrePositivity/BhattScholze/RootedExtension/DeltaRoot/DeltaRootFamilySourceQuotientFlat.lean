module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourceQuotientFlat
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootFamilySourceCoefficientResidue
public import SerrePositivity.CommutativeAlgebra.WittGhostInjective
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology

/-! # 実商環上の根添加導来還元

(p,d)の通常商への実基底変更を扱う。Koszul還元との同一視や完備化後の
有限根族について、実商係数環上の離散性と元のA/(p,d)上のH0忠実平坦性を証明する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) {m : ℕ}
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
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ (MvPolynomial.C d) c₀
local notation "r₀" => Ideal.Quotient.mk
  (deltaAdjoinDivisionResidueIdeal E₀ (MvPolynomial.C d) c₀)

/-- 実商環上の還元のホモロジーを制限した対象と、raw残余商とのH0同型。 -/
def deltaRootFamilySourceQuotientDerivedRestrictedH0Iso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        (DeltaRootSourceQuotientDerived D d b).obj) ≅ MRes :=
  ((derivedRestrictScalarsHomologyIso q₀ 0).app
      (DeltaRootSourceQuotientDerived D d b).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaRootSourceQuotientDerivedRestrictionIso D d b)) ≪≫
    deltaRootFamilySourceCoefficientResidueHomologyZeroIso
      D d b s hpA v hv

/-- 有限根族について、実商環上の還元そのものの非零次数ホモロジーが消える。 -/
theorem deltaRootFamilySourceQuotientDerived_homology_isZero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (DeltaRootSourceQuotientDerived D d b).obj) := by
  have hz := deltaRootFamilySourceCoefficientResidue_homology_isZero
    D d b s hpA v hv i hi
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (deltaRootSourceQuotientDerivedRestrictionIso D d b)))
  have hr := (derivedRestrictScalarsHomologyIso q₀ i).app
    (DeltaRootSourceQuotientDerived D d b).obj
  have hs := hr.isZero_iff.mp hz'
  let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (DeltaRootSourceQuotientDerived D d b).obj) :=
    ModuleCat.subsingleton_of_isZero (R := L₀) hs
  exact ModuleCat.isZero_of_subsingleton _

/-- 実商環上でのH0同型。qの全射性により、L線形比較を実Q線形比較へ昇格する。 -/
def deltaRootFamilySourceQuotientDerivedH0Iso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
      (DeltaRootSourceQuotientDerived D d b).obj) ≅ ModuleCat.of Q₀ Res₀ := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  let e := deltaRootFamilySourceQuotientDerivedRestrictedH0Iso
    D d b s hpA v hv ≪≫ (deltaRootSourceQuotientResidueRestrictionIso D d b).symm
  refine
    { hom := { hom' :=
        { toFun := e.hom.hom
          map_add' := e.hom.hom.map_add
          map_smul' := ?_ } }
      inv := { hom' :=
        { toFun := e.inv.hom
          map_add' := e.inv.hom.map_add
          map_smul' := ?_ } }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.hom.hom.map_smul r x
    change e.hom.hom ((q₀ r) • x) = (q₀ r) • e.hom.hom x at h
    exact h
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.inv.hom.map_smul r x
    change e.inv.hom ((q₀ r) • x) = (q₀ r) • e.inv.hom x at h
    exact h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.hom_inv_id
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.inv_hom_id

set_option maxHeartbeats 800000 in
-- 実商環上のホモロジーと複数の商作用を同時に照合するため。
/-- 有限根族について、実導来商還元のH0は元のA/(p,d)上忠実平坦。 -/
theorem deltaRootFamilySourceQuotientDerivedH0_faithfullyFlat (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat (A ⧸ k₀)
      ((ModuleCat.restrictScalars (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (DeltaRootSourceQuotientDerived D d b).obj)) := by
  have hpP : Function.Injective (fun x : P₀ => (p : P₀) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₀)
  have hpL : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
  have hg := witt_ghostMap_injective_of_mul_prime_injective p L₀ hpL
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  let := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpP hpL hg v hv
  let H := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
    (DeltaRootSourceQuotientDerived D d b).obj
  let M := (ModuleCat.restrictScalars
    (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj H
  let eQ := deltaRootFamilySourceQuotientDerivedH0Iso D d b s hpA v hv
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

local notation "X₀" => DeltaRootSourceQuotientDerived D d b

/-- 有限根族の実商還元は、標準t構造の非負部分に属する。 -/
theorem deltaRootFamilySourceQuotientDerived_isGE_zero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DerivedCategory.IsGE (X₀).obj 0 := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact deltaRootFamilySourceQuotientDerived_homology_isZero
    D d b s hpA v hv i (by omega)

/-- 同じ入力の下で標準t構造の非正部分にも属する。 -/
theorem deltaRootFamilySourceQuotientDerived_isLE_zero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DerivedCategory.IsLE (X₀).obj 0 := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact deltaRootFamilySourceQuotientDerived_homology_isZero
    D d b s hpA v hv i (by omega)

/-- 実Q上の還元対象は、作用を降下した既存raw残余商の次数零対象と同型。 -/
def deltaRootFamilySourceQuotientDerivedSingleIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    X₀ ≅ boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Res₀) := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  have := deltaRootFamilySourceQuotientDerived_isGE_zero D d b s hpA v hv
  have := deltaRootFamilySourceQuotientDerived_isLE_zero D d b s hpA v hv
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso (X₀).obj 0) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (deltaRootFamilySourceQuotientDerivedH0Iso D d b s hpA v hv)

/-- この導来同型のH0は、前工程で構成した具体的な商環線形同型そのもの。 -/
theorem deltaRootFamilySourceQuotientDerivedSingleIso_homologyZero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
        (deltaRootFamilySourceQuotientDerivedSingleIso
          D d b s hpA v hv).hom.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q₀) 0).hom.app
        (ModuleCat.of Q₀ Res₀) =
      (deltaRootFamilySourceQuotientDerivedH0Iso D d b s hpA v hv).hom := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  have := deltaRootFamilySourceQuotientDerived_isGE_zero D d b s hpA v hv
  have := deltaRootFamilySourceQuotientDerived_isLE_zero D d b s hpA v hv
  let e := deltaRootFamilySourceQuotientDerivedH0Iso D d b s hpA v hv
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q₀) 0).hom.naturality
    e.hom
  change (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
      ((DerivedCategory.singleFunctor (ModuleCat Q₀) 0).map e.hom) ≫ _ = _ at hn
  change (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
    ((normalizedPureHomologyIso (X₀).obj 0).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat Q₀) 0).map e.hom) ≫ _ = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    normalizedPureHomologyIso_homology, Category.id_comp]
  rfl

end SerrePositivity.BhattScholze
