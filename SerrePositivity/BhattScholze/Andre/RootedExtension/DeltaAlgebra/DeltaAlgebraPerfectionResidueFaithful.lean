module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionResidueFlat

/-! # 実Frobenius各段の標準剰余の単位と忠実性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "F₀" => deltaAlgebraFrobeniusStageModuleDiagram E j ⋙ ModuleCat.extendScalars q₀

/-- 各実段の標準剰余内の、元の環単位から来る元。 -/
def deltaAlgebraFrobeniusStageResidueUnit (n : ℕ) : (F₀).obj n :=
  (show baseChangeScalarModule q₀ from (1 : Q₀)) ⊗ₜ[A]
    (show baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) from (1 : B))

/-- 標準剰余の各隣接射は元の環単位を保つ。 -/
theorem deltaAlgebraFrobeniusStageResidueUnit_succ (n : ℕ) :
    (F₀).map (homOfLE (Nat.le_succ n)) (deltaAlgebraFrobeniusStageResidueUnit E j d n) =
      deltaAlgebraFrobeniusStageResidueUnit E j d (n + 1) := by
  change (ModuleCat.extendScalars q₀).map
    ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE (Nat.le_succ n))) _ = _
  rw [deltaAlgebraFrobeniusStageModuleDiagram_map_succ]
  simp only [deltaAlgebraFrobeniusStageResidueUnit, ModuleCat.ExtendScalars.map_tmul]
  apply congrArg (fun b : B =>
    (show baseChangeScalarModule q₀ from (1 : Q₀)) ⊗ₜ[A]
      (show baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j (n + 1)) from b))
  exact E.frobeniusLift.map_one

/-- 正確な標準剰余の単位によるテンソル写像は、各実環段で単射。 -/
theorem deltaAlgebraFrobeniusStageResidue_unitTensor_injective
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (n : ℕ) (N : Type u) [AddCommGroup N] [Module Q₀ N] :
    Function.Injective (TensorProduct.mk Q₀ ((F₀).obj n) N
      (deltaAlgebraFrobeniusStageResidueUnit E j d n)) := by
  let : Algebra A B := (deltaAlgebraFrobeniusCoefficient E j n).toAlgebra
  let : Algebra A Q₀ := (q₀).toAlgebra
  have h := deltaAlgebraFrobeniusStageResidueTensor_faithfullyFlat
    D E j d n hD hj hzero hFF
  let : Module.FaithfullyFlat Q₀ (Q₀ ⊗[A] B) := h
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := Q₀) (B := Q₀ ⊗[A] B) N

/-- 任意二段の標準剰余射も、元の環単位を保つ。 -/
theorem deltaAlgebraFrobeniusStageResidueUnit_map {i k : ℕ} (h : i ≤ k) :
    (F₀).map (homOfLE h) (deltaAlgebraFrobeniusStageResidueUnit E j d i) =
      deltaAlgebraFrobeniusStageResidueUnit E j d k := by
  change (ModuleCat.extendScalars q₀).map
    ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE h)) _ = _
  simp only [deltaAlgebraFrobeniusStageResidueUnit, ModuleCat.ExtendScalars.map_tmul]
  rw [deltaAlgebraFrobeniusStageModuleDiagram_map_apply]
  apply congrArg (fun b : B =>
    (show baseChangeScalarModule q₀ from (1 : Q₀)) ⊗ₜ[A]
      (show baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j k) from b))
  exact (E.frobeniusLift ^ (k - i)).map_one

/-- 単位を保つ実図式の有限段検出により、実δ完全化の標準剰余は忠実平坦。 -/
theorem deltaAlgebraPerfectionResidueTensor_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀ ((ModuleCat.extendScalars q₀).obj
      (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))) := by
  let M := (ModuleCat.extendScalars q₀).obj
    (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality Q₀ M).mpr
  refine ⟨deltaAlgebraPerfectionResidueTensor_flat D E j d hD hj hzero hFF, ?_⟩
  intro N _ _ hN
  let F := F₀
  let H := tensorRight (ModuleCat.of Q₀ N)
  let K := F ⋙ H
  let e : colimit K ≅ H.obj M :=
    (preservesColimitIso H F).symm ≪≫
      H.mapIso (deltaAlgebraPerfectionResidueColimitIso E j d)
  have : Subsingleton (N ⊗[Q₀] M) := hN
  have : Subsingleton (M ⊗[Q₀] N) := (TensorProduct.comm Q₀ M N).injective.subsingleton
  have : Subsingleton (H.obj M) := by
    change Subsingleton (M ⊗[Q₀] N)
    infer_instance
  have : Subsingleton (colimit K : ModuleCat Q₀) := e.toLinearEquiv.injective.subsingleton
  let U := forget (ModuleCat.{u} Q₀)
  let : PreservesFilteredColimitsOfSize.{0, 0} U :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let ht := isColimitOfPreserves U (colimit.isColimit K)
  refine ⟨fun x y => ?_⟩
  let z := deltaAlgebraFrobeniusStageResidueUnit E j d 0
  have heq : (U.mapCocone (colimit.cocone K)).ι.app 0 (z ⊗ₜ[Q₀] x) =
      (U.mapCocone (colimit.cocone K)).ι.app 0 (z ⊗ₜ[Q₀] y) := by
    change (colimit.ι K 0).hom (z ⊗ₜ[Q₀] x) = (colimit.ι K 0).hom (z ⊗ₜ[Q₀] y)
    exact Subsingleton.elim _ _
  obtain ⟨k, f, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff' ht
    (z ⊗ₜ[Q₀] x) (z ⊗ₜ[Q₀] y)).mp heq
  have hf : f = homOfLE (Nat.zero_le k) := Subsingleton.elim _ _
  subst f
  change (F.map (homOfLE (Nat.zero_le k))).hom.rTensor N (z ⊗ₜ[Q₀] x) =
    (F.map (homOfLE (Nat.zero_le k))).hom.rTensor N (z ⊗ₜ[Q₀] y) at hk
  rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul] at hk
  dsimp only [z] at hk
  rw [deltaAlgebraFrobeniusStageResidueUnit_map] at hk
  exact deltaAlgebraFrobeniusStageResidue_unitTensor_injective
    D E j d hD hj hzero hFF k N hk

/-- 忠実平坦な通常標準剰余を、同じ実導来還元のH0へ戻す。 -/
theorem deltaAlgebraPerfectionResidueH0_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj
          (boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)))).obj) := by
  let M := (ModuleCat.extendScalars q₀).obj
    (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))
  have : Module.FaithfullyFlat Q₀ M :=
    deltaAlgebraPerfectionResidueTensor_faithfullyFlat D E j d hD hj hzero hFF
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M
    ((boundedAboveDerivedBaseChangeModuleH0Iso q₀).app
      (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))).toLinearEquiv

end SerrePositivity.BhattScholze
