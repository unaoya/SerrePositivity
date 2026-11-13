module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechAugmentation
public import SerrePositivity.AlgebraicGeometry.CechRefinementConeExactness
public import SerrePositivity.HomologicalAlgebra.Cech.Diagonal

/-!
概要：二つの完全な増大 Čech の細分写像の cone は完全。
方針：共通の大域切断を増大項に取り、既存の cone の加群計算に渡す。
規約：ここでは両方の増大 Čech の完全性を前提とする。
使われ方：共通細分の二重図式の正次数の行。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
variable (U : ι → Opens X) (V : κ → Opens X) (ρ : κ → ι) (hρ : ∀ i, V i ≤ U (ρ i))

/-- 共通増大項を保つ、二つの完全な Čech の細分写像の cone の完全性。 -/
theorem openCoverCechRefinementCone_exact
    (hU : OpenCoverCechAcyclic P U) (hV : OpenCoverCechAcyclic P V) :
    SerrePositivity.Cech.RowExact
      (fun i _ ↦ cechRefinementConeTerm (fullCechComplex (openCoverCechDiagram P U))
        (fullCechComplex (openCoverCechDiagram P V)) i)
      (fun i _ ↦ (cechRefinementConeDifferential (fullCechComplex (openCoverCechDiagram P U))
        (fullCechComplex (openCoverCechDiagram P V))
        (openCoverCechRefinementMap P U V ρ hρ) i).toAddHom) 0 := by
  let A := fullCechComplex (openCoverCechDiagram P U)
  let B := fullCechComplex (openCoverCechDiagram P V)
  let f := openCoverCechRefinementMap P U V ρ hρ
  let a := openCoverCechAugmentation P U
  let b := openCoverCechAugmentation P V
  have hab : (f.f 0).hom.comp a = b := openCoverCechRefinement_augmentation P U V ρ hρ
  have ha : Function.Exact a (A.d 0 1).hom := openCoverCechAugmentation_exact P U hU
  have hb : Function.Exact b (B.d 0 1).hom := openCoverCechAugmentation_exact P V hV
  constructor
  · exact cechRefinementCone_zero_kernel A B f a b hab
      (openCoverCechAugmentation_injective P V hV) ha
  · apply cechRefinementCone_cycle_boundary A B f a b hab ha hb
    · intro n
      change Function.Exact (A.d n (n + 1)).hom (A.d (n + 1) ((n + 1) + 1)).hom
      simpa only [A, fullCechComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
        using hU.exact (n + 1)
    · intro n
      change Function.Exact (B.d n (n + 1)).hom (B.d (n + 1) ((n + 1) + 1)).hom
      simpa only [B, fullCechComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
        using hV.exact (n + 1)

end SerrePositivity.AlgebraicGeometry
