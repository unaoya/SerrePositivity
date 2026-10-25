module

public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # δ環射から実Frobenius環段の正確な係数加群へ -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B)

/-- 実Frobenius環段の係数射。基底作用を元のjと暗黙に同一視しない。 -/
def deltaAlgebraFrobeniusCoefficient (n : ℕ) : A →+* B := (E.frobeniusLift ^ n).comp j

/-- δ環射の自然性により、実段の係数作用は基底Frobeniusの制限作用と一致する。 -/
theorem deltaAlgebraFrobeniusCoefficient_apply (hj : D.IsDeltaHom E j) (n : ℕ) (a : A) :
    deltaAlgebraFrobeniusCoefficient E j n a = j ((D.frobeniusLift ^ n) a) := by
  change (E.frobeniusLift : B → B)^[n] (j a) = j ((D.frobeniusLift : A → A)^[n] a)
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hj.map_frobeniusLift]

/-- 正確なj_n作用を持つ実B段と、実基底Frobenius制限加群の恒等線形同型。 -/
def deltaAlgebraFrobeniusStageModuleIso (hj : D.IsDeltaHom E j) (n : ℕ) :
    (ModuleCat.restrictScalars (D.frobeniusLift ^ n)).obj (baseChangeScalarModule j) ≅
      baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) := by
  let e : (ModuleCat.restrictScalars (D.frobeniusLift ^ n)).obj (baseChangeScalarModule j) ≃ₗ[A]
      baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change B at x
        rw [RingHom.id_apply]
        change j ((D.frobeniusLift ^ n) a) * x = deltaAlgebraFrobeniusCoefficient E j n a * x
        rw [deltaAlgebraFrobeniusCoefficient_apply D E j hj] }
  exact e.toModuleIso

/-- 同じ係数比較を、実導来制限と既存の実段single対象の比較へ持ち上げる。 -/
def deltaAlgebraFrobeniusStageSingleIso (hj : D.IsDeltaHom E j) (n : ℕ) :
    (boundedAboveDerivedRestrictScalars (D.frobeniusLift ^ n)).obj
      (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j)) ≅
        boundedAboveDerivedSingleFunctor.obj
          (baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n)) :=
  ObjectProperty.isoMk _
    ((derivedRestrictScalarsSingleIso (D.frobeniusLift ^ n) 0).app (baseChangeScalarModule j) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
        (deltaAlgebraFrobeniusStageModuleIso D E j hj n))

/-- 実φ_Bの隣接遷移は、各段の正確な係数作用についてA線形。 -/
def deltaAlgebraFrobeniusStageTransition (n : ℕ) :
    baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) ⟶
      baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j (n + 1)) := by
  let f : baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) →ₗ[A]
      baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j (n + 1)) :=
    { toFun := fun x => E.frobeniusLift x
      map_add' := E.frobeniusLift.map_add
      map_smul' := by
        intro a x
        change B at x
        rw [RingHom.id_apply]
        change E.frobeniusLift (deltaAlgebraFrobeniusCoefficient E j n a * x) =
          deltaAlgebraFrobeniusCoefficient E j (n + 1) a * E.frobeniusLift x
        rw [map_mul]
        change E.frobeniusLift ((E.frobeniusLift : B → B)^[n] (j a)) * E.frobeniusLift x =
          (E.frobeniusLift : B → B)^[n + 1] (j a) * E.frobeniusLift x
        rw [Function.iterate_succ_apply'] }
  exact { hom' := f }

/-- 実Frobenius各環段の、正確な元A作用を持つ逐次加群図式。 -/
def deltaAlgebraFrobeniusStageModuleDiagram : ℕ ⥤ ModuleCat.{u} A :=
  Functor.ofSequence (fun n => deltaAlgebraFrobeniusStageTransition E j n)

/-- 図式の隣接射は、定義した実Frobenius遷移そのもの。 -/
theorem deltaAlgebraFrobeniusStageModuleDiagram_map_succ (n : ℕ) :
    (deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE (Nat.le_succ n)) =
      deltaAlgebraFrobeniusStageTransition E j n :=
  Functor.ofSequence_map_homOfLE_succ _ n

end SerrePositivity.BhattScholze
