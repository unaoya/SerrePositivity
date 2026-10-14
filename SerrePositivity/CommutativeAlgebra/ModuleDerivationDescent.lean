module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # 全射な代数写像に沿う加群値導分の降下

終域の加群を値域とし、核を消すことを確認してから導分を降ろす。
値域が終域の環自身である必要はない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {R S T V : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [AddCommGroup V] [Module R V] [Module S V] [Module T V] [IsScalarTower S T V]

/-- 全射の核を消す加群値導分を、その同じ加群へ降ろす。 -/
def descendModuleDerivation (hf : Function.Surjective (algebraMap S T))
    (δ : Derivation R S V) (hδ : ∀ x, algebraMap S T x = 0 → δ x = 0) :
    Derivation R T V := by
  let f := (IsScalarTower.toAlgHom R S T).toLinearMap
  have hk : LinearMap.ker f ≤ LinearMap.ker δ.toLinearMap := fun x hx ↦ hδ x hx
  let g := f.liftOfSurjective hf ⟨δ.toLinearMap, hk⟩
  have hg (x : S) : g (algebraMap S T x) = δ x :=
    LinearMap.equivOfSurjective_apply hf hk
  refine { toLinearMap := g, map_one_eq_zero' := ?_, leibniz' := ?_ }
  · rw [← map_one (algebraMap S T), hg, δ.map_one_eq_zero]
  · intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, hg, hg, hg]
    simpa only [algebraMap_smul] using δ.leibniz a b

@[simp] theorem descendModuleDerivation_apply (hf : Function.Surjective (algebraMap S T))
    (δ : Derivation R S V) (hδ : ∀ x, algebraMap S T x = 0 → δ x = 0) (x : S) :
    descendModuleDerivation hf δ hδ (algebraMap S T x) = δ x :=
  LinearMap.equivOfSurjective_apply hf _
end SerrePositivity
