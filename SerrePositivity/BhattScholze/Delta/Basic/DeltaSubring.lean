module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaIdentities

/-! # δ安定部分環へのδ構造の制限

既存ofFunctionとWittベクトルの自然性を用いる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ安定部分環には、元のδ作用を制限したδ構造が入る。 -/
def subring (D : DeltaStructure p A) (S : Subring A)
    (hS : ∀ x ∈ S, D.delta x ∈ S) : DeltaStructure p S := by
  let δ : S → S := fun x ↦ ⟨D.delta x, hS x x.property⟩
  apply ofFunction δ
  · exact Subtype.ext D.delta_zero
  · exact Subtype.ext D.delta_one
  · intro x y
    apply Subtype.ext
    have hc : S.subtype ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1) =
        (WittVector.teichmuller p (x : A) + WittVector.teichmuller p (y : A)).coeff 1 := by
      rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
        WittVector.map_teichmuller]
      rfl
    change D.delta ((x : A) + (y : A)) = D.delta x + D.delta y +
      S.subtype ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1)
    rw [hc, D.delta_add]
  · intro x y
    apply Subtype.ext
    change D.delta ((x : A) * (y : A)) =
      (x : A) ^ p * D.delta y + D.delta x * (y : A) ^ p + (p : A) * D.delta x * D.delta y
    exact D.delta_mul x y

/-- 制限したδ作用は、元のδ作用の部分型への制限そのもの。 -/
theorem subring_delta (D : DeltaStructure p A) (S : Subring A)
    (hS : ∀ x ∈ S, D.delta x ∈ S) (x : S) :
    (D.subring S hS).delta x = ⟨D.delta x, hS x x.property⟩ := rfl

/-- δ安定部分環の包含はδ射。 -/
theorem subring_subtype_isDeltaHom (D : DeltaStructure p A) (S : Subring A)
    (hS : ∀ x ∈ S, D.delta x ∈ S) : (D.subring S hS).IsDeltaHom D S.subtype := by
  intro x
  rfl

/-- 包含をδ射にする部分環のδ構造は、制限したδ構造と一意に一致する。 -/
theorem subring_unique (D : DeltaStructure p A) (S : Subring A)
    (hS : ∀ x ∈ S, D.delta x ∈ S) (E : DeltaStructure p S)
    (hE : E.IsDeltaHom D S.subtype) : E = D.subring S hS := by
  apply DeltaStructure.ext
  intro x
  apply Subtype.ext
  exact hE x

end SerrePositivity.BhattScholze.DeltaStructure
