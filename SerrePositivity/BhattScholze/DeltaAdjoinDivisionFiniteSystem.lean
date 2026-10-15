module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionReindexFunctorial
public import Mathlib.Algebra.Colimit.DirectLimit

/-! # 有限部分族raw包の具体的な有向系 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

/-- 元の係数δ環上の有限部分族raw除算包。 -/
abbrev DeltaAdjoinDivisionFiniteStage (T : Finset σ) :=
  DeltaAdjoinDivision D d (fun t : T ↦ a t)

/-- 有限集合包含に沿う標準raw包δ射。 -/
def deltaAdjoinDivisionFiniteMap {S T : Finset σ} (h : S ⊆ T) :
    DeltaAdjoinDivisionFiniteStage D d a S →+* DeltaAdjoinDivisionFiniteStage D d a T :=
  deltaAdjoinDivisionReindex D d (fun s : S ↦ a s) (fun t : T ↦ a t)
    (fun s ↦ ⟨s, h s.property⟩) (fun _ ↦ rfl)

/-- 有限部分族遷移射のδ・係数・初期変数の公式。 -/
theorem deltaAdjoinDivisionFiniteMap_spec {S T : Finset σ} (h : S ⊆ T) :
    (deltaAdjoinDivisionStructure D d (fun s : S ↦ a s)).IsDeltaHom
        (deltaAdjoinDivisionStructure D d (fun t : T ↦ a t))
        (deltaAdjoinDivisionFiniteMap D d a h) ∧
      (deltaAdjoinDivisionFiniteMap D d a h).comp
        (deltaAdjoinDivisionMap D d (fun s : S ↦ a s)) =
          deltaAdjoinDivisionMap D d (fun t : T ↦ a t) ∧
      ∀ s : S, deltaAdjoinDivisionFiniteMap D d a h
        (deltaAdjoinDivisionVariable D d (fun s : S ↦ a s) s) =
          deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) ⟨s, h s.property⟩ :=
  deltaAdjoinDivisionReindex_spec D d (fun s : S ↦ a s) (fun t : T ↦ a t)
    (fun s ↦ ⟨s, h s.property⟩) (fun _ ↦ rfl)

/-- 有限部分族の恒等包含はraw包の恒等射。 -/
theorem deltaAdjoinDivisionFiniteMap_self (T : Finset σ) :
    deltaAdjoinDivisionFiniteMap D d a (Finset.Subset.refl T) =
      RingHom.id (DeltaAdjoinDivisionFiniteStage D d a T) :=
  deltaAdjoinDivisionReindex_id D d (fun t : T ↦ a t)

/-- 有限部分族の包含合成はraw包の遷移射の合成を保つ。 -/
theorem deltaAdjoinDivisionFiniteMap_comp {S T U : Finset σ} (h : S ⊆ T) (k : T ⊆ U) :
    (deltaAdjoinDivisionFiniteMap D d a k).comp (deltaAdjoinDivisionFiniteMap D d a h) =
      deltaAdjoinDivisionFiniteMap D d a (h.trans k) :=
  deltaAdjoinDivisionReindex_comp D d (fun s : S ↦ a s) (fun t : T ↦ a t)
    (fun t : U ↦ a t) (fun s ↦ ⟨s, h s.property⟩) (fun t ↦ ⟨t, k t.property⟩)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- 有限部分族raw環のMathlib有向系。 -/
instance deltaAdjoinDivisionFiniteDirectedSystem :
    DirectedSystem (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
      (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h) where
  map_self {i} x := by
    rw [deltaAdjoinDivisionFiniteMap_self]
    rfl
  map_map {k j i} hij hjk x :=
    RingHom.congr_fun (deltaAdjoinDivisionFiniteMap_comp D d a hij hjk) x

/-- 有限部分族raw包から全族raw包への標準δ射。 -/
def deltaAdjoinDivisionFiniteToFull (T : Finset σ) :
    DeltaAdjoinDivisionFiniteStage D d a T →+* DeltaAdjoinDivision D d a :=
  deltaAdjoinDivisionReindex D d (fun t : T ↦ a t) a Subtype.val (fun _ ↦ rfl)

/-- 全族への標準射のδ・係数・初期変数の公式。 -/
theorem deltaAdjoinDivisionFiniteToFull_spec (T : Finset σ) :
    (deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).IsDeltaHom
        (deltaAdjoinDivisionStructure D d a) (deltaAdjoinDivisionFiniteToFull D d a T) ∧
      (deltaAdjoinDivisionFiniteToFull D d a T).comp
        (deltaAdjoinDivisionMap D d (fun t : T ↦ a t)) = deltaAdjoinDivisionMap D d a ∧
      ∀ t : T, deltaAdjoinDivisionFiniteToFull D d a T
        (deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) t) =
          deltaAdjoinDivisionVariable D d a t :=
  deltaAdjoinDivisionReindex_spec D d (fun t : T ↦ a t) a Subtype.val (fun _ ↦ rfl)

/-- 全族への標準射は有限部分族の全遷移射と両立する。 -/
theorem deltaAdjoinDivisionFiniteToFull_compatible {S T : Finset σ} (h : S ⊆ T) :
    (deltaAdjoinDivisionFiniteToFull D d a T).comp (deltaAdjoinDivisionFiniteMap D d a h) =
      deltaAdjoinDivisionFiniteToFull D d a S :=
  deltaAdjoinDivisionReindex_comp D d (fun s : S ↦ a s) (fun t : T ↦ a t) a
    (fun s ↦ ⟨s, h s.property⟩) Subtype.val (fun _ ↦ rfl) (fun _ ↦ rfl)

end SerrePositivity.BhattScholze
