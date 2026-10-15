module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionFiniteSystem
public import Mathlib.Algebra.Colimit.Ring

/-! # 有限部分族raw包の環余極限と標準δ構造 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

/-- 有限部分族raw包のMathlib環余極限。 -/
abbrev DeltaAdjoinDivisionFiniteColimit :=
  Ring.DirectLimit (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
    (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h)

/-- 有限部分族から環余極限への標準環射。 -/
def deltaAdjoinDivisionFiniteColimitOf (T : Finset σ) :
    DeltaAdjoinDivisionFiniteStage D d a T →+* DeltaAdjoinDivisionFiniteColimit D d a :=
  Ring.DirectLimit.of _ _ T

/-- 標準段射と有限部分族の遷移射の可換性。 -/
theorem deltaAdjoinDivisionFiniteColimitOf_compatible {S T : Finset σ} (h : S ⊆ T)
    (x : DeltaAdjoinDivisionFiniteStage D d a S) :
    deltaAdjoinDivisionFiniteColimitOf D d a T (deltaAdjoinDivisionFiniteMap D d a h x) =
      deltaAdjoinDivisionFiniteColimitOf D d a S x :=
  Ring.DirectLimit.of_f (G := fun T ↦ DeltaAdjoinDivisionFiniteStage D d a T)
    (f := fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h) h x

/-- 各段のW₂切断を移した余極限上の環切断。 -/
def deltaAdjoinDivisionFiniteColimitSection :
    DeltaAdjoinDivisionFiniteColimit D d a →+*
      WittTwo p (DeltaAdjoinDivisionFiniteColimit D d a) :=
  Ring.DirectLimit.lift _ _ _
    (fun T ↦ (wittTwoMap (deltaAdjoinDivisionFiniteColimitOf D d a T)).comp
      (deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).sectionHom) (by
      intro S T h x
      apply TruncatedWittVector.ext
      intro k
      fin_cases k
      · simp only [RingHom.comp_apply, wittTwoMap_coeff]
        change deltaAdjoinDivisionFiniteColimitOf D d a T
          (((deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).sectionHom
            (deltaAdjoinDivisionFiniteMap D d a h x)).coeff 0) =
          deltaAdjoinDivisionFiniteColimitOf D d a S
            (((deltaAdjoinDivisionStructure D d (fun s : S ↦ a s)).sectionHom x).coeff 0)
        rw [DeltaStructure.coeff_zero, DeltaStructure.coeff_zero]
        exact deltaAdjoinDivisionFiniteColimitOf_compatible D d a h x
      · simp only [RingHom.comp_apply, wittTwoMap_coeff]
        change deltaAdjoinDivisionFiniteColimitOf D d a T
          ((deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).delta
            (deltaAdjoinDivisionFiniteMap D d a h x)) =
          deltaAdjoinDivisionFiniteColimitOf D d a S
            ((deltaAdjoinDivisionStructure D d (fun s : S ↦ a s)).delta x)
        rw [← (deltaAdjoinDivisionFiniteMap_spec D d a h).1 x]
        exact deltaAdjoinDivisionFiniteColimitOf_compatible D d a h _)

/-- 余極限の切断の各有限段上の公式。 -/
theorem deltaAdjoinDivisionFiniteColimitSection_of (T : Finset σ)
    (x : DeltaAdjoinDivisionFiniteStage D d a T) :
    deltaAdjoinDivisionFiniteColimitSection D d a (deltaAdjoinDivisionFiniteColimitOf D d a T x) =
      wittTwoMap (deltaAdjoinDivisionFiniteColimitOf D d a T)
        ((deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).sectionHom x) :=
  Ring.DirectLimit.lift_of _ _ _ T x

/-- 有限部分族環余極限の標準δ構造。 -/
def deltaAdjoinDivisionFiniteColimitStructure :
    DeltaStructure p (DeltaAdjoinDivisionFiniteColimit D d a) where
  sectionHom := deltaAdjoinDivisionFiniteColimitSection D d a
  coeff_zero := by
    classical
    intro x
    obtain ⟨T, y, rfl⟩ := Ring.DirectLimit.exists_of x
    change (deltaAdjoinDivisionFiniteColimitSection D d a
      (deltaAdjoinDivisionFiniteColimitOf D d a T y)).coeff 0 =
        deltaAdjoinDivisionFiniteColimitOf D d a T y
    rw [deltaAdjoinDivisionFiniteColimitSection_of, wittTwoMap_coeff, DeltaStructure.coeff_zero]

/-- 全ての有限段の標準射はδ射。 -/
theorem deltaAdjoinDivisionFiniteColimitOf_isDeltaHom (T : Finset σ) :
    (deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).IsDeltaHom
      (deltaAdjoinDivisionFiniteColimitStructure D d a)
      (deltaAdjoinDivisionFiniteColimitOf D d a T) := by
  intro x
  change deltaAdjoinDivisionFiniteColimitOf D d a T
      ((deltaAdjoinDivisionStructure D d (fun t : T ↦ a t)).delta x) =
    (deltaAdjoinDivisionFiniteColimitSection D d a
      (deltaAdjoinDivisionFiniteColimitOf D d a T x)).coeff 1
  rw [deltaAdjoinDivisionFiniteColimitSection_of, wittTwoMap_coeff]
  rfl

/-- 環余極限から全族raw包への標準環射。 -/
def deltaAdjoinDivisionFiniteColimitToFull :
    DeltaAdjoinDivisionFiniteColimit D d a →+* DeltaAdjoinDivision D d a :=
  Ring.DirectLimit.lift _ _ _ (fun T ↦ deltaAdjoinDivisionFiniteToFull D d a T) (by
    intro S T h x
    exact DFunLike.congr_fun (deltaAdjoinDivisionFiniteToFull_compatible D d a h) x)

/-- 全族への標準射は各有限段の既存標準射を延長する。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_of (T : Finset σ)
    (x : DeltaAdjoinDivisionFiniteStage D d a T) :
    deltaAdjoinDivisionFiniteColimitToFull D d a (deltaAdjoinDivisionFiniteColimitOf D d a T x) =
      deltaAdjoinDivisionFiniteToFull D d a T x :=
  Ring.DirectLimit.lift_of _ _ _ T x

/-- 環余極限から全族raw包への標準射はδ射。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom :
    (deltaAdjoinDivisionFiniteColimitStructure D d a).IsDeltaHom
      (deltaAdjoinDivisionStructure D d a) (deltaAdjoinDivisionFiniteColimitToFull D d a) := by
  classical
  intro x
  obtain ⟨T, y, rfl⟩ := Ring.DirectLimit.exists_of x
  change deltaAdjoinDivisionFiniteColimitToFull D d a
    ((deltaAdjoinDivisionFiniteColimitStructure D d a).delta
      (deltaAdjoinDivisionFiniteColimitOf D d a T y)) =
    (deltaAdjoinDivisionStructure D d a).delta
      (deltaAdjoinDivisionFiniteColimitToFull D d a
        (deltaAdjoinDivisionFiniteColimitOf D d a T y))
  rw [← deltaAdjoinDivisionFiniteColimitOf_isDeltaHom D d a T y,
    deltaAdjoinDivisionFiniteColimitToFull_of, deltaAdjoinDivisionFiniteColimitToFull_of]
  exact (deltaAdjoinDivisionFiniteToFull_spec D d a T).1 y

/-- 空有限段を通る余極限への標準係数射。 -/
def deltaAdjoinDivisionFiniteColimitBaseMap : A →+* DeltaAdjoinDivisionFiniteColimit D d a :=
  (deltaAdjoinDivisionFiniteColimitOf D d a ∅).comp
    (deltaAdjoinDivisionMap D d (fun t : (∅ : Finset σ) ↦ a t))

/-- 標準係数射は任意の有限段を通る。 -/
theorem deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage (T : Finset σ) (x : A) :
    deltaAdjoinDivisionFiniteColimitBaseMap D d a x =
      deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionMap D d (fun t : T ↦ a t) x) := by
  have h := deltaAdjoinDivisionFiniteColimitOf_compatible D d a (Finset.empty_subset T)
    (deltaAdjoinDivisionMap D d (fun t : (∅ : Finset σ) ↦ a t) x)
  have hc := DFunLike.congr_fun
    (deltaAdjoinDivisionFiniteMap_spec D d a (Finset.empty_subset T)).2.1 x
  change deltaAdjoinDivisionFiniteMap D d a (Finset.empty_subset T)
    (deltaAdjoinDivisionMap D d (fun t : (∅ : Finset σ) ↦ a t) x) = _ at hc
  rw [hc] at h
  exact h.symm

/-- 余極限の標準係数射はδ射。 -/
theorem deltaAdjoinDivisionFiniteColimitBaseMap_isDeltaHom :
    D.IsDeltaHom (deltaAdjoinDivisionFiniteColimitStructure D d a)
      (deltaAdjoinDivisionFiniteColimitBaseMap D d a) :=
  (deltaAdjoinDivisionFiniteColimitOf_isDeltaHom D d a ∅).comp
    (deltaAdjoinDivisionMap_isDeltaHom D d (fun t : (∅ : Finset σ) ↦ a t))

/-- 全族への射と余極限への係数射の合成は全族の標準係数射。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_comp_base :
    (deltaAdjoinDivisionFiniteColimitToFull D d a).comp
      (deltaAdjoinDivisionFiniteColimitBaseMap D d a) = deltaAdjoinDivisionMap D d a := by
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage D d a ∅,
    deltaAdjoinDivisionFiniteColimitToFull_of]
  exact DFunLike.congr_fun (deltaAdjoinDivisionFiniteToFull_spec D d a ∅).2.1 x

end SerrePositivity.BhattScholze
