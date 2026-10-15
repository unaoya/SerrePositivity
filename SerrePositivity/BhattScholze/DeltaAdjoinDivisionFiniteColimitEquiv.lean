module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionFiniteColimit

/-! # 有限部分族raw環余極限と全族raw包の標準δ同型 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L" => DeltaAdjoinDivisionFiniteColimit D d a
local notation "DL" => deltaAdjoinDivisionFiniteColimitStructure D d a
local notation "B" => DeltaAdjoinDivision D d a
local notation "DB" => deltaAdjoinDivisionStructure D d a
local notation "jL" => deltaAdjoinDivisionFiniteColimitBaseMap D d a
local notation "jB" => deltaAdjoinDivisionMap D d a
local notation "toB" => deltaAdjoinDivisionFiniteColimitToFull D d a

/-- 単元部分族を通る余極限の標準除算変数。 -/
def deltaAdjoinDivisionFiniteColimitVariable (s : σ) : L := by
  classical
  exact deltaAdjoinDivisionFiniteColimitOf D d a {s}
    (deltaAdjoinDivisionVariable D d (fun t : ({s} : Finset σ) ↦ a t)
      ⟨s, Finset.mem_singleton_self s⟩)

/-- 余極限変数は、それを含む任意の有限段の変数の像と一致する。 -/
theorem deltaAdjoinDivisionFiniteColimitVariable_eq_stage (T : Finset σ) (s : T) :
    deltaAdjoinDivisionFiniteColimitVariable D d a s =
      deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) s) := by
  classical
  have h : ({(s : σ)} : Finset σ) ⊆ T := Finset.singleton_subset_iff.mpr s.property
  have hc := deltaAdjoinDivisionFiniteColimitOf_compatible D d a h
    (deltaAdjoinDivisionVariable D d (fun t : ({(s : σ)} : Finset σ) ↦ a t)
      ⟨s, Finset.mem_singleton_self _⟩)
  rw [(deltaAdjoinDivisionFiniteMap_spec D d a h).2.2] at hc
  exact hc.symm

/-- 全ての余極限変数は元の除算関係を満たす。 -/
theorem deltaAdjoinDivisionFiniteColimit_relation (s : σ) :
    jL d * deltaAdjoinDivisionFiniteColimitVariable D d a s = jL (a s) := by
  classical
  rw [deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage D d a {s} d,
    deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage D d a {s} (a s)]
  change deltaAdjoinDivisionFiniteColimitOf D d a {s}
      (deltaAdjoinDivisionMap D d (fun t : ({s} : Finset σ) ↦ a t) d) *
    deltaAdjoinDivisionFiniteColimitOf D d a {s}
      (deltaAdjoinDivisionVariable D d (fun t : ({s} : Finset σ) ↦ a t)
        ⟨s, Finset.mem_singleton_self _⟩) = _
  rw [← map_mul, deltaAdjoinDivision_relation]

/-- 全族raw包から有限部分族余極限への標準δ射の普遍性。 -/
theorem existsUnique_deltaAdjoinDivisionFullToFiniteColimit :
    ∃! f : B →+* L, (DB).IsDeltaHom DL f ∧ f.comp jB = jL ∧
      ∀ s, f (deltaAdjoinDivisionVariable D d a s) =
        deltaAdjoinDivisionFiniteColimitVariable D d a s := by
  apply existsUnique_deltaAdjoinDivisionHom D DL d a jL
    (deltaAdjoinDivisionFiniteColimitBaseMap_isDeltaHom D d a)
  exact deltaAdjoinDivisionFiniteColimit_relation D d a

/-- 全族raw包から有限部分族余極限への標準δ射。 -/
def deltaAdjoinDivisionFullToFiniteColimit : B →+* L :=
  (existsUnique_deltaAdjoinDivisionFullToFiniteColimit D d a).choose

/-- 標準逆方向射のδ・係数・変数公式。 -/
theorem deltaAdjoinDivisionFullToFiniteColimit_spec :
    (DB).IsDeltaHom DL (deltaAdjoinDivisionFullToFiniteColimit D d a) ∧
      (deltaAdjoinDivisionFullToFiniteColimit D d a).comp jB = jL ∧
      ∀ s, deltaAdjoinDivisionFullToFiniteColimit D d a
        (deltaAdjoinDivisionVariable D d a s) =
          deltaAdjoinDivisionFiniteColimitVariable D d a s :=
  (existsUnique_deltaAdjoinDivisionFullToFiniteColimit D d a).choose_spec.1

/-- 余極限から全族への射は各標準除算変数を保つ。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_variable (s : σ) :
    toB (deltaAdjoinDivisionFiniteColimitVariable D d a s) =
      deltaAdjoinDivisionVariable D d a s := by
  classical
  change toB (deltaAdjoinDivisionFiniteColimitOf D d a {s}
    (deltaAdjoinDivisionVariable D d (fun t : ({s} : Finset σ) ↦ a t)
      ⟨s, Finset.mem_singleton_self _⟩)) = _
  rw [deltaAdjoinDivisionFiniteColimitToFull_of]
  exact (deltaAdjoinDivisionFiniteToFull_spec D d a {s}).2.2 _

/-- 全族raw包上で標準二方向射の合成は恒等射。 -/
theorem deltaAdjoinDivisionFiniteColimitToFull_comp_inverse :
    (toB).comp (deltaAdjoinDivisionFullToFiniteColimit D d a) = RingHom.id B := by
  have hi := deltaAdjoinDivisionFullToFiniteColimit_spec D d a
  apply deltaAdjoinDivisionHom_ext D DB d a _ _
    ((deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom D d a).comp hi.1) (DB).isDeltaHom_id
  · rw [RingHom.comp_assoc, hi.2.1, deltaAdjoinDivisionFiniteColimitToFull_comp_base,
      RingHom.id_comp]
  · intro s
    rw [RingHom.comp_apply, hi.2.2, deltaAdjoinDivisionFiniteColimitToFull_variable]
    rfl

/-- 有限部分族余極限上でも標準二方向射の合成は恒等射。 -/
theorem deltaAdjoinDivisionFullToFiniteColimit_comp_inverse :
    (deltaAdjoinDivisionFullToFiniteColimit D d a).comp toB = RingHom.id L := by
  have hi := deltaAdjoinDivisionFullToFiniteColimit_spec D d a
  apply Ring.DirectLimit.hom_ext
  intro T
  apply deltaAdjoinDivisionHom_ext D DL d (fun t : T ↦ a t) _ _
    ((hi.1.comp (deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom D d a)).comp
      (deltaAdjoinDivisionFiniteColimitOf_isDeltaHom D d a T))
    ((DL).isDeltaHom_id.comp (deltaAdjoinDivisionFiniteColimitOf_isDeltaHom D d a T))
  · apply RingHom.ext
    intro x
    change deltaAdjoinDivisionFullToFiniteColimit D d a
      (toB (deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionMap D d (fun t : T ↦ a t) x))) =
      deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionMap D d (fun t : T ↦ a t) x)
    rw [deltaAdjoinDivisionFiniteColimitToFull_of]
    have hc := DFunLike.congr_fun (deltaAdjoinDivisionFiniteToFull_spec D d a T).2.1 x
    change deltaAdjoinDivisionFiniteToFull D d a T
      (deltaAdjoinDivisionMap D d (fun t : T ↦ a t) x) = jB x at hc
    rw [hc]
    have hb := DFunLike.congr_fun hi.2.1 x
    change deltaAdjoinDivisionFullToFiniteColimit D d a (jB x) = jL x at hb
    rw [hb, deltaAdjoinDivisionFiniteColimitBaseMap_eq_stage D d a T]
  · intro s
    change deltaAdjoinDivisionFullToFiniteColimit D d a
      (toB (deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) s))) =
      deltaAdjoinDivisionFiniteColimitOf D d a T
        (deltaAdjoinDivisionVariable D d (fun t : T ↦ a t) s)
    rw [deltaAdjoinDivisionFiniteColimitToFull_of,
      (deltaAdjoinDivisionFiniteToFull_spec D d a T).2.2, hi.2.2,
      deltaAdjoinDivisionFiniteColimitVariable_eq_stage]

/-- 任意族raw包は有限部分族raw環余極限と標準同型。 -/
def deltaAdjoinDivisionFiniteColimitEquiv : L ≃+* B :=
  RingEquiv.ofRingHom toB (deltaAdjoinDivisionFullToFiniteColimit D d a)
    (deltaAdjoinDivisionFiniteColimitToFull_comp_inverse D d a)
    (deltaAdjoinDivisionFullToFiniteColimit_comp_inverse D d a)

/-- 標準余極限同型の両方向はδ構造を保つ。 -/
theorem deltaAdjoinDivisionFiniteColimitEquiv_isDeltaHom :
    (DL).IsDeltaHom DB (deltaAdjoinDivisionFiniteColimitEquiv D d a).toRingHom ∧
      (DB).IsDeltaHom DL (deltaAdjoinDivisionFiniteColimitEquiv D d a).symm.toRingHom :=
  ⟨deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom D d a,
    (deltaAdjoinDivisionFullToFiniteColimit_spec D d a).1⟩

/-- 標準余極限同型は任意有限段の標準射を延長する。 -/
theorem deltaAdjoinDivisionFiniteColimitEquiv_of (T : Finset σ)
    (x : DeltaAdjoinDivisionFiniteStage D d a T) :
    deltaAdjoinDivisionFiniteColimitEquiv D d a (deltaAdjoinDivisionFiniteColimitOf D d a T x) =
      deltaAdjoinDivisionFiniteToFull D d a T x :=
  deltaAdjoinDivisionFiniteColimitToFull_of D d a T x

end SerrePositivity.BhattScholze
