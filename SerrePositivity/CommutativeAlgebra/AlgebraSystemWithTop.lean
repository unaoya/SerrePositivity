module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Order.WithBot
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Flat.Basic

/-! # 有向代数図式へ新しい終段を加える

既存図式からTへの実際の両立する写像を使い、WithTopで終段を追加する。
自己写像・合成則と、指定終域への写像の両立を証明する。
図式の存在を仮定した構造体で置き換えず、遷移写像を具体的に定義する。
-/

@[expose] public section
namespace SerrePositivity
universe u
variable {B ι : Type*} [CommRing B] [Preorder ι]
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
variable (T : Type u) [CommRing T] [Algebra B T]

/-- 新しい終段Tを持つ段の族。 -/
def algebraSystemWithTopObj : WithTop ι → Type u
  | none => T
  | some i => S i

instance (i : WithTop ι) : CommRing (algebraSystemWithTopObj S T i) :=
  match i with
  | none => inferInstanceAs (CommRing T)
  | some j => inferInstanceAs (CommRing (S j))

instance (i : WithTop ι) : Algebra B (algebraSystemWithTopObj S T i) :=
  match i with
  | none => inferInstanceAs (Algebra B T)
  | some j => inferInstanceAs (Algebra B (S j))

instance algebraSystemWithTop_local [∀ i, IsLocalRing (S i)] [IsLocalRing T]
    (i : WithTop ι) : IsLocalRing (algebraSystemWithTopObj S T i) :=
  match i with
  | none => inferInstanceAs (IsLocalRing T)
  | some j => inferInstanceAs (IsLocalRing (S j))

instance algebraSystemWithTop_flat [∀ i, Module.Flat B (S i)] [Module.Flat B T]
    (i : WithTop ι) : Module.Flat B (algebraSystemWithTopObj S T i) :=
  match i with
  | none => inferInstanceAs (Module.Flat B T)
  | some j => inferInstanceAs (Module.Flat B (S j))

instance algebraSystemWithTop_baseLocal [∀ i, IsLocalHom (algebraMap B (S i))]
    [IsLocalHom (algebraMap B T)] (i : WithTop ι) :
    IsLocalHom (algebraMap B (algebraSystemWithTopObj S T i)) :=
  match i with
  | none => inferInstanceAs (IsLocalHom (algebraMap B T))
  | some j => inferInstanceAs (IsLocalHom (algebraMap B (S j)))

omit [Preorder ι] in
/-- 極大イデアルが基底の拡張であることを、追加した終段を含む全段で保持する。 -/
theorem algebraSystemWithTop_maximalIdeal_map [IsLocalRing B]
    [∀ i, IsLocalRing (S i)] [IsLocalRing T]
    (hS : ∀ i, (IsLocalRing.maximalIdeal B).map (algebraMap B (S i)) =
      IsLocalRing.maximalIdeal (S i))
    (hT : (IsLocalRing.maximalIdeal B).map (algebraMap B T) = IsLocalRing.maximalIdeal T) :
    ∀ i, (IsLocalRing.maximalIdeal B).map (algebraMap B (algebraSystemWithTopObj S T i)) =
      IsLocalRing.maximalIdeal (algebraSystemWithTopObj S T i) := by
  intro i
  cases i with
  | top => exact hT
  | coe j => exact hS j

variable (f : ∀ i j, i ≤ j → S i →ₐ[B] S j) [DirectedSystem S (f · · ·)]
variable (c : ∀ i, S i →ₐ[B] T)
variable (hc : ∀ i j h x, c j (f i j h x) = c i x)

/-- 旧段どうしはf、旧段から新終段へはc、新終段の自己写像は恒等写像。 -/
def algebraSystemWithTopMap :
    ∀ i j, i ≤ j → algebraSystemWithTopObj S T i →ₐ[B] algebraSystemWithTopObj S T j
  | some i, some j, h => f i j (WithTop.coe_le_coe.mp h)
  | some i, none, _ => c i
  | none, none, _ => AlgHom.id B T
  | none, some j, h => False.elim (WithTop.not_top_le_coe j h)

include hc in
/-- 新終段を加えた遷移写像は、実際に有向図式の法則を満たす。 -/
theorem algebraSystemWithTop_directedSystem :
    DirectedSystem (algebraSystemWithTopObj S T) (algebraSystemWithTopMap S T f c · · ·) := by
  constructor
  · intro i x
    cases i with
    | top => rfl
    | coe i => exact DirectedSystem.map_self' (f := f) x
  · intro k j i hij hjk x
    cases i with
    | top =>
      have hj : j = ⊤ := WithTop.top_le_iff.mp hij
      subst j
      have hk : k = ⊤ := WithTop.top_le_iff.mp hjk
      subst k
      rfl
    | coe i =>
      cases j with
      | top =>
        have hk : k = ⊤ := WithTop.top_le_iff.mp hjk
        subst k
        rfl
      | coe j =>
        cases k with
        | top => exact hc i j (WithTop.coe_le_coe.mp hij) x
        | coe k =>
          exact DirectedSystem.map_map' (f := f)
            (WithTop.coe_le_coe.mp hij) (WithTop.coe_le_coe.mp hjk) x

omit [DirectedSystem S (f · · ·)] in
/-- 旧遷移と新終段への写像が局所なら、追加後の遷移も局所である。 -/
theorem algebraSystemWithTopMap_isLocalHom
    (hf : ∀ i j h, IsLocalHom (f i j h).toRingHom)
    (hcLocal : ∀ i, IsLocalHom (c i).toRingHom) :
    ∀ i j h, IsLocalHom (algebraSystemWithTopMap S T f c i j h).toRingHom := by
  intro i j h
  cases i with
  | top =>
    have hj : j = ⊤ := WithTop.top_le_iff.mp h
    subst j
    exact inferInstanceAs (IsLocalHom (RingHom.id T))
  | coe i =>
    cases j with
    | top => exact hcLocal i
    | coe j => exact hf i j (WithTop.coe_le_coe.mp h)

/-- 前段の直極限からTへの写像を使い、旧図式の全ての段を新終段へ接続する。 -/
theorem algebraSystemWithTop_of_directLimit [IsDirectedOrder ι] [Nonempty ι]
    (q : DirectLimit S f →ₐ[B] T) :
    DirectedSystem (algebraSystemWithTopObj S T)
      (algebraSystemWithTopMap S T f
        (fun i ↦ q.comp (DirectLimit.Algebra.of S f i)) · · ·) := by
  apply algebraSystemWithTop_directedSystem
  intro i j h x
  simp only [AlgHom.comp_apply, DirectLimit.Algebra.of_f]

section Target
variable {K : Type*} [CommRing K] [Algebra B K]
variable (g : ∀ i, S i →ₐ[B] K) (gT : T →ₐ[B] K)
variable (hg : ∀ i j h x, g j (f i j h x) = g i x)
variable (hgc : ∀ i x, gT (c i x) = g i x)

/-- 追加した終段を含む、指定終域への段写像。 -/
def algebraSystemWithTopTarget : ∀ i, algebraSystemWithTopObj S T i →ₐ[B] K
  | none => gT
  | some i => g i

omit [DirectedSystem S (f · · ·)] in
include hg hgc in
/-- 新終段の写像が旧段の写像と両立すれば、追加後も全ての段で両立する。 -/
theorem algebraSystemWithTopTarget_compatible :
    ∀ i j h x, algebraSystemWithTopTarget S T g gT j
      (algebraSystemWithTopMap S T f c i j h x) = algebraSystemWithTopTarget S T g gT i x := by
  intro i j h x
  cases i with
  | top =>
    have hj : j = ⊤ := WithTop.top_le_iff.mp h
    subst j
    rfl
  | coe i =>
    cases j with
    | top => exact hgc i x
    | coe j => exact hg i j (WithTop.coe_le_coe.mp h) x

include hg in
/-- 直極限から新終段への写像が指定終域への写像と両立すれば、延長図式も両立する。 -/
theorem algebraSystemWithTopTarget_of_directLimit [IsDirectedOrder ι] [Nonempty ι]
    (q : DirectLimit S f →ₐ[B] T)
    (hq : gT.comp q = DirectLimit.Algebra.lift S f K g hg) :
    ∀ i j h x, algebraSystemWithTopTarget S T g gT j
      (algebraSystemWithTopMap S T f
        (fun i ↦ q.comp (DirectLimit.Algebra.of S f i)) i j h x) =
      algebraSystemWithTopTarget S T g gT i x := by
  apply algebraSystemWithTopTarget_compatible
  · exact hg
  · intro i x
    change (gT.comp q) (DirectLimit.Algebra.of S f i x) = g i x
    rw [hq, DirectLimit.Algebra.lift_of]

end Target
end SerrePositivity
