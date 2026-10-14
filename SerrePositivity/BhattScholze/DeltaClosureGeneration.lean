module

public import SerrePositivity.BhattScholze.DeltaQuotient
public import Mathlib.Logic.Function.Iterate

/-! # 反復δ像によるδ閉包の生成

BS著者版Example 2.10の表示を、δ安定イデアルの最小性と比較する。
生成元でのδ安定性をイデアル全体へ拡張する際にδの加法・積公式を用いる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- x,yがイデアルIに属すれば、δ加法の繰上り項もIに属する。
商へのWitt写像で両Teichmüller元を零へ送る。 -/
theorem additionCarry_mem (I : Ideal A) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hx0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hy0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
  simp only [← WittVector.map_coeff, map_add, WittVector.map_teichmuller, hx0, hy0,
    WittVector.teichmuller_zero, add_zero, WittVector.zero_coeff]

/-- 生成元のδが生成イデアルに属すれば、そのイデアルはδ安定。
加法の繰上り項と積公式の各項がイデアルに属することを生成帰納法で示す。 -/
theorem isStable_span (D : DeltaStructure p A) (s : Set A)
    (hs : ∀ x ∈ s, D.delta x ∈ Ideal.span s) : D.IsStable (Ideal.span s) := by
  intro x hx
  change x ∈ Submodule.span A s at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [D.delta_add]
      exact (Ideal.span s).add_mem ((Ideal.span s).add_mem ihx ihy)
        (additionCarry_mem (Ideal.span s) hx hy)
  | smul r x hx ih =>
      change D.delta (r * x) ∈ Ideal.span s
      rw [D.delta_mul]
      exact (Ideal.span s).add_mem
        ((Ideal.span s).add_mem ((Ideal.span s).mul_mem_left (r ^ p) ih)
          ((Ideal.span s).mul_mem_left (D.delta r)
            ((Ideal.span s).pow_mem_of_mem hx p (Fact.out : p.Prime).pos)))
        ((Ideal.span s).mul_mem_left ((p : A) * D.delta r) ih)

/-- δ閉包はIのすべての反復δ像で生成されるイデアル（BS Example 2.10）。
抽象的な交わりによる構成に、具体的な生成元表示を与える。 -/
theorem deltaClosure_eq_span_iterates (D : DeltaStructure p A) (I : Ideal A) :
    D.deltaClosure I = Ideal.span (⋃ n : ℕ, D.delta^[n] '' (I : Set A)) := by
  let s : Set A := ⋃ n : ℕ, D.delta^[n] '' (I : Set A)
  have hI : I ≤ Ideal.span s := by
    intro x hx
    apply Ideal.subset_span
    exact Set.mem_iUnion.mpr ⟨0, x, hx, rfl⟩
  have hs : D.IsStable (Ideal.span s) := by
    apply D.isStable_span s
    intro x hx
    obtain ⟨n, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
    apply Ideal.subset_span
    exact Set.mem_iUnion.mpr ⟨n + 1, a, ha, Function.iterate_succ_apply' D.delta n a⟩
  apply le_antisymm (D.deltaClosure_le hI hs)
  apply Ideal.span_le.mpr
  intro x hx
  obtain ⟨n, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
  clear hx
  induction n with
  | zero => exact D.le_deltaClosure I ha
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact D.isStable_deltaClosure I _ ih

end SerrePositivity.BhattScholze.DeltaStructure
