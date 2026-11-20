module

public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
概要：KST §5、Stacks 051R の一般自由性のための有限個の先頭次数の選択。
方針：Dickson の補題から先頭次数集合の有限な極小元を選び、それらを持つ多項式を取る。
規約：単項式次数の比較は座標毎の順序。係数環の整域性は選択自体には不要。
使われ方：有限個の先頭係数を反転して商の標準単項式基底を作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：良準順序を持つ半順序集合の任意の部分集合は、有限個のその元で下から覆える。
方針：部分集合の極小元の反鎖の有限性と、各元の下の極小元の存在を使う。
規約：KST §5、Stacks 051R の Dickson の補題の利用。空集合も許す。
使われ方：イデアルの先頭単項式の有限な支配集合。
-/
theorem exists_finite_lower_cover
    {α : Type u} [PartialOrder α] [WellQuasiOrderedLE α] (D : Set α) :
    ∃ s : Finset α, (s : Set α) ⊆ D ∧ ∀ d ∈ D, ∃ e ∈ s, e ≤ d := by
  classical
  let E : Set α := {x | Minimal (fun y => y ∈ D) x}
  have hanti : IsAntichain (· ≤ ·) E := by
    intro a ha b hb hab hle
    exact hab (le_antisymm hle (hb.2 ha.1 hle))
  have hfin := WellQuasiOrderedLE.finite_of_isAntichain hanti
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro e he
    exact (hfin.mem_toFinset.mp he).1
  · intro d hd
    obtain ⟨e, hed, he⟩ := exists_minimal_le_of_wellFoundedLT (fun y => y ∈ D) d hd
    exact ⟨e, hfin.mem_toFinset.mpr he, hed⟩

/--
概要：有限変数多項式のイデアルの非零元の先頭次数は、有限個の非零イデアル元の先頭次数で覆える。
方針：先頭次数の集合に Dickson の有限被覆を適用し、その有限集合の各次数の代表を選ぶ。
規約：KST §5、Stacks 051R、次数の不等式は座標毎のもの。係数環の Noether 性は不要。
使われ方：有限個の先頭係数を同時に単元にする局所化の選択。
-/
theorem exists_finite_leading_degree_cover
    {σ R : Type u} [Finite σ] [CommRing R] (m : MonomialOrder σ)
    (H : Ideal (MvPolynomial σ R)) :
    ∃ G : Finset (MvPolynomial σ R),
      (∀ g ∈ G, g ∈ H ∧ g ≠ 0) ∧
      ∀ h ∈ H, h ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree h := by
  classical
  let D : Set (σ →₀ ℕ) := {d | ∃ g ∈ H, g ≠ 0 ∧ m.degree g = d}
  obtain ⟨s, hs, hcover⟩ := exists_finite_lower_cover D
  have hchoose (d : s) : ∃ g ∈ H, g ≠ 0 ∧ m.degree g = d.val := hs d.property
  choose g hgH hg0 hgd using hchoose
  let G : Finset (MvPolynomial σ R) := Finset.univ.image g
  refine ⟨G, ?_, ?_⟩
  · intro p hp
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hgH d, hg0 d⟩
  · intro h hh hh0
    obtain ⟨d, hd, hdh⟩ := hcover (m.degree h) ⟨h, hh, hh0, rfl⟩
    refine ⟨g ⟨d, hd⟩, Finset.mem_image.mpr ⟨⟨d, hd⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    rwa [hgd]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
