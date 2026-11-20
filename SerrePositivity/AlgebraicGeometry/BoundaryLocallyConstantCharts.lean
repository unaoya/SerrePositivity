module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BoundaryFiniteClopenSeparation
public import Mathlib.Topology.LocallyConstant.Basic

/-!
概要：KST §5、Stacks 0811 の境界外の局所定数関数をチャートごとに一定にする中心。
方針：コンパクト性から値の集合を有限とし、開閉ファイバーの有限分割を分離する。
規約：通常の blowup の生成元チャートを用い、境界外の点での等式を返す。
使われ方：一般階数の局所定数性から、一定階数の特殊形を使えるチャートを選ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry

variable {R α : Type*} [CommRing R]

/--
概要：境界外の局所定数関数を各生成元チャートの境界外で一定にする有限生成中心が存在する。
方針：有限個の値の開閉ファイバーを分離し、各チャートの逆像が全体であることを等式に直す。
規約：KST §5、Stacks 0811, Lemma 38.30.3・Lemma 31.35.5、基礎環の Noether 性は不要。
使われ方：階数の一定性を未証明の追加仮定として残さず、実際のチャートで実現する。
-/
theorem exists_fg_center_constant_on_boundary_charts (f : R) (hf : IsRegular f)
    (ρ : PrimeSpectrum (Localization.Away f) → α) (hρ : IsLocallyConstant ρ) :
    ∃ (I : Ideal R) (a : Set.range ρ → I),
      I.FG ∧ affineCenterComplement I = PrimeSpectrum.basicOpen f ∧
      (⨆ i, affineBlowupChart I (a i)) = ⊤ ∧
      Pairwise (fun i j => Disjoint (affineBlowupChart I (a i)) (affineBlowupChart I (a j))) ∧
      ∀ i (P : PrimeSpectrum (Localization.Away (chartBaseMap I (a i) f))),
        ρ (PrimeSpectrum.comap (Localization.awayMap (chartBaseMap I (a i)) f) P) = i.val := by
  let : Fintype (Set.range ρ) := hρ.range_finite.fintype
  let s : Set.range ρ → Set (PrimeSpectrum (Localization.Away f)) :=
    fun i => {P | ρ P = i.val}
  have hs (i : Set.range ρ) : IsClopen (s i) := hρ.isClopen_fiber i.val
  have hd : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro P hi hj
    apply hij
    exact Subtype.ext (hi.symm.trans hj)
  have hc : (⋃ i, s i) = Set.univ := by
    ext P
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨⟨ρ P, ⟨P, rfl⟩⟩, rfl⟩
  obtain ⟨I, a, hfg, hI, hcover, hdisj, h1, _⟩ :=
    exists_fg_center_separating_boundary_finite_clopen_partition f hf s hs hd hc
  refine ⟨I, a, hfg, hI, hcover, hdisj, ?_⟩
  intro i P
  have hmem : P ∈ (PrimeSpectrum.comap (Localization.awayMap (chartBaseMap I (a i)) f)) ⁻¹'
      s i := by rw [h1 i]; trivial
  exact hmem

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
