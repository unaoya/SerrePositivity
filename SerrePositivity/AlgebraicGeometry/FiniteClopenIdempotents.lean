module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Idempotents

/-!
概要：KST §5、Stacks 00EE・Lemma 31.35.5 の有限開閉分割を表す完全直交冪等元。
方針：各開閉部分の冪等元を選び、基本開の非交差性と被覆性で積と総和を判定する。
規約：空の分割による零環も含む。
使われ方：境界外の有限階数部分を一段の blowup 中心で分離する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R ι : Type*} [CommRing R] [Fintype ι]

/--
概要：有限個の互いに交わらない開閉部分による被覆は完全直交冪等元の族で表せる。
方針：各部分の冪等元を選び、積の基本開が空であることと総和の基本開が全体であることを使う。
規約：KST §5、Stacks 00EE・Lemma 31.35.5、環の Noether 性は不要。
使われ方：有限開閉分割から直交分子中心を構成する。
-/
theorem exists_completeOrthogonalIdempotents_of_finite_clopen_partition
    (s : ι → Set (PrimeSpectrum R)) (hs : ∀ i, IsClopen (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hc : (⋃ i, s i) = Set.univ) :
    ∃ e : ι → R, CompleteOrthogonalIdempotents e ∧
      ∀ i, s i = (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum R)) := by
  classical
  choose e he hse using fun i => PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hs i)
  have hortho : OrthogonalIdempotents e := by
    refine ⟨he, ?_⟩
    intro i j hij
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem ((he i).mul (he j)) .zero
    rw [PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_zero]
    apply bot_unique
    intro P hP
    apply (Set.disjoint_left.mp (hd hij))
    · exact (hse i).symm ▸ hP.1
    · exact (hse j).symm ▸ hP.2
  have hsumIdem : IsIdempotentElem (∑ i, e i) := by
    simpa using hortho.isIdempotentElem_sum (s := Finset.univ)
  have hsum : (∑ i, e i) = 1 := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem hsumIdem .one
    rw [PrimeSpectrum.basicOpen_one]
    apply top_unique
    intro P _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc.symm ▸ (Set.mem_univ P))
    rw [hse i] at hi
    have hei : e i ∉ P.asIdeal := hi
    intro hP
    apply hei
    have hmul : e i * (∑ j, e j) = e i := by
      simpa using hortho.mul_sum_of_mem (i := i) (s := Finset.univ) (Finset.mem_univ i)
    rw [← hmul]
    exact Ideal.mul_mem_left P.asIdeal (e i) hP
  exact ⟨e, ⟨hortho, hsum⟩, hse⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
