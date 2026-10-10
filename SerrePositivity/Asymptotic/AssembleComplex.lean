module

public import SerrePositivity.Asymptotic.SequenceComplex
public import SerrePositivity.Asymptotic.RankQuotient
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# 自由複体の族を自由列の複体に組み戻す

各段の複体に有限自由な項とランクの `O(s)` 評価があれば、基底を選んで
`FreeSequence` 上の実際の複体を構成できる。共通の次数範囲と `o(s)` 条件も
保存する。各段との比較は鎖複体の同型であり、ホモロジーだけの比較ではない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}
  (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ → ℕ → ℕ)
  (hr : ∀ i, (fun n ↦ (r i n : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ)))
  (e : ∀ n i, ModuleCat.of R (Fin (r i n) → R) ≅ (P n).X i)

/-- 指定された基底の同型で微分を移して、自由列の複体を作る。 -/
def assembleComplex : CochainComplex (FreeSequence R s) ℤ where
  X i := ⟨r i, hr i⟩
  d i j n := ((e n i).hom ≫ (P n).d i j ≫ (e n j).inv).hom
  shape i j hij := by
    funext n
    change ((e n i).hom ≫ (P n).d i j ≫ (e n j).inv).hom = 0
    rw [(P n).shape i j hij, zero_comp, comp_zero]
    rfl
  d_comp_d' i j k _ _ := by
    funext n
    have h : ((e n i).hom ≫ (P n).d i j ≫ (e n j).inv) ≫
        ((e n j).hom ≫ (P n).d j k ≫ (e n k).inv) = 0 := by simp
    exact congrArg ModuleCat.Hom.hom h

/-- 組み戻した複体を評価すると、元の複体と鎖同型になる。 -/
def evaluateAssembleIso (n : ℕ) :
    (evaluateComplex n).obj (assembleComplex P r hr e) ≅ P n :=
  HomologicalComplex.Hom.isoOfComponents (e n) (by
    intro i j _
    change (e n i).hom ≫ (P n).d i j =
      ((e n i).hom ≫ (P n).d i j ≫ (e n j).inv) ≫ (e n j).hom
    simp)

/-- 段ごとの共通有界性は、組み戻した自由列の複体の有界性になる。 -/
lemma assembleComplex_bounded (a b : ℤ)
    (hb : ∀ n i, (i < a ∨ b < i) → IsZero ((P n).X i)) :
    strictlyBoundedComplex (FreeSequence R s) (assembleComplex P r hr e) := by
  have hzero (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((assembleComplex P r hr e).X i) := by
    apply (IsZero.iff_id_eq_zero _).2
    funext n
    exact congrArg ModuleCat.Hom.hom
      (((hb n i hi).of_iso (e n i)).eq_of_src
        (𝟙 (ModuleCat.of R (Fin (r i n) → R))) 0)
  exact ⟨a, b, (CochainComplex.isStrictlyGE_iff _ a).2 (fun i hi ↦ hzero i (.inl hi)),
    (CochainComplex.isStrictlyLE_iff _ b).2 (fun i hi ↦ hzero i (.inr hi))⟩

/-- 各項のランクが `o(s)` なら、組み戻した共通有界複体はランク商で消える側に属する。 -/
lemma assembleComplex_rankSmall (a b : ℤ)
    (hb : ∀ n i, (i < a ∨ b < i) → IsZero ((P n).X i))
    (hsmall : ∀ i, (fun n ↦ (r i n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    rankSmallComplex (assembleComplex P r hr e) :=
  ⟨assembleComplex_bounded P r hr e a b hb, hsmall⟩

end SerrePositivity.Asymptotic
