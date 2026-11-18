module

public import SerrePositivity.EInfinity.BarrattEccles.OperadStructure
public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurGeneratorWeights
public import SerrePositivity.EInfinity.BarrattEccles.Theory.WeightedTensorFamily

/-!
# Schur 表示の基底と重み保存の射

## 概要
Berger–Fresse §1.1 の係数を重み零とし、Berger–Moerdijk §1 の Schur 生成射を扱う。

## 方針
非正次数の正則基底と、正次数の空の基底を合わせる。

## 規約
係数の重みは零であり、元の入力だけを数える。

## 使われ方
自由代数の演算の合成が重みを増やさないことの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory DifferentialGraded
attribute [local implicit_reducible] SymmetricSequence SymmetricSequence.level
variable {A : Type u} [CommRing A]

/-- The regular coefficient indices in all degrees, empty in positive degrees. -/
def arityGradedIndex (n : ℕ) (p : ℤ) : Type u :=
  if p ≤ 0 then ULift.{u} (BasedNondegenerate n (-p).toNat) × Equiv.Perm (Fin n)
  else PEmpty

/-- A homogeneous basis for every degree of a Barratt–Eccles coefficient complex. -/
def arityGradedBasis (n : ℕ) (p : ℤ) :
    Module.Basis (arityGradedIndex n p) A (((operad A).arity n).X p) := by
  change Module.Basis (arityGradedIndex n p) A ((complex A n).X p)
  classical
  by_cases hp : p ≤ 0
  · have he : p = -(((-p).toNat : ℕ) : ℤ) := by omega
    have b := equivariantBasis A n (-p).toNat
    rw [← he] at b
    simpa only [arityGradedIndex, ite_eq_left hp] using b
  · haveI : Subsingleton ((complex A n).X p) :=
      ModuleCat.subsingleton_of_isZero (complex_isZero_positive A n p (by omega))
    change Module.Basis (if p ≤ 0 then _ else PEmpty) A _
    rw [ite_eq_right hp]
    exact Module.Basis.empty _

/-- Coefficients have their actual homogeneous basis and weight zero. -/
abbrev arityWeightBasis (n : ℕ) : ComplexWeightBasis ((operad A).arity n) :=
  ⟨arityGradedIndex n, arityGradedBasis n, fun _ => 0⟩

/-- The Schur basis is weighted by the total weight of its original inputs. -/
abbrev schurWeightBasis {K : Complex A} (b : ComplexWeightBasis K) :
    ComplexWeightBasis ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K) :=
  ⟨SchurWordIndex b.index, schurWordBasis b.basis, fun x => schurWordWeight b.weight x.2⟩

/-- A Schur generator preserves the total input weight, including arbitrary coefficients. -/
lemma preserves_schurι {K : Complex A} (b : ComplexWeightBasis K) (n : ℕ) :
    ((arityWeightBasis n).tensor (b.power n)).Preserves (schurWeightBasis b)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n) := by
  intro i N x hx
  apply map_mem_basisWeightSpan
    (tensorGradedBasis (arityGradedBasis n) (powerGradedBasis b.basis n) i)
    (schurWordBasis b.basis i)
    (tensorGradedWeight (fun _ => 0) (powerGradedWeightFamily b.weight n) i)
    (schurWordWeight b.weight) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n).f i).hom ?_ N hx
  rintro ⟨a, z, y⟩
  rw [tensorGradedBasis_apply]
  have h := schurGenerator_mem_basisWeightSpan_all b.basis b.weight
    a.1.1 a.1.2 i a.2 n (arityGradedBasis n a.1.1 z) _
    (basis_mem_basisWeightSpan (powerGradedBasis b.basis n a.1.2)
      (powerGradedWeight b.weight n a.1.2) y)
  simp only [tensorGradedWeight, powerGradedWeightFamily, zero_add] at h ⊢
  exact h

/-- Every map into a weight-zero coefficient basis preserves the input bound. -/
lemma preserves_to_arity {K : Complex A} (b : ComplexWeightBasis K) (n : ℕ)
    (f : K ⟶ (operad A).arity n) : b.Preserves (arityWeightBasis n) f := by
  intro i N x hx
  exact mem_basisWeightSpan_zero (arityGradedBasis n i) N (f.f i x)

end SerrePositivity.EInfinity.BarrattEccles
