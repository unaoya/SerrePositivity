module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialNaturality

/-!
# 完備した厳密な標的模型の行ごとの擬同型に対する不変性

## 概要
元の入力を一様下界のある行ごとの擬同型で替えると、同じ S 完備標的 Tot も擬同型となる。

## 方針
元の Tot の擬同型性と、標準比較の自然性・同型性を同じ四角形へ入れる。

## 規約
対象ごとの同型だけで図式の模型を同一視せず、実際の余単体的射を使う。

## 使われ方
BS 著者版 Lemma 4.22 の厳密な行模型の擬同型による照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 行ごとの擬同型は、元の完備導来底変換の厳密な標的模型の Tot の擬同型となる。 -/
theorem resolvedCompletedTotalMap_quasiIso (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (c : ℕ) (hf : SerrePositivity.HasCochainCompleteTorAmplitude f x c)
    {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) (bX bY : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < bX → IsZero ((X.obj ⦋n⦌).homology i))
    (hY : ∀ n : ℕ, ∀ i : ℤ, i < bY → IsZero ((Y.obj ⦋n⦌).homology i))
    (hg : ∀ n : ℕ, QuasiIso (g.app ⦋n⦌)) :
    QuasiIso (cosimplicialTotalMap (resolvedCompletedCosimplicialMap f x g)) := by
  haveI : QuasiIso (cosimplicialTotalMap g) :=
    total_map_quasiIso_of_rows ((alternatingCofaceMapComplex (Complex R)).map g) (min bX bY)
      (fun n i hi => hX n i (lt_of_lt_of_le hi (min_le_left _ _)))
      (fun n i hi => hY n i (lt_of_lt_of_le hi (min_le_right _ _))) hg
  haveI := cosimplicialNativeCompletedBaseChangeComparison_isIso f x c hf X bX hX
  haveI := cosimplicialNativeCompletedBaseChangeComparison_isIso f x c hf Y bY hY
  have hn := cosimplicialNativeCompletedBaseChangeComparison_naturality f x g bX bY hX hY
  haveI : IsIso (cosimplicialNativeCompletedBaseChangeComparison f x X bX hX ≫
      DerivedCategory.Q.map (cosimplicialTotalMap (resolvedCompletedCosimplicialMap f x g))) := by
    rw [← hn]
    infer_instance
  have hT : IsIso (DerivedCategory.Q.map
      (cosimplicialTotalMap (resolvedCompletedCosimplicialMap f x g))) :=
    IsIso.of_isIso_comp_left (cosimplicialNativeCompletedBaseChangeComparison f x X bX hX) _
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} S) _).mp hT

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
