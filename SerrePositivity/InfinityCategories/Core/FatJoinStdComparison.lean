module

public import SerrePositivity.InfinityCategories.Core.FatJoinStdSection
public import SerrePositivity.InfinityCategories.Core.FatJoinCylinderEpi
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の標準単体の fat join 比較の前合成の同値条件。
方針：比較と切断の合成を正規化に同一視し、二対六則を適用する。
規約：任意の二つの自然数の標準単体。一般の因子への貼り合わせは別工程。
使われ方：Kerodon Theorem 4.6.2.8 の標準単体の場合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準単体の円柱の比較から切断に戻すと左右の正規化の円柱写像になる。
方針：各頂点の三成分に有限順序集合の計算を適用する。
規約：円柱から円柱への射の厳密な等式。
使われ方：Kerodon §4.6.2 の切断と正規化の同一視。 -/
lemma joinCylinderMap_stdSectionCylinder (n m : ℕ) :
    (joinCylinderMap (Δ[n] : SSet.{u}) Δ[m] ≫ (joinStdSimplexIso n m).hom) ≫
      fatJoinStdSectionCylinder n m =
        fatJoinTransformCylinder (stdSimplexProductMap (FatJoinStd.leftClamp n))
          (stdSimplexProductMap (FatJoinStd.rightClamp m)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, t⟩, b⟩
  let w : (Δ[n + m + 1] : SSet.{u}) _⦋d⦌ :=
    (joinStdSimplexIso n m).hom.app (Opposite.op ⦋d⦌)
      ((joinCylinderMap Δ[n] Δ[m]).app (Opposite.op ⦋d⦌) ((a, t), b))
  have he (i : Fin (d + 1)) := FatJoinStd.section_encode n m (a i) (t i) (b i) (w i)
    (joinCylinderMap_stdSimplex_val n m d a t b i)
  apply Prod.ext
  · apply Prod.ext
    · apply stdSimplex.ext
      intro i
      exact congrArg (fun q ↦ q.1.1) (he i)
    · apply stdSimplex.ext
      intro i
      exact congrArg (fun q ↦ q.1.2) (he i)
  · apply stdSimplex.ext
    intro i
    exact congrArg (fun q ↦ q.2) (he i)

/-- 概要：標準単体の fat join の比較と切断の合成は左右の正規化。
方針：円柱がエピ射であることを使い、円柱上の三成分の計算で比較する。
規約：全ての次数の射の厳密な等式。
使われ方：Kerodon Theorem 4.6.2.8 の変形による検出。 -/
lemma fatJoinComparison_stdSection (n m : ℕ) :
    fatJoinComparison (Δ[n] : SSet.{u}) Δ[m] ≫ fatJoinStdSection n m =
      fatJoinStdNormalize n m := by
  have : Nonempty ((Δ[n] : SSet.{u}) _⦋0⦌) := ⟨stdSimplex.obj₀Equiv.symm 0⟩
  have : Nonempty ((Δ[m] : SSet.{u}) _⦋0⦌) := ⟨stdSimplex.obj₀Equiv.symm 0⟩
  apply (cancel_epi (fatJoinCylinder (Δ[n] : SSet.{u}) Δ[m])).1
  rw [← Category.assoc, fatJoinCylinder_comparison]
  calc
    joinCylinderMap (Δ[n] : SSet.{u}) Δ[m] ≫ fatJoinStdSection n m =
        ((joinCylinderMap Δ[n] Δ[m] ≫ (joinStdSimplexIso n m).hom) ≫
          fatJoinStdSectionCylinder n m) ≫ fatJoinCylinder Δ[n] Δ[m] := by
      simp only [fatJoinStdSection, fatJoinStdSectionSimplex, Category.assoc]
    _ = fatJoinTransformCylinder (stdSimplexProductMap (FatJoinStd.leftClamp n))
          (stdSimplexProductMap (FatJoinStd.rightClamp m)) ≫ fatJoinCylinder Δ[n] Δ[m] := by
      rw [joinCylinderMap_stdSectionCylinder]
    _ = fatJoinCylinder Δ[n] Δ[m] ≫ fatJoinStdNormalize n m :=
      (fatJoinCylinder_transform _ _ _ _).symm

/-- 概要：任意の二つの標準単体の fat join 比較は前合成の同値条件を満たす。
方針：一方の合成が恒等、他方が可逆な変形を持つ正規化になる切断に二対六則を使う。
規約：任意の n、m。任意の quasicategory への前合成が同値という結論。
使われ方：Kerodon Theorem 4.6.2.8 の標準単体の場合。 -/
@[kerodon 01HY]
lemma isPrecompositionEquivalence_fatJoinComparison_stdSimplex (n m : ℕ) :
    IsPrecompositionEquivalence (fatJoinComparison (Δ[n] : SSet.{u}) Δ[m]) := by
  apply isPrecompositionEquivalence_of_composites (f := fatJoinStdSection n m)
    (h := fatJoinStdSection n m)
  · rw [fatJoinStdSection_comparison]
    exact isPrecompositionEquivalence_id _
  · rw [fatJoinComparison_stdSection]
    exact isPrecompositionEquivalence_fatJoinStdNormalize n m

end SerrePositivity.InfinityCategories
