module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinStdSection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinCylinderEpi
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の標準単体の fat join 比較の前合成の同値条件。
方針：比較と切断の合成を正規化に同一視し、二対六則を適用する。
規約：任意の二つの自然数の標準単体。一般の因子への貼り合わせは別工程。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の場合。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：標準単体の円柱の比較から切断に戻すと左右の正規化の円柱写像になる。
方針：各頂点の三成分に有限順序集合の計算を適用する。
規約：円柱から円柱への射の厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の切断と正規化の同一視。 -/
lemma joinCylinderMap_stdSectionCylinder (n m : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap (Δ[n] : SSet.{u}) Δ[m] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSectionCylinder n m =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClamp m)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, t⟩, b⟩
  let w : (Δ[n + m + 1] : SSet.{u}) _⦋d⦌ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom.app (Opposite.op ⦋d⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[n] Δ[m]).app (Opposite.op ⦋d⦌) ((a, t), b))
  have he (i : Fin (d + 1)) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinStd.section_encode n m (a i) (t i) (b i) (w i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_stdSimplex_val n m d a t b i)
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
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の変形による検出。 -/
lemma fatJoinComparison_stdSection (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[n] : SSet.{u}) Δ[m] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSection n m =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdNormalize n m := by
  have : Nonempty ((Δ[n] : SSet.{u}) _⦋0⦌) := ⟨stdSimplex.obj₀Equiv.symm 0⟩
  have : Nonempty ((Δ[m] : SSet.{u}) _⦋0⦌) := ⟨stdSimplex.obj₀Equiv.symm 0⟩
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder (Δ[n] : SSet.{u}) Δ[m])).1
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_comparison]
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap (Δ[n] : SSet.{u}) Δ[m] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSection n m =
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[n] Δ[m] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSectionCylinder n m) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[n] Δ[m] := by
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSectionSimplex, Category.assoc]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransformCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClamp m)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[n] Δ[m] := by
      rw [joinCylinderMap_stdSectionCylinder]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[n] Δ[m] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdNormalize n m :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_transform _ _ _ _).symm

/-- 概要：任意の二つの標準単体の fat join 比較は前合成の同値条件を満たす。
方針：一方の合成が恒等、他方が可逆な変形を持つ正規化になる切断に二対六則を使う。
規約：任意の n、m。任意の quasicategory への前合成が同値という結論。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の場合。 -/
@[kerodon 01HY]
lemma isPrecompositionEquivalence_fatJoinComparison_stdSimplex (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[n] : SSet.{u}) Δ[m]) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_composites (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSection n m)
    (h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSection n m)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSection_comparison]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _
  · rw [fatJoinComparison_stdSection]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinStdNormalize n m

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
