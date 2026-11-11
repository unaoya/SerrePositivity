module

public import SerrePositivity.EInfinity.ComplexLimits.KProjectiveDerivedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeKProjective

/-!
# 同じ K-projective 導来源と既存 D(R) の同値

概要：実半自由分解の K-projective 部分圏への制限は同じ順方向を持つ ∞ 同値。
方針：既存の半自由 retract の全頂点比較と証明済みの充満忠実性を使う。
規約：D(R) や元の分解を別の模型へ置き換えない。
使われ方：元の cofibrant probe の実写像空間を既存 D(R) へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma kProjectiveDerivedSource_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (kProjectiveDerivedSource A) := by
  intro y
  let Y := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := A) (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A)) y
  let X : KProjectiveComplex A := ⟨Y.val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective A Y.property⟩
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X, ?_⟩
  have e := (complexSemifreeResolutionRetractIso A).app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y = y :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := A) (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A)).symm_apply_apply y
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) := e
  exact ⟨e' ≪≫ eqToIso (congrArg HomotopyCategory.mk hy)⟩

lemma kProjectiveDerivedSource_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (kProjectiveDerivedSource A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (kProjectiveDerivedSource_isFullyFaithful A)
    (kProjectiveDerivedSource_isEssentiallySurjective A)

end SerrePositivity.EInfinity.ComplexLimits
