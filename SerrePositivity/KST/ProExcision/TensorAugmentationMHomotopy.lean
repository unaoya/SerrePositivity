module
public import SerrePositivity.KST.ProExcision.NormalizedTensorComparison
public import SerrePositivity.KST.ProExcision.LowChainComparisonReconstruction

/-!
# augmentation 補正したテンソルの実 m 次ホモトピー

概要：二つの因子内の低次ホモトピーから、補正した三項の和への実区間比較を構成する。
方針：厳密化、正規化した差のテンソルの消滅、実 EZ 比較、低次の区間復元を合成する。
規約：KST Construction A.5 の右辺の augmentation 補正 f⊗e′+e⊗g−e⊗e′。
使われ方：最後に T の対角と明示的な群準同型 μ の射を適用する。ここでは自然性の同変版は別工程。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology

/-- 概要：二因子の低次ホモトピーから補正したテンソルの実 (m+m′+1) 次ホモトピーを作る。
方針：二つの全鎖比較の比較先が低次で一致することを使って実区間へ復元する。
規約：KST A.5 の augmentation 補正。前合成 a と後合成 b は明示的な実単体的射。
使われ方：非可換標的の群準同型 μ を最後の後合成として適用する。 -/
def linearizedTensorAugmentationMHomotopy
    {X Y Z : SSet.{u}} {D E F : SimplicialObject (ModuleCat.{u} ℤ)}
    {f e : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D} {g e' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y ⟶ E} {m m' : ℕ}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f e m) (h' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy g e' m')
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor D E ⟶ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f g ≫ b)
      (a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f e' + _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap e g -
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap e e') ≫ b) (m + m' + 1) := by
  let R₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((normalizedMooreComplex _).map h.strictifiedMap)
      ((normalizedMooreComplex _).map h'.strictifiedMap) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle D E
  let S₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((normalizedMooreComplex _).map h.strictifiedMap)
        ((normalizedMooreComplex _).map e') +
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((normalizedMooreComplex _).map e)
        ((normalizedMooreComplex _).map h'.strictifiedMap) -
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((normalizedMooreComplex _).map e)
        ((normalizedMooreComplex _).map e')) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle D E
  let R := (((normalizedMooreComplex _).map a) ≫ R₀) ≫ (normalizedMooreComplex _).map b
  let S := (((normalizedMooreComplex _).map a) ≫ S₀) ≫ (normalizedMooreComplex _).map b
  let H₀ := normalizedTensorComparisonWithHomotopies f g
    h.normalizedStrictificationHomotopy h'.normalizedStrictificationHomotopy
  let H₁ := normalizedTensorAugmentationComparison f e g e'
    h.normalizedStrictificationHomotopy h'.normalizedStrictificationHomotopy
  have HR : Homotopy ((normalizedMooreComplex _).map (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f g ≫ b)) R := by
    refine (Homotopy.ofEq ?_).trans
      ((H₀.compLeft ((normalizedMooreComplex _).map a)).compRight ((normalizedMooreComplex _).map b))
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have HS : Homotopy ((normalizedMooreComplex _).map
      (a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f e' + _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap e g -
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap e e') ≫ b)) S := by
    refine (Homotopy.ofEq ?_).trans
      ((H₁.compLeft ((normalizedMooreComplex _).map a)).compRight ((normalizedMooreComplex _).map b))
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  apply linearizedMHomotopyOfChainComparisons HR HS (m + m' + 1)
  intro n hn
  dsimp only [R, S, R₀, S₀]
  simp only [comp_f, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedStrictifiedTensor_eq_low h h' n hn]

end SerrePositivity.KST.ProExcision
