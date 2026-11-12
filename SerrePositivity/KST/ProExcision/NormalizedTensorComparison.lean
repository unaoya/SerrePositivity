module
public import SerrePositivity.KST.ProExcision.NormalizedEZHomotopyNaturality
public import SerrePositivity.KST.ProExcision.NormalizedFunctorAdditivity

/-!
# 正規化したテンソル写像と AW/shuffle による比較

概要：単体的テンソルの射を、正規化した両因子の全テンソルを通る射へ実鎖ホモトピーで移す。
方針：始域の正規化 EZ ホモトピー、shuffle の自然性、両因子の鎖ホモトピーを合成する。
規約：KST Construction A.5 の augmentation 補正、非被約な零次を含む。
使われ方：厳密化した二つの差の全テンソルの低次消滅を実 m 次比較へ送る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology
variable {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)}

/-- 概要：単体的テンソルの射と正規化した因子の全テンソルを通る射の全鎖比較。
方針：始域の EZ ホモトピーを射の後合成へ移し、shuffle の自然性で整理する。
規約：KST A.5。使われ方：二つのテンソル比較の共通前半。 -/
def normalizedTensorComparisonHomotopy (f : C ⟶ C') (g : D ⟶ D') :
    Homotopy ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f g))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney C D ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle C' D') := by
  let h := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedEZHomotopy C D).compRight
    ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f g))
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · exact (Category.id_comp _).symm
  · rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle_naturality f g]

/-- 概要：両因子の鎖比較を単体的テンソルの全鎖比較へ移す。
方針：標準テンソル比較の後で二つの鎖ホモトピーの全テンソルを AW と shuffle で挟む。
規約：KST A.5、比較先の二つの写像は明示的な実鎖写像。
使われ方：厳密化した二つの射の全テンソルへの比較。 -/
def normalizedTensorComparisonWithHomotopies (f : C ⟶ C') (g : D ⟶ D')
    {F : (normalizedMooreComplex _).obj C ⟶ (normalizedMooreComplex _).obj C'}
    {G : (normalizedMooreComplex _).obj D ⟶ (normalizedMooreComplex _).obj D'}
    (hf : Homotopy ((normalizedMooreComplex _).map f) F)
    (hg : Homotopy ((normalizedMooreComplex _).map g) G) :
    Homotopy ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f g))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney C D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap F G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle C' D') := by
  let h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorHomotopy hf hg).compLeft
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney C D)).compRight (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle C' D')
  refine (normalizedTensorComparisonHomotopy f g).trans
    ((Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_)))
  · simp only [Category.assoc]
  · simp only [Category.assoc]

/-- 概要：augmentation 補正した三項の和を厳密化した両因子の全テンソルへ比較する。
方針：二つの因子の比較を各項へ適用し、第三の項の負の比較を足す。
規約：KST A.5 の右辺の augmentation 補正 f⊗e′+e⊗g−e⊗e′。
使われ方：全テンソルの低次補正式の右辺の実鎖比較。 -/
def normalizedTensorAugmentationComparison
    (f e : C ⟶ C') (g e' : D ⟶ D')
    {F : (normalizedMooreComplex _).obj C ⟶ (normalizedMooreComplex _).obj C'}
    {G : (normalizedMooreComplex _).obj D ⟶ (normalizedMooreComplex _).obj D'}
    (hf : Homotopy ((normalizedMooreComplex _).map f) F)
    (hg : Homotopy ((normalizedMooreComplex _).map g) G) :
    Homotopy ((normalizedMooreComplex _).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f e' + _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap e g - _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap e e'))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney C D ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap F ((normalizedMooreComplex _).map e') +
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((normalizedMooreComplex _).map e) G -
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((normalizedMooreComplex _).map e) ((normalizedMooreComplex _).map e')) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle C' D') := by
  let h₁ := normalizedTensorComparisonWithHomotopies f e' hf
    (Homotopy.refl ((normalizedMooreComplex _).map e'))
  let h₂ := normalizedTensorComparisonWithHomotopies e g
    (Homotopy.refl ((normalizedMooreComplex _).map e)) hg
  let h₃ := normalizedTensorComparisonHomotopy e e'
  let h := (h₁.add h₂).add (h₃.smul (-1 : ℤ))
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · simp only [CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_neg,
      neg_smul, one_smul, sub_eq_add_neg]
  · simp only [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp,
      Preadditive.sub_comp, Preadditive.comp_neg, Preadditive.neg_comp,
      neg_smul, one_smul, sub_eq_add_neg, Category.assoc]

end SerrePositivity.KST.ProExcision
