module
public import SerrePositivity.KST.ProExcision.GroupProductNerve
public import SerrePositivity.KST.ProExcision.LinearizedEndpoints

/-!
# 群の積の nerve の自由整数テンソルへの移送

概要：共通始域の対角と群準同型 μ を非被約な自由整数加群のテンソル界面へ移す。
方針：自由化と積のテンソル同型の自然性を使う。
規約：KST Construction A.5 の μ 版。標的群の可換性を仮定しない。
使われ方：一般テンソルの augmentation 補正式を群準同型の実射へ同定する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

/-- 概要：単体的集合の対角を自由整数加群のテンソルへの射にする。
方針：幾何的対角の自由化に積とテンソルの同型の逆を合成する。
規約：KST A.5。使われ方：二つの因子の共通始域。 -/
def linearizedDiagonal (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (simplicialDiagonal X) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso X X).inv

/-- 概要：直積群からの μ を自由整数加群のテンソルからの実射へ移す。
方針：積の自由化との同型の後に実 nerve の μ の射を適用する。
規約：KST A.5 の原典の一般文言との差、μ を明示し H を非可換のまま保つ。
使われ方：テンソルの実区間比較の最後の後合成。 -/
def linearizedGroupProduct {P Q H : Type u} [Group P] [Group Q] [Group H] (μ : P × Q →* H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj P)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj Q))) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj H)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso (nerve (SingleObj P)) (nerve (SingleObj Q))).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (groupProductNerve μ)

/-- 概要：対角・二因子・μ の実テンソル合成は合成群準同型の自由化と一致。
方針：テンソル同型の自然性で幾何的な合成へ戻し、nerve の積の実公式を使う。
規約：KST A.5 の μ 版、可換な群への置換を使わない。
使われ方：A.5 の左辺と補正した三つの項の同定。 -/
lemma linearizedGroupProduct_comp {T P Q H : Type u}
    [Group T] [Group P] [Group Q] [Group H] (μ : P × Q →* H) (α : T →* P) (β : T →* Q) :
    linearizedDiagonal (nerve (SingleObj T)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (groupLinearizedMap α) (groupLinearizedMap β) ≫ linearizedGroupProduct μ =
    groupLinearizedMap (μ.comp (α.prod β)) := by
  have ht := congrArg (fun k ↦ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (groupProductNerve μ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso_naturality (nerveMap (SingleObj.mapHom _ _ α))
      (nerveMap (SingleObj.mapHom _ _ β)))
  simp only [Category.assoc] at ht
  dsimp only [linearizedDiagonal, linearizedGroupProduct, groupLinearizedMap]
  simp only [Category.assoc]
  rw [ht, Iso.inv_hom_id_assoc]
  change ((SimplicialObject.whiskering _ _).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization).map
      (simplicialDiagonal (nerve (SingleObj T))) ≫
    ((SimplicialObject.whiskering _ _).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization).map
      (nerveMap (SingleObj.mapHom _ _ α) ⊗ₘ nerveMap (SingleObj.mapHom _ _ β)) ≫
    ((SimplicialObject.whiskering _ _).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization).map (groupProductNerve μ) = _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, groupProductNerve_comp]

/-- 概要：μ に両因子の単位を入れる準同型は自明な準同型。
方針：直積群の単位を μ が単位へ送ることを使う。
規約：KST A.5 の augmentation 補正。使われ方：第三項を C(e_H) に同定する。 -/
lemma groupProduct_trivial {T P Q H : Type u} [Group T] [Group P] [Group Q] [Group H]
    (μ : P × Q →* H) : μ.comp ((1 : T →* P).prod (1 : T →* Q)) = 1 := by
  ext t
  exact μ.map_one

end SerrePositivity.KST.ProExcision
