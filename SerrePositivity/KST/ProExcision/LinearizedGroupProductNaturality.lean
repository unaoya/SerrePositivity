module
public import SerrePositivity.KST.ProExcision.LinearizedGroupProduct

/-!
# 対角と非可換標的 μ の自然性

概要：A.5 の前合成の対角と後合成の μ はデータの射と可換。
方針：自由加群の基底と群の nerve の射ラベルで計算する。
規約：KST Construction A.5 の μ 版、H の可換性を仮定しない。
使われ方：最後に μ を適用する外部 G 同変なホモトピーの構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

/-- 概要：線形対角は単体の基底を同じ基底の純テンソルへ送る。
方針：積の自由化との同型の逆を評価する。
規約：KST A.5。使われ方：対角の自然性の基底計算。 -/
lemma linearizedDiagonal_generator (X : SSet.{u}) (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    (linearizedDiagonal X).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) =
      TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso (X.obj n) (X.obj n)).inv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((simplicialDiagonal X).app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  exact integerTensorIso_inv_generator (X.obj n) (X.obj n) x x

/-- 概要：線形対角は単体的写像に自然。
方針：基底を同じ単体の対へ送ることを使う。
規約：KST A.5。使われ方：共通始域の外部作用との可換性。 -/
lemma linearizedDiagonal_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f ≫ linearizedDiagonal Y =
      linearizedDiagonal X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f) := by
  apply NatTrans.ext
  funext n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change (linearizedDiagonal Y).app n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (f.app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, linearizedDiagonal_generator]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f).app n) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f).app n)
    ((linearizedDiagonal X).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
  rw [linearizedDiagonal_generator]
  change _ = TensorProduct.tmul ℤ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (f.app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (f.app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]

/-- 概要：μ の線形射は純テンソルの基底に μ の nerve を適用する。
方針：積とテンソルの標準同型を評価する。
規約：KST A.5 の μ 版。使われ方：非可換標的への最後の射の自然性。 -/
lemma linearizedGroupProduct_generator {P Q H : Type u} [Group P] [Group Q] [Group H]
    (μ : P × Q →* H) (n : SimplexCategoryᵒᵖ)
    (p : (nerve (SingleObj P)).obj n) (q : (nerve (SingleObj Q)).obj n) :
    (linearizedGroupProduct μ).app n (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator ((groupProductNerve μ).app n (p, q)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((groupProductNerve μ).app n)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso _ _).hom (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator q))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]

/-- 概要：μ の線形射は μ と可換な三つの群準同型に自然。
方針：純テンソルの基底に帰着し、nerve の各射ラベルで可換性を使う。
規約：KST A.5、非可換な H のまま μ を最後に適用する。
使われ方：外部 G の自己準同型作用との可換性。 -/
lemma linearizedGroupProduct_naturality {P Q H P' Q' H' : Type u}
    [Group P] [Group Q] [Group H] [Group P'] [Group Q'] [Group H']
    (μ : P × Q →* H) (μ' : P' × Q' →* H')
    (a : P →* P') (b : Q →* Q') (c : H →* H')
    (hμ : ∀ p q, μ' (a p, b q) = c (μ (p, q))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (groupLinearizedMap a) (groupLinearizedMap b) ≫ linearizedGroupProduct μ' =
      linearizedGroupProduct μ ≫ groupLinearizedMap c := by
  apply NatTrans.ext
  funext n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_hom_ext
  intro p q
  change (linearizedGroupProduct μ').app n
    (TensorProduct.tmul ℤ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom _ _ a)).app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom _ _ b)).app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator q))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator,
    linearizedGroupProduct_generator]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom _ _ c)).app n)
    ((linearizedGroupProduct μ).app n (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator q)))
  rw [linearizedGroupProduct_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator
  apply (SerrePositivity.KST.Comparison.monoidWordEquiv (MonCat.of H') n.unop.len).injective
  funext i
  exact hμ _ _

end SerrePositivity.KST.ProExcision
