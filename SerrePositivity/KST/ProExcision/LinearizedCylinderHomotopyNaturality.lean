module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MHomotopyHomology
public import SerrePositivity.KST.ProExcision.LinearizedEndpoints

/-!
# 線形化した標準区間ホモトピーの自然性

概要：標準区間の組合せ的ホモトピーの成分を自由基底で計算し、始域の射に自然と示す。
方針：退化した入力単体と区間の標準単体の純テンソルへ評価する。
規約：KST Definition A.3、Construction A.5。
使われ方：同変な区間写像から正規化鎖ホモトピーの自然性を得る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：標準区間ホモトピーの成分は退化した入力と標準区間単体の純テンソル。
方針：幾何的区間の恒等写像と自由化の積の同型の逆を基底上で評価する。
規約：KST A.3・A.5。使われ方：標準区間の入力の射に関する自然性。 -/
lemma linearizedCylinderHomotopy_generator (X : SSet.{u}) (n : ℕ) (i : Fin (n + 1))
    (x : X.obj (op ⦋n⦌)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X).h i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) =
      TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (X.σ i x))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.objMk₁ i.succ.castSucc)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso _ _).inv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.geometricCylinderHomotopy X).toSimplicialObjectHomotopy.h i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  have hx : ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.geometricCylinderHomotopy X).toSimplicialObjectHomotopy.h i) x =
      (X.σ i x, SSet.stdSimplex.objMk₁ i.succ.castSucc) := by rfl
  rw [hx, integerTensorIso_inv_generator]

/-- 概要：標準区間ホモトピーの成分は単体的集合の射に自然。
方針：基底上の純テンソルの公式と退化写像の自然性を使う。
規約：KST A.3・A.5、外部群の各作用射に適用する。
使われ方：区間から誘導される鎖ホモトピーの同変性。 -/
lemma linearizedCylinderHomotopy_naturality {X Y : SSet.{u}} (a : X ⟶ Y)
    (n : ℕ) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a).app (op ⦋n⦌) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy Y).h i =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X).h i ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))).app
          (op ⦋n + 1⦌) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy Y).h i
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (a.app (op ⦋n⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, linearizedCylinderHomotopy_generator]
  change TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (Y.σ i (a.app (op ⦋n⦌) x)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.objMk₁ i.succ.castSucc)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a).app (op ⦋n + 1⦌)) (𝟙 _)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X).h i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
  rw [linearizedCylinderHomotopy_generator]
  change TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (Y.σ i (a.app (op ⦋n⦌) x)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.objMk₁ i.succ.castSucc)) =
    TensorProduct.tmul ℤ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (a.app (op ⦋n + 1⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (X.σ i x)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.objMk₁ i.succ.castSucc))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  have hs := congrArg (fun k ↦ k x) (a.naturality (SimplexCategory.σ i).op)
  exact congrArg (fun z ↦ TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.objMk₁ i.succ.castSucc))) hs.symm

end SerrePositivity.KST.ProExcision
