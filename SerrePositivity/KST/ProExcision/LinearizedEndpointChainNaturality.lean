module
public import SerrePositivity.KST.ProExcision.LinearizedCylinderHomotopyNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedStrictification
public import SerrePositivity.KST.ProExcision.ChainHomotopySquare

/-!
# 同変な線形区間からの鎖ホモトピーの自然性

概要：実線形区間写像の可換な正方形は誘導される鎖ホモトピーの自然性を与える。
方針：標準区間の各成分の自然性を有限交代和へ移し、Moore 包含・射影で挟む。
規約：KST Definition A.3、Construction A.5、外部作用の各射に適用する。
使われ方：因子内の同変な厳密化比較を正規化した全テンソルへ渡す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial
variable {X X' Y Y' : SSet.{u}}
variable (l : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y)
variable (l' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder X' ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y') (a : X ⟶ X') (b : Y ⟶ Y')
variable (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a)
  (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫ l' = l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b)
include hl

/-- 概要：区間の各組合せ的ホモトピー成分の可換な正方形。
方針：標準区間の自然性と線形区間写像の正方形を合成する。
規約：KST A.3・A.5。使われ方：交代面複体のホモトピーの自然性。 -/
lemma linearizedEndpointSimplicialHomotopy_naturality (n : ℕ) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a).app (op ⦋n⦌) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X').postcomp l').h i =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X).postcomp l).h i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b).app (op ⦋n + 1⦌) := by
  have hc := congrArg (fun k ↦ k.app (op ⦋n + 1⦌)) hl
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))).app (op ⦋n + 1⦌) ≫ l'.app (op ⦋n + 1⦌) =
    l.app (op ⦋n + 1⦌) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b).app (op ⦋n + 1⦌) at hc
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a).app (op ⦋n⦌) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X').h i ≫ l'.app (op ⦋n + 1⦌)) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X).h i ≫ l.app (op ⦋n + 1⦌)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b).app (op ⦋n + 1⦌)
  rw [← Category.assoc, linearizedCylinderHomotopy_naturality, Category.assoc, hc, ← Category.assoc]

/-- 概要：線形区間の実両端の鎖ホモトピーは入力の正方形に自然。
方針：組合せ的ホモトピーの交代和に各成分の自然性を適用する。
規約：KST A.3・A.5、非被約交代面複体。
使われ方：Moore 正規化へ移す前の同変性。 -/
lemma linearizedEndpointChainHomotopy_square :
    ChainHomotopySquare ((alternatingFaceMapComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a))
      ((alternatingFaceMapComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X).postcomp l).toChainHomotopy)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X').postcomp l').toChainHomotopy) := by
  intro n
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a).app (op ⦋n⦌) ≫
      SimplicialObject.Homotopy.ToChainHomotopy.hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X').postcomp l') n (n + 1) =
    SimplicialObject.Homotopy.ToChainHomotopy.hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X).postcomp l) n (n + 1) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b).app (op ⦋n + 1⦌)
  rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact linearizedEndpointSimplicialHomotopy_naturality l l' a b hl n i

/-- 概要：線形区間から得る正規化鎖ホモトピーも自然。
方針：交代面複体の自然性を自然な Moore 包含と射影で挟む。
規約：KST A.3・A.5、実鎖ホモトピーの成分の性質。
使われ方：同変な厳密化を正規化した全テンソルへ移す。 -/
lemma normalizedLinearizedEndpointHomotopy_square :
    ChainHomotopySquare ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a))
      ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedChainHomotopy ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X).postcomp l))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedChainHomotopy ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy X').postcomp l')) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedChainHomotopy]
  apply ChainHomotopySquare.trans
  · apply ChainHomotopySquare.ofEq
  · apply ChainHomotopySquare.trans
    · apply ChainHomotopySquare.compRight
      · apply ChainHomotopySquare.compLeft (linearizedEndpointChainHomotopy_square l l' a b hl)
        exact (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a)
      · exact PInftyToNormalizedMooreComplex_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b)
    · apply ChainHomotopySquare.ofEq

end SerrePositivity.KST.ProExcision
