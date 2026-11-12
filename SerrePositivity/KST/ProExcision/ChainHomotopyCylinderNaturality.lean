module
public import SerrePositivity.KST.ProExcision.ChainHomotopyCylinder
public import SerrePositivity.KST.ProExcision.ChainIntervalEvaluationChainNaturality

/-!
# 鎖ホモトピーから復元した実区間射の自然性

概要：端点と鎖ホモトピーの自然な正方形は復元した単体的区間射の自然性を与える。
方針：AW・Moore 射影・区間評価の自然性を合成し、Dold–Kan の忠実性で戻す。
規約：KST Definition A.3、Construction A.5、外部群同変性を結論の仮定にはしない。
使われ方：構成済みの正規化 EZ 比較を同変な C(H) の実区間へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial
variable {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)}
variable {f g : C ⟶ D} {f' g' : C' ⟶ D'}
variable (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g))
variable (H' : Homotopy ((normalizedMooreComplex _).map f') ((normalizedMooreComplex _).map g'))
variable (a : C ⟶ C') (b : D ⟶ D') (hf : a ≫ f' = f ≫ b) (hg : a ≫ g' = g ≫ b)
variable (hH : ChainHomotopySquare ((normalizedMooreComplex _).map a)
  ((normalizedMooreComplex _).map b) H H')
include hf hg hH

/-- 概要：正規化前の単体的区間からの実鎖写像は自然。
方針：AW、二つの比較、鎖区間評価の自然性を合成する。
規約：KST A.3・A.5。使われ方：Moore 包含による正規化前の段階。 -/
lemma chainHomotopyCylinderCore_naturality :
    (alternatingFaceMapComplex _).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))) ≫
      chainHomotopyCylinderCore H' = chainHomotopyCylinderCore H ≫ (normalizedMooreComplex _).map b := by
  have haw := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_naturality a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))
  simp only [CategoryTheory.Functor.map_id] at haw
  have hp := PInftyToNormalizedMooreComplex_naturality a
  change (alternatingFaceMapComplex _).map a ≫ PInftyToNormalizedMooreComplex C' =
    PInftyToNormalizedMooreComplex C ≫ (normalizedMooreComplex _).map a at hp
  have ht :
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((alternatingFaceMapComplex _).map a)
          (𝟙 ((alternatingFaceMapComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap (PInftyToNormalizedMooreComplex C') integerIntervalComparison =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap (PInftyToNormalizedMooreComplex C) integerIntervalComparison ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((normalizedMooreComplex _).map a) (𝟙 integerChainInterval) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_comp, hp]
    simp only [Category.id_comp, Category.comp_id]
  have hfn := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hf
  have hgn := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hg
  simp only [CategoryTheory.Functor.map_comp] at hfn hgn
  have he := chainHomotopyInterval_naturality H H' ((normalizedMooreComplex _).map a)
    ((normalizedMooreComplex _).map b) hfn hgn hH
  dsimp only [chainHomotopyCylinderCore]
  rw [← Category.assoc, haw]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((alternatingFaceMapComplex _).map a) _), ht]
  simp only [Category.assoc]
  rw [he]

/-- 概要：正規化した単体的区間からの実鎖写像も自然。
方針：Moore 包含の自然性と正規化前の自然性を合成する。
規約：KST A.3・A.5。使われ方：復元の自然性を忠実性で検出する。 -/
lemma chainHomotopyCylinderMap_naturality :
    (normalizedMooreComplex _).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))) ≫
      chainHomotopyCylinderMap H' = chainHomotopyCylinderMap H ≫ (normalizedMooreComplex _).map b := by
  have hi := (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))))
  change (normalizedMooreComplex _).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))) ≫
    inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor C' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) =
    inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫
      (alternatingFaceMapComplex _).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))) at hi
  rw [chainHomotopyCylinderMap, chainHomotopyCylinderMap, ← Category.assoc, hi, Category.assoc,
    chainHomotopyCylinderCore_naturality H H' a b hf hg hH, Category.assoc]

/-- 概要：Dold–Kan で復元した実単体的区間射は両入力の射に自然。
方針：正規化後の鎖写像の自然性を忠実性で実射へ戻す。
規約：KST Definition A.3、Construction A.5、外部群の作用を保つ復元。
使われ方：構成済みの正規化ホモトピーの G 同変な実区間への移送。 -/
lemma chainHomotopyCylinderReconstruct_naturality :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫
      chainHomotopyCylinderReconstruct H' = chainHomotopyCylinderReconstruct H ≫ b := by
  apply normalizedMap_eq_of_map_eq
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    chainHomotopyCylinderReconstruct_map, chainHomotopyCylinderReconstruct_map]
  exact chainHomotopyCylinderMap_naturality H H' a b hf hg hH

end SerrePositivity.KST.ProExcision
