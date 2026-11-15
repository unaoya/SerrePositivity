module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleAWProjected
public import SerrePositivity.KST.ProExcision.NormalizedEZHomotopyNaturality

/-!
概要：指定 shuffle→AW ホモトピーが両入力の射に自然であることを証明する。
方針：Moore 収縮の自然性を、指定包含・shuffle・AW・射影で前後合成する。
規約：KST の ChainHomotopySquare を完全修飾で参照し、既存ホモトピーを保持する。
使われ方：HA 1.2.4、G10 の重みの図式方向を保つ比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)}

/-- 逆順ホモトピーの包含・shuffle の前半は自然。 -/
theorem shuffleAWPrefix_naturality (f : C ⟶ C') (g : D ⟶ D') :
    chainIntegerTensorMap ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g) ≫
      (chainIntegerTensorMap (inclusionOfMooreComplexMap C') (inclusionOfMooreComplexMap D') ≫
        shuffle C' D') =
    (chainIntegerTensorMap (inclusionOfMooreComplexMap C) (inclusionOfMooreComplexMap D) ≫
      shuffle C D) ≫ (alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g) := by
  have hf := (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality f
  have hg := (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality g
  rw [← Category.assoc, ← chainIntegerTensorMap_comp]
  erw [hf, hg]
  rw [chainIntegerTensorMap_comp, Category.assoc, shuffle_naturality, Category.assoc]
  rfl

/-- 逆順ホモトピーの AW・射影の後半は自然。 -/
theorem shuffleAWSuffix_naturality (f : C ⟶ C') (g : D ⟶ D') :
    (alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g) ≫
      (alexanderWhitney C' D' ≫ chainIntegerTensorMap
        (PInftyToNormalizedMooreComplex C') (PInftyToNormalizedMooreComplex D')) =
    (alexanderWhitney C D ≫ chainIntegerTensorMap
      (PInftyToNormalizedMooreComplex C) (PInftyToNormalizedMooreComplex D)) ≫
      chainIntegerTensorMap ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g) := by
  rw [← Category.assoc, alexanderWhitney_naturality, Category.assoc,
    ← chainIntegerTensorMap_comp]
  erw [PInftyToNormalizedMooreComplex_naturality f, PInftyToNormalizedMooreComplex_naturality g]
  rw [chainIntegerTensorMap_comp, Category.assoc]
  rfl

/-- 指定逆順ホモトピーの全次数の自然な四角形。 -/
theorem normalizedShuffleAWHomotopy_square (f : C ⟶ C') (g : D ⟶ D') :
    SerrePositivity.KST.ProExcision.ChainHomotopySquare
      (chainIntegerTensorMap ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g))
      (chainIntegerTensorMap ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g))
      (normalizedShuffleAWHomotopy C D) (normalizedShuffleAWHomotopy C' D') := by
  let a := (alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g)
  let b := chainIntegerTensorMap ((normalizedMooreComplex _).map f)
    ((normalizedMooreComplex _).map g)
  have hm : SerrePositivity.KST.ProExcision.ChainHomotopySquare a a
      (homotopyPInftyToId (simplicialIntegerTensor C D))
      (homotopyPInftyToId (simplicialIntegerTensor C' D')) := by
    intro n
    exact SerrePositivity.KST.ProExcision.moorePInftyHomotopy_naturality
      (simplicialIntegerTensorMap f g) n
  have hl := hm.compLeft
    (chainIntegerTensorMap (inclusionOfMooreComplexMap C) (inclusionOfMooreComplexMap D) ≫ shuffle C D)
    (chainIntegerTensorMap (inclusionOfMooreComplexMap C') (inclusionOfMooreComplexMap D') ≫ shuffle C' D')
    b (shuffleAWPrefix_naturality f g)
  have hr := hl.compRight
    (alexanderWhitney C D ≫ chainIntegerTensorMap
      (PInftyToNormalizedMooreComplex C) (PInftyToNormalizedMooreComplex D))
    (alexanderWhitney C' D' ≫ chainIntegerTensorMap
      (PInftyToNormalizedMooreComplex C') (PInftyToNormalizedMooreComplex D'))
    b (shuffleAWSuffix_naturality f g)
  dsimp only [normalizedShuffleAWHomotopy]
  apply SerrePositivity.KST.ProExcision.ChainHomotopySquare.trans
  · apply SerrePositivity.KST.ProExcision.ChainHomotopySquare.ofEq
  · apply SerrePositivity.KST.ProExcision.ChainHomotopySquare.trans hr
    apply SerrePositivity.KST.ProExcision.ChainHomotopySquare.ofEq

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
