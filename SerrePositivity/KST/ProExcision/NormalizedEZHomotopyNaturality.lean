module
public import SerrePositivity.KST.ProExcision.NormalizedEZHomotopy
public import SerrePositivity.KST.ProExcision.MooreTensorHomotopyNaturality
public import SerrePositivity.KST.ProExcision.ChainHomotopySquare

/-!
# 正規化 EZ ホモトピーの自然性

概要：構成済みの正規化比較ホモトピーが二つの入力の射に成分ごとに自然。
方針：普遍 EZ 比較と Moore 収縮のテンソルの自然性を前後合成・連結へ移す。
規約：KST Construction A.5、外部群の同変性を結論に追加仮定しない。
使われ方：外部 G の作用を保った augmentation 補正式への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
variable {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)}

/-- 概要：実 EZ ホモトピーは両入力の射について自然な正方形を作る。
方針：普遍鎖の評価で得た成分の自然性を使う。
規約：KST A.5。使われ方：正規化前の比較の自然性。 -/
lemma ezHomotopy_square (f : C ⟶ C') (g : D ⟶ D') :
    ChainHomotopySquare ((alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g))
      ((alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g))
      (ezHomotopy C D) (ezHomotopy C' D') := by
  intro n
  simp only [ezHomotopy, Pi.single_eq_same]
  exact ezHomotopyApp_naturality C D f g n

/-- 概要：Moore 包含と AW の前半合成は自然。
方針：Moore 包含の自然性と実 AW の自然性を合成する。
規約：KST A.5。使われ方：Moore 収縮のテンソルへの前合成。 -/
lemma normalizedEZPrefix_naturality (f : C ⟶ C') (g : D ⟶ D') :
    (normalizedMooreComplex _).map (simplicialIntegerTensorMap f g) ≫
      (inclusionOfMooreComplexMap (simplicialIntegerTensor C' D') ≫ alexanderWhitney C' D') =
    (inclusionOfMooreComplexMap (simplicialIntegerTensor C D) ≫ alexanderWhitney C D) ≫
      chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
        ((alternatingFaceMapComplex _).map g) := by
  have hi := (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality (simplicialIntegerTensorMap f g)
  change (normalizedMooreComplex _).map (simplicialIntegerTensorMap f g) ≫
    inclusionOfMooreComplexMap (simplicialIntegerTensor C' D') =
    inclusionOfMooreComplexMap (simplicialIntegerTensor C D) ≫
      (alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g) at hi
  rw [← Category.assoc, hi, Category.assoc, alexanderWhitney_naturality, Category.assoc]

/-- 概要：shuffle と Moore 射影の後半合成は自然。
方針：実 shuffle の自然性と Moore 射影の自然性を合成する。
規約：KST A.5。使われ方：Moore 収縮のテンソルへの後合成。 -/
lemma normalizedEZSuffix_naturality (f : C ⟶ C') (g : D ⟶ D') :
    chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
        ((alternatingFaceMapComplex _).map g) ≫
      (shuffle C' D' ≫ PInftyToNormalizedMooreComplex (simplicialIntegerTensor C' D')) =
    (shuffle C D ≫ PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)) ≫
      (normalizedMooreComplex _).map (simplicialIntegerTensorMap f g) := by
  have hp := PInftyToNormalizedMooreComplex_naturality (simplicialIntegerTensorMap f g)
  change (alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g) ≫
    PInftyToNormalizedMooreComplex (simplicialIntegerTensor C' D') =
    PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D) ≫
      (normalizedMooreComplex _).map (simplicialIntegerTensorMap f g) at hp
  rw [← Category.assoc, shuffle_naturality, Category.assoc, hp, Category.assoc]

/-- 概要：対角だけを正規化した EZ 比較は自然。
方針：実 EZ の自然性を Moore 包含・射影で挟む。
規約：KST A.5。使われ方：正規化比較の前半。 -/
lemma normalizedEZRawHomotopy_square (f : C ⟶ C') (g : D ⟶ D') :
    ChainHomotopySquare ((normalizedMooreComplex _).map (simplicialIntegerTensorMap f g))
      ((normalizedMooreComplex _).map (simplicialIntegerTensorMap f g))
      (normalizedEZRawHomotopy C D) (normalizedEZRawHomotopy C' D') := by
  dsimp only [normalizedEZRawHomotopy]
  apply ChainHomotopySquare.trans
  · apply ChainHomotopySquare.ofEq
  · apply ChainHomotopySquare.trans
    · apply ChainHomotopySquare.compRight
      · apply ChainHomotopySquare.compLeft (ezHomotopy_square f g)
        exact (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality (simplicialIntegerTensorMap f g)
      · exact PInftyToNormalizedMooreComplex_naturality (simplicialIntegerTensorMap f g)
    · apply ChainHomotopySquare.ofEq

/-- 概要：両因子を正規化する比較ホモトピーも自然。
方針：Moore 収縮の全テンソルの自然性を反転し、自然な前半と後半で挟む。
規約：KST A.5。使われ方：正規化した標準比較の後半。 -/
lemma normalizedEZInsertMooreHomotopy_square (f : C ⟶ C') (g : D ⟶ D') :
    ChainHomotopySquare ((normalizedMooreComplex _).map (simplicialIntegerTensorMap f g))
      ((normalizedMooreComplex _).map (simplicialIntegerTensorMap f g))
      (normalizedEZInsertMooreHomotopy C D) (normalizedEZInsertMooreHomotopy C' D') := by
  dsimp only [normalizedEZInsertMooreHomotopy]
  apply ChainHomotopySquare.trans
  · apply ChainHomotopySquare.ofEq
  · apply ChainHomotopySquare.trans
    · apply ChainHomotopySquare.compRight
      · apply ChainHomotopySquare.compLeft
        · apply ChainHomotopySquare.symm
          exact chainIntegerTensorMooreRetraction_naturality f g
        · exact normalizedEZPrefix_naturality f g
      · exact normalizedEZSuffix_naturality f g
    · apply ChainHomotopySquare.ofEq

/-- 概要：正規化した恒等と AW→shuffle の間の実鎖ホモトピーは両入力に自然。
方針：構成済みの二段階の比較の自然性を連結する。
規約：KST Construction A.5、外部 G 同変性を仮定せずに導く。
使われ方：同変な低次補正式を単体的区間へ復元するための入力。 -/
lemma normalizedEZHomotopy_square (f : C ⟶ C') (g : D ⟶ D') :
    ChainHomotopySquare ((normalizedMooreComplex _).map (simplicialIntegerTensorMap f g))
      ((normalizedMooreComplex _).map (simplicialIntegerTensorMap f g))
      (normalizedEZHomotopy C D) (normalizedEZHomotopy C' D') :=
  (normalizedEZRawHomotopy_square f g).trans (normalizedEZInsertMooreHomotopy_square f g)

end SerrePositivity.KST.ProExcision
