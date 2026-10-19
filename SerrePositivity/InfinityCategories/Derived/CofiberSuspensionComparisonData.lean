module
public import SerrePositivity.InfinityCategories.Derived.CofiberToSuspensionMap
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareMiddleData

/-! # Cofiber から suspension への二段比較の四角形データ

概要：終点への cone 写像の後合成と右下を零にする変更を、標準 suspension と同定する。
方針：cone の包含と次数 −1 のホモトピーの保存を四角形の全データに適用する。
規約：通常の h の可換性ではなく全データの等式。使われ方：D7 の接続射の実際の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex HomComplex
open scoped ZeroObject
variable {S : Type u} [CommRing S] {A B : Complex S}

/-- 後合成後の右辺は零対象を通る。 -/
lemma cofiberToSuspensionRightFactor (f : A ⟶ B) :
    (0 : B ⟶ 0) ≫ pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0) =
      ((cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose (cofiberToSuspensionMap f)).right := by
  change (0 : B ⟶ 0) ≫ _ = pushoutInclusionB f (0 : A ⟶ 0) ≫ cofiberToSuspensionMap f
  simp only [zero_comp]
  exact (cofiberToSuspensionMap_inclusionB f).symm

/-- 終点の後合成後に右下の対象を零に変更した四角形。 -/
def cofiberToSuspensionIntermediateData (f : A ⟶ B) :
    ComplexSquareData A 0 0 (pushoutCofiber (0 : A ⟶ 0) (0 : A ⟶ 0)) :=
  ((cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose
    (cofiberToSuspensionMap f)).changeBottomMiddle
    (0 : B ⟶ 0) (pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0)) (cofiberToSuspensionRightFactor f)

/-- 二段比較の終端は標準 suspension の四角形の全データ。 -/
lemma cofiberToSuspensionIntermediateData_eq (f : A ⟶ B) :
    cofiberToSuspensionIntermediateData f =
      cofiberComplexSquareData (0 : A ⟶ 0) (0 : A ⟶ 0) := by
  apply ComplexSquareData.ext
  · simp only [cofiberToSuspensionIntermediateData, ComplexSquareData.changeBottomMiddle,
      ComplexSquareData.postcompose, cofiberComplexSquareData, comp_zero]
  · rfl
  · rfl
  · exact Subsingleton.elim _ _
  · simp only [cofiberToSuspensionIntermediateData, ComplexSquareData.changeBottomMiddle,
      ComplexSquareData.postcompose, cofiberComplexSquareData, pushoutDiagonal, zero_comp]
  · exact cofiberToSuspensionMap_inl f
  · simp only [cofiberToSuspensionIntermediateData, ComplexSquareData.changeBottomMiddle,
      ComplexSquareData.postcompose, cofiberComplexSquareData, Cochain.zero_comp]

end SerrePositivity.InfinityCategories
