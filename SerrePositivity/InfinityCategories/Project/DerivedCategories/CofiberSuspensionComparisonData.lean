module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberToSuspensionMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareMiddleData

/-! # Cofiber から suspension への二段比較の四角形データ

概要：終点への cone 写像の後合成と右下を零にする変更を、標準 suspension と同定する。
方針：cone の包含と次数 −1 のホモトピーの保存を四角形の全データに適用する。
規約：通常の h の可換性ではなく全データの等式。使われ方：D7 の接続射の実際の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
open scoped ZeroObject
variable {S : Type u} [CommRing S] {A B : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 後合成後の右辺は零対象を通る。 -/
lemma cofiberToSuspensionRightFactor (f : A ⟶ B) :
    (0 : B ⟶ 0) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).right := by
  change (0 : B ⟶ 0) ≫ _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f (0 : A ⟶ 0) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f
  simp only [zero_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap_inclusionB f).symm

/-- 終点の後合成後に右下の対象を零に変更した四角形。 -/
def cofiberToSuspensionIntermediateData (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A 0 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber (0 : A ⟶ 0) (0 : A ⟶ 0)) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).changeBottomMiddle
    (0 : B ⟶ 0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0)) (cofiberToSuspensionRightFactor f)

/-- 二段比較の終端は標準 suspension の四角形の全データ。 -/
lemma cofiberToSuspensionIntermediateData_eq (f : A ⟶ B) :
    cofiberToSuspensionIntermediateData f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData (0 : A ⟶ 0) (0 : A ⟶ 0) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.ext
  · simp only [cofiberToSuspensionIntermediateData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.changeBottomMiddle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.postcompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData, comp_zero]
  · rfl
  · rfl
  · exact Subsingleton.elim _ _
  · simp only [cofiberToSuspensionIntermediateData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.changeBottomMiddle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.postcompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal, zero_comp]
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap_inl f
  · simp only [cofiberToSuspensionIntermediateData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.changeBottomMiddle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.postcompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData, Cochain.zero_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
