module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanBoundaryData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanUnknownIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly

/-! # span の境界からの充填候補の既知部分

概要：実際の join 境界写像から二つの単体データを作り、既知の面と既知集合の方程式を確認する。
方針：部分境界写像に未知の射族を加え、回収した面から方程式を移送する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：D7 の未知六成分の方程式だけを残す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：境界写像の左セルの既知成分と指定された未知成分から単体データを作る。
方針：全頂点を覆う後続の面の集合で成分を組み立てる。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：左の四未知成分を入れる充填候補。 -/
def spanBoundaryLeftData {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeft F))) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeft F) unknown

/-- 概要：境界写像の右セルの既知成分と指定された未知成分から単体データを作る。
方針：全頂点を覆う後続の面の集合で成分を組み立てる。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：右の四未知成分を入れる充填候補。 -/
def spanBoundaryRightData {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRight F))) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRight F) unknown

/-- 概要：左のデータの全ての既知面は、元の join 境界写像の対応する制限。
方針：選んだ面への組み立てデータの制限と、部分境界の面の復元を使う。
規約：HTT §1.2.13。使われ方：左の充填候補の境界一致。 -/
lemma spanBoundaryLeftData_pullback_face {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeft F))) (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (spanBoundaryLeftData F unknown).pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n j hj ≫ F)).toSimplexData := by
  unfold spanBoundaryLeftData
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData_pullback_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeft_face]

/-- 概要：右のデータの全ての既知面は、元の join 境界写像の対応する制限。
方針：選んだ面への組み立てデータの制限と、部分境界の面の復元を使う。
規約：HTT §1.2.13。使われ方：右の充填候補の境界一致。 -/
lemma spanBoundaryRightData_pullback_face {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRight F))) (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (spanBoundaryRightData F unknown).pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n j hj ≫ F)).toSimplexData := by
  unfold spanBoundaryRightData
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData_pullback_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRight_face]

/-- 概要：左のデータは後続の全頂点を含まない全ての集合で方程式を満たす。
方針：後続の一点を欠くことを既知成分の被覆条件に戻し、面から方程式を回収する。
規約：HA Proposition 1.3.1.10。使われ方：左セルで未知四集合の方程式だけを残す。 -/
lemma spanBoundaryLeftData_equation {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeft F))) (I : Finset (Fin (n + 4)))
    (hI : ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I) : (spanBoundaryLeftData F unknown).Equation I :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData_equation _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n) _ unknown I
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_known_iff I).mpr hI)

/-- 概要：右のデータは後続の全頂点を含まない全ての集合で方程式を満たす。
方針：後続の一点を欠くことを既知成分の被覆条件に戻し、面から方程式を回収する。
規約：HA Proposition 1.3.1.10。使われ方：右セルで未知四集合の方程式だけを残す。 -/
lemma spanBoundaryRightData_equation {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRight F))) (I : Finset (Fin (n + 4)))
    (hI : ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I) : (spanBoundaryRightData F unknown).Equation I :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData_equation _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n) _ unknown I
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_known_iff I).mpr hI)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
