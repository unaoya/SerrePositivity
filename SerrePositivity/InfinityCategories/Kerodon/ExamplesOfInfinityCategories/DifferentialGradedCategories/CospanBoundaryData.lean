module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanJoinCells
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanPrefixIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceLifts

/-! # cospan の slice 境界から二セルの既知部分への写像

概要：join の境界写像を左右の標準セルの先頭の面の和へ制限する。
方針：各先頭面を境界へ持ち上げ、join の境界包含の単射性から整合性を得て貼り合わせる。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：N7c の実際の境界からの成分回収。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：先頭因子の境界を全体に含める join の写像。
方針：境界包含と cospan の恒等写像の join を取る。
規約：HTT §1.2.13。使われ方：境界の面の持ち上げの比較先。 -/
def cospanBoundaryInclusion (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{u}) (SSet.horn 2 2) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[n + 1] (SSet.horn 2 2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.boundary (n + 1)).ι (𝟙 (SSet.horn 2 2 : SSet.{u}))

/-- 概要：cospan の join の境界包含は単射。
方針：joinMap が二つの単射から単射を作ることを使う。
規約：HTT §1.2.13。使われ方：持ち上げた二面の共通部分の比較。 -/
instance cospanBoundaryInclusion_mono (n : ℕ) : Mono (cospanBoundaryInclusion.{u} n) := by
  unfold cospanBoundaryInclusion
  infer_instance

/-- 概要：左セルの先頭面を join の境界へ持ち上げる。
方針：小さい左セルと先頭因子の境界の面包含を合成する。
規約：HTT §1.2.13。使われ方：左セルの既知の面の評価。 -/
def cospanBoundaryLeftLift (n : ℕ) (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet) (SSet.horn 2 2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.boundary.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaceIndex j hj))
    (𝟙 (SSet.horn 2 2 : SSet.{u}))

/-- 概要：右セルの先頭面を join の境界へ持ち上げる。
方針：小さい右セルと先頭因子の境界の面包含を合成する。
規約：HTT §1.2.13。使われ方：右セルの既知の面の評価。 -/
def cospanBoundaryRightLift (n : ℕ) (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet) (SSet.horn 2 2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.boundary.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaceIndex j hj))
    (𝟙 (SSet.horn 2 2 : SSet.{u}))

/-- 概要：左の持ち上げを境界包含で送ると大きい左セルの対応する面になる。
方針：joinMap の合成則と左セルの面の可換性を使う。
規約：HTT §1.2.13。使われ方：左の境界面の整合性の検証。 -/
lemma cospanBoundaryLeftLift_inclusion (n : ℕ) (j : Fin (n + 4))
    (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    cospanBoundaryLeftLift.{u} n j hj ≫ cospanBoundaryInclusion n =
      SSet.stdSimplex.δ j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft (n + 1) := by
  rw [cospanBoundaryLeftLift, cospanBoundaryInclusion, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    SSet.boundary.ι_ι, Category.id_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft_face, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaceIndex_castAdd]

/-- 概要：右の持ち上げを境界包含で送ると大きい右セルの対応する面になる。
方針：joinMap の合成則と右セルの面の可換性を使う。
規約：HTT §1.2.13。使われ方：右の境界面の整合性の検証。 -/
lemma cospanBoundaryRightLift_inclusion (n : ℕ) (j : Fin (n + 4))
    (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    cospanBoundaryRightLift.{u} n j hj ≫ cospanBoundaryInclusion n =
      SSet.stdSimplex.δ j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight (n + 1) := by
  rw [cospanBoundaryRightLift, cospanBoundaryInclusion, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    SSet.boundary.ι_ι, Category.id_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight_face, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaceIndex_castAdd]

/-- 概要：join の境界写像から左セルの部分境界写像を作る。
方針：単射への持ち上げによる整合性を用いて全ての既知の面を貼る。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：左の既知成分の recoverHom への入力。 -/
def cospanBoundaryLeft {n : ℕ} {X : SSet.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet) (SSet.horn 2 2) ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) : SSet) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)
    (fun j hj => SSet.yonedaEquiv (cospanBoundaryLeftLift n j hj ≫ F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compatible_of_lifts _ (cospanBoundaryInclusion n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft (n + 1))
      (cospanBoundaryLeftLift n) (cospanBoundaryLeftLift_inclusion n) F)

/-- 概要：join の境界写像から右セルの部分境界写像を作る。
方針：単射への持ち上げによる整合性を用いて全ての既知の面を貼る。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：右の既知成分の recoverHom への入力。 -/
def cospanBoundaryRight {n : ℕ} {X : SSet.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet) (SSet.horn 2 2) ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) : SSet) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)
    (fun j hj => SSet.yonedaEquiv (cospanBoundaryRightLift n j hj ≫ F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compatible_of_lifts _ (cospanBoundaryInclusion n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight (n + 1))
      (cospanBoundaryRightLift n) (cospanBoundaryRightLift_inclusion n) F)

/-- 概要：左の部分境界写像の各面は元の join 境界写像の対応する制限。
方針：整合的な族の貼り合わせが元の面を復元する公式を使う。
規約：HTT §1.2.13。使われ方：左の回収成分と元の slice 境界の一致。 -/
lemma cospanBoundaryLeft_face {n : ℕ} {X : SSet.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet) (SSet.horn 2 2) ⟶ X)
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    (cospanBoundaryLeft F).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face _ j hj) =
      SSet.yonedaEquiv (cospanBoundaryLeftLift n j hj ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.desc_face _ _ _ j hj

/-- 概要：右の部分境界写像の各面は元の join 境界写像の対応する制限。
方針：整合的な族の貼り合わせが元の面を復元する公式を使う。
規約：HTT §1.2.13。使われ方：右の回収成分と元の slice 境界の一致。 -/
lemma cospanBoundaryRight_face {n : ℕ} {X : SSet.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet) (SSet.horn 2 2) ⟶ X)
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    (cospanBoundaryRight F).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face _ j hj) =
      SSet.yonedaEquiv (cospanBoundaryRightLift n j hj ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.desc_face _ _ _ j hj

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
