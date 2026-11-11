module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanJoinFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanUnknownIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceLifts

/-! # span の coslice 境界から二セルの既知部分へ

概要：join の境界写像を左右の標準セルの可変頂点の面の和へ制限する。
方針：各面を join の境界へ持ち上げ、境界包含の単射性で整合性を得て貼り合わせる。
規約：値域は任意の単体集合。使われ方：D7 の実際の coslice 境界からの成分回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：span の join の可変因子の境界を全体へ含める。
方針：固定 span の恒等写像と境界包含の join を取る。
規約：境界は右因子。使われ方：二セルの既知面の共通の値域。 -/
def spanBoundaryInclusion (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{u}) (SSet.boundary (n + 1)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0) Δ[n + 1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u})) (SSet.boundary (n + 1)).ι

/-- 概要：span の join の境界包含は単射。
方針：二つの単射の join の単射性を使う。
規約：全ての次元。使われ方：面の持ち上げの整合性。 -/
instance spanBoundaryInclusion_mono (n : ℕ) : Mono (spanBoundaryInclusion.{u} n) := by
  unfold spanBoundaryInclusion
  infer_instance

/-- 概要：左セルの可変頂点を除いた面を join の境界へ持ち上げる。
方針：小さい左セルと右因子の境界面を合成する。
規約：固定頂点 A,B は保つ。使われ方：左の既知面の回収。 -/
def spanBoundaryLeftLift (n : ℕ) (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0) (SSet.boundary (n + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u}))
    (SSet.boundary.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaceIndex j hj))

/-- 概要：右セルの可変頂点を除いた面を join の境界へ持ち上げる。
方針：小さい右セルと右因子の境界面を合成する。
規約：固定頂点 A,C は保つ。使われ方：右の既知面の回収。 -/
def spanBoundaryRightLift (n : ℕ) (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0) (SSet.boundary (n + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u}))
    (SSet.boundary.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaceIndex j hj))

/-- 概要：左の持ち上げを含めると大きい左セルの対応する面になる。
方針：join の合成と可変面の式を使う。
規約：元の面番号を厳密に回収する。使われ方：左の面の整合性。 -/
lemma spanBoundaryLeftLift_inclusion (n : ℕ) (j : Fin (n + 4))
    (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    spanBoundaryLeftLift.{u} n j hj ≫ spanBoundaryInclusion n =
      SSet.stdSimplex.δ j ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft (n + 1) := by
  rw [spanBoundaryLeftLift, spanBoundaryInclusion, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    SSet.boundary.ι_ι, Category.id_comp, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaceIndex_succ_succ]

/-- 概要：右の持ち上げを含めると大きい右セルの対応する面になる。
方針：join の合成と可変面の式を使う。
規約：元の面番号を厳密に回収する。使われ方：右の面の整合性。 -/
lemma spanBoundaryRightLift_inclusion (n : ℕ) (j : Fin (n + 4))
    (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    spanBoundaryRightLift.{u} n j hj ≫ spanBoundaryInclusion n =
      SSet.stdSimplex.δ j ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight (n + 1) := by
  rw [spanBoundaryRightLift, spanBoundaryInclusion, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    SSet.boundary.ι_ι, Category.id_comp, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaceIndex_succ_succ]

/-- 概要：join の境界写像から左セルの既知部分への写像を作る。
方針：持ち上げた面の整合性を単射性から得て全ての既知面を貼る。
規約：値域は任意の単体集合。使われ方：左の dg nerve 成分の回収の入力。 -/
def spanBoundaryLeft {n : ℕ} {X : SSet.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{u}) (SSet.boundary (n + 1)) ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) : SSet) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.desc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)
    (fun j hj ↦ SSet.yonedaEquiv (spanBoundaryLeftLift n j hj ≫ F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compatible_of_lifts _ (spanBoundaryInclusion n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft (n + 1))
      (spanBoundaryLeftLift n) (spanBoundaryLeftLift_inclusion n) F)

/-- 概要：join の境界写像から右セルの既知部分への写像を作る。
方針：持ち上げた面の整合性を単射性から得て全ての既知面を貼る。
規約：値域は任意の単体集合。使われ方：右の dg nerve 成分の回収の入力。 -/
def spanBoundaryRight {n : ℕ} {X : SSet.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{u}) (SSet.boundary (n + 1)) ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) : SSet) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.desc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)
    (fun j hj ↦ SSet.yonedaEquiv (spanBoundaryRightLift n j hj ≫ F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compatible_of_lifts _ (spanBoundaryInclusion n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight (n + 1))
      (spanBoundaryRightLift n) (spanBoundaryRightLift_inclusion n) F)

/-- 概要：左の部分境界写像の各面は元の join 境界の対応する制限。
方針：既知面を貼った写像の制限の公式を使う。
規約：全ての選んだ面。使われ方：回収した左成分の境界との一致。 -/
lemma spanBoundaryLeft_face {n : ℕ} {X : SSet.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{u}) (SSet.boundary (n + 1)) ⟶ X)
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (spanBoundaryLeft F).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face _ j hj) =
      SSet.yonedaEquiv (spanBoundaryLeftLift n j hj ≫ F) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.desc_face _ _ _ j hj

/-- 概要：右の部分境界写像の各面は元の join 境界の対応する制限。
方針：既知面を貼った写像の制限の公式を使う。
規約：全ての選んだ面。使われ方：回収した右成分の境界との一致。 -/
lemma spanBoundaryRight_face {n : ℕ} {X : SSet.{u}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{u}) (SSet.boundary (n + 1)) ⟶ X)
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (spanBoundaryRight F).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face _ j hj) =
      SSet.yonedaEquiv (spanBoundaryRightLift n j hj ≫ F) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.desc_face _ _ _ j hj

end SerrePositivity.InfinityCategories.Project.DerivedCategories
