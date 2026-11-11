module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeTriangleFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRestriction

/-!
概要：任意の right anodyne な単射に沿い、上の余錐族と底の族を同時に延長する。
方針：像への同型で相対 coslice の自明 Kan 性を移し、底の同じ切断に沿って持ち上げる。
規約：境界族・底の延長・可変終点を厳密に保持する。パラメータの Kan 性は不要。
使われ方：実際の左三角形の終端辺から、その全 Hom の族を三角形全体へ延長する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- right anodyne な任意の単射による相対 coslice 制限は、自明 Kan fibration。 -/
lemma relativeCosliceRestriction_of_rightAnodyne {K L E B : SSet.{u}}
    (t : K ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (j : L ⟶ K) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q j) := by
  let R : K.Subcomplex := Subfunctor.range j
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono j
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions R.ι :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.arrow_mk_iso_iff
      (Arrow.isoMk (asIso (Subfunctor.toRange j)) (Iso.refl K) (by rfl))).1 hj
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_trivialKanFibration_of_rightAnodyne t q R hR
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceRestriction_trivialKanFibration_subcomplexIso t q R
    (asIso (Subfunctor.toRange j))

/-- 指定した right anodyne な境界から、底の余錐を延長する切断。 -/
def rightCosliceSection {K L B : SSet.{u}} [Quasicategory B]
    (t : K ⟶ B) (j : L ⟶ K) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ t) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration t j hj
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j)).choose

/-- 底の切断は、入力した境界上の全余錐族を厳密に回収する。 -/
lemma rightCosliceSection_boundary {K L B : SSet.{u}} [Quasicategory B]
    (t : K ⟶ B) (j : L ⟶ K) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j) :
    rightCosliceSection t j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j = 𝟙 _ := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration t j hj
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j)).choose_spec

/-- 上の境界と底の延長を同時に指定した、全パラメータ族の相対延長。 -/
lemma exists_relativeRightCosliceFamily {K L E B T : SSet.{u}}
    (t : K ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (j : L ⟶ K) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ t)) (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (t ≫ q))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (j ≫ t) q = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (t ≫ q) j) :
    ∃ U : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t,
      U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j = a ∧ U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q = b := by
  have := relativeCosliceRestriction_of_rightAnodyne t q j hj
  let v := pullback.lift a b h
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q j)
  refine ⟨v ≫ s, ?_, ?_⟩
  · have hh := congrArg (fun k ↦ v ≫ k ≫ pullback.fst _ _) hs
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_fst, Category.id_comp, v] using hh
  · have hh := congrArg (fun k ↦ v ≫ k ≫ pullback.snd _ _) hs
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_snd, Category.id_comp, v] using hh

/-- 同じ底の切断を使い、上の境界の全余錐空間を一度に延長する。 -/
def relativeRightCosliceSection {K L E B : SSet.{u}} [Quasicategory B]
    (t : K ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (j : L ⟶ K) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ t) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t :=
  (exists_relativeRightCosliceFamily t q j hj (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (j ≫ t) q ≫ rightCosliceSection (t ≫ q) j hj) (by
      simp only [Category.assoc, rightCosliceSection_boundary, Category.id_comp]
      exact (Category.comp_id _).symm)).choose

/-- 相対切断の境界は、元の族そのもの。 -/
lemma relativeRightCosliceSection_boundary {K L E B : SSet.{u}} [Quasicategory B]
    (t : K ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (j : L ⟶ K) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j) :
    relativeRightCosliceSection t q j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j = 𝟙 _ :=
  (exists_relativeRightCosliceFamily t q j hj (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (j ≫ t) q ≫ rightCosliceSection (t ≫ q) j hj) (by
      simp only [Category.assoc, rightCosliceSection_boundary, Category.id_comp]
      exact (Category.comp_id _).symm)).choose_spec.1

/-- 相対切断の底は、同じ指定した底の切断による延長である。 -/
lemma relativeRightCosliceSection_base {K L E B : SSet.{u}} [Quasicategory B]
    (t : K ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (j : L ⟶ K) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j) :
    relativeRightCosliceSection t q j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (j ≫ t) q ≫ rightCosliceSection (t ≫ q) j hj :=
  (exists_relativeRightCosliceFamily t q j hj (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (j ≫ t) q ≫ rightCosliceSection (t ≫ q) j hj) (by
      simp only [Category.assoc, rightCosliceSection_boundary, Category.id_comp]
      exact (Category.comp_id _).symm)).choose_spec.2

/-- 相対切断は可変な終点も厳密に保つ。 -/
lemma relativeRightCosliceSection_projection {K L E B : SSet.{u}} [Quasicategory B]
    (t : K ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (j : L ⟶ K) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j) :
    relativeRightCosliceSection t q j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ t) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection t j, ← Category.assoc,
    relativeRightCosliceSection_boundary, Category.id_comp]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
