module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceShapePushout
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFamilies
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialFibrationHomotopy

/-!
概要：底の三角形が長辺の退化なら、長辺上の余錐の全パラメータ族を二単体全体へ延長する。
方針：底の族を退化で延長し、長辺への相対 coslice 制限の自明 Kan fibration 性を使う。
規約：パラメータの Kan 性は不要。長辺と底の族を厳密に保つ。
使われ方：指定右修正辺を含む二単体から、共通 end に必要な互いに整合する三面の族を作る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 長辺の相対族の底を、底の図式を保つ形状の退化で三角形全体へ延長する。 -/
def retractedCosliceBaseFamily {K L E B T : SSet.{u}}
    (t : K ⟶ E) (q : E ⟶ B) (j : L ⟶ K) (r : K ⟶ L)
    (hbase : r ≫ ((j ≫ t) ≫ q) = t ≫ q) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ t)) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (t ≫ q) :=
  (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (j ≫ t) q) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction ((j ≫ t) ≫ q) r hbase

/-- 退化による底の延長を長辺へ戻すと、入力した族の底そのものになる。 -/
lemma retractedCosliceBaseFamily_restrict {K L E B T : SSet.{u}}
    (t : K ⟶ E) (q : E ⟶ B) (j : L ⟶ K) (r : K ⟶ L)
    (hsplit : j ≫ r = 𝟙 L) (hbase : r ≫ ((j ≫ t) ≫ q) = t ≫ q)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ t)) :
    retractedCosliceBaseFamily t q j r hbase a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (t ≫ q) j =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (j ≫ t) q := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective ((j ≫ t) ≫ q)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, retractedCosliceBaseFamily,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, hsplit,
    Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]

/-- 底の退化が入力と可換なら、長辺の全パラメータ族を底も含めて厳密に延長できる。 -/
lemma exists_retractedRelativeCosliceFamily {K L E B T : SSet.{u}}
    (t : K ⟶ E) (q : E ⟶ B) (j : L ⟶ K) (r : K ⟶ L)
    (hsplit : j ≫ r = 𝟙 L) (hbase : r ≫ ((j ≫ t) ≫ q) = t ≫ q)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q j)]
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ t)) :
    ∃ l : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t,
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j = a ∧
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q = retractedCosliceBaseFamily t q j r hbase a := by
  let b := retractedCosliceBaseFamily t q j r hbase a
  let v := pullback.lift a b (retractedCosliceBaseFamily_restrict t q j r hsplit hbase a).symm
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q j)
  refine ⟨v ≫ s, ?_, ?_⟩
  · have h := congrArg (fun z ↦ v ≫ z ≫ pullback.fst _ _) hs
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_fst, Category.id_comp, v] using h
  · have h := congrArg (fun z ↦ v ≫ z ≫ pullback.snd _ _) hs
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_snd, Category.id_comp, v] using h

/-- 同じ長辺と同じ底を持つ二つの延長は、その両方を保つホモトピーで結べる。 -/
lemma relativeCosliceFamilies_homotopy {K L E B T : SSet.{u}}
    (t : K ⟶ E) (q : E ⟶ B) (j : L ⟶ K)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q j)]
    (l m : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t)
    (hside : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j = m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j)
    (hbase : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q = m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q) :
    ∃ H : SSet.Homotopy l m,
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j = fst T (Δ[1] : SSet.{u}) ≫ m ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j ∧
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q = fst T (Δ[1] : SSet.{u}) ≫ m ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q := by
  have h : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q j = m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q j := by
    apply pullback.hom_ext
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
        pullback.lift_fst] using hside
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
        pullback.lift_snd] using hbase
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q j) l m h
  refine ⟨H, ?_, ?_⟩
  · have h := congrArg (fun z ↦ z ≫ pullback.fst _ _) hH
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_fst] using h
  · have h := congrArg (fun z ↦ z ≫ pullback.snd _ _) hH
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_snd] using h

/-- 長辺包含と右退化の往復は恒等射。 -/
lemma triangleLongEdge_degeneracy_retraction :
    (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫ stdSimplex.σ (1 : Fin 2) =
      𝟙 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 底が右退化した辺なら、長辺で制限して退化で戻しても底の三角形を厳密に保つ。 -/
lemma triangleBase_retraction {E B : SSet.{u}} (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B)
    (e : (Δ[1] : SSet.{u}) ⟶ B) (ht : t ≫ q = stdSimplex.σ (1 : Fin 2) ≫ e) :
    stdSimplex.σ (1 : Fin 2) ≫ ((stdSimplex.δ (1 : Fin 3) ≫ t) ≫ q) = t ≫ q := by
  rw [Category.assoc (stdSimplex.δ (1 : Fin 3)) t q, ht]
  rw [← Category.assoc (stdSimplex.δ (1 : Fin 3)), triangleLongEdge_degeneracy_retraction,
    Category.id_comp]

/-- inner fibration 上の実際の右退化三角形は、長辺上の任意の族から相対的に延長できる。 -/
lemma exists_relativeDegenerateTriangleFamily {E B T : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (e : (Δ[1] : SSet.{u}) ⟶ B) (ht : t ≫ q = stdSimplex.σ (1 : Fin 2) ≫ e)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ t)) :
    ∃ l : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t,
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (1 : Fin 3)) = a ∧
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q = retractedCosliceBaseFamily t q
        (stdSimplex.δ (1 : Fin 3)) (stdSimplex.σ (1 : Fin 2))
        (triangleBase_retraction t q e ht) a := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceRestriction_triangleLongEdge t q
  exact exists_retractedRelativeCosliceFamily t q _ _
    triangleLongEdge_degeneracy_retraction (triangleBase_retraction t q e ht) a

/-- 長辺の全余錐空間を一度に延長する切断。任意の族はこの切断への前合成で延長する。 -/
def relativeDegenerateTriangleSection {E B : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (e : (Δ[1] : SSet.{u}) ⟶ B) (ht : t ≫ q = stdSimplex.σ (1 : Fin 2) ≫ e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ t) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t :=
  (exists_relativeDegenerateTriangleFamily t q e ht (𝟙 _)).choose

/-- 選んだ全パラメータ延長の長辺は恒等射。 -/
lemma relativeDegenerateTriangleSection_longEdge {E B : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (e : (Δ[1] : SSet.{u}) ⟶ B) (ht : t ≫ q = stdSimplex.σ (1 : Fin 2) ≫ e) :
    relativeDegenerateTriangleSection t q e ht ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (1 : Fin 3)) = 𝟙 _ :=
  (exists_relativeDegenerateTriangleFamily t q e ht (𝟙 _)).choose_spec.1

/-- 選んだ延長の底は、長辺の底の族を元の退化で延長したものそのもの。 -/
lemma relativeDegenerateTriangleSection_base {E B : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (e : (Δ[1] : SSet.{u}) ⟶ B) (ht : t ≫ q = stdSimplex.σ (1 : Fin 2) ≫ e) :
    relativeDegenerateTriangleSection t q e ht ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (1 : Fin 3) ≫ t) q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction ((stdSimplex.δ (1 : Fin 3) ≫ t) ≫ q)
          (stdSimplex.σ (1 : Fin 2)) (triangleBase_retraction t q e ht) := by
  simpa only [relativeDegenerateTriangleSection, retractedCosliceBaseFamily,
    Category.id_comp] using
    (exists_relativeDegenerateTriangleFamily t q e ht (𝟙 _)).choose_spec.2

/-- 長辺と底を保つ三角形の延長は、可変終点も全単体で厳密に保つ。 -/
lemma relativeDegenerateTriangleSection_projection {E B : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (e : (Δ[1] : SSet.{u}) ⟶ B) (ht : t ≫ q = stdSimplex.σ (1 : Fin 2) ≫ e) :
    relativeDegenerateTriangleSection t q e ht ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (1 : Fin 3) ≫ t) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection t (stdSimplex.δ (1 : Fin 3)), ← Category.assoc,
    relativeDegenerateTriangleSection_longEdge, Category.id_comp]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
