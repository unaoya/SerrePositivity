module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightAnodyneJoinPrefix
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.RelativeTriangleFamilies

/-!
概要：四面体の終端三角形上の全パラメータ族を、底の選んだ延長を保って四面体全体へ延長する。
方針：終端面への制限の right anodyne 性から、絶対・相対 coslice の切断を選ぶ。
規約：終端面と可変終点を全単体で厳密に保持する。
使われ方：共通部分の始対象の比較辺を含む四面体へ、指定余錐の全 Hom の族を延長する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- inner fibration の四面体から終端面への相対 coslice 制限は自明 Kan fibration。 -/
lemma relativeCosliceRestriction_tetrahedronTerminalFace {E B : SSet.{u}}
    (t : (Δ[3] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q (stdSimplex.δ (0 : Fin 4))) := by
  let A : (Δ[3] : SSet.{u}).Subcomplex := stdSimplex.face {(0 : Fin 4)}ᶜ
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions A.ι := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.cancel_left_of_respectsIso
      (stdSimplex.faceSingletonComplIso (0 : Fin 4)).hom,
      stdSimplex.faceSingletonComplIso_hom_ι]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.tetrahedronTerminalFace_rightAnodyne
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_trivialKanFibration_of_rightAnodyne t q A hA
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceRestriction_trivialKanFibration_subcomplexIso t q A
    (stdSimplex.faceSingletonComplIso (0 : Fin 4))
  simpa only [A, stdSimplex.faceSingletonComplIso_hom_ι] using h

/-- quasicategory の四面体から終端面への coslice 制限も自明 Kan fibration。 -/
lemma sliceUnderRestrict_tetrahedronTerminalFace {B : SSet.{u}} [Quasicategory B]
    (t : (Δ[3] : SSet.{u}) ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (0 : Fin 4))) := by
  let A : (Δ[3] : SSet.{u}).Subcomplex := stdSimplex.face {(0 : Fin 4)}ᶜ
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions A.ι := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.cancel_left_of_respectsIso
      (stdSimplex.faceSingletonComplIso (0 : Fin 4)).hom,
      stdSimplex.faceSingletonComplIso_hom_ι]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.tetrahedronTerminalFace_rightAnodyne
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_of_rightAnodyne t A hA
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_subcomplexIso t A
    (stdSimplex.faceSingletonComplIso (0 : Fin 4))
  simpa only [A, stdSimplex.faceSingletonComplIso_hom_ι] using h

/-- 終端三角形の族を四面体全体へ延長する絶対切断。 -/
def tetrahedronTerminalFaceSection {B : SSet.{u}} [Quasicategory B]
    (t : (Δ[3] : SSet.{u}) ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 4) ≫ t) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t := by
  have := sliceUnderRestrict_tetrahedronTerminalFace t
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (0 : Fin 4)))).choose

/-- 絶対切断は終端面の全パラメータ族を厳密に回収する。 -/
lemma tetrahedronTerminalFaceSection_target {B : SSet.{u}} [Quasicategory B]
    (t : (Δ[3] : SSet.{u}) ⟶ B) :
    tetrahedronTerminalFaceSection t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (0 : Fin 4)) = 𝟙 _ := by
  have := sliceUnderRestrict_tetrahedronTerminalFace t
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (0 : Fin 4)))).choose_spec

/-- 終端面と指定した底の四面体族を同時に保つ、全パラメータの相対延長。 -/
lemma exists_relativeTetrahedronFamily {E B T : SSet.{u}}
    (t : (Δ[3] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 4) ≫ t))
    (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (t ≫ q))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 4) ≫ t) q =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (t ≫ q) (stdSimplex.δ (0 : Fin 4))) :
    ∃ l : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t,
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (0 : Fin 4)) = a ∧
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q = b := by
  have := relativeCosliceRestriction_tetrahedronTerminalFace t q
  let v := pullback.lift a b h
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q (stdSimplex.δ (0 : Fin 4)))
  refine ⟨v ≫ s, ?_, ?_⟩
  · have hh := congrArg (fun k ↦ v ≫ k ≫ pullback.fst _ _) hs
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_fst, Category.id_comp, v] using hh
  · have hh := congrArg (fun k ↦ v ≫ k ≫ pullback.snd _ _) hs
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_snd, Category.id_comp, v] using hh

/-- 終端面の全余錐空間を、底の同じ絶対切断を使って一度に延長する。 -/
def relativeTetrahedronTerminalFaceSection {E B : SSet.{u}} [Quasicategory B]
    (t : (Δ[3] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 4) ≫ t) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t :=
  (exists_relativeTetrahedronFamily t q (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 4) ≫ t) q ≫
      tetrahedronTerminalFaceSection (t ≫ q)) (by
        simp only [Category.assoc, tetrahedronTerminalFaceSection_target, Category.id_comp]
        exact (Category.comp_id _).symm)).choose

/-- 相対切断は、元の終端三角形上の全パラメータ族を回収する。 -/
lemma relativeTetrahedronTerminalFaceSection_target {E B : SSet.{u}} [Quasicategory B]
    (t : (Δ[3] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    relativeTetrahedronTerminalFaceSection t q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (0 : Fin 4)) = 𝟙 _ :=
  (exists_relativeTetrahedronFamily t q (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 4) ≫ t) q ≫
      tetrahedronTerminalFaceSection (t ≫ q)) (by
        simp only [Category.assoc, tetrahedronTerminalFaceSection_target, Category.id_comp]
        exact (Category.comp_id _).symm)).choose_spec.1

/-- 相対切断の底は、元の終端面の底を同じ四面体上で延長したものそのもの。 -/
lemma relativeTetrahedronTerminalFaceSection_base {E B : SSet.{u}} [Quasicategory B]
    (t : (Δ[3] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    relativeTetrahedronTerminalFaceSection t q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 4) ≫ t) q ≫
        tetrahedronTerminalFaceSection (t ≫ q) :=
  (exists_relativeTetrahedronFamily t q (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 4) ≫ t) q ≫
      tetrahedronTerminalFaceSection (t ≫ q)) (by
        simp only [Category.assoc, tetrahedronTerminalFaceSection_target, Category.id_comp]
        exact (Category.comp_id _).symm)).choose_spec.2

/-- 相対切断は、四面体族の可変終点も厳密に保持する。 -/
lemma relativeTetrahedronTerminalFaceSection_projection {E B : SSet.{u}} [Quasicategory B]
    (t : (Δ[3] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    relativeTetrahedronTerminalFaceSection t q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 4) ≫ t) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection t (stdSimplex.δ (0 : Fin 4)), ← Category.assoc,
    relativeTetrahedronTerminalFaceSection_target, Category.id_comp]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
