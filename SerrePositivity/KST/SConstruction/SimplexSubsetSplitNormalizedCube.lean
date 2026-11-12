module
public import SerrePositivity.KST.SConstruction.ConcreteCubeFaceConjugation
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitNormalizedDimensions
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitFaceSign

/-! # 元の分割一面と削除零面の同じ濃度座標
概要：元の実二 bead refinement を濃度次元で読み、元の削除零面と同じ座標の一面と同定。
方針：元の次元共役と、元の右側頂点数による座標の一致を使う。
規約：元の実 cube 射と右端座標を保持。使われ方：標準両面の同じ HA 境界への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
variable {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
  (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
  (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))

/-- 元の分割共有座標を、元の全体部分集合の濃度次元で読む。 -/
def simplexSubsetSplitNormalizedCoordinate : Fin (I.card - 2) :=
  Fin.cast (simplexSubsetSplit_whole_dimension I hI j hj
    (simplexSubsetSplitLeft_two I hI j hj hjm) (simplexSubsetSplitRight_two I hI j hj hjM))
    (necklaceRefinementMissingCoordinate
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{0} ((I.filter (· ≤ j)).card - 1))
        (necklaceBead ((I.filter (j ≤ ·)).card - 1)))
      (necklaceWedgeBeadSeam ((I.filter (· ≤ j)).card - 1) ((I.filter (j ≤ ·)).card - 1)
        (by have h := simplexSubsetSplitLeft_two I hI j hj hjm; omega)
        (by have h := simplexSubsetSplitRight_two I hI j hj hjM; omega)))

/-- 元の分割一面と削除零面は、元の濃度次元の同じ右端座標を持つ。 -/
lemma simplexSubsetSplitNormalizedCoordinate_eq :
    simplexSubsetSplitNormalizedCoordinate I hI j hj hjm hjM =
      simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM := by
  apply Fin.ext
  have hs := simplexSubsetSplit_face_coordinate.{0} I j hj
    (simplexSubsetSplitLeft_two I hI j hj hjm) (simplexSubsetSplitRight_two I hI j hj hjM)
  have he := simplexSubsetCoordinate_right_count I hI
    (simplexSubsetEraseCoordinate I hI j hj hjm hjM)
  rw [simplexSubsetEraseCoordinate_recovery] at he
  change (necklaceRefinementMissingCoordinate
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{0} ((I.filter (· ≤ j)).card - 1))
      (necklaceBead ((I.filter (j ≤ ·)).card - 1)))
    (necklaceWedgeBeadSeam ((I.filter (· ≤ j)).card - 1) ((I.filter (j ≤ ·)).card - 1)
      (by have h := simplexSubsetSplitLeft_two I hI j hj hjm; omega)
      (by have h := simplexSubsetSplitRight_two I hI j hj hjM; omega))).val =
    (simplexSubsetEraseCoordinate I hI j hj hjm hjM).val
  omega

/-- 元の実二 bead refinement を、元の削除・全体の濃度次元へ移した実 cube 射。 -/
def simplexSubsetSplitNormalizedCube :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2) :=
  (concreteCubeDimensionIso (simplexSubsetSplit_wedge_erase_dimension
    I hI j hj hjm hjM).symm).hom ≫
    necklaceConcreteCubeMap (necklaceWedgeBeadRefinement.{u}
      ((I.filter (· ≤ j)).card - 1) ((I.filter (j ≤ ·)).card - 1)) ≫
      (concreteCubeDimensionIso (simplexSubsetSplit_whole_dimension I hI j hj
        (simplexSubsetSplitLeft_two I hI j hj hjm)
        (simplexSubsetSplitRight_two I hI j hj hjM)).symm).inv

/-- 元の濃度次元の分割実 cube 射は、元の削除と同じ座標の標準一面。 -/
lemma simplexSubsetSplit_normalized_one_face :
    simplexSubsetSplitNormalizedCube.{u} I hI j hj hjm hjM ≫
      (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
        (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2 + 1))
        (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)).hom =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true ((I.erase j).card - 2)
      (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
        (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM)) := by
  have hL := simplexSubsetSplitLeft_two I hI j hj hjm
  have hR := simplexSubsetSplitRight_two I hI j hj hjM
  have hp : 0 < (I.filter (· ≤ j)).card - 1 := by omega
  have hq : 0 < (I.filter (j ≤ ·)).card - 1 := by omega
  have h := concreteCube_face_conjugate true
    (simplexSubsetSplit_wedge_erase_dimension I hI j hj hjm hjM).symm
    (simplexSubsetSplit_whole_dimension I hI j hj hL hR).symm
    (necklaceWedgeBead_codimension _ _ hp hq)
    (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
    (necklaceConcreteCubeMap (necklaceWedgeBeadRefinement.{u}
      ((I.filter (· ≤ j)).card - 1) ((I.filter (j ≤ ·)).card - 1)))
    (necklaceRefinementMissingCoordinate
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} ((I.filter (· ≤ j)).card - 1))
        (necklaceBead ((I.filter (j ≤ ·)).card - 1)))
      (necklaceWedgeBeadSeam _ _ hp hq))
    (necklaceWedgeBeadRefinement_one_face _ _ hp hq)
  exact h.trans (congrArg (fun i => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true ((I.erase j).card - 2)
    (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM) i))
      (simplexSubsetSplitNormalizedCoordinate_eq I hI j hj hjm hjM))

end SerrePositivity.KST.SConstruction
