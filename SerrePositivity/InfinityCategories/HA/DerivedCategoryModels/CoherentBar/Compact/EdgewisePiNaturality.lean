module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EdgewisePiComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelation
/-!
概要：全基点の反転 π 比較は、元の Kan 射と可換する。
方針：同じ定値解像基点上の両端射影の厳密な自然性を使う。
規約：元の実射と基点を保持し、任意の同値を選び直さない。
使われ方：反転した線形 Hom のホモロジーチャートの脚自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial

/-- 共通解像から反転空間への、同じ定値基点を保つ π 同型。 -/
def dgBarCompactEdgewiseLeftPiEquiv (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X)).isSimplicialHomotopyEquivalence)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_left x)

/-- 共通解像から元の空間への、同じ定値基点を保つ π 同型。 -/
def dgBarCompactEdgewiseRightPiEquiv (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X)).isSimplicialHomotopyEquivalence)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_right x)

lemma dgBarCompactOppositePiEquiv_naturality {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (n : ℕ) (x : X _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.op n (SSet.opObjEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositePiEquiv Y n (f.app _ x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (x := SSet.opObjEquiv.symm x)
        (y := SSet.opObjEquiv.symm (f.app _ x)) (SSet.opFunctor.map f) rfl a) =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n f x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactOppositePiEquiv X n x a) := by
  let LX := dgBarCompactEdgewiseLeftPiEquiv X n x
  let LY := dgBarCompactEdgewiseLeftPiEquiv Y n (f.app _ x)
  let RX := dgBarCompactEdgewiseRightPiEquiv X n x
  let RY := dgBarCompactEdgewiseRightPiEquiv Y n (f.app _ x)
  obtain ⟨a₀, rfl⟩ := LX.surjective a
  have hL := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square (d := SSet.opObjEquiv.symm (f.app _ x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f) (SSet.opFunctor.map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality f)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_map f x) rfl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_left x)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_left (f.app _ x)) n a₀
  have hL' : LY (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_map f x) a₀) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (x := SSet.opObjEquiv.symm x)
        (y := SSet.opObjEquiv.symm (f.app _ x)) (SSet.opFunctor.map f) rfl (LX a₀) := by
    dsimp only [LY, LX, dgBarCompactEdgewiseLeftPiEquiv]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply]
    exact hL
  have hR := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f) f
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality f)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_map f x) rfl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_right x)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_right (f.app _ x)) n a₀
  have hR' : RY (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEdgewiseVertex_map f x) a₀) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl (RX a₀) := by
    simpa only [RY, RX, dgBarCompactEdgewiseRightPiEquiv,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply] using hR
  change RY (LY.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (x := SSet.opObjEquiv.symm x)
        (y := SSet.opObjEquiv.symm (f.app _ x)) (SSet.opFunctor.map f) rfl (LX a₀))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl (RX (LX.symm (LX a₀)))
  rw [← hL', MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact hR'

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
