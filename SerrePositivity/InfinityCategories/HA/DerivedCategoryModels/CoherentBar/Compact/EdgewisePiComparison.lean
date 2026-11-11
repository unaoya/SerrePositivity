module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationValueCohomology
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseLeftFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseRightFilling
/-!
概要：元の Kan 空間と反転した空間の全基点 π を、同じ共通解像で比較する。
方針：同じ定値頂点上の両端射影の π 同型を合成する。
規約：基点を選び直さず、指定した元の頂点から定値頂点を作る。
使われ方：coslice 比較に現れる反転した線形 Hom のホモロジーチャート。
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
variable {X Y : SSet.{u}}

/-- 共通 edgewise 解像の同じ元の頂点による定値頂点。 -/
def dgBarCompactEdgewiseVertex (X : SSet.{u}) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋0⦌ := SSet.const x

lemma dgBarCompactEdgewiseVertex_right (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X).app _ (dgBarCompactEdgewiseVertex X x) = x := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0].op Δ[0] ≫ SSet.const x) = x
  rw [SSet.comp_const, SSet.yonedaEquiv_const]

lemma dgBarCompactEdgewiseVertex_left (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X).app _ (dgBarCompactEdgewiseVertex X x) = SSet.opObjEquiv.symm x := by
  change SSet.opObjEquiv.symm (SSet.yonedaEquiv
    ((stdSimplex.opIso ⦋0⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0].op Δ[0] ≫ SSet.const x)) = _
  rw [SSet.comp_const, SSet.comp_const, SSet.yonedaEquiv_const]

lemma dgBarCompactEdgewiseVertex_map (f : X ⟶ Y) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f).app _ (dgBarCompactEdgewiseVertex X x) =
      dgBarCompactEdgewiseVertex Y (f.app _ x) := by
  change SSet.const x ≫ f = SSet.const (f.app _ x)
  exact SSet.const_comp x f

/-- 同じ定値解像基点での、反転した空間と元の空間の正次数 π の比較。 -/
def dgBarCompactOppositePiEquiv (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.op n (SSet.opObjEquiv.symm x) ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x := by
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X)).isSimplicialHomotopyEquivalence
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X)).isSimplicialHomotopyEquivalence
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X) hL
    (dgBarCompactEdgewiseVertex_left x)).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X) hR
        (dgBarCompactEdgewiseVertex_right x))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
