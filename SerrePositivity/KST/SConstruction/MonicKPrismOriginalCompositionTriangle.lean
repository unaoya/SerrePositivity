module
public import SerrePositivity.KST.SConstruction.KCompositionCompatibilityTriangle
public import SerrePositivity.KST.SConstruction.MonicKPrismCompositeCylinderTransport

/-! # 単射源に移した元の合成適合三角形
概要：元の実比較三角形の全体を、単射置換源からの suspension Hom に移す。
方針：同じ源の置換射影による前合成を、全二単体に適用する。
規約：三つの適合区間の全時刻を保持し、零段も別扱いしない。
使われ方：既存の全段補正列と元の合成適合三角形を同じ Hom 内で照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance monicKPrismOriginalCompositionTrianglePointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 同じ元の全比較三角形を、単射源の元の suspension Hom に移す。 -/
def monicKPrismOriginalCompositionTriangle : (Δ[2] : SSet.{u}) ⟶
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level r).space)
      ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
  SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityTriangle r F f g).simplex ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
      ((kKanSequence (F.obj z)).level (r + 1)).space

/-- 元の前の適合区間の実後合成は、同じ源の射影を通した区間として保たれる。 -/
lemma monicKPrismOriginalCompositionTriangle_first :
    stdSimplex.δ 2 ≫ monicKPrismOriginalCompositionTriangle r F f g =
      (SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F f).edge ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
          (kKanSequenceLevelMap (F.map g) (r + 1))).right) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  rw [monicKPrismOriginalCompositionTriangle, ← Category.assoc,
    (kKanOriginalCompositionCompatibilityTriangle_original_faces r F f g).1]

/-- 元の後の適合区間の実前合成も、同じ源の射影を通した全区間である。 -/
lemma monicKPrismOriginalCompositionTriangle_second :
    stdSimplex.δ 0 ≫ monicKPrismOriginalCompositionTriangle r F f g =
      (SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F g).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
          ((kKanSequence (F.obj z)).level (r + 1)).space) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  rw [monicKPrismOriginalCompositionTriangle, ← Category.assoc,
    (kKanOriginalCompositionCompatibilityTriangle_original_faces r F f g).2.1]

/-- 合成射の元の適合区間も、単射源への同じ前合成を厳密に回収する。 -/
lemma monicKPrismOriginalCompositionTriangle_composite :
    stdSimplex.δ 1 ≫ monicKPrismOriginalCompositionTriangle r F f g =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F (f ≫ g)).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  rw [monicKPrismOriginalCompositionTriangle, ← Category.assoc,
    (kKanOriginalCompositionCompatibilityTriangle_original_faces r F f g).2.2]

end SerrePositivity.KST.SConstruction
