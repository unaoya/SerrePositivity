module
public import SerrePositivity.KST.SConstruction.KCompositionCompatibilityData

/-! # 元の三適合区間を三面に持つ実比較三角形
概要：元の六セルから、合成射の適合区間と入力二射の適合区間の実合成を比較する。
方針：内部構成した六セルデータの実三角形を取り出し、元の三辺を照合する。
規約：区間の存在や trace の互換性を仮定せず、元のセルから構成する。
使われ方：全段補正と合わせる端点固定の二次元入力。
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
local instance kCompositionCompatibilityTrianglePointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 六セルの実境界から得る、三つの元の適合辺の実比較三角形。 -/
def kKanOriginalCompositionCompatibilityTriangle :
    SSet.Edge.CompStruct (kKanOriginalCompositionCompatibilityData r F f g).first
      (kKanOriginalCompositionCompatibilityData r F f g).second
      (kKanOriginalCompositionCompatibilityData r F f g).composite := by
  letI : KanComplex
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
        ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact (kKanOriginalCompositionCompatibilityData r F f g).comparison

/-- 六セルデータの composite 辺は、同じ元の適合区間の実前後合成。 -/
lemma kKanOriginalCompositionCompatibilityData_composite :
    SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).composite.edge =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F (f ≫ g)).edge := by
  change SSet.yonedaEquiv.symm
    ((PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      ((kKanSequence (F.obj z)).level (r + 1)).space).right.δ 0
        (SSet.yonedaEquiv (kKanOriginalCompositionPastingTriangle r F f g 0))) = _
  rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]
  have h := kKanOriginalCompositionSpecifiedPasting_composite_compatibility r F f g
  rw [kKanOriginalCompositionSpecifiedPasting_triangle] at h
  exact h

/-- 六セルデータの first 辺は、同じ元の適合区間の実前後合成。 -/
lemma kKanOriginalCompositionCompatibilityData_first :
    SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).first.edge =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F f).edge ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
          (kKanSequenceLevelMap (F.map g) (r + 1))).right := by
  change SSet.yonedaEquiv.symm
    ((PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      ((kKanSequence (F.obj z)).level (r + 1)).space).right.δ 0
        (SSet.yonedaEquiv (kKanOriginalCompositionPastingTriangle r F f g 1))) = _
  rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]
  have h := kKanOriginalCompositionSpecifiedPasting_first_compatibility r F f g
  rw [kKanOriginalCompositionSpecifiedPasting_triangle] at h
  exact h

/-- 六セルデータの second 辺は、同じ元の適合区間の実前後合成。 -/
lemma kKanOriginalCompositionCompatibilityData_second :
    SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).second.edge =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F g).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  change SSet.yonedaEquiv.symm
    ((PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      ((kKanSequence (F.obj z)).level (r + 1)).space).right.δ 0
        (SSet.yonedaEquiv (kKanOriginalCompositionPastingTriangle r F f g 2))) = _
  rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]
  have h := kKanOriginalCompositionSpecifiedPasting_second_compatibility r F f g
  rw [kKanOriginalCompositionSpecifiedPasting_triangle] at h
  exact h

/-- 実比較三角形の 2 面は、元の first 適合区間の全体。 -/
lemma kKanOriginalCompositionCompatibilityTriangle_face_first :
    stdSimplex.δ 2 ≫
      SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityTriangle r F f g).simplex =
      SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).first.edge := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm,
    (kKanOriginalCompositionCompatibilityTriangle r F f g).d₂]

/-- 実比較三角形の 0 面は、元の second 適合区間の全体。 -/
lemma kKanOriginalCompositionCompatibilityTriangle_face_second :
    stdSimplex.δ 0 ≫
      SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityTriangle r F f g).simplex =
      SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).second.edge := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm,
    (kKanOriginalCompositionCompatibilityTriangle r F f g).d₀]

/-- 実比較三角形の 1 面は、元の composite 適合区間の全体。 -/
lemma kKanOriginalCompositionCompatibilityTriangle_face_composite :
    stdSimplex.δ 1 ≫
      SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityTriangle r F f g).simplex =
      SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).composite.edge := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm,
    (kKanOriginalCompositionCompatibilityTriangle r F f g).d₁]

/-- 比較三角形の全三面は、元の三つの適合区間の実前後合成を同時に保持する。 -/
lemma kKanOriginalCompositionCompatibilityTriangle_original_faces :
    stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityTriangle r F f g).simplex =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F f).edge ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
          (kKanSequenceLevelMap (F.map g) (r + 1))).right ∧
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityTriangle r F f g).simplex =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F g).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
          ((kKanSequence (F.obj z)).level (r + 1)).space ∧
    stdSimplex.δ 1 ≫
        SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityTriangle r F f g).simplex =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F (f ≫ g)).edge :=
  ⟨(kKanOriginalCompositionCompatibilityTriangle_face_first r F f g).trans
      (kKanOriginalCompositionCompatibilityData_first r F f g),
    (kKanOriginalCompositionCompatibilityTriangle_face_second r F f g).trans
      (kKanOriginalCompositionCompatibilityData_second r F f g),
    (kKanOriginalCompositionCompatibilityTriangle_face_composite r F f g).trans
      (kKanOriginalCompositionCompatibilityData_composite r F f g)⟩

end SerrePositivity.KST.SConstruction
