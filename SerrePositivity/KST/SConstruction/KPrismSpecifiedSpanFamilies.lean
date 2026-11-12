module
public import SerrePositivity.KST.SConstruction.KPrismBoundaryLegs
public import SerrePositivity.KST.SConstruction.SpecifiedPointSpanFamilies
public import SerrePositivity.KST.SConstruction.KSuspensionSpecifiedPasting

/-! # 元の K prism の全精密化族を指定した適合辺へ相対合成する
概要：元の上下の二円柱から、指定頂点で既存の適合辺と外側三角形を保持する実比較族を作る。
方針：元の二成分と同じ指定三角形を一点の境界データへ移し、相対延長する。
規約：追加の円柱・境界三角形を入力せず、元の選択を全時刻で回収する。
使われ方：元の段の写像を全精密化パラメータで BF 厳密化へ渡す際の指定境界を供給する。
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
local instance kPrismSpecifiedSpanFamilies_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の次段の Kan 性から得る、同じ native Hom の Kan 性。 -/
local instance kPrismSpecifiedSpanFamilies_native_kan {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x y : I) :
    KanComplex (SimplicialCategory.sHom
      (PointedSimplicialSet.circle.{u} ⊗ ((kKanSequence (F.obj x)).level r).space)
      ((kKanSequence (F.obj y)).level (r + 1)).space) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の指定外側三角形と、二円柱の指定成分・指定適合辺の三面の厳密な回収。 -/
def kKanOriginalPrismSpecifiedOuterTriangleData {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    {t : (kKanOriginalSuspensionMappingTarget r F x y) _⦋2⦌ //
      (kKanOriginalSuspensionMappingTarget r F x y).map (SimplexCategory.δ (2 : Fin 3)).op t =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (kKanOriginalPrismUpperCompositeContraction r F f)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))).edge ∧
      (kKanOriginalSuspensionMappingTarget r F x y).map (SimplexCategory.δ (0 : Fin 3)).op t =
        (kKanSuspensionCompatibilityEdge r F f).edge ∧
      (kKanOriginalSuspensionMappingTarget r F x y).map (SimplexCategory.δ (1 : Fin 3)).op t =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (kKanOriginalPrismLowerCompositeContraction r F f)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))).edge} := by
  let T := kanMappingSpanOuterTriangle (kKanSuspensionCompatibilityComposition r F f)
  exact ⟨T.simplex,
    T.d₂.trans (kKanOriginalPrismUpperCompositeContraction_boundary_leg r F f).symm,
    T.d₀, T.d₁.trans (kKanOriginalPrismLowerCompositeContraction_boundary_leg r F f).symm⟩

/-- 全三面を回収しても、既存の同じ外側三角形の二単体は変わらない。 -/
lemma kKanOriginalPrismSpecifiedOuterTriangleData_simplex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).val =
      (kanMappingSpanOuterTriangle (kKanSuspensionCompatibilityComposition r F f)).simplex := rfl

/-- 元の K prism から直接供給する、全精密化パラメータの指定境界付き実適合族。 -/
def kKanOriginalPrismSpecifiedCompatibilityFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy
      (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (PointedMapping.familyVertex
        ((kKanSequence (F.obj x)).sigma r ≫ kKanSequenceLevelMap (F.map f) (r + 1))))
      (SSet.const (PointedMapping.familyVertex
        (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r ≫
          (kKanSequence (F.obj y)).sigma r))) :=
  specifiedPointSpanComposite (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))
    (kKanOriginalPrismUpperCompositeContraction r F f)
    (kKanOriginalPrismLowerCompositeContraction r F f) (kKanSuspensionCompatibilityEdge r F f)
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).val
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).property.1
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).property.2.1
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).property.2.2

/-- 指定頂点の比較円柱は、元の指定した適合辺の同じ実区間を厳密に回収する。 -/
lemma kKanOriginalPrismSpecifiedCompatibilityFamily_boundary {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[1] : SSet.{u})) ≫
      (kKanOriginalPrismSpecifiedCompatibilityFamily r F f).h =
        snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F f).edge :=
  specifiedPointSpanComposite_boundary _ _ _ _ _ _ _ _

/-- 同じ選択で元の上下の二円柱を全パラメータで保持する実二単体族。 -/
def kKanOriginalPrismSpecifiedTriangleFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ (Δ[2] : SSet.{u}) ⟶
      kKanOriginalSuspensionMappingTarget r F x y :=
  specifiedPointSpanTriangleFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))
    (kKanOriginalPrismUpperCompositeContraction r F f)
    (kKanOriginalPrismLowerCompositeContraction r F f) (kKanSuspensionCompatibilityEdge r F f)
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).val
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).property.1
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).property.2.1
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).property.2.2

/-- 指定頂点では元の適合辺だけでなく、同じ元の外側三角形全体を回収する。 -/
lemma kKanOriginalPrismSpecifiedTriangleFamily_boundary {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[2] : SSet.{u})) ≫
      kKanOriginalPrismSpecifiedTriangleFamily r F f =
        snd (Δ[0] : SSet.{u}) (Δ[2] : SSet.{u}) ≫ SSet.yonedaEquiv.symm
          (kanMappingSpanOuterTriangle (kKanSuspensionCompatibilityComposition r F f)).simplex :=
  specifiedPointSpanTriangleFamily_boundary _ _ _ _ _ _ _ _

/-- 第一面は元の上側の実円柱そのもの。 -/
lemma kKanOriginalPrismSpecifiedTriangleFamily_upper {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ◁ stdSimplex.δ 2) ≫
      kKanOriginalPrismSpecifiedTriangleFamily r F f =
        (kKanOriginalPrismUpperCompositeContraction r F f).h :=
  specifiedPointSpanTriangleFamily_source _ _ _ _ _ _ _ _

/-- 第二面は元の下側の実円柱そのもの。 -/
lemma kKanOriginalPrismSpecifiedTriangleFamily_lower {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ◁ stdSimplex.δ 1) ≫
      kKanOriginalPrismSpecifiedTriangleFamily r F f =
        (kKanOriginalPrismLowerCompositeContraction r F f).h :=
  specifiedPointSpanTriangleFamily_target _ _ _ _ _ _ _ _

/-- 残りの面は同じ選択の全適合円柱そのもの。 -/
lemma kKanOriginalPrismSpecifiedTriangleFamily_compatibility {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ◁ stdSimplex.δ 0) ≫
      kKanOriginalPrismSpecifiedTriangleFamily r F f =
        (kKanOriginalPrismSpecifiedCompatibilityFamily r F f).h :=
  specifiedPointSpanTriangleFamily_composite _ _ _ _ _ _ _ _

end SerrePositivity.KST.SConstruction
