module
public import SerrePositivity.KST.SConstruction.KPrismSpecifiedSpanFamilies
public import SerrePositivity.KST.SConstruction.SequenceCompatibilityFamilyTransport
public import SerrePositivity.KST.SConstruction.MonicKPrismCompatibility

/-! # 単射源からの元の K prism の指定境界付き全適合族
概要：全精密化パラメータの元の適合族を、元の単射置換の射影で前合成する。
方針：同じ実円柱と三角形族を写像空間で後合成し、指定辺と全境界を回収する。
規約：元の monicKPrismCompatibilityEdge を保持し、辺や円柱を選び直さない。
使われ方：指定した補正列を保つ BF の族の厳密化への具体的入力を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 単射源の元の段の比較に対する、指定境界を保持した全精密化上の実適合族。 -/
def monicKPrismSpecifiedCompatibilityFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy
      (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (familyVertex
        ((monicKKanSequence (F.obj x)).sigma r ≫ monicKToRawLevelMap (F.map f) (r + 1))))
      (SSet.const (familyVertex (PointedSimplicialSet.circle.{u} ◁ monicKToRawLevelMap (F.map f) r ≫
        (kKanSequence (F.obj y)).sigma r))) :=
  sequenceCompatibilityFamily_precompose (monicKKanSequenceProjection (F.obj x))
    (kKanSequenceLevelMap (F.map f)) r (kKanOriginalPrismSpecifiedCompatibilityFamily r F f)

/-- 単射源に移した全適合円柱は、元の円柱の同じ前合成である。 -/
lemma monicKPrismSpecifiedCompatibilityFamily_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (monicKPrismSpecifiedCompatibilityFamily r F f).h =
      (kKanOriginalPrismSpecifiedCompatibilityFamily r F f).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁
          (monicKKanSequenceProjection (F.obj x)).app r)
          ((kKanSequence (F.obj y)).level (r + 1)).space := rfl

/-- 指定頂点で元の単射源の適合辺の同じ実区間を厳密に回収する。 -/
lemma monicKPrismSpecifiedCompatibilityFamily_boundary {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[1] : SSet.{u})) ≫
      (monicKPrismSpecifiedCompatibilityFamily r F f).h =
        snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          SSet.yonedaEquiv.symm (monicKPrismCompatibilityEdge r F f).edge :=
  sequenceCompatibilityFamily_precompose_boundary (monicKKanSequenceProjection (F.obj x))
    (kKanSequenceLevelMap (F.map f)) r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
    (kKanOriginalPrismSpecifiedCompatibilityFamily r F f) (kKanSuspensionCompatibilityEdge r F f)
    (kKanOriginalPrismSpecifiedCompatibilityFamily_boundary r F f)

/-- 単射源へ移しても、同じ全二単体族と元の上下の二円柱を保持する。 -/
def monicKPrismSpecifiedTriangleFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ (Δ[2] : SSet.{u}) ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((monicKKanSequence (F.obj x)).level r).space)
        ((kKanSequence (F.obj y)).level (r + 1)).space).right :=
  kKanOriginalPrismSpecifiedTriangleFamily r F f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁
      (monicKKanSequenceProjection (F.obj x)).app r)
      ((kKanSequence (F.obj y)).level (r + 1)).space

/-- 指定頂点では、元の指定外側三角形全体の同じ前合成を回収する。 -/
lemma monicKPrismSpecifiedTriangleFamily_boundary {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[2] : SSet.{u})) ≫
      monicKPrismSpecifiedTriangleFamily r F f =
        (snd (Δ[0] : SSet.{u}) (Δ[2] : SSet.{u}) ≫ SSet.yonedaEquiv.symm
          (kKanOriginalPrismSpecifiedOuterTriangleData r F f).val) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁
            (monicKKanSequenceProjection (F.obj x)).app r)
            ((kKanSequence (F.obj y)).level (r + 1)).space := by
  rw [monicKPrismSpecifiedTriangleFamily, ← Category.assoc,
    kKanOriginalPrismSpecifiedTriangleFamily_boundary,
    kKanOriginalPrismSpecifiedOuterTriangleData_simplex]
  rfl

/-- 三角形族の比較面は、同じ単射源の全適合円柱そのもの。 -/
lemma monicKPrismSpecifiedTriangleFamily_compatibility {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ◁ stdSimplex.δ 0) ≫
      monicKPrismSpecifiedTriangleFamily r F f =
        (monicKPrismSpecifiedCompatibilityFamily r F f).h := by
  rw [monicKPrismSpecifiedTriangleFamily, ← Category.assoc,
    kKanOriginalPrismSpecifiedTriangleFamily_compatibility]
  rfl

/-- 上側の面は元の同じ実円柱の単射源による前合成そのもの。 -/
lemma monicKPrismSpecifiedTriangleFamily_upper {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ◁ stdSimplex.δ 2) ≫
      monicKPrismSpecifiedTriangleFamily r F f =
        (kKanOriginalPrismUpperCompositeContraction r F f).h ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁
            (monicKKanSequenceProjection (F.obj x)).app r)
            ((kKanSequence (F.obj y)).level (r + 1)).space := by
  rw [monicKPrismSpecifiedTriangleFamily, ← Category.assoc,
    kKanOriginalPrismSpecifiedTriangleFamily_upper]

/-- 下側の面は元の同じ実円柱の単射源による前合成そのもの。 -/
lemma monicKPrismSpecifiedTriangleFamily_lower {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ◁ stdSimplex.δ 1) ≫
      monicKPrismSpecifiedTriangleFamily r F f =
        (kKanOriginalPrismLowerCompositeContraction r F f).h ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁
            (monicKKanSequenceProjection (F.obj x)).app r)
            ((kKanSequence (F.obj y)).level (r + 1)).space := by
  rw [monicKPrismSpecifiedTriangleFamily, ← Category.assoc,
    kKanOriginalPrismSpecifiedTriangleFamily_lower]

end SerrePositivity.KST.SConstruction
