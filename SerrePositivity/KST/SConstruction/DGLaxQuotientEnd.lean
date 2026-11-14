module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.DGPointedQuotientEndZero
public import SerrePositivity.KST.SConstruction.DGPointedQuotientEndExtension
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Category
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedZeroVertex

/-! # 元の dg gluing の対角商と (0,b,0) の実 dg End
概要：元の零対象・右対象・実対角関手を保持し、その対角像の商の指定 End を構成する。
方針：全 gluing 複体と元の path 商を使い、同じ零比較を持つ指定対象を商へ送る。
規約：右対象の生成性・Morita 比較・具体的 ⊙ 同定は未主張。使われ方：LT §1.2 の模型。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (P : Type t) [_root_.SerrePositivity.DifferentialGraded.DGCategory R P]

/-- 元の dg gluing の実対角関手と、指定した (0,b,0) のためのデータ。 -/
structure DGLaxQuotientEndInput where
  diagonal : DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  leftZero : C
  leftZero_isZero : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex leftZero)
  rightPoint : D

namespace DGLaxQuotientEndInput
variable {R C D M P} (d : DGLaxQuotientEndInput R C D M P)

/-- 元の閉零圏の実零対象から、同じ実対角・右対象を持つ入力を構成する。 -/
def ofClosedZero (j : DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) (z : C)
    (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)) (b : D) :
    DGLaxQuotientEndInput R C D M P where
  diagonal := j
  leftZero := z
  leftZero_isZero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_of_closed_isZero z hz
  rightPoint := b

/-- 元の零左成分・元の右対象・零比較を保持する、実 gluing 対象 (0,b,0)。 -/
def point : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M := ⟨d.leftZero, d.rightPoint, 0⟩

omit [Small.{u} D] in
/-- 指定した gluing 対象の左成分は、元の零対象そのもの。 -/
lemma point_left : d.point.left = d.leftZero := rfl

omit [Small.{u} D] in
/-- 指定した gluing 対象の右成分は、元の右対象そのもの。 -/
lemma point_right : d.point.right = d.rightPoint := rfl

omit [Small.{u} D] in
/-- 指定した gluing 対象の比較は、元の双加群の閉零元そのもの。 -/
lemma point_comparison : d.point.gluing = 0 := rfl

omit [Small.{u} D] in
/-- 指定した同じ左成分は、元の dg nerve の零対象。 -/
lemma point_left_isZero : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex d.point.left) :=
  d.leftZero_isZero

/-- 元の実対角像を消す、同じ dg gluing の Drinfeld 商の対象。 -/
abbrev quotientObject := PointedDGQuotientObject R d.diagonal

/-- 同じ実商での指定対象 (0,b,0) の、全 dg End の一対象模型。 -/
abbrev endObject := PointedDGQuotientEndObject R d.diagonal d.point

/-- 元の gluing から、元の実対角像を消す同じ商への実 dg 関手。 -/
def projection : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) d.quotientObject :=
  pointedDGQuotientProjection R d.diagonal

/-- 同じ (0,b,0) の全 dg End から、元の実商への包含。 -/
def endInclusion : _root_.SerrePositivity.DifferentialGraded.DGFunctor R d.endObject d.quotientObject :=
  pointedDGQuotientEndInclusion R d.diagonal d.point

/-- 同じ (0,b,0) の元の End から、その実商での End への実 dg 射。 -/
def endUnitMap : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.EndomorphismObject d.point) d.endObject :=
  pointedDGQuotientEndUnitMap R d.diagonal d.point

/-- 同じ End の全 Hom は、元の指定点の同じ非有界 path 商複体。 -/
lemma end_hom (x y : d.endObject) : _root_.SerrePositivity.DifferentialGraded.homObject R d.endObject x y =
    DGQuotient.quotientHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
      (dgQuotientImage R d.diagonal) d.point d.point := rfl

/-- 元の対角像は、同じ指定 ε により実商の dg nerve の零対象になる。 -/
lemma diagonal_isZero (a : P) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R d.quotientObject)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (d.projection.obj (d.diagonal.obj a))) :=
  pointedDGQuotientDiagonal_isZero R d.diagonal a

end DGLaxQuotientEndInput
end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Construction §1 ⊙" (partial := component) "仮定：可換基礎環上の dg 圏、指定対角・左零・右代表（Lean が強い）。結論：(0,b,0) の dg 商での自己準同型とその dg 代数模型。一般の E₁ 環スペクトル版との比較は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.DGLaxQuotientEndInput.endObject
