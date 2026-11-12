module
public import SerrePositivity.KST.SConstruction.TrivialKanTriangleLifting
public import SerrePositivity.KST.SConstruction.RelativeKanOuterSpanFamilies

/-! # 全三辺と指定境界の全二単体を保つ三角形族
概要：anodyne なパラメータ部分上の三角形を、元の三円柱を固定して延長する。
方針：内部 Hom の制限の全単射 RLP を使い、三角形境界を一度に持ち上げる。
規約：三円柱を新しく選ばず、指定部分では全二単体を厳密に保持する。
使われ方：直通列の指定比較を、全合成列パラメータへ延ばす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
variable {T U E : SSet.{u}} [KanComplex E] (j : T ⟶ U) (hj : anodyneExtensions j)
  {F G H : U ⟶ E} (a : SSet.Homotopy F G) (b : SSet.Homotopy G H)
  (c : SSet.Homotopy F H)
  (t : SSet.Edge.CompStruct
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E))
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E))
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy c)).map ((pre j).app E)))

/-- 三つの元の全円柱と、指定境界の元の全二単体を固定する相対三角形。 -/
def relativeSpecifiedTriangleFamilyData :=
  trivialKanTriangleLift ((pre j).app E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_pre_rlp_monomorphisms j hj E)
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy c)) t

/-- 同じ全三角形を、全パラメータの実二単体族として取り出す。 -/
def relativeSpecifiedTriangleFamily : U ⊗ (Δ[2] : SSet.{u}) ⟶ E :=
  uncurry (SSet.yonedaEquiv.symm (relativeSpecifiedTriangleFamilyData j hj a b c t).val.simplex)

/-- パラメータ部分上では、指定した全三角形族そのものを回収する。 -/
lemma relativeSpecifiedTriangleFamily_boundary :
    (j ▷ (Δ[2] : SSet.{u})) ≫ relativeSpecifiedTriangleFamily j hj a b c t =
      uncurry (SSet.yonedaEquiv.symm t.simplex) := by
  rw [relativeSpecifiedTriangleFamily, ← uncurry_pre_app, SSet.yonedaEquiv_symm_comp,
    (relativeSpecifiedTriangleFamilyData j hj a b c t).property]

/-- 全三角形族の 01 辺は、元の第一円柱の全時刻。 -/
lemma relativeSpecifiedTriangleFamily_first :
    (U ◁ stdSimplex.δ 2) ≫ relativeSpecifiedTriangleFamily j hj a b c t = a.h := by
  rw [relativeSpecifiedTriangleFamily, ← uncurry_natural_left,
    stdSimplex.δ_comp_yonedaEquiv_symm, (relativeSpecifiedTriangleFamilyData j hj a b c t).val.d₂]
  change uncurry (curry a.h) = _
  exact uncurry_curry _

/-- 全三角形族の 12 辺も、元の第二円柱の全時刻。 -/
lemma relativeSpecifiedTriangleFamily_second :
    (U ◁ stdSimplex.δ 0) ≫ relativeSpecifiedTriangleFamily j hj a b c t = b.h := by
  rw [relativeSpecifiedTriangleFamily, ← uncurry_natural_left,
    stdSimplex.δ_comp_yonedaEquiv_symm, (relativeSpecifiedTriangleFamilyData j hj a b c t).val.d₀]
  change uncurry (curry b.h) = _
  exact uncurry_curry _

/-- 全三角形族の 02 辺も、元の合成円柱の全時刻を変更しない。 -/
lemma relativeSpecifiedTriangleFamily_composite :
    (U ◁ stdSimplex.δ 1) ≫ relativeSpecifiedTriangleFamily j hj a b c t = c.h := by
  rw [relativeSpecifiedTriangleFamily, ← uncurry_natural_left,
    stdSimplex.δ_comp_yonedaEquiv_symm, (relativeSpecifiedTriangleFamilyData j hj a b c t).val.d₁]
  change uncurry (curry c.h) = _
  exact uncurry_curry _

end SerrePositivity.KST.SConstruction
