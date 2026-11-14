module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGNerveOppositeNaturality
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
/-!
概要：dg 反対圏の実 nerve を、元の dg nerve の単体的反対圏と厳密に同定する。
方針：全 HA 方程式を持つ単体反転の全単射と、任意単体作用との自然性を接続する。
規約：H⁰ の反対圏比較で代用しない。使われ方：β5 の反変 Hom の全 ∞ 関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGNerveOppositeIndex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ全実単体の符号付き反転による、dg nerve の反対圏比較同型。 -/
def dgNerveOppositeIso : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Dᵒᵖ :=
  NatIso.ofComponents
    (fun n ↦ (SSet.opObjEquiv.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplexEquiv R D n.unop.len)).toIso)
    (by
      intro n m f
      ext s
      change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex (s.pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom f.unop.toOrderHom)) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex s).pullback f.unop.toOrderHom
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom_reverse] using
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex_pullback s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom f.unop.toOrderHom))
/-- 反転は実対象の頂点を、同じ dg 反対対象の頂点へ送る。 -/
lemma opSimplex_vertex (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex (R := R) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Opposite.op x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_hom_heq _ _
/-- 同じ反対圏比較の零単体への作用は、実対象の反対操作そのもの。 -/
lemma dgNerveOppositeIso_hom_vertex (x : D) :
    (dgNerveOppositeIso R D).hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) _⦋0⦌)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Opposite.op x) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Dᵒᵖ) _⦋0⦌) :=
  opSimplex_vertex R D x
end SerrePositivity.InfinityCategories.Project.DerivedCategories
