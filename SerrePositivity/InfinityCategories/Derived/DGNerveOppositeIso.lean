module
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerveOppositeData DGNerveOppositeIndex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 同じ全実単体の符号付き反転による、dg nerve の反対圏比較同型。 -/
def dgNerveOppositeIso : (dgNerve R D).op ≅ dgNerve R Dᵒᵖ :=
  NatIso.ofComponents
    (fun n ↦ (SSet.opObjEquiv.trans (simplexEquiv R D n.unop.len)).toIso)
    (by
      intro n m f
      ext s
      change opSimplex (s.pullback (reverseOrderHom f.unop.toOrderHom)) =
        (opSimplex s).pullback f.unop.toOrderHom
      simpa only [reverseOrderHom_reverse] using
        opSimplex_pullback s (reverseOrderHom f.unop.toOrderHom))
/-- 反転は実対象の頂点を、同じ dg 反対対象の頂点へ送る。 -/
lemma opSimplex_vertex (x : D) :
    opSimplex (R := R) (Simplex.vertex x) = Simplex.vertex (Opposite.op x) := by
  apply Simplex.ext
  apply SimplexData.ext
  · rfl
  · exact zero_hom_heq _ _
/-- 同じ反対圏比較の零単体への作用は、実対象の反対操作そのもの。 -/
lemma dgNerveOppositeIso_hom_vertex (x : D) :
    (dgNerveOppositeIso R D).hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (Simplex.vertex x : (dgNerve R D) _⦋0⦌)) =
        (Simplex.vertex (Opposite.op x) : (dgNerve R Dᵒᵖ) _⦋0⦌) :=
  opSimplex_vertex R D x
end SerrePositivity.InfinityCategories
