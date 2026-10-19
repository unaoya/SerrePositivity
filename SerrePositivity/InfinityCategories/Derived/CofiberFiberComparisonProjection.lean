module
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberComparisonSlice
public import SerrePositivity.InfinityCategories.Core.RightFibration

/-! # 錐比較辺の射影は明示的な比較写像

概要：slice の実際の比較辺を射影した一単体を cofiberFiberLift の辺と同定する。
方針：join の先頭を左セルの先頭二頂点で計算し、比較単体の最初の辺を読む。
規約：端点の等式だけに依存する。使われ方：D7 の比較辺の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial

/-- 左セルの最初の辺は join の左因子。 -/
lemma cospanJoinLeft_firstEdge :
    SSet.stdSimplex.map (SimplexCategory.mkHom (joinLeftOrderHom 1 1)) ≫
      cospanJoinLeft.{u} 1 = joinInl Δ[1] (SSet.horn 2 2 : SSet.{u}) := by
  unfold cospanJoinLeft
  rw [← joinStdSimplexIso_inl]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, joinInl_joinMap, Category.id_comp]

variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 比較 join 写像の左因子への制限は明示的な比較射の辺。 -/
lemma cofiberFiberComparisonJoin_prefix (f : A ⟶ B) (g : A ⟶ C) :
    joinInl (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ≫ cofiberFiberComparisonJoin f g =
      SSet.yonedaEquiv.symm (complexEdge (cofiberFiberLift f g)).edge := by
  rw [← cospanJoinLeft_firstEdge, Category.assoc, cofiberFiberComparisonJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  exact prepend_triangle_firstEdge _ _

/-- 実際の slice 比較辺を射影すると明示的比較射と同じ一単体になる。 -/
lemma cofiberFiberComparisonSliceEdge_projection (f : A ⟶ B) (g : A ⟶ C) :
    ((cofiberFiberComparisonSliceEdge f g).map ((SSet.truncation 2).map
      (sliceOverProjection (pullbackCospan (standardFiberSquare
        (pushoutInclusionB f g) (pushoutInclusionC f g)))))).edge =
      (complexEdge (cofiberFiberLift f g)).edge := by
  change (sliceOverProjection (pullbackCospan (standardFiberSquare
    (pushoutInclusionB f g) (pushoutInclusionC f g)))).app _
    (SSet.yonedaEquiv (sliceOverCurry (cofiberFiberComparisonJoin f g)
      (cofiberFiberComparisonJoin_fixed f g))) = _
  rw [← SSet.yonedaEquiv_comp, sliceOverCurry_projection, cofiberFiberComparisonJoin_prefix]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories
