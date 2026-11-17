module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowThreeSimplexCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft

/-!
概要：元の twisted-arrow の辺の四つの射影の合成則。
方針：同じ三単体の計算を元の実際の辺へ移し、同じ零次の包含で端点を保つ。
規約：任意の単体集合で述べ、Kan 性や模型構造は仮定しない。
使われ方：元の corrected pairing の指定成分の単位・合成の計算。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 四つの指定辺の座標が同じなら、同じ三単体の合成等式をその辺に移す。 -/
lemma twistedSquare_composite_of_edge_coordinates {C : SSet.{u}}
    (σ : (Δ[3] : SSet.{u}) ⟶ C)
    {q x y z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x y)
    (r : SSet.Edge y z) (b : SSet.Edge q z)
    (hp : ((twistedSquareStdEdge 3 0 1 (by decide)).map σ).edge = p.edge)
    (ha : ((twistedSquareStdEdge 3 1 2 (by decide)).map σ).edge = a.edge)
    (hr : ((twistedSquareStdEdge 3 2 3 (by decide)).map σ).edge = r.edge)
    (hb : ((twistedSquareStdEdge 3 0 3 (by decide)).map σ).edge = b.edge) :
    HomotopyCategory.homMk p ≫ HomotopyCategory.homMk a ≫
      HomotopyCategory.homMk r = HomotopyCategory.homMk b := by
  have hq : σ.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) = q := by
    rw [← ((twistedSquareStdEdge 3 0 1 (by decide)).map σ).src_eq, hp, p.src_eq]
  have hx : σ.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = x := by
    rw [← ((twistedSquareStdEdge 3 0 1 (by decide)).map σ).tgt_eq, hp, p.tgt_eq]
  have hy : σ.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 2) = y := by
    rw [← ((twistedSquareStdEdge 3 1 2 (by decide)).map σ).tgt_eq, ha, a.tgt_eq]
  have hz : σ.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 3) = z := by
    rw [← ((twistedSquareStdEdge 3 2 3 (by decide)).map σ).tgt_eq, hr, r.tgt_eq]
  subst q
  subst x
  subst y
  subst z
  have ep : (twistedSquareStdEdge 3 0 1 (by decide)).map σ = p := by ext; exact hp
  have ea : (twistedSquareStdEdge 3 1 2 (by decide)).map σ = a := by ext; exact ha
  have er : (twistedSquareStdEdge 3 2 3 (by decide)).map σ = r := by ext; exact hr
  have eb : (twistedSquareStdEdge 3 0 3 (by decide)).map σ = b := by ext; exact hb
  rw [← ep, ← ea, ← er, ← eb]
  exact twistedSquare_three_composite σ

/-- 標準単体の指定辺の像と、同じ辺の Yoneda 表示を照合する。 -/
lemma twistedSquare_mapped_edge_yoneda {C : SSet.{u}} (σ : (Δ[3] : SSet.{u}) ⟶ C)
    (i j : Fin 4) (h : i ≤ j) :
    SSet.yonedaEquiv.symm (((twistedSquareStdEdge 3 i j h).map σ).edge) =
      stdSimplex.map (stdSimplex.edge.{u} 3 i j h).down ≫ σ := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map]
  rfl

/-- 元の twisted-arrow の四つの射影の式から、元の三辺の合成等式を得る。 -/
lemma twistedSquare_composite_of_projections {C : SSet.{u}}
    (s : (TwistedArrow C) _⦋1⦌)
    {q x y z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x y)
    (r : SSet.Edge y z) (b : SSet.Edge q z)
    (hp : SSet.opObjEquiv ((edgewiseLeft C).app _ s) = p.edge)
    (ha : (TwistedArrow C).δ 1 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm a.edge)
    (hr : (edgewiseRight C).app _ s = r.edge)
    (hb : (TwistedArrow C).δ 0 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm b.edge) :
    HomotopyCategory.homMk p ≫ HomotopyCategory.homMk a ≫
      HomotopyCategory.homMk r = HomotopyCategory.homMk b := by
  apply twistedSquare_composite_of_edge_coordinates (twistedSquareThreeSimplex s) p a r b
  · apply SSet.yonedaEquiv.symm.injective
    rw [twistedSquare_mapped_edge_yoneda, ← twistedSquare_left_simplex.{u, u}, hp]
  · apply SSet.yonedaEquiv.symm.injective
    rw [twistedSquare_mapped_edge_yoneda, ← twistedSquare_source_simplex.{u, u}, ha, Iso.inv_hom_id_assoc]
  · apply SSet.yonedaEquiv.symm.injective
    rw [twistedSquare_mapped_edge_yoneda, ← twistedSquare_right_simplex.{u, u}, hr]
  · apply SSet.yonedaEquiv.symm.injective
    rw [twistedSquare_mapped_edge_yoneda, ← twistedSquare_target_simplex.{u, u}, hb, Iso.inv_hom_id_assoc]

/-- 同じ合成が元の単位の合成に一致し、両端が可逆なら、内側の射は恒等射。 -/
lemma twistedSquare_unit_of_projections {C : SSet.{u}}
    (s : (TwistedArrow C) _⦋1⦌)
    {q x z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x x)
    (r : SSet.Edge x z) (b : SSet.Edge q z)
    [IsIso (HomotopyCategory.homMk p)] [IsIso (HomotopyCategory.homMk r)]
    (hp : SSet.opObjEquiv ((edgewiseLeft C).app _ s) = p.edge)
    (ha : (TwistedArrow C).δ 1 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm a.edge)
    (hr : (edgewiseRight C).app _ s = r.edge)
    (hb : (TwistedArrow C).δ 0 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm b.edge)
    (hu : HomotopyCategory.homMk b = HomotopyCategory.homMk p ≫ HomotopyCategory.homMk r) :
    HomotopyCategory.homMk a = 𝟙 (HomotopyCategory.mk x) := by
  have h := twistedSquare_composite_of_projections s p a r b hp ha hr hb
  rw [hu] at h
  apply (cancel_mono (HomotopyCategory.homMk r)).mp
  apply (cancel_epi (HomotopyCategory.homMk p)).mp
  simpa only [Category.assoc, Category.comp_id, Category.id_comp] using h

open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 次数0の左包含を、元の辺の始点の面と照合する。 -/
lemma twistedSquare_zero_left_inclusion :
    (stdSimplex.opIso ⦋0⦌).inv ≫ joinInl (Δ[0] : SSet.{u}).op Δ[0] =
      stdSimplex.δ 1 ≫ (edgewiseWeightIso 0).inv := by
  apply (cancel_mono (edgewiseWeightIso 0).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [edgewiseWeightIso_inl, Iso.inv_hom_id_assoc]
  congr 1
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  fin_cases a; rfl

/-- 次数0の右包含を、元の辺の終点の面と照合する。 -/
lemma twistedSquare_zero_right_inclusion :
    joinInr (Δ[0] : SSet.{u}).op Δ[0] =
      stdSimplex.δ 0 ≫ (edgewiseWeightIso 0).inv := by
  apply (cancel_mono (edgewiseWeightIso 0).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [edgewiseWeightIso_inr]
  congr 1
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  fin_cases a; rfl

/-- twisted-arrow の頂点を、同じ左右射影を端点とする元の辺として読む。 -/
def twistedArrowVertexEdge {C : SSet.{u}} (a : (TwistedArrow C) _⦋0⦌) :
    SSet.Edge (SSet.opObjEquiv ((edgewiseLeft C).app _ a)) ((edgewiseRight C).app _ a) where
  edge := SSet.yonedaEquiv ((edgewiseWeightIso 0).inv ≫ a)
  src_eq := by
    change C.map (SimplexCategory.δ 1).op (SSet.yonedaEquiv ((edgewiseWeightIso 0).inv ≫ a)) = _
    rw [SSet.yonedaEquiv_naturality]
    change SSet.yonedaEquiv (stdSimplex.δ 1 ≫ (edgewiseWeightIso 0).inv ≫ a) =
      SSet.opObjEquiv (SSet.opObjEquiv.symm (SSet.yonedaEquiv
        ((stdSimplex.opIso ⦋0⦌).inv ≫ joinInl _ _ ≫ a)))
    rw [Equiv.apply_symm_apply, ← Category.assoc, ← twistedSquare_zero_left_inclusion, Category.assoc]
  tgt_eq := by
    change C.map (SimplexCategory.δ 0).op (SSet.yonedaEquiv ((edgewiseWeightIso 0).inv ≫ a)) = _
    rw [SSet.yonedaEquiv_naturality]
    change SSet.yonedaEquiv (stdSimplex.δ 0 ≫ (edgewiseWeightIso 0).inv ≫ a) =
      SSet.yonedaEquiv (joinInr _ _ ≫ a)
    rw [← Category.assoc, ← twistedSquare_zero_right_inclusion]

/-- 元の重みの表示へ戻すと、同じ元の頂点を回収する。 -/
lemma twistedArrowVertexEdge_inverse {C : SSet.{u}} (a : (TwistedArrow C) _⦋0⦌) :
    (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm (twistedArrowVertexEdge a).edge = a := by
  change (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv ((edgewiseWeightIso 0).inv ≫ a)) = a
  rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

/-- 元の twisted-arrow の辺の左右射影と両頂点の辺は、同じ合成等式を満たす。 -/
lemma twistedArrowEdge_composition {C : SSet.{u}} {a b : (TwistedArrow C) _⦋0⦌}
    (s : SSet.Edge a b) :
    HomotopyCategory.homMk (SSet.Edge.ofTruncated (edgeUnop (s.map (edgewiseLeft C)).toTruncated)) ≫
      HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
        HomotopyCategory.homMk (s.map (edgewiseRight C)) =
      HomotopyCategory.homMk (twistedArrowVertexEdge b) := by
  apply twistedSquare_composite_of_projections s.edge
  · rfl
  · rw [s.src_eq, twistedArrowVertexEdge_inverse]
  · rfl
  · rw [s.tgt_eq, twistedArrowVertexEdge_inverse]
end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
