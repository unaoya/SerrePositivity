module
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearBoundaryEdge
public import SerrePositivity.InfinityCategories.Derived.PinchedTopComparison

/-! # 比較原始元からの実 pinched 辺の端点

概要：原始元から作った線形辺の両端を、入力した零次元単体と厳密に同定する。
方針：唯一の成分による外延性と線形表示の面の自然性を使う。
規約：最上位比較は第二単体から第一単体への辺を与える。使われ方：相対比較の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 零次元線形単体は唯一の成分で決まる。 -/
lemma pinchedLinearVertexValue_injective :
    Function.Injective (pinchedLinearVertexValue (A := A) (x := x) (y := y)) := by
  intro s t he
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  have hfull : J = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun j => by
    obtain ⟨a, ha⟩ := hJ
    have haj : a = j := by omega
    simpa only [haj] using ha)
  subst J
  have hk0 : k = 0 := by simpa using hk
  subst hk0
  exact he

/-- 線形辺の二つの面は、指定された両端そのもの。 -/
lemma pinchedLinearBoundaryEdge_pullback (s t : LinearSimplex A x y 0)
    (e : GradedHom A x y (-1))
    (he : (homObject A D x y).d (-1) 0 e =
      pinchedLinearVertexValue t - pinchedLinearVertexValue s) (j : Fin 2) :
    LinearSimplex.pullback j.succAboveOrderEmb.toOrderHom (pinchedLinearBoundaryEdge s t e he) =
      if j = 0 then t else s := by
  apply pinchedLinearVertexValue_injective
  change (LinearData.pullback j.succAboveOrderEmb.toOrderHom
    (pinchedLinearBoundaryEdge s t e he).val).component Finset.univ 0 Finset.univ_nonempty _ = _
  rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  fin_cases j <;>
    simp [LinearData.component, pinchedLinearBoundaryEdge, pinchedLinearBoundaryEdgeData,
      Finset.univ_unique, pinchedLinearVertexValue]

/-- 指定原始元を持つ、入力二頂点の間の実 pinched 辺。 -/
def pinchedBoundaryPrimitiveEdge (s t : LinearSimplex A x y 0)
    (e : GradedHom A x y (-1))
    (he : (homObject A D x y).d (-1) 0 e =
      pinchedLinearVertexValue t - pinchedLinearVertexValue s) :
    (DGNerve.pinchedHom A D x y).Edge s.toPinched t.toPinched := by
  refine SSet.Edge.mk (pinchedLinearBoundaryEdge s t e he).toPinched ?_ ?_
  · apply (linearEquiv x y 0).injective
    change toLinearSimplex
      ((pinchedLinearBoundaryEdge s t e he).toPinched.pullback (SimplexCategory.δ 1)) =
        toLinearSimplex s.toPinched
    rw [toLinearSimplex_pullback, LinearSimplex.toLinearSimplex_toPinched,
      LinearSimplex.toLinearSimplex_toPinched]
    change LinearSimplex.pullback (1 : Fin 2).succAboveOrderEmb.toOrderHom
      (pinchedLinearBoundaryEdge s t e he) = s
    exact pinchedLinearBoundaryEdge_pullback s t e he 1
  · apply (linearEquiv x y 0).injective
    change toLinearSimplex
      ((pinchedLinearBoundaryEdge s t e he).toPinched.pullback (SimplexCategory.δ 0)) =
        toLinearSimplex t.toPinched
    rw [toLinearSimplex_pullback, LinearSimplex.toLinearSimplex_toPinched,
      LinearSimplex.toLinearSimplex_toPinched]
    change LinearSimplex.pullback (0 : Fin 2).succAboveOrderEmb.toOrderHom
      (pinchedLinearBoundaryEdge s t e he) = t
    exact pinchedLinearBoundaryEdge_pullback s t e he 0

/-- 構成した実辺の最上位成分は、指定された原始元そのもの。 -/
lemma pinchedBoundaryPrimitiveEdge_top (s t : LinearSimplex A x y 0)
    (e : GradedHom A x y (-1))
    (he : (homObject A D x y).d (-1) 0 e =
      pinchedLinearVertexValue t - pinchedLinearVertexValue s) :
    (toLinearSimplex (pinchedBoundaryPrimitiveEdge s t e he).edge).val.component
      Finset.univ (-1) Finset.univ_nonempty (by decide) = e := by
  change (toLinearSimplex (pinchedLinearBoundaryEdge s t e he).toPinched).val.component
    Finset.univ (-1) Finset.univ_nonempty (by decide) = e
  rw [LinearSimplex.toLinearSimplex_toPinched]
  simp [pinchedLinearBoundaryEdge, pinchedLinearBoundaryEdgeData, LinearData.component]

/-- 零次元の最上位比較を、指定方向の実 pinched 辺へ昇格する。 -/
def PinchedTopComparison.edge_zero {s t : LinearSimplex A x y 0}
    (c : PinchedTopComparison s t) : (DGNerve.pinchedHom A D x y).Edge t.toPinched s.toPinched :=
  pinchedBoundaryPrimitiveEdge t s c.primitive c.differential_primitive

/-- 零次元比較の指定原始元から、実際の単体的ホモトピーを得る。 -/
def PinchedTopComparison.homotopy_zero {s t : LinearSimplex A x y 0}
    (c : PinchedTopComparison s t) :
    SSet.Homotopy (SSet.yonedaEquiv.symm t.toPinched) (SSet.yonedaEquiv.symm s.toPinched) where
  h := CartesianMonoidalCategory.snd _ _ ≫ SSet.yonedaEquiv.symm c.edge_zero.edge
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_snd, SSet.const_comp, SSet.yonedaEquiv_symm_zero]
    congr 1
    exact c.edge_zero.src_eq
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_snd, SSet.const_comp, SSet.yonedaEquiv_symm_zero]
    congr 1
    exact c.edge_zero.tgt_eq
  rel := by
    ext n z
    change ((⊥ : (Δ[0] : SSet.{max u v}).Subcomplex).obj n) × (Δ[1] : SSet).obj n at z
    have hz := z.1.property
    change False at hz
    exact hz.elim

end SerrePositivity.InfinityCategories
