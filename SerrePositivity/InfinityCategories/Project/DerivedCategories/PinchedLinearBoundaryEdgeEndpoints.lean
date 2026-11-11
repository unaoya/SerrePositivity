module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedLinearBoundaryEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison

/-! # 比較原始元からの実 pinched 辺の端点

概要：原始元から作った線形辺の両端を、入力した零次元単体と厳密に同定する。
方針：唯一の成分による外延性と線形表示の面の自然性を使う。
規約：最上位比較は第二単体から第一単体への辺を与える。使われ方：相対比較の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedLinearBoundaryEdgeEndpoints
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 零次元線形単体は唯一の成分で決まる。 -/
lemma pinchedLinearVertexValue_injective :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue (A := A) (x := x) (y := y)) := by
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
lemma pinchedLinearBoundaryEdge_pullback (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0)
    (e : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (-1))
    (he : (_root_.SerrePositivity.DifferentialGraded.homObject A D x y).d (-1) 0 e =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue t - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue s) (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback j.succAboveOrderEmb.toOrderHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge s t e he) =
      if j = 0 then t else s := by
  apply pinchedLinearVertexValue_injective
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge s t e he).val).component Finset.univ 0 Finset.univ_nonempty _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  fin_cases j <;>
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdgeData,
      Finset.univ_unique, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue]

/-- 指定原始元を持つ、入力二頂点の間の実 pinched 辺。 -/
def pinchedBoundaryPrimitiveEdge (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0)
    (e : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (-1))
    (he : (_root_.SerrePositivity.DifferentialGraded.homObject A D x y).d (-1) 0 e =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue t - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y).Edge s.toPinched t.toPinched := by
  refine SSet.Edge.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge s t e he).toPinched ?_ ?_
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y 0).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge s t e he).toPinched.pullback (SimplexCategory.δ 1)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s.toPinched
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback (1 : Fin 2).succAboveOrderEmb.toOrderHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge s t e he) = s
    exact pinchedLinearBoundaryEdge_pullback s t e he 1
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y 0).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge s t e he).toPinched.pullback (SimplexCategory.δ 0)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t.toPinched
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback (0 : Fin 2).succAboveOrderEmb.toOrderHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge s t e he) = t
    exact pinchedLinearBoundaryEdge_pullback s t e he 0

/-- 構成した実辺の最上位成分は、指定された原始元そのもの。 -/
lemma pinchedBoundaryPrimitiveEdge_top (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0)
    (e : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (-1))
    (he : (_root_.SerrePositivity.DifferentialGraded.homObject A D x y).d (-1) 0 e =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue t - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (pinchedBoundaryPrimitiveEdge s t e he).edge).val.component
      Finset.univ (-1) Finset.univ_nonempty (by decide) = e := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge s t e he).toPinched).val.component
    Finset.univ (-1) Finset.univ_nonempty (by decide) = e
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdge, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearBoundaryEdgeData, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component]

/-- 零次元の最上位比較を、指定方向の実 pinched 辺へ昇格する。 -/
def PinchedTopComparison.edge_zero {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y).Edge t.toPinched s.toPinched :=
  pinchedBoundaryPrimitiveEdge t s c.primitive c.differential_primitive

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedLinearBoundaryEdgeEndpoints.PinchedTopComparison (edge_zero)


/-- 零次元比較の指定原始元から、実際の単体的ホモトピーを得る。 -/
def PinchedTopComparison.homotopy_zero {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedLinearBoundaryEdgeEndpoints.PinchedTopComparison (homotopy_zero)


end SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedLinearBoundaryEdgeEndpoints
