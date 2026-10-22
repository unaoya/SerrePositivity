module

public import SerrePositivity.KST.NonConnective.DGKappaSwindle
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransVertex
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedFunctorExact

/-!
概要：同じ dg cone の厳密 swindle を、元の dg nerve 上の実関手同型として保持する。
方針：指定した全斉次自然変換の実ホモトピーと、同じ閉同型の可逆性を使う。
規約：F1 の Ind 安定性を仮定しない。入力の κ-compact dg 模型の存在は依然明示入力。
使われ方：K の加法性に渡す元の id ⊕ T ≃ T の ∞ 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open DGNerve.HomotopyComparison
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ dg cone の実可算直和関手は、native nerve 上で完全。 -/
lemma dgKappaConeCountableSum_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgKappaConeCountableSum R D I)) :=
  dgPretriangulatedFunctor_isExactFunctor R (DGKappaCone R D I) (DGKappaCone R D I)
    (dgKappaConeCountableSum R D I)

/-- 同じ dg cone の id ⊕ T も、native nerve 上で完全。 -/
lemma dgKappaSwindleSource_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgKappaSwindleSource R D I)) :=
  dgPretriangulatedFunctor_isExactFunctor R (DGKappaCone R D I) (DGKappaCone R D I)
    (dgKappaSwindleSource R D I)

/-- 元の閉 dg 同型の同じ実辺は、同じ dg cone の nerve で可逆。 -/
lemma dgKappaSwindleComponent_isInvertible (X : DGKappaCone R D I) :
    IsInvertibleEdge (X := dgNerve R (DGKappaCone R D I)) (dgClosedEdge R (DGKappaCone R D I)
      (dgKappaSwindleComponentIso R D I X).hom) := by
  let e := dgClosedEdge R (DGKappaCone R D I) (dgKappaSwindleComponentIso R D I X).hom
  have h : IsIso ((toH0 R (DGKappaCone R D I)).map
      (Truncated.HomotopyCategory₂.homMk e)) := by
    rw [toH0_homMk, dgClosedEdge_closed]
    infer_instance
  have : IsIso (Truncated.HomotopyCategory₂.homMk e) :=
    isIso_of_reflects_iso _ (toH0 R (DGKappaCone R D I))
  exact (edgeToPathHomotopyCategory _).map_isIso (Truncated.HomotopyCategory₂.homMk e)

/-- 元の厳密 swindle の同じ実ホモトピーは、全頂点で可逆な辺を持つ。 -/
lemma dgKappaSwindleHomotopy_pointwise (z : (dgNerve R (DGKappaCone R D I)) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge (dgKappaSwindleStrictHom R D I).homotopy
      z).toTruncated := by
  obtain ⟨X, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  have he := dgStrictNatTrans_homotopy_vertex_edge (dgKappaSwindleStrictHom R D I) X
  rw [dgKappaSwindleStrictHom_app] at he
  apply (isInvertibleEdge_congr he).mpr
  exact dgKappaSwindleComponent_isInvertible R D I X

/-- 同じ κ-compact dg cone 内の id ⊕ T と T の、実関手同型。 -/
def dgKappaSwindleInfinityIso :
    FunctorIso (dgNerve.map (dgKappaSwindleSource R D I))
      (dgNerve.map (dgKappaConeCountableSum R D I)) :=
  functorIsoOfPointwiseInvertibleHomotopy (dgKappaSwindleStrictHom R D I).homotopy
    (dgKappaSwindleHomotopy_pointwise R D I)

end SerrePositivity.KST.NonConnective
