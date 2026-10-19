module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverVertexInverse
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTriangle
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDenominators

/-! # 実 Verdier over 圏の細分辺も実分母である

概要：実分母 over の始域射影は、全ての一単体を元の Verdier 分母へ送る。
方針：over の指定二単体の二脚を分母条件で判定し、二対三性を適用する。
規約：細分は厳密閉射のものに限らない。使われ方：商内の屋根添字の全辺の反転。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 実分母 over の任意の細分辺の始域射影は、再び実 Verdier 分母。 -/
lemma dgVerdierOverSource_edge_mem (P : Set D) (x : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋1⦌) :
    (dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) σ ∈ dgVerdierEdges A D P := by
  let a := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let τ := roofPointSliceTriangle a σ.val
  have h (i : Fin 2) : SSet.yonedaEquiv (stdSimplex.δ i.castSucc ≫ τ) ∈
      dgVerdierEdges A D P := by
    rw [roofPointSliceTriangle_leg]
    exact dgVerdierOverVertex_mem A D P x ((dgVerdierOver A D P x : SSet).δ i σ)
  have ht := (dgVerdierEdges_twoOfThree A D P τ).2.2 (h 0) (h 1)
  change SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫
    roofPointSliceTriangle a σ.val) ∈ dgVerdierEdges A D P at ht
  rw [roofPointSliceTriangle_base] at ht
  exact ht

/-- 元の分母を反転する任意の関手は、実屋根添字の全細分辺を反転する。 -/
lemma dgVerdierOverSource_inverts_of_inverts (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    InvertsEdges (dgVerdierOverSource A D P x ≫ F) Set.univ := by
  intro σ _
  exact (isInvertibleEdge_congr (show
    ((edgeOfSimplex ((dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) σ)).map
      ((truncation 2).map F)).edge =
    ((edgeOfSimplex σ).map ((truncation 2).map (dgVerdierOverSource A D P x ≫ F))).edge
      from rfl)).mp (hF (dgVerdierOverSource_edge_mem A D P x σ))

/-- 平坦商での実屋根の始域写像は、添字の全ての辺を反転する。 -/
lemma dgVerdierOverSource_quotient_inverts (P : Set D) (x : D)
    (hP : DGQuotient.localKFlat A D P) :
    InvertsEdges (dgVerdierOverSource A D P x ≫ dgQuotientNerveProjection A D P) Set.univ :=
  dgVerdierOverSource_inverts_of_inverts A D P x _
    (dgQuotientNerveProjection_invertsVerdierEdges A D P hP)

/-- 平坦分解後の商でも、実屋根の始域写像は添字の全ての辺を反転する。 -/
lemma dgVerdierOverSource_resolvedQuotient_inverts (P : Set D) (x : D) :
    InvertsEdges (dgVerdierOverSource A D P x ≫ resolvedDGQuotientFunctor A D P) Set.univ :=
  dgVerdierOverSource_inverts_of_inverts A D P x _
    (resolvedDGQuotientFunctor_invertsVerdierEdges A D P)

end SerrePositivity.InfinityCategories
