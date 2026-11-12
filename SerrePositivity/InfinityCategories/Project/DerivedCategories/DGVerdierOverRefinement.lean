module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOverVertexInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofSliceTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDenominators

/-! # 実 Verdier over 圏の細分辺も実分母である

概要：実分母 over の始域射影は、全ての一単体を元の Verdier 分母へ送る。
方針：over の指定二単体の二脚を分母条件で判定し、二対三性を適用する。
規約：細分は厳密閉射のものに限らない。使われ方：商内の屋根添字の全辺の反転。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 実分母 over の任意の細分辺の始域射影は、再び実 Verdier 分母。 -/
lemma dgVerdierOverSource_edge_mem (P : Set D) (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) σ ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := by
  let a := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let τ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a σ.val
  have h (i : Fin 2) : SSet.yonedaEquiv (stdSimplex.δ i.castSucc ≫ τ) ∈
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertex_mem A D P x ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i σ)
  have ht := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges_twoOfThree A D P τ).2.2 (h 0) (h 1)
  change SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a σ.val) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P at ht
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_base] at ht
  exact ht

/-- 元の分母を反転する任意の関手は、実屋根添字の全細分辺を反転する。 -/
lemma dgVerdierOverSource_inverts_of_inverts (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F) Set.univ := by
  intro σ _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) σ)).map
      ((truncation 2).map F)).edge =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex σ).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F))).edge
      from rfl)).mp (hF (dgVerdierOverSource_edge_mem A D P x σ))

/-- 平坦商での実屋根の始域写像は、添字の全ての辺を反転する。 -/
lemma dgVerdierOverSource_quotient_inverts (P : Set D) (x : D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) Set.univ :=
  dgVerdierOverSource_inverts_of_inverts A D P x _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_invertsVerdierEdges A D P hP)

/-- 平坦分解後の商でも、実屋根の始域写像は添字の全ての辺を反転する。 -/
lemma dgVerdierOverSource_resolvedQuotient_inverts (P : Set D) (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P) Set.univ :=
  dgVerdierOverSource_inverts_of_inverts A D P x _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_invertsVerdierEdges A D P)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
