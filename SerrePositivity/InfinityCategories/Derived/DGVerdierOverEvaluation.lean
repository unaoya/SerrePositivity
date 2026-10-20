module
public import SerrePositivity.InfinityCategories.Derived.SliceEvaluationVertex
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOver
public import SerrePositivity.InfinityCategories.Derived.DGQuotientLocalizingEdges
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
/-!
概要：実 Verdier 分母の普遍評価を商へ送り、元の同じ実辺を成分とする関手同型を構成する。
方針：実 slice 評価の成分公式と、商関手の実分母反転を使う。
規約：全添字の coherent な関手同型。使われ方：右 Kan 形状への逆分母図式の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
/-- 実 Verdier 分母の商像から、同じ標準商頂点への全添字の実評価ホモトピー。 -/
def dgVerdierOverQuotientEvaluationHomotopy (P : Set D) (x : D) :
    SSet.Homotopy (dgVerdierOverSource A D P x ≫ dgQuotientNerveProjection A D P)
      (SSet.const (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) :=
  stableHomotopyRetarget (functorHomotopyPostcomp
    (functorHomotopyPrecomp (roofSliceEvaluationHomotopy (X := dgNerve A D) (Simplex.vertex x))
      (dgVerdierOver A D P x).ι) (dgQuotientNerveProjection A D P)) rfl (by
        rw [SSet.comp_const, SSet.const_comp]
        exact congrArg (fun a => SSet.const a)
          (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x))
/-- 全添字の評価ホモトピーの各成分は、元の同じ実分母の商像そのもの。 -/
lemma dgVerdierOverQuotientEvaluationHomotopy_vertex (P : Set D) (x : D)
    (s : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (dgVerdierOverQuotientEvaluationHomotopy A D P x) s).edge =
      (dgQuotientNerveProjection A D P).app (Opposite.op ⦋1⦌)
        (roofPointSliceVertexEdge ((SSet.yonedaEquiv (X := dgNerve A D)).symm
          (Simplex.vertex x)) s.val).edge := by
  exact congrArg ((dgQuotientNerveProjection A D P).app (Opposite.op ⦋1⦌))
    (roofSliceEvaluationHomotopy_vertex_edge (X := dgNerve A D) (Simplex.vertex x) s.val)
/-- 実分母の商での普遍評価は、全ての成分が実際に可逆。 -/
lemma dgVerdierOverQuotientEvaluationHomotopy_invertible [IsDGPretriangulated A D]
    (P : Set D) (hP : DGQuotient.localKFlat A D P) (x : D)
    (s : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge
        (dgVerdierOverQuotientEvaluationHomotopy A D P x) s).toTruncated := by
  have hs : (roofPointSliceVertexEdge ((SSet.yonedaEquiv (X := dgNerve A D)).symm
      (Simplex.vertex x)) s.val).edge ∈ dgVerdierEdges A D P :=
    fullSubcomplexOnVertices_vertex s
  exact (isInvertibleEdge_congr
    (dgVerdierOverQuotientEvaluationHomotopy_vertex A D P x s)).mpr
      (dgQuotientNerveProjection_invertsVerdierEdges A D P hP hs)
/-- 実分母図式の商像から標準商頂点への、全添字にわたる一つの関手同型。 -/
def dgVerdierOverQuotientEvaluationIso [IsDGPretriangulated A D]
    (P : Set D) (hP : DGQuotient.localKFlat A D P) (x : D) :
    FunctorIso (dgVerdierOverSource A D P x ≫ dgQuotientNerveProjection A D P)
      (SSet.const (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) :=
  functorIsoOfPointwiseInvertibleHomotopy (dgVerdierOverQuotientEvaluationHomotopy A D P x)
    (dgVerdierOverQuotientEvaluationHomotopy_invertible A D P hP x)

/-- 任意標的での実分母の全添字の評価ホモトピー。 -/
def dgVerdierOverEvaluationHomotopy (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) :
    SSet.Homotopy (dgVerdierOverSource A D P x ≫ F)
      (SSet.const (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))) :=
  stableHomotopyRetarget (functorHomotopyPostcomp
    (functorHomotopyPrecomp (roofSliceEvaluationHomotopy (X := dgNerve A D) (Simplex.vertex x))
      (dgVerdierOver A D P x).ι) F) rfl (by
        rw [SSet.comp_const, SSet.const_comp])
omit [Small.{u} D] in
/-- 任意標的での評価成分も、元の同じ実分母の像そのもの。 -/
lemma dgVerdierOverEvaluationHomotopy_vertex (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (s : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (dgVerdierOverEvaluationHomotopy A D P x F) s).edge =
      F.app (Opposite.op ⦋1⦌)
        (roofPointSliceVertexEdge ((SSet.yonedaEquiv (X := dgNerve A D)).symm
          (Simplex.vertex x)) s.val).edge := by
  exact congrArg (F.app (Opposite.op ⦋1⦌))
    (roofSliceEvaluationHomotopy_vertex_edge (X := dgNerve A D) (Simplex.vertex x) s.val)
omit [Small.{u} D] in
/-- 任意反転標的での全添字評価は、指定した実成分そのものが可逆。 -/
lemma dgVerdierOverEvaluationHomotopy_invertible (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (s : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge (dgVerdierOverEvaluationHomotopy A D P x F) s).toTruncated := by
  have hs : (roofPointSliceVertexEdge ((SSet.yonedaEquiv (X := dgNerve A D)).symm
      (Simplex.vertex x)) s.val).edge ∈ dgVerdierEdges A D P :=
    fullSubcomplexOnVertices_vertex s
  exact (isInvertibleEdge_congr (dgVerdierOverEvaluationHomotopy_vertex A D P x F s)).mpr (hF hs)
/-- 任意の実分母反転関手の実分母図式は、全添字で元の対象の定値図式に同型。 -/
def dgVerdierOverEvaluationIso (P : Set D) (x : D) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    FunctorIso (dgVerdierOverSource A D P x ≫ F)
      (SSet.const (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))) :=
  functorIsoOfPointwiseInvertibleHomotopy (dgVerdierOverEvaluationHomotopy A D P x F)
    (dgVerdierOverEvaluationHomotopy_invertible A D P x F hF)
end SerrePositivity.InfinityCategories
