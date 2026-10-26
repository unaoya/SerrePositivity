module

public import SerrePositivity.KST.LocalizingInvariants.FixedSpanConeFamily
public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexDenominators
public import SerrePositivity.InfinityCategories.Core.SliceConeFamilyEquivalence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexEquivalenceLifting

/-!
概要：実分母条件を持つ二終点上の実 slice と、元の固定端点 span は同値。
方針：元の slice→全錐族の比較を、同型不変な元の分母条件へ制限する。
規約：元の Verdier 列のみを使い、実族の比較の同値性を入力にしない。
使われ方：実分母・次辺族と完成分数比較の間の全関手比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の実区間の分母条件は、同じ区間の商像の可逆性と同値。 -/
lemma weakIntervalVertex_iff {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (v : ((ihom (Δ[1] : SSet.{u})).obj B.obj) _⦋0⦌) :
    intervalFunctorVertexEdge v ∈ weakEquivalences i ↔
      IsEquivalencePathVertex (((ihom (Δ[1] : SSet.{u})).map q.hom).app (Opposite.op ⦋0⦌) v) := by
  change intervalFunctorVertexEdge v ∈ weakEquivalences i ↔ IsInvertibleEdge
    (edgeOfSimplex (intervalFunctorVertexEdge
      (((ihom (Δ[1] : SSet.{u})).map q.hom).app (Opposite.op ⦋0⦌) v)))
  rw [intervalFunctorVertexEdge_postcomp]
  exact (mem_weakEquivalences_iff_invertible h
    (edgeOfSimplex (intervalFunctorVertexEdge v))).trans (isInvertibleEdge_congr rfl)

/-- 元の左脚の分母条件は、全錐族の同型で保存される。 -/
lemma markedSpanConeVertex_iff_of_vertexIso {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌)
    {a b : (coneFamily (intervalMappingBoundary x y)) _⦋0⦌} (e : VertexIso a b) :
    (intervalFunctorVertexEdge ((spanConeDenominatorFamily x y).app (Opposite.op ⦋0⦌) a) ∈
      weakEquivalences i) ↔
    (intervalFunctorVertexEdge ((spanConeDenominatorFamily x y).app (Opposite.op ⦋0⦌) b) ∈
      weakEquivalences i) := by
  rw [weakIntervalVertex_iff h, weakIntervalVertex_iff h]
  exact isEquivalencePathVertex_iff_of_vertexIso (VertexIso.map e
    (spanConeDenominatorFamily x y ≫ (ihom (Δ[1] : SSet.{u})).map q.hom))

/-- 元の全錐族への比較で、同じ実左脚が分母になる実 slice の全部分複体。 -/
def markedSpanSlice {X : SSet.{u}} (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    (sliceOver (intervalMappingBoundary x y)).Subcomplex :=
  fullSubcomplexOnVertices _ (fun v => intervalFunctorVertexEdge
    ((sliceConeFamilyMap (intervalMappingBoundary x y) ≫ spanConeDenominatorFamily x y).app
      (Opposite.op ⦋0⦌) v) ∈ W)

instance markedSpanSlice_quasicategory {X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    Quasicategory (markedSpanSlice W x y : SSet.{u}) := by
  dsimp only [markedSpanSlice]
  infer_instance

/-- 元の slice→全錐族の比較を、同じ実分母条件へ制限する。 -/
def markedSpanSliceConeComparison {X : SSet.{u}} (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    (markedSpanSlice W x y : SSet.{u}) ⟶ (markedSpanConeFamily W x y : SSet.{u}) :=
  fullSubcomplexLift _ ((markedSpanSlice W x y).ι ≫
    sliceConeFamilyMap (intervalMappingBoundary x y))
      (fun v => fullSubcomplexOnVertices_vertex v)

lemma markedSpanSliceConeComparison_ι {X : SSet.{u}} (W : Set (X _⦋1⦌))
    (x y : X _⦋0⦌) : markedSpanSliceConeComparison W x y ≫ (markedSpanConeFamily W x y).ι =
      (markedSpanSlice W x y).ι ≫ sliceConeFamilyMap (intervalMappingBoundary x y) :=
  fullSubcomplexLift_ι _ _ _

/-- 元の実分母条件への制限も、全写像空間で元の slice 比較の同値性を保持する。 -/
lemma markedSpanSliceConeComparison_isQCatEquivalence
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    IsQCatEquivalence (markedSpanSliceConeComparison (weakEquivalences i) x y) := by
  exact isQCatEquivalence_fullSubcomplexRestriction _ _
    (fun e => markedSpanConeVertex_iff_of_vertexIso h x y e)
    (sliceConeFamilyMap (intervalMappingBoundary x y))
    (isQCatEquivalence_sliceConeFamilyMap _) _
    (markedSpanSliceConeComparison_ι (weakEquivalences i) x y) (fun _ hv => hv)

/-- 元の実分母条件を持つ二終点上の実 slice から、元の固定端点 span への比較。 -/
def markedSpanSliceToFixed {X : SSet.{u}} (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    (markedSpanSlice W x y : SSet.{u}) ⟶ fixedMarkedSpans X W x y :=
  markedSpanSliceConeComparison W x y ≫ (fixedMarkedSpanConeFamilyIso X W x y).inv

/-- 元の Verdier 分母について、実 slice と元の固定端点 span の全関手比較は同値。 -/
lemma markedSpanSliceToFixed_isQCatEquivalence
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    IsQCatEquivalence (markedSpanSliceToFixed (weakEquivalences i) x y) :=
  (markedSpanSliceConeComparison_isQCatEquivalence h x y).comp
    ((qCatEquivalenceOfIso
      (fixedMarkedSpanConeFamilyIso B.obj (weakEquivalences i) x y).symm).isQCatEquivalence)

end SerrePositivity.KST.LocalizingInvariants
