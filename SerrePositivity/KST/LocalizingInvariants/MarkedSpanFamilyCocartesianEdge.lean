module

public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanCocartesianEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.MarkedSpanFamilyInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge

/-!
概要：第一終点固定の span 族で、共通始点の成分が可逆な射は cocartesian。
方針：二終点制限の外ホーン充填を、定値第一終点と指定第二終点の境界上で行う。
規約：元の射と全ての境界を保つ。使われ方：cocartesian lift の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma markedSpan_source_of_boundary_diagram {A X : SSet.{u}} (W : Set (X _⦋1⦌))
    (F : A ⟶ markedSpans X W) (f g : A ⟶ X)
    (h : F ≫ markedSpanBoundary X W = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g)) :
    F ≫ markedSpanSource X W = f := by
  have hh := congrArg (fun k : A ⟶ (ihom (boundary 1 : SSet.{u})).obj X =>
    k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 2),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 0⟩ : (boundary 1 : SSet.{u}) _⦋0⦌)) h
  simpa only [Category.assoc, markedSpanBoundary_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.intervalBoundaryCurry_source] using hh

lemma markedSpan_target_of_boundary_diagram {A X : SSet.{u}} (W : Set (X _⦋1⦌))
    (F : A ⟶ markedSpans X W) (f g : A ⟶ X)
    (h : F ≫ markedSpanBoundary X W = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g)) :
    F ≫ markedSpanTarget X W = g := by
  have hh := congrArg (fun k : A ⟶ (ihom (boundary 1 : SSet.{u})).obj X =>
    k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 2),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 1⟩ : (boundary 1 : SSet.{u}) _⦋0⦌)) h
  simpa only [Category.assoc, markedSpanBoundary_target, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.intervalBoundaryCurry_target] using hh

def markedSpanFamilyApex (X : SSet.{u}) (W : Set (X _⦋1⦌)) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x ⟶ X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanApex X W

lemma hasCocartesianHornLifting_markedSpanFamilyProjection_of_apex
    {X : SSet.{u}} [Quasicategory X] (W : Set (X _⦋1⦌)) (x : X _⦋0⦌)
    {f g : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x)) f g)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (markedSpanFamilyApex X W x)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) e := by
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x
  let e' := e.map ((truncation 2).map r)
  have he' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e'.map ((truncation 2).map (markedSpanApex X W))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e.map ((truncation 2).map (markedSpanFamilyApex X W x)))
      (f := e'.map ((truncation 2).map (markedSpanApex X W))) rfl).mp he
  have hc := hasCocartesianHornLifting_markedSpanBoundary_of_apex W e' he'
  intro m σ β hσ hw
  let d := curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (SSet.const x : Δ[m + 2] ⟶ X) β)
  have hd : (σ ≫ r) ≫ markedSpanBoundary X W = (horn (m + 2) 0).ι ≫ d := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily_boundary]
    dsimp only [d]
    rw [← curry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, SSet.comp_const, hw]
  obtain ⟨G, hG, hGb⟩ := hc m (σ ≫ r) d
    (congrArg (r.app (Opposite.op ⦋1⦌)) hσ) hd
  have hs : G ≫ markedSpanSource X W = SSet.const x :=
    markedSpan_source_of_boundary_diagram W G _ _ hGb
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (markedSpanSource X W) x G hs
  have hF : F ≫ r = G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  refine ⟨F, ?_, ?_⟩
  · have : Mono r := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.vertexFiberι_mono _ _
    apply (cancel_mono r).mp
    rw [Category.assoc, hF]
    exact hG
  · change (F ≫ r) ≫ markedSpanTarget X W = β
    rw [hF]
    exact markedSpan_target_of_boundary_diagram W G _ _ hGb

lemma isCocartesianEdge_markedSpanFamilyProjection_of_apex
    {X : SSet.{u}} [Quasicategory X] (W : Set (X _⦋1⦌)) (x : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x) _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map
      ((truncation 2).map (markedSpanFamilyApex X W x)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) e := by
  intro n a b ha sq
  obtain ⟨F, hF, hFp⟩ := hasCocartesianHornLifting_markedSpanFamilyProjection_of_apex W x
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e) he n a b ha sq.w
  exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFp }

end SerrePositivity.KST.LocalizingInvariants
