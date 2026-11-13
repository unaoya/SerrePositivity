module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanFamilies
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-!
概要：零終点 span の可縮性と、固定した実 span 上の零隅四角形の始対象。
方針：二辺の相対持ち上げ、全制限写像、同じ厳密 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def IsZeroOuterSpanVertex {X : SSet.{u}}
    (v : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) v) ∧
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (((pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋0⦌) v)
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpans (X : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
    IsZeroOuterSpanVertex : SSet.{u})
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpanLeftArrow (X : SSet.{u}) : zeroOuterSpans X ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrows X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroOuterSpanVertex).ι ≫ (pre horn₂₀.ι₀₁).app X)
    (fun v ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).1)
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpanRightArrow (X : SSet.{u}) : zeroOuterSpans X ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrows X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroOuterSpanVertex).ι ≫ (pre horn₂₀.ι₀₂).app X)
    (fun v ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).2)
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpanSource (X : SSet.{u}) : zeroOuterSpans X ⟶ X :=
  zeroOuterSpanLeftArrow X ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroOuterSpanRightArrow_source (X : SSet.{u}) :
    zeroOuterSpanRightArrow X ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X = zeroOuterSpanSource X := by
  simp only [zeroOuterSpanSource, zeroOuterSpanRightArrow, zeroOuterSpanLeftArrow,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpanFamilyOfArrows {A X : SSet.{u}} (L R : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrows X)
    (h : L ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X = R ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X) :
    A ⟶ zeroOuterSpans X := by
  let L' := L ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow).ι
  let R' := R ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow).ι
  have h' : L' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      R' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    simpa only [L', R', Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource] using h
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsZeroOuterSpanVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows L' R' h') ?_
  intro v
  constructor
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
      (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows L' R' h' ≫ (pre horn₂₀.ι₀₁).app X).app
        (Opposite.op ⦋0⦌)) v)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (L.app (Opposite.op ⦋0⦌) v)
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
      (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows L' R' h' ≫ (pre horn₂₀.ι₀₂).app X).app
        (Opposite.op ⦋0⦌)) v)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (R.app (Opposite.op ⦋0⦌) v)

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
instance zeroOuterSpanSource_trivialKanFibration (X : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (zeroOuterSpanSource X) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  constructor
  intro a b sq
  have hL : CommSq (a ≫ zeroOuterSpanLeftArrow X) (boundary n).ι
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X) b := by
    constructor
    simpa only [Category.assoc, zeroOuterSpanSource] using sq.w
  have hR : CommSq (a ≫ zeroOuterSpanRightArrow X) (boundary n).ι
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X) b := by
    constructor
    rw [Category.assoc, zeroOuterSpanRightArrow_source]
    exact sq.w
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X) (boundary n).ι inferInstance
  let L := hL.lift
  let R := hR.lift
  let g := zeroOuterSpanFamilyOfArrows L R (hL.fac_right.trans hR.fac_right.symm)
  refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroOuterSpanVertex).ι).1
    dsimp only [g, zeroOuterSpanFamilyOfArrows]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamily_hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left, ← Category.assoc, hL.fac_left]
      simp only [zeroOuterSpanLeftArrow, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right, ← Category.assoc, hR.fac_left]
      simp only [zeroOuterSpanRightArrow, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  · change g ≫ (zeroOuterSpanLeftArrow X ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X) = b
    dsimp only [g, zeroOuterSpanFamilyOfArrows, zeroOuterSpanLeftArrow, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource]
    simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
    simp only [Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left]
    exact hL.fac_right


/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroOuterSpanSourceFiber_isContractibleKan (X : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (zeroOuterSpanSource X) x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
instance zeroOuterSpanSourceFiber_kanComplex (X : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
    (x : X _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (zeroOuterSpanSource X) x) :=
  (zeroOuterSpanSourceFiber_isContractibleKan X x).kanComplex
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
