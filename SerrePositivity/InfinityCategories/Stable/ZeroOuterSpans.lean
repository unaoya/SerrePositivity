module
public import SerrePositivity.InfinityCategories.Stable.SpanFamilies
public import SerrePositivity.InfinityCategories.Stable.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.Core.VertexFiber

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
namespace SerrePositivity.InfinityCategories

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def IsZeroOuterSpanVertex {X : SSet.{u}}
    (v : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  IsZeroTargetArrow (((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) v) ∧
    IsZeroTargetArrow (((pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋0⦌) v)
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpans (X : SSet.{u}) : SSet.{u} :=
  (fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
    IsZeroOuterSpanVertex : SSet.{u})
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpanLeftArrow (X : SSet.{u}) : zeroOuterSpans X ⟶ zeroTargetArrows X :=
  fullSubcomplexLift IsZeroTargetArrow
    ((fullSubcomplexOnVertices _ IsZeroOuterSpanVertex).ι ≫ (pre horn₂₀.ι₀₁).app X)
    (fun v ↦ (fullSubcomplexOnVertices_vertex v).1)
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpanRightArrow (X : SSet.{u}) : zeroOuterSpans X ⟶ zeroTargetArrows X :=
  fullSubcomplexLift IsZeroTargetArrow
    ((fullSubcomplexOnVertices _ IsZeroOuterSpanVertex).ι ≫ (pre horn₂₀.ι₀₂).app X)
    (fun v ↦ (fullSubcomplexOnVertices_vertex v).2)
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpanSource (X : SSet.{u}) : zeroOuterSpans X ⟶ X :=
  zeroOuterSpanLeftArrow X ≫ zeroTargetArrowSource X
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroOuterSpanRightArrow_source (X : SSet.{u}) :
    zeroOuterSpanRightArrow X ≫ zeroTargetArrowSource X = zeroOuterSpanSource X := by
  simp only [zeroOuterSpanSource, zeroOuterSpanRightArrow, zeroOuterSpanLeftArrow,
    zeroTargetArrowSource, ← Category.assoc, fullSubcomplexLift_ι]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroOuterSpanFamilyOfArrows {A X : SSet.{u}} (L R : A ⟶ zeroTargetArrows X)
    (h : L ≫ zeroTargetArrowSource X = R ≫ zeroTargetArrowSource X) :
    A ⟶ zeroOuterSpans X := by
  let L' := L ≫ (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι
  let R' := R ≫ (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι
  have h' : L' ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      R' ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    simpa only [L', R', Category.assoc, zeroTargetArrowSource] using h
  refine fullSubcomplexLift IsZeroOuterSpanVertex (stable_spanFamilyOfArrows L' R' h') ?_
  intro v
  constructor
  · change IsZeroTargetArrow
      (((stable_spanFamilyOfArrows L' R' h' ≫ (pre horn₂₀.ι₀₁).app X).app
        (Opposite.op ⦋0⦌)) v)
    rw [stable_spanFamilyOfArrows_left]
    exact fullSubcomplexOnVertices_vertex (L.app (Opposite.op ⦋0⦌) v)
  · change IsZeroTargetArrow
      (((stable_spanFamilyOfArrows L' R' h' ≫ (pre horn₂₀.ι₀₂).app X).app
        (Opposite.op ⦋0⦌)) v)
    rw [stable_spanFamilyOfArrows_right]
    exact fullSubcomplexOnVertices_vertex (R.app (Opposite.op ⦋0⦌) v)

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
instance zeroOuterSpanSource_trivialKanFibration (X : SSet.{u}) [HasZeroVertex X] :
    TrivialKanFibration (zeroOuterSpanSource X) := by
  apply (trivialKanFibration_iff_boundary _).mpr
  intro n
  constructor
  intro a b sq
  have hL : CommSq (a ≫ zeroOuterSpanLeftArrow X) (boundary n).ι
      (zeroTargetArrowSource X) b := by
    constructor
    simpa only [Category.assoc, zeroOuterSpanSource] using sq.w
  have hR : CommSq (a ≫ zeroOuterSpanRightArrow X) (boundary n).ι
      (zeroTargetArrowSource X) b := by
    constructor
    rw [Category.assoc, zeroOuterSpanRightArrow_source]
    exact sq.w
  have := TrivialKanFibration.mem (p := zeroTargetArrowSource X) (boundary n).ι inferInstance
  let L := hL.lift
  let R := hR.lift
  let g := zeroOuterSpanFamilyOfArrows L R (hL.fac_right.trans hR.fac_right.symm)
  refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_mono (fullSubcomplexOnVertices _ IsZeroOuterSpanVertex).ι).1
    dsimp only [g, zeroOuterSpanFamilyOfArrows]
    rw [Category.assoc, fullSubcomplexLift_ι]
    apply stable_spanFamily_hom_ext
    · rw [Category.assoc, stable_spanFamilyOfArrows_left, ← Category.assoc, hL.fac_left]
      simp only [zeroOuterSpanLeftArrow, Category.assoc, fullSubcomplexLift_ι]
    · rw [Category.assoc, stable_spanFamilyOfArrows_right, ← Category.assoc, hR.fac_left]
      simp only [zeroOuterSpanRightArrow, Category.assoc, fullSubcomplexLift_ι]
  · change g ≫ (zeroOuterSpanLeftArrow X ≫ zeroTargetArrowSource X) = b
    dsimp only [g, zeroOuterSpanFamilyOfArrows, zeroOuterSpanLeftArrow, zeroTargetArrowSource]
    simp only [← Category.assoc, fullSubcomplexLift_ι]
    simp only [Category.assoc, reassoc_of% stable_spanFamilyOfArrows_left]
    exact hL.fac_right


/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroOuterSpanSourceFiber_isContractibleKan (X : SSet.{u}) [HasZeroVertex X]
    (x : X _⦋0⦌) : IsContractibleKan (vertexFiber (zeroOuterSpanSource X) x) :=
  vertexFiber_isContractibleKan _ _
/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
instance zeroOuterSpanSourceFiber_kanComplex (X : SSet.{u}) [HasZeroVertex X]
    (x : X _⦋0⦌) : KanComplex (vertexFiber (zeroOuterSpanSource X) x) :=
  (zeroOuterSpanSourceFiber_isContractibleKan X x).kanComplex
end SerrePositivity.InfinityCategories
