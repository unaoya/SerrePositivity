module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.VerdierDenominatorOver
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.MarkedSpanFamilies
public import SerrePositivity.InfinityCategories.Core.RightFibrationContractible
public import SerrePositivity.InfinityCategories.Core.VertexFiberPullback
public import SerrePositivity.InfinityCategories.Derived.SliceEvaluationVertex
public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting

/-!
概要：実分母 over の上に、同じ始域からの実次辺の全族を構成する。
方針：次辺の実 slice の右 fibration を分母の始域射影で引き戻す。
規約：分母と次辺の始域は全パラメータで厳密に一致する。
使われ方：filtered な実分母添字上の分数模型と元の固定端点 span の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 元の分母の実始域を、元の安定圏へ戻す射影。 -/
def verdierDenominatorOverSource {A B : StableCategory.{u}} (i : ExactMap A B)
    (x : B.obj _⦋0⦌) : (verdierDenominatorOver i x : SSet.{u}) ⟶ B.obj :=
  (verdierDenominatorOver i x).ι ≫ sliceOverProjection (SSet.yonedaEquiv.symm x)

/-- 実分母と、その同じ始域から指定終点への実次辺を保持する全空間。 -/
def verdierDenominatorSpanFamily {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : SSet.{u} :=
  pullback (sliceOverProjection (SSet.yonedaEquiv.symm y))
    (verdierDenominatorOverSource i x)

/-- 実次辺族から、元の実分母添字への射影。 -/
def verdierDenominatorSpanProjection {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶
      (verdierDenominatorOver i x : SSet.{u}) := pullback.snd _ _

/-- 同じ右 fibration を引き戻すので、実分母に沿う次辺族は右 fibration。 -/
instance verdierDenominatorSpanProjection_rightFibration {A B : StableCategory.{u}}
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    RightFibration (verdierDenominatorSpanProjection i x y) :=
  rightFibration_pullback_snd _ _

instance verdierDenominatorSpanFamily_quasicategory {A B : StableCategory.{u}}
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    Quasicategory (verdierDenominatorSpanFamily i x y) :=
  quasicategory_of_innerFibration (verdierDenominatorSpanProjection i x y)

/-- 指定した分母上の fiber は、同じ実始域から y への元の右写像空間。 -/
def verdierDenominatorSpanFiberIso {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    vertexFiber (verdierDenominatorSpanProjection i x y) d ≅
      vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm y))
        ((verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d) :=
  vertexFiberPullbackIso _ _ _

/-- 元の同じ実分母を、その実 slice 全族として回収する。 -/
def verdierDenominatorSpanDenominator {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶
      sliceOver (SSet.yonedaEquiv.symm x) :=
  verdierDenominatorSpanProjection i x y ≫ (verdierDenominatorOver i x).ι

/-- 元の同じ実次辺を、その実 slice 全族として回収する。 -/
def verdierDenominatorSpanNumerator {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶
      sliceOver (SSet.yonedaEquiv.symm y) := pullback.fst _ _

/-- 始域の共有は、全族の射の厳密な等式。 -/
lemma verdierDenominatorSpan_sharedSource {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) :
    verdierDenominatorSpanNumerator i x y ≫ sliceOverProjection (SSet.yonedaEquiv.symm y) =
      verdierDenominatorSpanDenominator i x y ≫
        sliceOverProjection (SSet.yonedaEquiv.symm x) := by
  dsimp only [verdierDenominatorSpanDenominator]
  rw [Category.assoc]
  exact pullback.condition

/-- 回収した分母の一次単体は、元の弱同値集合そのものに属する。 -/
lemma verdierDenominatorSpan_denominator_mem {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) (v : (verdierDenominatorSpanFamily i x y) _⦋0⦌) :
    (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x)
      ((verdierDenominatorSpanDenominator i x y).app (Opposite.op ⦋0⦌) v)).edge ∈
        weakEquivalences i :=
  fullSubcomplexOnVertices_vertex
    ((verdierDenominatorSpanProjection i x y).app (Opposite.op ⦋0⦌) v)

def sliceArrowFamily {T X : SSet.{u}} (x : X _⦋0⦌)
    (F : T ⟶ sliceOver (SSet.yonedaEquiv.symm x)) : T ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry ((β_ (Δ[1] : SSet.{u}) T).hom ≫
    (functorHomotopyPrecomp (roofSliceEvaluationHomotopy x) F).h)

lemma sliceArrowFamily_source {T X : SSet.{u}} (x : X _⦋0⦌)
    (F : T ⟶ sliceOver (SSet.yonedaEquiv.symm x)) :
    sliceArrowFamily x F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      F ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) := by
  rw [sliceArrowFamily, curry_evaluateFunctorAt_interval _ 0]
  have hi : prismEndpoint 0 T ≫ (β_ (Δ[1] : SSet.{u}) T).hom = SSet.ι₀ := rfl
  rw [← Category.assoc, hi, (functorHomotopyPrecomp (roofSliceEvaluationHomotopy x) F).h₀]

lemma sliceArrowFamily_target {T X : SSet.{u}} (x : X _⦋0⦌)
    (F : T ⟶ sliceOver (SSet.yonedaEquiv.symm x)) :
    sliceArrowFamily x F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.const x := by
  rw [sliceArrowFamily, curry_evaluateFunctorAt_interval _ 1]
  have hi : prismEndpoint 1 T ≫ (β_ (Δ[1] : SSet.{u}) T).hom = SSet.ι₁ := rfl
  rw [← Category.assoc, hi, (functorHomotopyPrecomp (roofSliceEvaluationHomotopy x) F).h₁,
    SSet.comp_const]

lemma sliceArrowFamily_vertex_edge {T X : SSet.{u}} (x : X _⦋0⦌)
    (F : T ⟶ sliceOver (SSet.yonedaEquiv.symm x)) (v : T _⦋0⦌) :
    intervalFunctorVertexEdge ((sliceArrowFamily x F).app (Opposite.op ⦋0⦌) v) =
      (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) (F.app _ v)).edge := by
  rw [sliceArrowFamily, intervalFunctorVertexEdge_curry, pinchedConstant_one]
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  change (functorHomotopyPrecomp (roofSliceEvaluationHomotopy x) F).h.app
    (Opposite.op ⦋1⦌) ((Truncated.Edge.id (X := (truncation 2).obj T) v).edge,
      SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _
  rw [hi]
  exact (simplicialHomotopyVertexEdge_precomp_edge _ F v).trans
    (roofSliceEvaluationHomotopy_vertex_edge x (F.app _ v))

lemma pre_source_evaluation (X : SSet.{u}) :
    (pre (stdSimplex.δ (1 : Fin 2))).app X ≫ (pointFunctorEvaluationIso X).hom =
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change (pre (stdSimplex.δ (1 : Fin 2))).app X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
  rw [stable_pre_evaluateFunctorAt]
  rfl

lemma spanArrowFamily_compatible {T X : SSet.{u}}
    (a b : T ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (h : a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :
    a ≫ (pre (stdSimplex.δ (1 : Fin 2))).app X =
      b ≫ (pre (stdSimplex.δ (1 : Fin 2))).app X := by
  apply (cancel_mono (pointFunctorEvaluationIso X).hom).mp
  simpa only [Category.assoc, pre_source_evaluation] using h

def spanArrowFamilyGlue {T X : SSet.{u}}
    (a b : T ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (h : a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :
    T ⟶ (ihom (horn 2 0 : SSet.{u})).obj X :=
  (isPullback_pre_of_isPushout horn₂₀.isPushout X).flip.lift a b
    (spanArrowFamily_compatible a b h)

lemma spanArrowFamilyGlue_left {T X : SSet.{u}}
    (a b : T ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (h : a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :
    spanArrowFamilyGlue a b h ≫ (pre horn₂₀.ι₀₁).app X = a :=
  (isPullback_pre_of_isPushout horn₂₀.isPushout X).flip.lift_fst _ _ _

lemma spanArrowFamilyGlue_right {T X : SSet.{u}}
    (a b : T ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (h : a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :
    spanArrowFamilyGlue a b h ≫ (pre horn₂₀.ι₀₂).app X = b :=
  (isPullback_pre_of_isPushout horn₂₀.isPushout X).flip.lift_snd _ _ _

def denominatorSpanRaw {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶
      (ihom (horn 2 0 : SSet.{u})).obj B.obj :=
  spanArrowFamilyGlue
    (sliceArrowFamily x (verdierDenominatorSpanDenominator i x y))
    (sliceArrowFamily y (verdierDenominatorSpanNumerator i x y))
    (by
      rw [sliceArrowFamily_source, sliceArrowFamily_source]
      exact (verdierDenominatorSpan_sharedSource i x y).symm)

lemma denominatorSpanRaw_left {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : denominatorSpanRaw i x y ≫ (pre horn₂₀.ι₀₁).app B.obj =
      sliceArrowFamily x (verdierDenominatorSpanDenominator i x y) :=
  spanArrowFamilyGlue_left _ _ _

lemma denominatorSpanRaw_right {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : denominatorSpanRaw i x y ≫ (pre horn₂₀.ι₀₂).app B.obj =
      sliceArrowFamily y (verdierDenominatorSpanNumerator i x y) :=
  spanArrowFamilyGlue_right _ _ _

def denominatorSpanMarked {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶ markedSpans B.obj
      (weakEquivalences i) :=
  fullSubcomplexLift _ (denominatorSpanRaw i x y) (by
    intro v
    change intervalFunctorVertexEdge
      ((denominatorSpanRaw i x y ≫ (pre horn₂₀.ι₀₁).app B.obj).app _ v) ∈ _
    rw [denominatorSpanRaw_left, sliceArrowFamily_vertex_edge]
    exact verdierDenominatorSpan_denominator_mem i x y v)

lemma denominatorSpanMarked_inclusion {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : denominatorSpanMarked i x y ≫
      markedSpanInclusion B.obj (weakEquivalences i) = denominatorSpanRaw i x y :=
  fullSubcomplexLift_ι _ _ _

lemma denominatorSpanMarked_source {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : denominatorSpanMarked i x y ≫
      markedSpanSource B.obj (weakEquivalences i) = SSet.const x := by
  change denominatorSpanMarked i x y ≫ (markedSpanInclusion B.obj (weakEquivalences i) ≫
    (pre horn₂₀.ι₀₁).app B.obj ≫ evaluateFunctorAt _) = _
  rw [← Category.assoc, denominatorSpanMarked_inclusion, ← Category.assoc,
    denominatorSpanRaw_left, sliceArrowFamily_target]

lemma denominatorSpanMarked_target {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : denominatorSpanMarked i x y ≫
      markedSpanTarget B.obj (weakEquivalences i) = SSet.const y := by
  change denominatorSpanMarked i x y ≫ (markedSpanInclusion B.obj (weakEquivalences i) ≫
    (pre horn₂₀.ι₀₂).app B.obj ≫ evaluateFunctorAt _) = _
  rw [← Category.assoc, denominatorSpanMarked_inclusion, ← Category.assoc,
    denominatorSpanRaw_right, sliceArrowFamily_target]

lemma denominatorSpanMarked_boundary {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : denominatorSpanMarked i x y ≫
      markedSpanBoundary B.obj (weakEquivalences i) =
        SSet.const (functorVertex (intervalMappingBoundary x y)) := by
  change denominatorSpanMarked i x y ≫ curry (intervalBoundaryDiagram
    (markedSpanSource B.obj (weakEquivalences i))
    (markedSpanTarget B.obj (weakEquivalences i))) = _
  rw [← curry_natural_left, intervalBoundaryDiagram_naturality,
    denominatorSpanMarked_source, denominatorSpanMarked_target]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_const_functorVertex]
  rfl

/-- 同じ実分母・次辺を元の固定端点 marked span の全族へ貼る。 -/
def verdierDenominatorSpanToFixed {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶
      fixedMarkedSpans B.obj (weakEquivalences i) x y := by
  exact vertexFiberLift _ _ (denominatorSpanMarked i x y) (denominatorSpanMarked_boundary i x y)

lemma verdierDenominatorSpanToFixed_inclusion {A B : StableCategory.{u}}
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    verdierDenominatorSpanToFixed i x y ≫ fixedMarkedSpanInclusion B.obj
      (weakEquivalences i) x y = denominatorSpanMarked i x y := vertexFiberLift_ι _ _ _ _

/-- 元の左脚は、同じ実分母の全評価ホモトピー。 -/
def verdierDenominatorSpanDenominatorArrow {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶
      (ihom (Δ[1] : SSet.{u})).obj B.obj := by
  exact sliceArrowFamily x (verdierDenominatorSpanDenominator i x y)

/-- 元の右脚は、同じ実次辺の全評価ホモトピー。 -/
def verdierDenominatorSpanNumeratorArrow {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶
      (ihom (Δ[1] : SSet.{u})).obj B.obj := by
  exact sliceArrowFamily y (verdierDenominatorSpanNumerator i x y)

/-- 貼合せ後の分母の制限は、元の全分母族に厳密に一致する。 -/
lemma verdierDenominatorSpanToFixed_denominator {A B : StableCategory.{u}}
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    verdierDenominatorSpanToFixed i x y ≫ fixedMarkedSpanInclusion B.obj
      (weakEquivalences i) x y ≫ markedSpanInclusion B.obj (weakEquivalences i) ≫
        (pre horn₂₀.ι₀₁).app B.obj = verdierDenominatorSpanDenominatorArrow i x y := by
  rw [← Category.assoc, verdierDenominatorSpanToFixed_inclusion,
    ← Category.assoc, denominatorSpanMarked_inclusion, denominatorSpanRaw_left]
  rfl

/-- 貼合せ後の次辺の制限は、元の全次辺族に厳密に一致する。 -/
lemma verdierDenominatorSpanToFixed_numerator {A B : StableCategory.{u}}
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    verdierDenominatorSpanToFixed i x y ≫ fixedMarkedSpanInclusion B.obj
      (weakEquivalences i) x y ≫ markedSpanInclusion B.obj (weakEquivalences i) ≫
        (pre horn₂₀.ι₀₂).app B.obj = verdierDenominatorSpanNumeratorArrow i x y := by
  rw [← Category.assoc, verdierDenominatorSpanToFixed_inclusion,
    ← Category.assoc, denominatorSpanMarked_inclusion, denominatorSpanRaw_right]
  rfl

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanMarked (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanMarked := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanMarked

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanMarked_boundary := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanMarked_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanMarked_inclusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanMarked_inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanMarked_source := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanMarked_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanMarked_target := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanMarked_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanRaw (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanRaw := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanRaw

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanRaw_left := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanRaw_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanRaw_right := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanRaw_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.pre_source_evaluation := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pre_source_evaluation

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.sliceArrowFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.sliceArrowFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.sliceArrowFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.sliceArrowFamily_source := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.sliceArrowFamily_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.sliceArrowFamily_target := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.sliceArrowFamily_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.sliceArrowFamily_vertex_edge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.sliceArrowFamily_vertex_edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanArrowFamilyGlue (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanArrowFamilyGlue := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanArrowFamilyGlue

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanArrowFamilyGlue_left := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanArrowFamilyGlue_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanArrowFamilyGlue_right := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanArrowFamilyGlue_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanArrowFamily_compatible := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanArrowFamily_compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorOverSource (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorOverSource := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorOverSource

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanDenominator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanDenominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanDenominator

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanDenominatorArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanDenominatorArrow := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanDenominatorArrow

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanFamily_quasicategory := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily_quasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanFiberIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumerator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanNumerator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumerator

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumeratorArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanNumeratorArrow := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumeratorArrow

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanProjection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection_rightFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanProjection_rightFibration := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection_rightFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanToFixed (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanToFixed := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanToFixed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanToFixed_denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanToFixed_denominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanToFixed_inclusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanToFixed_inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanToFixed_numerator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanToFixed_numerator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpan_denominator_mem := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpan_denominator_mem

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpan_sharedSource := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpan_sharedSource

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanMarked._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanMarked._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.denominatorSpanRaw._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.denominatorSpanRaw._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.sliceArrowFamily.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.sliceArrowFamily.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanArrowFamilyGlue._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanArrowFamilyGlue._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanArrowFamilyGlue._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanArrowFamilyGlue._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanArrowFamilyGlue._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanArrowFamilyGlue._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanFamily._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily._proof_1
