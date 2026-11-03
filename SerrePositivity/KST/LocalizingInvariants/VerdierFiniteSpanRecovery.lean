module

public import SerrePositivity.KST.LocalizingInvariants.VerdierSpanCanonicalResolution
public import SerrePositivity.KST.Fibration.GroupoidCompletionKanComparison
public import SerrePositivity.InfinityCategories.Core.CoconeTransport
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightKanShapeCommaComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ContinuousKanFiniteFactorization
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ContinuousKanHomotopy

/-!
概要：完成した実分母・次辺族の有限パラメータを、一つの実分母上へ戻す。
方針：有限な台を分母の共通錐へ輸送し、Kan な実 fiber の置換を除く。
規約：比較は全パラメータの同型。指定境界の相対化は別の工程。
使われ方：完成分数族から実分母・実次辺族を回収する有限検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の錐全体から、同じ頂点の定値族からの指定ホモトピーを得る。 -/
def spanRecoveryConeHomotopy {K D : SSet.{u}} {p : K ⟶ D} (c : JoinCone p) :
    SSet.Homotopy (SSet.const c.vertex) p := by
  have hp : joinInl (Δ[0] : SSet.{u}) K ≫ c.val = SSet.yonedaEquiv.symm c.vertex := by
    rw [c.vertex_eq, Equiv.symm_apply_apply]
  let f := sliceUnderCurry c.val hp
  have hf : f ≫ sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex) = p := by
    rw [← sliceUnderUncurry_projection, sliceUnderUncurry_curry]
    exact c.property
  exact Eq.mp (congrArg (fun q : K ⟶ D ↦ SSet.Homotopy (SSet.const c.vertex) q) hf)
    (F1B.kanPointCosliceHomotopy c.vertex f)

/-- 有限な実族の全体を、一つの実分母上の次辺族へ輸送する。 -/
lemma verdierDenominatorSpan_finite_fiber_detection
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {K : SSet.{u}} [K.Finite] (f : K ⟶ verdierDenominatorSpanFamily i x y) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i x y) d,
        Nonempty (SSet.Homotopy
          (g ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d) f) := by
  let p := verdierDenominatorSpanProjection i x y
  obtain ⟨c⟩ := exists_verdierDenominatorOver_finiteCone h x (f ≫ p)
  let H := spanRecoveryConeHomotopy c
  let b := (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
  have hb : prismEndpoint 1 K ≫ b = f ≫ p := by
    dsimp only [b]
    rw [← Category.assoc, prismEndpoint_one_braiding]
    exact H.h₁
  obtain ⟨L, hL₁, hLp⟩ := stable_rightFibration_lift_prism p K f b hb
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ L
  have hR₁ : SSet.ι₁ ≫ R = f := by
    dsimp only [R]
    rw [← prismEndpoint_one_braiding K, Category.assoc, ← Category.assoc
      (β_ (Δ[1] : SSet.{u}) K).hom, SymmetricCategory.symmetry, Category.id_comp]
    exact hL₁
  have hRp : R ≫ p = H.h := by
    dsimp only [R]
    rw [Category.assoc, hLp]
    dsimp only [b]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have ht : (SSet.ι₀ ≫ R) ≫ p = SSet.const c.vertex := by
    rw [Category.assoc, hRp]
    exact H.h₀
  let g := vertexFiberLift p c.vertex (SSet.ι₀ ≫ R) ht
  refine ⟨c.vertex, g, ⟨⟨R, ?_, hR₁, ?_⟩⟩⟩
  · exact (vertexFiberLift_ι p c.vertex (SSet.ι₀ ≫ R) ht).symm
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- Kan 置換後の有限族も、置換前の一つの実分母上の次辺族で表せる。 -/
lemma verdierDenominatorSpan_continuous_finite_fiber_detection
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {K : SSet.{u}} [K.Finite]
    (f : K ⟶ F2.continuousKanReplacement.obj (verdierDenominatorSpanFamily i x y)) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i x y) d,
        Nonempty (SSet.Homotopy f
          (g ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d ≫
            F2.continuousKanReplacementUnit.app (verdierDenominatorSpanFamily i x y))) := by
  let E := verdierDenominatorSpanFamily i x y
  let p := verdierDenominatorSpanProjection i x y
  obtain ⟨J, a, ha⟩ := F2.continuousKanReplacement_finite_factorization f
  obtain ⟨d, g, ⟨H⟩⟩ := verdierDenominatorSpan_finite_fiber_detection h x y J.val.ι
  obtain ⟨H'⟩ := F2.continuousKanReplacement_map_homotopy H
  have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨functorHomotopyPrecomp H' a⟩
  have : KanComplex ((𝟭 SSet.{u}).obj (vertexFiber p d)) := vertexFiber_kanComplex p d
  obtain ⟨r, _, ⟨Hr⟩⟩ := (F2.continuousKanReplacementUnit_isWeakHomotopyEquivalence
    (vertexFiber p d)).isSimplicialHomotopyEquivalence
  refine ⟨d, a ≫ F2.continuousKanReplacement.map g ≫ r,
    (functorVertex_piZero_eq_iff_homotopy _ _).1 ?_⟩
  have h₂ := (functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨functorHomotopyPrecomp
      (functorHomotopyPostcomp Hr (F2.continuousKanReplacement.map (vertexFiberι p d)))
      (a ≫ F2.continuousKanReplacement.map g)⟩
  simp only [Category.assoc, Category.id_comp,
    ← F2.continuousKanReplacementUnit.naturality (vertexFiberι p d)] at h₂
  simp only [CategoryTheory.Functor.map_comp, ← Category.assoc, ha] at h₁
  simpa only [Category.assoc, CategoryTheory.Functor.id_map] using h₁.symm.trans h₂.symm

/-- 元の完成分数の任意の有限族を、一つの実分母と実次辺の全族で表す。 -/
lemma verdierCompletedSpan_finite_realization
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {K : SSet.{u}} [K.Finite]
    (f : K ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y)) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i x y) d,
        Nonempty (FunctorIso
          (g ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d ≫
            verdierDenominatorSpanCanonicalComparison i x y ≫
            groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y)) f) := by
  let E := verdierDenominatorSpanFamily i x y
  let F := verdierDenominatorSpanCanonicalComparison i x y
  let U := (verdierSpanCanonicalCompletionMap_isQCatEquivalence h x y).choose
  let V := (groupoidCompletionKanComparison_isQCatEquivalence E).choose
  obtain ⟨d, g, ⟨H⟩⟩ := verdierDenominatorSpan_continuous_finite_fiber_detection h x y
    (f ≫ U.inv ≫ V.hom)
  let a := g ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d
  have hu : FunctorIso (F2.continuousKanReplacementUnit.app E ≫ V.inv)
      (groupoidCompletionMap E) := by
    have e := FunctorIso.postcomp (groupoidCompletionEvaluationIso
      (F2.continuousKanReplacementUnit.app E)).symm V.inv ≪≫
      FunctorIso.precomp V.homInvIso (groupoidCompletionMap E)
    simpa only [V, IsQCatEquivalence.choose, groupoidCompletionKanComparison,
      Category.assoc, Category.comp_id] using e
  have e₁ : FunctorIso (a ≫ F ≫ groupoidCompletionMap
      (fixedMarkedSpans B.obj (weakEquivalences i) x y))
      (a ≫ groupoidCompletionMap E ≫ U.hom) := by
    change FunctorIso _ (a ≫ groupoidCompletionMap E ≫ groupoidCompletionMapOf F)
    simpa only [Category.assoc] using FunctorIso.precomp (groupoidCompletionMapOfIso F).symm a
  have e₂ : FunctorIso (a ≫ groupoidCompletionMap E ≫ U.hom)
      (a ≫ F2.continuousKanReplacementUnit.app E ≫ V.inv ≫ U.hom) := by
    simpa only [Category.assoc] using
      FunctorIso.precomp (FunctorIso.postcomp hu.symm U.hom) a
  have e₃ : FunctorIso (a ≫ F2.continuousKanReplacementUnit.app E ≫ V.inv ≫ U.hom)
      (f ≫ U.inv ≫ V.hom ≫ V.inv ≫ U.hom) := by
    simpa only [a, Category.assoc] using
      FunctorIso.postcomp (functorIsoOfSimplicialHomotopy H).symm (V.inv ≫ U.hom)
  have e₄ : FunctorIso (f ≫ U.inv ≫ V.hom ≫ V.inv ≫ U.hom) f := by
    have e := (FunctorIso.precomp V.homInvIso (f ≫ U.inv)).postcomp U.hom ≪≫
      FunctorIso.precomp U.invHomIso f
    simpa only [Category.assoc, Category.comp_id] using e
  exact ⟨d, g, ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄⟩⟩

/-- 商の全写像空間の有限族は、一つの実分母と実次辺の族で表せる。 -/
lemma verdierFiniteMappingFamily_realization
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {K : SSet.{u}} [K.Finite]
    (f : K ⟶ intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
      (q.hom.app (Opposite.op ⦋0⦌) y)) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i x y) d,
        Nonempty (FunctorIso
          (g ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d ≫
            verdierDenominatorSpanCanonicalComparison i x y ≫
            fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y) f) := by
  let M := (weakFractionMappingComparison_isQCatEquivalence h x y).choose
  obtain ⟨d, g, ⟨e⟩⟩ := verdierCompletedSpan_finite_realization h x y (f ≫ M.inv)
  let a := g ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d ≫
    verdierDenominatorSpanCanonicalComparison i x y
  have e₁ := FunctorIso.precomp
    (fractionMappingComparisonIso q.hom (weakEquivalences i) h.inverts x y).symm a
  have e₂ := FunctorIso.postcomp e M.hom
  have e₃ := FunctorIso.precomp M.invHomIso f
  refine ⟨d, g, ⟨?_⟩⟩
  have e' : FunctorIso (a ≫ fixedFractionEvaluation q.hom (weakEquivalences i)
      h.inverts x y) f := by
    simpa only [a, M, IsQCatEquivalence.choose, Category.assoc, Category.comp_id] using
      e₁ ≪≫ e₂ ≪≫ e₃
  exact e'

end SerrePositivity.KST.LocalizingInvariants
