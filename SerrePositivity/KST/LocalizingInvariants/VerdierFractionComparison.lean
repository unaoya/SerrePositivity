module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FixedFractionTriangleEvaluation
public import SerrePositivity.KST.LocalizingInvariants.LocalizationHomotopyCategory
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.WeakEquivalences
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberHoDenominators
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.KST.LocalizingInvariants.IntervalPrecompositionFamily
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyFiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanFamilies
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IntervalIsoHomClass

/-!
概要：元の一般 Verdier 商の分数比較の充満忠実性を、元の辺を保って検証する。
方針：既存の安定な分母計算と全関手圏の局所化を用いる。
規約：補助計算は私有とし、新しい一般局所化・商 API を設けない。
使われ方：Sp-6 s4。現段階の私有均等化は全写像空間の充満忠実性そのものではない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)

include h

private lemma fraction_denominator_iff {x y : B.obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) x y) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW (Truncated.HomotopyCategory.homMk f) ↔
      f.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  have hd := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) f
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.stableClosure_essentialImage h] at hd
  exact hd.symm

private lemma fraction_ho_localization :
    (hoFunctor.map q.hom).toFunctor.IsLocalization
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW :=
  localizationHo_isLocalization q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.quotient
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW (fraction_denominator_iff h)

/-- 商で一致する元の二辺を、一つの実分母と共有合成二単体で均等化する。
全次数の写像空間の比較を、この h 圏の判定だけで完了とはしない。 -/
private lemma fraction_equal_images_refine {x y : B.obj _⦋0⦌}
    (f g : Truncated.Edge (X := (truncation 2).obj B.obj) x y)
    (he : (hoFunctor.map q.hom).toFunctor.map (Truncated.HomotopyCategory.homMk f) =
      (hoFunctor.map q.hom).toFunctor.map (Truncated.HomotopyCategory.homMk g)) :
    ∃ (a : B.obj _⦋0⦌)
      (t : Truncated.Edge (X := (truncation 2).obj B.obj) a x),
      t.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i ∧
      ∃ k : Truncated.Edge (X := (truncation 2).obj B.obj) a y,
        Nonempty (Truncated.Edge.CompStruct t f k) ∧
        Nonempty (Truncated.Edge.CompStruct t g k) := by
  let W := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW
  let L := (hoFunctor.map q.hom).toFunctor
  letI : L.IsLocalization W := fraction_ho_localization h
  obtain ⟨a, t, ht, heq⟩ := (MorphismProperty.map_eq_iff_precomp L W
    (Truncated.HomotopyCategory.homMk f) (Truncated.HomotopyCategory.homMk g)).mp he
  obtain ⟨a, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨t, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a x t
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a y
    (Truncated.HomotopyCategory.homMk t ≫ Truncated.HomotopyCategory.homMk f)
  exact ⟨a, t, (fraction_denominator_iff h t).mp ht, k,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hk.symm,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (heq.symm.trans hk.symm)⟩

/-- 元の実 roof の h 商における類。補助計算だけに使う。 -/
private def fractionClass {a x y : B.obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) a x)
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) a y)
    (hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    (hoFunctor.map q.hom).toFunctor.obj (HomotopyCategory.mk x) ⟶
      (hoFunctor.map q.hom).toFunctor.obj (HomotopyCategory.mk y) := by
  let W := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW
  let L := (hoFunctor.map q.hom).toFunctor
  letI : L.IsLocalization W := fraction_ho_localization h
  let φ : W.RightFraction (HomotopyCategory.mk x) (HomotopyCategory.mk y) :=
    ⟨Truncated.HomotopyCategory.homMk s, (fraction_denominator_iff h s).mpr hs,
      Truncated.HomotopyCategory.homMk f⟩
  exact φ.map L (Localization.inverts L W)

/-- 元の商で等しい二つの実 roof に、共有した実分母・実分子と四つの合成二単体を与える。 -/
private lemma equal_fractionClasses_refine {a₁ a₂ x y : B.obj _⦋0⦌}
    (s₁ : Truncated.Edge (X := (truncation 2).obj B.obj) a₁ x)
    (s₂ : Truncated.Edge (X := (truncation 2).obj B.obj) a₂ x)
    (f₁ : Truncated.Edge (X := (truncation 2).obj B.obj) a₁ y)
    (f₂ : Truncated.Edge (X := (truncation 2).obj B.obj) a₂ y)
    (hs₁ : s₁.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) (hs₂ : s₂.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
    (he : fractionClass h s₁ f₁ hs₁ = fractionClass h s₂ f₂ hs₂) :
    ∃ (a : B.obj _⦋0⦌)
      (t₁ : Truncated.Edge (X := (truncation 2).obj B.obj) a a₁)
      (t₂ : Truncated.Edge (X := (truncation 2).obj B.obj) a a₂)
      (s : Truncated.Edge (X := (truncation 2).obj B.obj) a x)
      (f : Truncated.Edge (X := (truncation 2).obj B.obj) a y),
      s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i ∧
      Nonempty (Truncated.Edge.CompStruct t₁ s₁ s) ∧
      Nonempty (Truncated.Edge.CompStruct t₂ s₂ s) ∧
      Nonempty (Truncated.Edge.CompStruct t₁ f₁ f) ∧
      Nonempty (Truncated.Edge.CompStruct t₂ f₂ f) := by
  let W := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW
  let L := (hoFunctor.map q.hom).toFunctor
  letI : L.IsLocalization W := fraction_ho_localization h
  let φ : W.RightFraction (HomotopyCategory.mk x) (HomotopyCategory.mk y) :=
    ⟨Truncated.HomotopyCategory.homMk s₁, (fraction_denominator_iff h s₁).mpr hs₁,
      Truncated.HomotopyCategory.homMk f₁⟩
  let ψ : W.RightFraction (HomotopyCategory.mk x) (HomotopyCategory.mk y) :=
    ⟨Truncated.HomotopyCategory.homMk s₂, (fraction_denominator_iff h s₂).mpr hs₂,
      Truncated.HomotopyCategory.homMk f₂⟩
  obtain ⟨a, t₁, t₂, hden, hnum, ht⟩ :=
    (MorphismProperty.RightFraction.map_eq_iff L W φ ψ).mp he
  obtain ⟨a, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨t₁, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a a₁ t₁
  obtain ⟨t₂, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a a₂ t₂
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a x
    (Truncated.HomotopyCategory.homMk t₁ ≫ Truncated.HomotopyCategory.homMk s₁)
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a y
    (Truncated.HomotopyCategory.homMk t₁ ≫ Truncated.HomotopyCategory.homMk f₁)
  have hsW : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
    apply (fraction_denominator_iff h s).mp
    rw [hs]
    exact ht
  exact ⟨a, t₁, t₂, s, f, hsW,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hs.symm,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (hden.symm.trans hs.symm),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hf.symm,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (hnum.symm.trans hf.symm)⟩

omit h in
private lemma fraction_precomposition_target {X : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ X)
    {a b : X _⦋0⦌} (s : Truncated.Edge (X := (truncation 2).obj X) a b)
    (hs : stdSimplex.δ (0 : Fin 3) ≫ T = SSet.yonedaEquiv.symm s.edge) :
    intervalPrecompositionFamily T ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const b := by
  rw [intervalPrecompositionFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_target]
  have hc : (SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) :
      (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫ stdSimplex.δ (0 : Fin 3) := by
    rw [SSet.const_comp]
    rfl
  rw [hc, Category.assoc, hs, SSet.const_comp]
  apply congrArg SSet.const
  have he := intervalMap_target (SSet.yonedaEquiv.symm (show X _⦋1⦌ from s.edge))
  rw [Equiv.apply_symm_apply] at he
  exact he.symm.trans s.tgt_eq

omit h in
/-- 二つの共有始点を持つ実合成三角形を、終点固定の span の族に貼る。 -/
private lemma fraction_refinement_family {X : SSet.{u}}
    {a b x y : X _⦋0⦌}
    (t : Truncated.Edge (X := (truncation 2).obj X) a b)
    (s : Truncated.Edge (X := (truncation 2).obj X) b x)
    (f : Truncated.Edge (X := (truncation 2).obj X) b y)
    (T U : (Δ[2] : SSet.{u}) ⟶ X)
    (hT₂ : stdSimplex.δ (2 : Fin 3) ≫ T = SSet.yonedaEquiv.symm t.edge)
    (hU₂ : stdSimplex.δ (2 : Fin 3) ≫ U = SSet.yonedaEquiv.symm t.edge)
    (hT₀ : stdSimplex.δ (0 : Fin 3) ≫ T = SSet.yonedaEquiv.symm s.edge)
    (hU₀ : stdSimplex.δ (0 : Fin 3) ≫ U = SSet.yonedaEquiv.symm f.edge) :
    ∃ G : (Δ[1] : SSet.{u}) ⟶ (ihom (horn 2 0 : SSet.{u})).obj X,
      G ≫ (pre horn₂₀.ι₀₁).app X = intervalPrecompositionFamily T ∧
      G ≫ (pre horn₂₀.ι₀₂).app X = intervalPrecompositionFamily U ∧
      G ≫ (pre horn₂₀.ι₀₁).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const x ∧
      G ≫ (pre horn₂₀.ι₀₂).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const y := by
  have hc : intervalPrecompositionFamily T ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      intervalPrecompositionFamily U ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    simp only [intervalPrecompositionFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_source, hT₂, hU₂]
  let G := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows (intervalPrecompositionFamily T)
    (intervalPrecompositionFamily U) hc
  have hl : G ≫ (pre horn₂₀.ι₀₁).app X = intervalPrecompositionFamily T :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left _ _ _
  have hr : G ≫ (pre horn₂₀.ι₀₂).app X = intervalPrecompositionFamily U :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right _ _ _
  refine ⟨G, hl, hr, ?_, ?_⟩
  · rw [← Category.assoc, hl]
    exact fraction_precomposition_target T s hT₀
  · rw [← Category.assoc, hr]
    exact fraction_precomposition_target U f hU₀

private lemma fraction_refinement_fixedFamily
    {a b x y : B.obj _⦋0⦌}
    (t : Truncated.Edge (X := (truncation 2).obj B.obj) a b)
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) b x)
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) b y)
    (s' : Truncated.Edge (X := (truncation 2).obj B.obj) a x)
    (f' : Truncated.Edge (X := (truncation 2).obj B.obj) a y)
    (cs : Truncated.Edge.CompStruct t s s') (cf : Truncated.Edge.CompStruct t f f')
    (hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) (hs' : s'.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    ∃ G : (Δ[1] : SSet.{u}) ⟶ fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y,
      G ≫ fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y ≫
        markedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) ≫ (pre horn₂₀.ι₀₁).app B.obj =
        intervalPrecompositionFamily (SSet.yonedaEquiv.symm cs.simplex) ∧
      G ≫ fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y ≫
        markedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) ≫ (pre horn₂₀.ι₀₂).app B.obj =
        intervalPrecompositionFamily (SSet.yonedaEquiv.symm cf.simplex) := by
  let T : (Δ[2] : SSet.{u}) ⟶ B.obj := SSet.yonedaEquiv.symm cs.simplex
  let U : (Δ[2] : SSet.{u}) ⟶ B.obj := SSet.yonedaEquiv.symm cf.simplex
  have hT₂ : stdSimplex.δ (2 : Fin 3) ≫ T = SSet.yonedaEquiv.symm t.edge := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm cs.d₂
  have hU₂ : stdSimplex.δ (2 : Fin 3) ≫ U = SSet.yonedaEquiv.symm t.edge := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm cf.d₂
  have hT₀ : stdSimplex.δ (0 : Fin 3) ≫ T = SSet.yonedaEquiv.symm s.edge := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm cs.d₀
  have hU₀ : stdSimplex.δ (0 : Fin 3) ≫ U = SSet.yonedaEquiv.symm f.edge := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm cf.d₀
  obtain ⟨F, hl, hr, hx, hy⟩ := fraction_refinement_family t s f T U hT₂ hU₂ hT₀ hU₀
  have hv : ∀ v : (Δ[1] : SSet.{u}) _⦋0⦌,
      spanLeftEdge (F.app (Opposite.op ⦋0⦌) v) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
    intro v
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    have he := congrArg (fun k => k.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm j)) hl
    change ((pre horn₂₀.ι₀₁).app B.obj).app (Opposite.op ⦋0⦌)
      (F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)) =
      (intervalPrecompositionFamily T).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm j) at he
    unfold spanLeftEdge
    rw [he]
    fin_cases j
    · have he₁ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T) = s'.edge := by
        rw [stdSimplex.yonedaEquiv_δ_comp]
        exact (congrArg (B.obj.δ (1 : Fin 3))
          (SSet.yonedaEquiv.apply_symm_apply cs.simplex)).trans cs.d₁
      exact (congrArg (fun z : B.obj _⦋1⦌ => z ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
        ((intervalPrecompositionFamily_edge_zero T).trans he₁)).mpr hs'
    · have he₀ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T) = s.edge := by
        rw [stdSimplex.yonedaEquiv_δ_comp]
        exact (congrArg (B.obj.δ (0 : Fin 3))
          (SSet.yonedaEquiv.apply_symm_apply cs.simplex)).trans cs.d₀
      exact (congrArg (fun z : B.obj _⦋1⦌ => z ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
        ((intervalPrecompositionFamily_edge_one T).trans he₀)).mpr hs
  let L : (Δ[1] : SSet.{u}) ⟶ markedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun z => spanLeftEdge z ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) F hv
  have hL : L ≫ markedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) = F :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hxs : L ≫ markedSpanSource B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) = SSet.const x := by
    change (L ≫ markedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)) ≫
      (pre horn₂₀.ι₀₁).app B.obj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
    rw [hL]
    exact hx
  have hys : L ≫ markedSpanTarget B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) = SSet.const y := by
    change (L ≫ markedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)) ≫
      (pre horn₂₀.ι₀₂).app B.obj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
    rw [hL]
    exact hy
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (markedSpanBoundary B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)) L
      (markedSpanBoundary_of_endpoints (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) L x y hxs hys)
  have hG : G ≫ fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y = L :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  refine ⟨G, ?_, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, hG, hL]
    exact hl
  · rw [← Category.assoc, ← Category.assoc, hG, hL]
    exact hr

omit h in
private lemma fraction_spanVertex_ext {X : SSet.{u}}
    {v w : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌}
    (hl : spanLeftEdge v = spanLeftEdge w)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋0⦌) v) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋0⦌) w)) : v = w := by
  obtain ⟨V, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) X).surjective v
  obtain ⟨W, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) X).surjective w
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₁ ≫ V)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₁ ≫ W)) at hl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ V)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ W)) at hr
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hl hr
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
  apply horn₂₀.isPushout.hom_ext
  · exact SSet.yonedaEquiv.injective hl
  · exact SSet.yonedaEquiv.injective hr

omit h in
private lemma fraction_fixedVertex_ext {X : SSet.{u}} {W : Set (X _⦋1⦌)}
    {x y : X _⦋0⦌} {v w : (fixedMarkedSpans X W x y) _⦋0⦌}
    (hl : spanLeftEdge v.val.val = spanLeftEdge w.val.val)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app X).app
      (Opposite.op ⦋0⦌) v.val.val) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge
        (((pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋0⦌) w.val.val)) : v = w := by
  apply Subtype.ext
  apply Subtype.ext
  exact fraction_spanVertex_ext hl hr

omit h in
private lemma fraction_fixedFamily_leg {X : SSet.{u}} {W : Set (X _⦋1⦌)}
    {x y : X _⦋0⦌} (G : (Δ[1] : SSet.{u}) ⟶ fixedMarkedSpans X W x y)
    (j : Fin 2) (k : (Δ[1] : SSet.{u}) ⟶ horn 2 0)
    (T : (Δ[2] : SSet.{u}) ⟶ X)
    (hG : G ≫ fixedMarkedSpanInclusion X W x y ≫ markedSpanInclusion X W ≫
      (pre k).app X = intervalPrecompositionFamily T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre k).app X).app (Opposite.op ⦋0⦌)
      (G.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)).val.val) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((intervalPrecompositionFamily T).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)) := by
  have he := congrArg (fun F => F.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm j)) hG
  change ((pre k).app X).app (Opposite.op ⦋0⦌)
    (G.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)).val.val =
      (intervalPrecompositionFamily T).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm j) at he
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge he

omit h in
private lemma fraction_precomposition_edges {X : SSet.{u}} {a b c : X _⦋0⦌}
    {t : Truncated.Edge (X := (truncation 2).obj X) a b}
    {f : Truncated.Edge (X := (truncation 2).obj X) b c}
    {k : Truncated.Edge (X := (truncation 2).obj X) a c}
    (τ : Truncated.Edge.CompStruct t f k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((intervalPrecompositionFamily
      (SSet.yonedaEquiv.symm τ.simplex)).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = k.edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((intervalPrecompositionFamily
      (SSet.yonedaEquiv.symm τ.simplex)).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = f.edge := by
  constructor
  · exact (intervalPrecompositionFamily_edge_zero _).trans
      ((stdSimplex.yonedaEquiv_δ_comp _ _).trans
        ((congrArg (X.δ (1 : Fin 3)) (SSet.yonedaEquiv.apply_symm_apply τ.simplex)).trans τ.d₁))
  · exact (intervalPrecompositionFamily_edge_one _).trans
      ((stdSimplex.yonedaEquiv_δ_comp _ _).trans
        ((congrArg (X.δ (0 : Fin 3)) (SSet.yonedaEquiv.apply_symm_apply τ.simplex)).trans τ.d₀))

private lemma fraction_refinement_component
    {a b x y : B.obj _⦋0⦌}
    (t : Truncated.Edge (X := (truncation 2).obj B.obj) a b)
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) b x)
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) b y)
    (s' : Truncated.Edge (X := (truncation 2).obj B.obj) a x)
    (f' : Truncated.Edge (X := (truncation 2).obj B.obj) a y)
    (cs : Truncated.Edge.CompStruct t s s') (cf : Truncated.Edge.CompStruct t f f')
    (hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) (hs' : s'.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
    (v : (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) _⦋0⦌)
    (hvs : spanLeftEdge v.val.val = s.edge)
    (hvf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app B.obj).app
      (Opposite.op ⦋0⦌) v.val.val) = f.edge) :
    ∃ w : (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) _⦋0⦌,
      SSet.π₀.mk w = SSet.π₀.mk v ∧ spanLeftEdge w.val.val = s'.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app B.obj).app
        (Opposite.op ⦋0⦌) w.val.val) = f'.edge := by
  obtain ⟨G, hL, hR⟩ := fraction_refinement_fixedFamily h t s f s' f' cs cf hs hs'
  let w := G.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let v' := G.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have hLs (j : Fin 2) := fraction_fixedFamily_leg G j horn₂₀.ι₀₁ _ hL
  have hRs (j : Fin 2) := fraction_fixedFamily_leg G j horn₂₀.ι₀₂ _ hR
  have hv' : v' = v := fraction_fixedVertex_ext
    ((hLs 1).trans ((fraction_precomposition_edges cs).2.trans hvs.symm))
    ((hRs 1).trans ((fraction_precomposition_edges cf).2.trans hvf.symm))
  have he : (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y).Edge w v' :=
    ⟨SSet.yonedaEquiv G, intervalMap_source G, intervalMap_target G⟩
  exact ⟨w, (SSet.π₀.sound he).trans (congrArg SSet.π₀.mk hv'),
    (hLs 0).trans (fraction_precomposition_edges cs).1,
    (hRs 0).trans (fraction_precomposition_edges cf).1⟩

/-- h 商で一致する実 roof の共通細分を、元の両端固定 span 空間の同じ成分へ戻す。 -/
private lemma equal_fractionClasses_component {a₁ a₂ x y : B.obj _⦋0⦌}
    (s₁ : Truncated.Edge (X := (truncation 2).obj B.obj) a₁ x)
    (s₂ : Truncated.Edge (X := (truncation 2).obj B.obj) a₂ x)
    (f₁ : Truncated.Edge (X := (truncation 2).obj B.obj) a₁ y)
    (f₂ : Truncated.Edge (X := (truncation 2).obj B.obj) a₂ y)
    (hs₁ : s₁.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) (hs₂ : s₂.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
    (he : fractionClass h s₁ f₁ hs₁ = fractionClass h s₂ f₂ hs₂)
    (v₁ v₂ : (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) _⦋0⦌)
    (hv₁s : spanLeftEdge v₁.val.val = s₁.edge)
    (hv₂s : spanLeftEdge v₂.val.val = s₂.edge)
    (hv₁f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app B.obj).app
      (Opposite.op ⦋0⦌) v₁.val.val) = f₁.edge)
    (hv₂f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app B.obj).app
      (Opposite.op ⦋0⦌) v₂.val.val) = f₂.edge) :
    SSet.π₀.mk v₁ = SSet.π₀.mk v₂ := by
  obtain ⟨a, t₁, t₂, s, f, hs, ⟨cs₁⟩, ⟨cs₂⟩, ⟨cf₁⟩, ⟨cf₂⟩⟩ :=
    equal_fractionClasses_refine h s₁ s₂ f₁ f₂ hs₁ hs₂ he
  obtain ⟨w₁, hw₁, hw₁s, hw₁f⟩ :=
    fraction_refinement_component h t₁ s₁ f₁ s f cs₁ cf₁ hs₁ hs v₁ hv₁s hv₁f
  obtain ⟨w₂, hw₂, hw₂s, hw₂f⟩ :=
    fraction_refinement_component h t₂ s₂ f₂ s f cs₂ cf₂ hs₂ hs v₂ hv₂s hv₂f
  have hw : w₁ = w₂ := fraction_fixedVertex_ext
    (hw₁s.trans hw₂s.symm) (hw₁f.trans hw₂f.symm)
  exact hw₁.symm.trans ((congrArg SSet.π₀.mk hw).trans hw₂)

omit h in
private lemma fraction_vertexEdge_endpoints {X : SSet.{u}}
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    X.δ (1 : Fin 2) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
        (Opposite.op ⦋0⦌) v ∧
    X.δ (0 : Fin 2) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
        (Opposite.op ⦋0⦌) v := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) X).surjective v
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  exact ⟨intervalMap_source f, intervalMap_target f⟩

/-- 両端固定の実 span の二辺を、元の一次単体を変えずに型付きで回収する。 -/
private lemma fraction_fixedVertex_edges {x y : B.obj _⦋0⦌}
    (v : (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) _⦋0⦌) :
    ∃ (a : B.obj _⦋0⦌)
      (s : Truncated.Edge (X := (truncation 2).obj B.obj) a x)
      (f : Truncated.Edge (X := (truncation 2).obj B.obj) a y),
      s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i ∧ spanLeftEdge v.val.val = s.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app B.obj).app
        (Opposite.op ⦋0⦌) v.val.val) = f.edge := by
  let l := ((pre horn₂₀.ι₀₁).app B.obj).app (Opposite.op ⦋0⦌) v.val.val
  let r := ((pre horn₂₀.ι₀₂).app B.obj).app (Opposite.op ⦋0⦌) v.val.val
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
    (Opposite.op ⦋0⦌) l
  have hl := congrArg (fun F => F.app (Opposite.op ⦋0⦌) v)
    (fixedMarkedSpan_source B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
    (Opposite.op ⦋0⦌) l = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0 at hl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hl
  have hr := congrArg (fun F => F.app (Opposite.op ⦋0⦌) v)
    (fixedMarkedSpan_target B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
    (Opposite.op ⦋0⦌) r = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0 at hr
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hr
  have ha : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
      (Opposite.op ⦋0⦌) r = a := by
    rfl
  let s : Truncated.Edge (X := (truncation 2).obj B.obj) a x :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge l, (fraction_vertexEdge_endpoints l).1,
      (fraction_vertexEdge_endpoints l).2.trans hl⟩
  let f : Truncated.Edge (X := (truncation 2).obj B.obj) a y :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge r, (fraction_vertexEdge_endpoints r).1.trans ha,
      (fraction_vertexEdge_endpoints r).2.trans hr⟩
  exact ⟨a, s, f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v.val, rfl, rfl⟩

omit h in
private lemma fraction_triangle_faceEdge {X : SSet.{u}}
    (T : (Δ[2] : SSet.{u}) ⟶ X) (j : Fin 3) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre (stdSimplex.δ j)).app X).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex T)) = X.δ j (SSet.yonedaEquiv T) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (stdSimplex.δ j ≫ T)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, stdSimplex.yonedaEquiv_δ_comp]

/-- 選択済みの評価三角形は、元の分母・分子の商像と回収した評価辺を三辺に持つ。 -/
private lemma fraction_evaluation_compStruct {a x y : B.obj _⦋0⦌}
    (v : (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) _⦋0⦌)
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) a x)
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) a y)
    (hvs : spanLeftEdge v.val.val = s.edge)
    (hvf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app B.obj).app
      (Opposite.op ⦋0⦌) v.val.val) = f.edge) :
    Nonempty (Truncated.Edge.CompStruct (s.map ((truncation 2).map q.hom))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex
        ((fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y).app
          (Opposite.op ⦋0⦌) v)).toTruncated (f.map ((truncation 2).map q.hom))) := by
  let z := (fractionEvaluationTriangle q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts).app
    (Opposite.op ⦋0⦌) v.val
  let T := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] : SSet.{u}) C.obj).symm z
  have hT : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex T = z := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply z
  have he := congrArg (fun F => F.app (Opposite.op ⦋0⦌) v)
    (fixedFractionEvaluation_inclusion q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y)
  change ((fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y).app
    (Opposite.op ⦋0⦌) v).val =
      ((pre (stdSimplex.δ (0 : Fin 3))).app C.obj).app (Opposite.op ⦋0⦌) z at he
  have h₀ := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge he
  rw [← hT, fraction_triangle_faceEdge] at h₀
  have hp := congrArg (fun F => F.app (Opposite.op ⦋0⦌) v.val)
    (fractionEvaluationTriangle_span q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts)
  change ((pre (horn 2 0).ι).app C.obj).app (Opposite.op ⦋0⦌) z =
    ((ihom (horn 2 0 : SSet.{u})).map q.hom).app
      (Opposite.op ⦋0⦌) v.val.val at hp
  have h₂ := congrArg spanLeftEdge hp
  rw [spanLeftEdge_postcomp, hvs, ← hT] at h₂
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre (stdSimplex.δ (2 : Fin 3))).app C.obj).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex T)) = q.hom.app (Opposite.op ⦋1⦌) s.edge at h₂
  rw [fraction_triangle_faceEdge] at h₂
  have h₁ := congrArg (fun w => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge
    (((pre horn₂₀.ι₀₂).app C.obj).app (Opposite.op ⦋0⦌) w)) hp
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre (stdSimplex.δ (1 : Fin 3))).app C.obj).app
    (Opposite.op ⦋0⦌) z) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((ihom (Δ[1] : SSet.{u})).map q.hom).app
        (Opposite.op ⦋0⦌) (((pre horn₂₀.ι₀₂).app B.obj).app
          (Opposite.op ⦋0⦌) v.val.val)) at h₁
  rw [intervalFunctorVertexEdge_postcomp, hvf, ← hT, fraction_triangle_faceEdge] at h₁
  exact ⟨⟨SSet.yonedaEquiv T, h₂, h₀.symm, h₁⟩⟩

/-- 実評価辺の h 類は、元の二辺から計算する同じ roof の類。 -/
private lemma fraction_evaluation_class {a x y : B.obj _⦋0⦌}
    (v : (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) _⦋0⦌)
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) a x)
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) a y)
    (hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
    (hvs : spanLeftEdge v.val.val = s.edge)
    (hvf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre horn₂₀.ι₀₂).app B.obj).app
      (Opposite.op ⦋0⦌) v.val.val) = f.edge) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex
      ((fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y).app
        (Opposite.op ⦋0⦌) v)).toTruncated = fractionClass h s f hs := by
  obtain ⟨τ⟩ := fraction_evaluation_compStruct h v s f hvs hvf
  let W := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW
  let L := (hoFunctor.map q.hom).toFunctor
  letI : L.IsLocalization W := fraction_ho_localization h
  let φ : W.RightFraction (HomotopyCategory.mk x) (HomotopyCategory.mk y) :=
    ⟨Truncated.HomotopyCategory.homMk s, (fraction_denominator_iff h s).mpr hs,
      Truncated.HomotopyCategory.homMk f⟩
  haveI : IsIso (L.map (Truncated.HomotopyCategory.homMk s)) :=
    Localization.inverts L W _ φ.hs
  apply (cancel_epi (L.map (Truncated.HomotopyCategory.homMk s))).mp
  exact (Truncated.HomotopyCategory.homMk_comp_homMk τ).trans
    (MorphismProperty.RightFraction.map_s_comp_map φ L (Localization.inverts L W)).symm

private lemma fraction_evaluation_component_class {x y : B.obj _⦋0⦌}
    {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
      (q.hom.app (Opposite.op ⦋0⦌) y)) _⦋0⦌}
    (he : SSet.π₀.mk v = SSet.π₀.mk w) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex v).toTruncated =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex w).toTruncated := by
  have hh := (SSet.π₀.mk_eq_mk_iff v w).mp he
  clear he
  induction hh with
  | rel _ _ e =>
    obtain ⟨e⟩ := e
    haveI : IsIso (Truncated.HomotopyCategory.homMk e.toTruncated) :=
      IsGroupoid.all_isIso (C := hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
        (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) y))) _
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalRecoveredHom_eq_of_vertexIso
      (asIso (Truncated.HomotopyCategory.homMk e.toTruncated))
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- 実評価によって同じ成分へ送られる元の roof は、元の span 空間でも同じ成分。 -/
private lemma fraction_evaluation_mapPiZero_injective (x y : B.obj _⦋0⦌) :
    Function.Injective (SSet.mapπ₀
      (fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y)) := by
  intro a b he
  obtain ⟨v₁, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨v₂, rfl⟩ := SSet.π₀.mk_surjective b
  obtain ⟨a₁, s₁, f₁, hs₁, hv₁s, hv₁f⟩ := fraction_fixedVertex_edges h v₁
  obtain ⟨a₂, s₂, f₂, hs₂, hv₂s, hv₂f⟩ := fraction_fixedVertex_edges h v₂
  have hc := fraction_evaluation_component_class h he
  rw [fraction_evaluation_class h v₁ s₁ f₁ hs₁ hv₁s hv₁f,
    fraction_evaluation_class h v₂ s₂ f₂ hs₂ hv₂s hv₂f] at hc
  exact equal_fractionClasses_component h s₁ s₂ f₁ f₂ hs₁ hs₂ hc
    v₁ v₂ hv₁s hv₂s hv₁f hv₂f

end SerrePositivity.KST.LocalizingInvariants
