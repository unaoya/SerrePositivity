module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCosliceSpanAttachment

/-!
概要：有限個の指定商 coslice 辺の実右分数 span を、元の同じ有限図式へ同時に貼る。
方針：端点対と span の有限 coproduct を一つの pushout に貼り、全 coslice 図式を保つ。
規約：元の図式・全ての分母分子・指定二単体を同じ有限台で保持する。
使われ方：有限境界付きの全族に対する一つの実全錐と共有比較の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {J : Type u} {K : SSet.{u}}

/-- 全ての指定端点対の、元の図式への包含。 -/
def finiteFractionDiagramTargets (k₀ k₁ : J → K _⦋0⦌) :
    (∐ fun _ : J => ((Δ[0] : SSet.{u}) ⨿ Δ[0])) ⟶ K :=
  Sigma.desc (fun j => _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionDiagramTargets (k₀ j) (k₁ j))

/-- 全ての端点対を、同じ添字の span へ入れる。 -/
def finiteFractionSpanTargets :
    (∐ fun _ : J => ((Δ[0] : SSet.{u}) ⨿ Δ[0])) ⟶
      (∐ fun _ : J => (horn 2 0 : SSet.{u})) :=
  Sigma.desc (fun j => _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSpanTargets ≫ Sigma.ι (fun _ : J => (horn 2 0 : SSet.{u})) j)

/-- 元の有限図式へ全ての実右分数 span を同時に貼った台。 -/
abbrev finiteFractionAttachmentShape (k₀ k₁ : J → K _⦋0⦌) : SSet.{u} :=
  pushout (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets

instance finiteFractionAttachmentShape_finite [Finite J] [K.Finite]
    (k₀ k₁ : J → K _⦋0⦌) : (finiteFractionAttachmentShape k₀ k₁).Finite := by
  apply SSet.finite_of_isColimit (pushoutIsPushout (finiteFractionDiagramTargets k₀ k₁)
    finiteFractionSpanTargets)
  rintro (_ | (_ | _)) <;> simp only [span_left, span_right, span_zero] <;> infer_instance

variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q} {a : (Δ[0] : SSet.{u}) ⟶ C.obj}
  (p : K ⟶ B.obj) (U : K ⟶ sliceUnder a) (k₀ k₁ : J → K _⦋0⦌)
  {e : ∀ j : J, Truncated.Edge (X := (truncation 2).obj (sliceUnder a))
    (U.app (Opposite.op ⦋0⦌) (k₀ j)) (U.app (Opposite.op ⦋0⦌) (k₁ j))}
  (r : ∀ j : J, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCosliceFractionNormalization h a (e j)
    (p.app (Opposite.op ⦋0⦌) (k₀ j)) (p.app (Opposite.op ⦋0⦌) (k₁ j)))

lemma finiteCosliceSpan_native_pair : finiteFractionSpanTargets ≫
    Sigma.desc (fun j => (r j).nativeSpan) = finiteFractionDiagramTargets k₀ k₁ ≫ p := by
  apply Sigma.hom_ext
  intro j
  simp only [← Category.assoc, finiteFractionSpanTargets, finiteFractionDiagramTargets,
    Sigma.ι_comp_desc]
  rw [Category.assoc, Sigma.ι_comp_desc]
  exact _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.cosliceSpan_native_pair p U (k₀ j) (k₁ j) (r j)

lemma finiteCosliceSpan_lift_pair : finiteFractionSpanTargets ≫
    Sigma.desc (fun j => (r j).spanLift) = finiteFractionDiagramTargets k₀ k₁ ≫ U := by
  apply Sigma.hom_ext
  intro j
  simp only [← Category.assoc, finiteFractionSpanTargets, finiteFractionDiagramTargets,
    Sigma.ι_comp_desc]
  rw [Category.assoc, Sigma.ι_comp_desc]
  exact _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.cosliceSpan_lift_pair p U (k₀ j) (k₁ j) (r j)

/-- 全ての実分数と元の図式を含む、同じ一つの実有限図式。 -/
def finiteCosliceSpanNativeDiagram : finiteFractionAttachmentShape k₀ k₁ ⟶ B.obj :=
  pushout.desc p (Sigma.desc (fun j => (r j).nativeSpan))
    (finiteCosliceSpan_native_pair p U k₀ k₁ r).symm

/-- 指定された全ての coslice 持ち上げを、同じ有限台で同時に保持する。 -/
def finiteCosliceSpanLiftDiagram : finiteFractionAttachmentShape k₀ k₁ ⟶ sliceUnder a :=
  pushout.desc U (Sigma.desc (fun j => (r j).spanLift))
    (finiteCosliceSpan_lift_pair p U k₀ k₁ r).symm

lemma finiteCosliceSpanNativeDiagram_original :
    pushout.inl (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets ≫
      finiteCosliceSpanNativeDiagram p U k₀ k₁ r = p := pushout.inl_desc _ _ _

lemma finiteCosliceSpanLiftDiagram_original :
    pushout.inl (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets ≫
      finiteCosliceSpanLiftDiagram p U k₀ k₁ r = U := pushout.inl_desc _ _ _

lemma finiteCosliceSpanNativeDiagram_fraction (j : J) :
    Sigma.ι (fun _ : J => (horn 2 0 : SSet.{u})) j ≫
      pushout.inr (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets ≫
        finiteCosliceSpanNativeDiagram p U k₀ k₁ r = (r j).nativeSpan := by
  rw [finiteCosliceSpanNativeDiagram, pushout.inr_desc, Sigma.ι_comp_desc]

lemma finiteCosliceSpanLiftDiagram_fraction (j : J) :
    Sigma.ι (fun _ : J => (horn 2 0 : SSet.{u})) j ≫
      pushout.inr (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets ≫
        finiteCosliceSpanLiftDiagram p U k₀ k₁ r = (r j).spanLift := by
  rw [finiteCosliceSpanLiftDiagram, pushout.inr_desc, Sigma.ι_comp_desc]

lemma finiteCosliceSpanLiftDiagram_projection
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    finiteCosliceSpanLiftDiagram p U k₀ k₁ r ≫ sliceUnderProjection a =
      finiteCosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom := by
  apply pushout.hom_ext
  · simp only [← Category.assoc, finiteCosliceSpanLiftDiagram,
      finiteCosliceSpanNativeDiagram, pushout.inl_desc]
    exact hU
  · simp only [← Category.assoc, finiteCosliceSpanLiftDiagram,
      finiteCosliceSpanNativeDiagram, pushout.inr_desc]
    apply Sigma.hom_ext
    intro j
    simp only [← Category.assoc, Sigma.ι_comp_desc]
    exact (r j).spanLift_projection

/-- 全ての実分数と元の図式を一度に保つ、同じ指定商全錐。 -/
def finiteCosliceSpanQuotientCone (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    JoinCone (finiteCosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom) :=
  ⟨sliceUnderUncurry (finiteCosliceSpanLiftDiagram p U k₀ k₁ r),
    (sliceUnderUncurry_projection _).trans
      (finiteCosliceSpanLiftDiagram_projection p U k₀ k₁ r hU)⟩

lemma finiteCosliceSpanQuotientCone_original
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    joinMap (𝟙 (Δ[0] : SSet.{u}))
        (pushout.inl (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets) ≫
      (finiteCosliceSpanQuotientCone p U k₀ k₁ r hU).val = sliceUnderUncurry U := by
  change joinMap (𝟙 (Δ[0] : SSet.{u})) _ ≫ sliceUnderUncurry _ = _
  rw [← sliceUnderUncurry_precomp, finiteCosliceSpanLiftDiagram_original]

lemma finiteCosliceSpanQuotientCone_fraction
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) (j : J) :
    joinMap (𝟙 (Δ[0] : SSet.{u}))
        (Sigma.ι (fun _ : J => (horn 2 0 : SSet.{u})) j ≫
          pushout.inr (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets) ≫
      (finiteCosliceSpanQuotientCone p U k₀ k₁ r hU).val = (r j).quotientCone.val := by
  change joinMap (𝟙 (Δ[0] : SSet.{u})) _ ≫ sliceUnderUncurry _ = sliceUnderUncurry _
  rw [← sliceUnderUncurry_precomp, Category.assoc, finiteCosliceSpanLiftDiagram_fraction]

/-- 同じ全 slice 同型から、元の全図式への比較を取り出す。 -/
def finiteCosliceSpanComparison_original
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom)
    (c : JoinCone (finiteCosliceSpanNativeDiagram p U k₀ k₁ r))
    (e' : VertexIso (X := sliceOver (finiteCosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom))
      (mapJoinCone q.hom c) (finiteCosliceSpanQuotientCone p U k₀ k₁ r hU)) :
    FunctorIso (joinMap (𝟙 (Δ[0] : SSet.{u}))
      (pushout.inl (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets) ≫
        c.val ≫ q.hom) (sliceUnderUncurry U) := by
  have e₀ := (coneFunctorIsoOfVertexIso _ _ e').precomp
    (joinMap (𝟙 (Δ[0] : SSet.{u}))
      (pushout.inl (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets))
  rw [finiteCosliceSpanQuotientCone_original] at e₀
  simpa only [mapJoinCone, Category.assoc] using e₀

/-- 全ての分数比較は、同じ全 slice 同型を同じ各 span へ制限して得る。 -/
def finiteCosliceSpanComparison_fraction
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom)
    (c : JoinCone (finiteCosliceSpanNativeDiagram p U k₀ k₁ r))
    (e' : VertexIso (X := sliceOver (finiteCosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom))
      (mapJoinCone q.hom c) (finiteCosliceSpanQuotientCone p U k₀ k₁ r hU)) (j : J) :
    FunctorIso (joinMap (𝟙 (Δ[0] : SSet.{u}))
      (Sigma.ι (fun _ : J => (horn 2 0 : SSet.{u})) j ≫
        pushout.inr (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets) ≫
          c.val ≫ q.hom) (r j).quotientCone.val := by
  have e₀ := (coneFunctorIsoOfVertexIso _ _ e').precomp
    (joinMap (𝟙 (Δ[0] : SSet.{u})) (Sigma.ι (fun _ : J => (horn 2 0 : SSet.{u})) j ≫
      pushout.inr (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets))
  rw [finiteCosliceSpanQuotientCone_fraction] at e₀
  simpa only [mapJoinCone, Category.assoc] using e₀

/-- 全ての指定分数と元の有限図式に共通な、一つの実全錐と全比較を回収する。 -/
lemma exists_finiteCosliceSpanAttachmentRefinement [Finite J] [K.Finite]
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    ∃ c : JoinCone (finiteCosliceSpanNativeDiagram p U k₀ k₁ r),
      ∃ _iso : VertexIso
        (X := sliceOver (finiteCosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom))
        (mapJoinCone q.hom c) (finiteCosliceSpanQuotientCone p U k₀ k₁ r hU),
        ∀ k : (finiteFractionAttachmentShape k₀ k₁) _⦋0⦌,
          IsInvertibleEdge (X := C.obj)
            (F2.nativeConeLeg (finiteCosliceSpanQuotientCone p U k₀ k₁ r hU) k) →
          (F2.nativeConeLeg c k).edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i := by
  obtain ⟨c, ⟨e'⟩⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierQuotientConeIsoRefinement h
    (finiteCosliceSpanNativeDiagram p U k₀ k₁ r) (finiteCosliceSpanQuotientCone p U k₀ k₁ r hU)
  refine ⟨c, e', ?_⟩
  intro k hk
  apply (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.mem_weakEquivalences_iff_invertible h (F2.nativeConeLeg c k)).mpr
  exact (isInvertibleEdge_congr (e := F2.nativeConeLeg (mapJoinCone q.hom c) k)
    (f := (F2.nativeConeLeg c k).map ((truncation 2).map q.hom)) rfl).mp
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.nativeConeLeg_invertible_of_sliceIso e' k hk)

/-- 有限個の指定商 coslice 辺から、全ての実分数・同じ有限全錐・全比較を一括回収する。 -/
lemma exists_verdierFiniteCosliceSpanFamilyAttachment [Finite J] [K.Finite]
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    ∃ r₀ : ∀ j : J, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCosliceFractionNormalization h a (e j)
        (p.app (Opposite.op ⦋0⦌) (k₀ j)) (p.app (Opposite.op ⦋0⦌) (k₁ j)),
      ∃ c : JoinCone (finiteCosliceSpanNativeDiagram p U k₀ k₁ r₀),
        ∃ _iso : VertexIso
          (X := sliceOver (finiteCosliceSpanNativeDiagram p U k₀ k₁ r₀ ≫ q.hom))
          (mapJoinCone q.hom c) (finiteCosliceSpanQuotientCone p U k₀ k₁ r₀ hU),
          ∀ k : (finiteFractionAttachmentShape k₀ k₁) _⦋0⦌,
            IsInvertibleEdge (X := C.obj)
              (F2.nativeConeLeg (finiteCosliceSpanQuotientCone p U k₀ k₁ r₀ hU) k) →
            (F2.nativeConeLeg c k).edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i := by
  have hk (k : K _⦋0⦌) :
      (sliceUnderProjection a).app (Opposite.op ⦋0⦌) (U.app (Opposite.op ⦋0⦌) k) =
        q.hom.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) k) :=
    congrArg (fun f : K ⟶ C.obj => f.app (Opposite.op ⦋0⦌) k) hU
  have hr (j : J) : Nonempty (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCosliceFractionNormalization h a (e j)
      (p.app (Opposite.op ⦋0⦌) (k₀ j)) (p.app (Opposite.op ⦋0⦌) (k₁ j))) :=
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierCosliceFractionNormalization h a (e j)
      (p.app (Opposite.op ⦋0⦌) (k₀ j)) (p.app (Opposite.op ⦋0⦌) (k₁ j)) (hk _) (hk _)
  let r₀ (j : J) := Classical.choice (hr j)
  obtain ⟨c, e', hw⟩ := exists_finiteCosliceSpanAttachmentRefinement p U k₀ k₁ r₀ hU
  exact ⟨r₀, c, e', hw⟩

end SerrePositivity.KST.LocalizingInvariants
