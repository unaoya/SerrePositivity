module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCosliceFractionNormalization
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits

/-!
概要：元の有限図式へ同じ実右分数 span を貼り、指定商錐を全図式のまま延長する。
方針：元の二頂点に沿う pushout に、実 span と同じ coslice 持ち上げを同時に貼る。
規約：元の図式・指定商錐の制限は厳密に固定し、新しい有限図式へ商錐回収を実適用する。
使われ方：有限線型図式の正規化で、隣接二辺の右分数を同じ有限台へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 二頂点を、実 span の二つの終点へ含める固定射。 -/
def fractionSpanTargets : ((Δ[0] : SSet.{u}) ⨿ Δ[0]) ⟶ (horn 2 0 : SSet.{u}) :=
  coprod.desc (stdSimplex.δ 0 ≫ horn₂₀.ι₀₁) (stdSimplex.δ 0 ≫ horn₂₀.ι₀₂)

/-- 元の図式で指定された同じ二頂点への包含。 -/
def fractionDiagramTargets {K : SSet.{u}} (k₀ k₁ : K _⦋0⦌) :
    ((Δ[0] : SSet.{u}) ⨿ Δ[0]) ⟶ K :=
  coprod.desc (SSet.yonedaEquiv.symm k₀) (SSet.yonedaEquiv.symm k₁)

/-- 元の図式へ一つの実右分数 span を貼った有限台。 -/
abbrev fractionSpanAttachmentShape {K : SSet.{u}} (k₀ k₁ : K _⦋0⦌) : SSet.{u} :=
  pushout (fractionDiagramTargets k₀ k₁) fractionSpanTargets

instance fractionSpanAttachmentShape_finite {K : SSet.{u}} [K.Finite]
    (k₀ k₁ : K _⦋0⦌) : (fractionSpanAttachmentShape k₀ k₁).Finite := by
  apply SSet.finite_of_isColimit (pushoutIsPushout (fractionDiagramTargets k₀ k₁)
    fractionSpanTargets)
  rintro (_ | (_ | _)) <;> simp only [span_left, span_right, span_zero] <;> infer_instance

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {K : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ C.obj}
  (p : K ⟶ B.obj) (U : K ⟶ sliceUnder a) (k₀ k₁ : K _⦋0⦌)
  {e : Truncated.Edge (X := (truncation 2).obj (sliceUnder a))
    (U.app (Opposite.op ⦋0⦌) k₀) (U.app (Opposite.op ⦋0⦌) k₁)}
  (r : VerdierCosliceFractionNormalization h a e
    (p.app (Opposite.op ⦋0⦌) k₀) (p.app (Opposite.op ⦋0⦌) k₁))

lemma cosliceSpan_native_pair : fractionSpanTargets ≫ r.nativeSpan =
    fractionDiagramTargets k₀ k₁ ≫ p := by
  apply coprod.hom_ext
  · simp only [← Category.assoc, fractionSpanTargets, fractionDiagramTargets, coprod.inl_desc]
    simp only [Category.assoc, VerdierCosliceFractionNormalization.nativeSpan,
      horn₂₀.isPushout.inl_desc]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
    have ht : B.obj.δ 0 r.denominator.edge = p.app (Opposite.op ⦋0⦌) k₀ :=
      r.denominator.tgt_eq
    rw [ht]
  · simp only [← Category.assoc, fractionSpanTargets, fractionDiagramTargets, coprod.inr_desc]
    simp only [Category.assoc, VerdierCosliceFractionNormalization.nativeSpan,
      horn₂₀.isPushout.inr_desc]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
    have ht : B.obj.δ 0 r.numerator.edge = p.app (Opposite.op ⦋0⦌) k₁ := r.numerator.tgt_eq
    rw [ht]

lemma cosliceSpan_lift_pair : fractionSpanTargets ≫ r.spanLift =
    fractionDiagramTargets k₀ k₁ ≫ U := by
  apply coprod.hom_ext
  · simp only [← Category.assoc, fractionSpanTargets, fractionDiagramTargets, coprod.inl_desc]
    simp only [Category.assoc, VerdierCosliceFractionNormalization.spanLift,
      horn₂₀.isPushout.inl_desc]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
    have ht : (sliceUnder a).δ 0 r.lift.first.edge = U.app (Opposite.op ⦋0⦌) k₀ :=
      r.lift.first.tgt_eq
    rw [ht]
  · simp only [← Category.assoc, fractionSpanTargets, fractionDiagramTargets, coprod.inr_desc]
    simp only [Category.assoc, VerdierCosliceFractionNormalization.spanLift,
      horn₂₀.isPushout.inr_desc]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
    have ht : (sliceUnder a).δ 0 r.lift.diagonal.edge = U.app (Opposite.op ⦋0⦌) k₁ :=
      r.lift.diagonal.tgt_eq
    rw [ht]

/-- 同じ元の図式と実右分数 span を貼った実全図式。 -/
def cosliceSpanNativeDiagram : fractionSpanAttachmentShape k₀ k₁ ⟶ B.obj :=
  pushout.desc p r.nativeSpan (cosliceSpan_native_pair p U k₀ k₁ r).symm

/-- 指定商錐の同じ coslice 図式を、同じ実 span の持ち上げで延長する。 -/
def cosliceSpanLiftDiagram : fractionSpanAttachmentShape k₀ k₁ ⟶ sliceUnder a :=
  pushout.desc U r.spanLift (cosliceSpan_lift_pair p U k₀ k₁ r).symm

lemma cosliceSpanNativeDiagram_original :
    pushout.inl (fractionDiagramTargets k₀ k₁) fractionSpanTargets ≫
      cosliceSpanNativeDiagram p U k₀ k₁ r = p := pushout.inl_desc _ _ _

lemma cosliceSpanLiftDiagram_original :
    pushout.inl (fractionDiagramTargets k₀ k₁) fractionSpanTargets ≫
      cosliceSpanLiftDiagram p U k₀ k₁ r = U := pushout.inl_desc _ _ _

lemma cosliceSpanLiftDiagram_projection
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    cosliceSpanLiftDiagram p U k₀ k₁ r ≫ sliceUnderProjection a =
      cosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom := by
  apply pushout.hom_ext
  · simp only [← Category.assoc, cosliceSpanNativeDiagram, cosliceSpanLiftDiagram,
      pushout.inl_desc]
    exact hU
  · simp only [← Category.assoc, cosliceSpanNativeDiagram, cosliceSpanLiftDiagram,
      pushout.inr_desc]
    exact r.spanLift_projection

/-- 元の指定商錐を固定した、同じ新しい有限実図式の全商錐。 -/
def cosliceSpanQuotientCone (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    JoinCone (cosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom) :=
  ⟨sliceUnderUncurry (cosliceSpanLiftDiagram p U k₀ k₁ r),
    (sliceUnderUncurry_projection _).trans
      (cosliceSpanLiftDiagram_projection p U k₀ k₁ r hU)⟩

lemma cosliceSpanQuotientCone_original (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    joinMap (𝟙 Δ[0]) (pushout.inl (fractionDiagramTargets k₀ k₁) fractionSpanTargets) ≫
      (cosliceSpanQuotientCone p U k₀ k₁ r hU).val = sliceUnderUncurry U := by
  rw [cosliceSpanQuotientCone, ← sliceUnderUncurry_precomp,
    cosliceSpanLiftDiagram_original]

/-- 拡大した同じ有限台の指定商錐を、元の実全錐へ全 slice 比較で回収する。 -/
lemma exists_cosliceSpanAttachmentRefinement [K.Finite]
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    ∃ c : JoinCone (cosliceSpanNativeDiagram p U k₀ k₁ r),
      Nonempty (VertexIso (X := sliceOver (cosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom))
        (mapJoinCone q.hom c) (cosliceSpanQuotientCone p U k₀ k₁ r hU)) :=
  exists_verdierQuotientConeIsoRefinement h _ _

/-- 同じ slice 同型は、指定された個々の実錐の脚の可逆性を反映する。 -/
lemma nativeConeLeg_invertible_of_sliceIso {L X : SSet.{u}} [Quasicategory X]
    {b : L ⟶ X} {c t : JoinCone b} (e : VertexIso (X := sliceOver b) c t)
    (k : L _⦋0⦌) (ht : IsInvertibleEdge (X := X) (F2.nativeConeLeg t k)) :
    IsInvertibleEdge (X := X) (F2.nativeConeLeg c k) := by
  let d := F2.coneDomainLeg k
  have ht' : IsInvertibleEdge (X := X) (d.map ((truncation 2).map t.val)) :=
    (isInvertibleEdge_congr (e := d.map ((truncation 2).map t.val))
      (f := F2.nativeConeLeg t k) rfl).mpr ht
  have hc : IsInvertibleEdge (X := X) (d.map ((truncation 2).map c.val)) :=
    (NatIso.isIso_map_iff (coneFunctorIsoOfVertexIso c t e).toNatIso
      (Truncated.HomotopyCategory.homMk d)).mpr ht'
  exact (isInvertibleEdge_congr (e := d.map ((truncation 2).map c.val))
    (f := F2.nativeConeLeg c k) rfl).mp hc

/-- 同じ有限全錐の比較を保ち、指定商錐の可逆な脚から実弱同値の脚を回収する。 -/
lemma exists_cosliceSpanAttachmentRefinement_with_weakLegs [K.Finite]
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    ∃ c : JoinCone (cosliceSpanNativeDiagram p U k₀ k₁ r),
      ∃ _iso : VertexIso (X := sliceOver (cosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom))
        (mapJoinCone q.hom c) (cosliceSpanQuotientCone p U k₀ k₁ r hU),
        ∀ k : (fractionSpanAttachmentShape k₀ k₁) _⦋0⦌,
          IsInvertibleEdge (X := C.obj)
            (F2.nativeConeLeg (cosliceSpanQuotientCone p U k₀ k₁ r hU) k) →
          (F2.nativeConeLeg c k).edge ∈ weakEquivalences i := by
  obtain ⟨c, ⟨e'⟩⟩ := exists_cosliceSpanAttachmentRefinement p U k₀ k₁ r hU
  refine ⟨c, e', ?_⟩
  intro k hk
  apply (mem_weakEquivalences_iff_invertible h (F2.nativeConeLeg c k)).mpr
  exact (isInvertibleEdge_congr (e := F2.nativeConeLeg (mapJoinCone q.hom c) k)
    (f := (F2.nativeConeLeg c k).map ((truncation 2).map q.hom)) rfl).mp
      (nativeConeLeg_invertible_of_sliceIso e' k hk)

/-- 有限な元の図式と指定商錐から、一つの右分数添付と実全錐を一括回収する。 -/
lemma exists_verdierFiniteCosliceSpanAttachment [K.Finite]
    (hU : U ≫ sliceUnderProjection a = p ≫ q.hom) :
    ∃ r₀ : VerdierCosliceFractionNormalization h a e
        (p.app (Opposite.op ⦋0⦌) k₀) (p.app (Opposite.op ⦋0⦌) k₁),
      ∃ c : JoinCone (cosliceSpanNativeDiagram p U k₀ k₁ r₀),
        ∃ _iso : VertexIso
            (X := sliceOver (cosliceSpanNativeDiagram p U k₀ k₁ r₀ ≫ q.hom))
            (mapJoinCone q.hom c) (cosliceSpanQuotientCone p U k₀ k₁ r₀ hU),
          ∀ k : (fractionSpanAttachmentShape k₀ k₁) _⦋0⦌,
            IsInvertibleEdge (X := C.obj)
              (F2.nativeConeLeg (cosliceSpanQuotientCone p U k₀ k₁ r₀ hU) k) →
            (F2.nativeConeLeg c k).edge ∈ weakEquivalences i := by
  have hk (k : K _⦋0⦌) :
      (sliceUnderProjection a).app (Opposite.op ⦋0⦌) (U.app (Opposite.op ⦋0⦌) k) =
      q.hom.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) k) :=
    congrArg (fun f : K ⟶ C.obj => f.app (Opposite.op ⦋0⦌) k) hU
  obtain ⟨r₀⟩ := exists_verdierCosliceFractionNormalization h a e
    (p.app (Opposite.op ⦋0⦌) k₀) (p.app (Opposite.op ⦋0⦌) k₁) (hk k₀) (hk k₁)
  obtain ⟨c, e', hw⟩ := exists_cosliceSpanAttachmentRefinement_with_weakLegs p U k₀ k₁ r₀ hU
  exact ⟨r₀, c, e', hw⟩

end SerrePositivity.KST.LocalizingInvariants
