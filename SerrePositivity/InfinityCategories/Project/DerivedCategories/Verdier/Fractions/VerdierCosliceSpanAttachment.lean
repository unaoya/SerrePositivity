module


public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 二頂点を、実 span の二つの終点へ含める固定射。 -/
def fractionSpanTargets : ((Δ[0] : SSet.{u}) ⨿ Δ[0]) ⟶ (horn 2 0 : SSet.{u}) :=
  coprod.desc (stdSimplex.δ 0 ≫ horn₂₀.ι₀₁) (stdSimplex.δ 0 ≫ horn₂₀.ι₀₂)

/-- 元の図式で指定された同じ二頂点への包含。 -/
def fractionDiagramTargets {K : SSet.{u}} (k₀ k₁ : K _⦋0⦌) :
    ((Δ[0] : SSet.{u}) ⨿ Δ[0]) ⟶ K :=
  coprod.desc (SSet.yonedaEquiv.symm k₀) (SSet.yonedaEquiv.symm k₁)

/-- 元の図式へ一つの実右分数 span を貼った有限台。 -/
abbrev fractionSpanAttachmentShape {K : SSet.{u}} (k₀ k₁ : K _⦋0⦌) : SSet.{u} :=
  pushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets k₀ k₁) _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets

instance fractionSpanAttachmentShape_finite {K : SSet.{u}} [K.Finite]
    (k₀ k₁ : K _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanAttachmentShape k₀ k₁).Finite := by
  apply SSet.finite_of_isColimit (pushoutIsPushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets k₀ k₁)
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets)
  rintro (_ | (_ | _)) <;> simp only [span_left, span_right, span_zero] <;> infer_instance

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {K : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ C.obj}
  (p : K ⟶ B.obj) (U : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) (k₀ k₁ : K _⦋0⦌)
  {e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a))
    (U.app (Opposite.op ⦋0⦌) k₀) (U.app (Opposite.op ⦋0⦌) k₁)}
  (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization h a e
    (p.app (Opposite.op ⦋0⦌) k₀) (p.app (Opposite.op ⦋0⦌) k₁))

lemma cosliceSpan_native_pair : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets ≫ r.nativeSpan =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets k₀ k₁ ≫ p := by
  apply coprod.hom_ext
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets, coprod.inl_desc]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.nativeSpan,
      horn₂₀.isPushout.inl_desc]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
    have ht : B.obj.δ 0 r.denominator.edge = p.app (Opposite.op ⦋0⦌) k₀ :=
      r.denominator.tgt_eq
    rw [ht]
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets, coprod.inr_desc]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.nativeSpan,
      horn₂₀.isPushout.inr_desc]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
    have ht : B.obj.δ 0 r.numerator.edge = p.app (Opposite.op ⦋0⦌) k₁ := r.numerator.tgt_eq
    rw [ht]

lemma cosliceSpan_lift_pair : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets ≫ r.spanLift =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets k₀ k₁ ≫ U := by
  apply coprod.hom_ext
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets, coprod.inl_desc]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.spanLift,
      horn₂₀.isPushout.inl_desc]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
    have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a).δ 0 r.lift.first.edge = U.app (Opposite.op ⦋0⦌) k₀ :=
      r.lift.first.tgt_eq
    rw [ht]
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets, coprod.inr_desc]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.spanLift,
      horn₂₀.isPushout.inr_desc]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
    have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a).δ 0 r.lift.diagonal.edge = U.app (Opposite.op ⦋0⦌) k₁ :=
      r.lift.diagonal.tgt_eq
    rw [ht]

/-- 同じ元の図式と実右分数 span を貼った実全図式。 -/
def cosliceSpanNativeDiagram : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanAttachmentShape k₀ k₁ ⟶ B.obj :=
  pushout.desc p r.nativeSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpan_native_pair p U k₀ k₁ r).symm

/-- 指定商錐の同じ coslice 図式を、同じ実 span の持ち上げで延長する。 -/
def cosliceSpanLiftDiagram : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanAttachmentShape k₀ k₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a :=
  pushout.desc U r.spanLift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpan_lift_pair p U k₀ k₁ r).symm

lemma cosliceSpanNativeDiagram_original :
    pushout.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets k₀ k₁) _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U k₀ k₁ r = p := pushout.inl_desc _ _ _

lemma cosliceSpanLiftDiagram_original :
    pushout.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets k₀ k₁) _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram p U k₀ k₁ r = U := pushout.inl_desc _ _ _

lemma cosliceSpanLiftDiagram_projection
    (hU : U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = p ≫ q.hom) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram p U k₀ k₁ r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom := by
  apply pushout.hom_ext
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram,
      pushout.inl_desc]
    exact hU
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram,
      pushout.inr_desc]
    exact r.spanLift_projection

/-- 元の指定商錐を固定した、同じ新しい有限実図式の全商錐。 -/
def cosliceSpanQuotientCone (hU : U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = p ≫ q.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram p U k₀ k₁ r),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram_projection p U k₀ k₁ r hU)⟩

lemma cosliceSpanQuotientCone_original (hU : U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = p ≫ q.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (pushout.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets k₀ k₁) _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone p U k₀ k₁ r hU).val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry U := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram_original]

/-- 拡大した同じ有限台の指定商錐を、元の実全錐へ全 slice 比較で回収する。 -/
lemma exists_cosliceSpanAttachmentRefinement [K.Finite]
    (hU : U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = p ≫ q.hom) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U k₀ k₁ r),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone p U k₀ k₁ r hU)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierQuotientConeIsoRefinement h _ _

/-- 同じ slice 同型は、指定された個々の実錐の脚の可逆性を反映する。 -/
lemma nativeConeLeg_invertible_of_sliceIso {L X : SSet.{u}} [Quasicategory X]
    {b : L ⟶ X} {c t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone b} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver b) c t)
    (k : L _⦋0⦌) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg t k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k) := by
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDomainLeg k
  have ht' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X) (d.map ((truncation 2).map t.val)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := d.map ((truncation 2).map t.val))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg t k) rfl).mpr ht
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X) (d.map ((truncation 2).map c.val)) :=
    (NatIso.isIso_map_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFunctorIsoOfVertexIso c t e).toNatIso
      (Truncated.HomotopyCategory.homMk d)).mpr ht'
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := d.map ((truncation 2).map c.val))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k) rfl).mp hc

/-- 同じ有限全錐の比較を保ち、指定商錐の可逆な脚から実弱同値の脚を回収する。 -/
lemma exists_cosliceSpanAttachmentRefinement_with_weakLegs [K.Finite]
    (hU : U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = p ≫ q.hom) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U k₀ k₁ r),
      ∃ _iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U k₀ k₁ r ≫ q.hom))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone p U k₀ k₁ r hU),
        ∀ k : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanAttachmentShape k₀ k₁) _⦋0⦌,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C.obj)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone p U k₀ k₁ r hU) k) →
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  obtain ⟨c, ⟨e'⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_cosliceSpanAttachmentRefinement p U k₀ k₁ r hU
  refine ⟨c, e', ?_⟩
  intro k hk
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k)).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) k)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k).map ((truncation 2).map q.hom)) rfl).mp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.nativeConeLeg_invertible_of_sliceIso e' k hk)

/-- 有限な元の図式と指定商錐から、一つの右分数添付と実全錐を一括回収する。 -/
lemma exists_verdierFiniteCosliceSpanAttachment [K.Finite]
    (hU : U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = p ≫ q.hom) :
    ∃ r₀ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization h a e
        (p.app (Opposite.op ⦋0⦌) k₀) (p.app (Opposite.op ⦋0⦌) k₁),
      ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U k₀ k₁ r₀),
        ∃ _iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
            (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U k₀ k₁ r₀ ≫ q.hom))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone p U k₀ k₁ r₀ hU),
          ∀ k : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanAttachmentShape k₀ k₁) _⦋0⦌,
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C.obj)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone p U k₀ k₁ r₀ hU) k) →
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  have hk (k : K _⦋0⦌) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) (U.app (Opposite.op ⦋0⦌) k) =
      q.hom.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) k) :=
    congrArg (fun f : K ⟶ C.obj => f.app (Opposite.op ⦋0⦌) k) hU
  obtain ⟨r₀⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierCosliceFractionNormalization h a e
    (p.app (Opposite.op ⦋0⦌) k₀) (p.app (Opposite.op ⦋0⦌) k₁) (hk k₀) (hk k₁)
  obtain ⟨c, e', hw⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_cosliceSpanAttachmentRefinement_with_weakLegs p U k₀ k₁ r₀ hU
  exact ⟨r₀, c, e', hw⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
