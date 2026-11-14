module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGOppositeClosedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ComplexMappingCoconeSndQuasiIso
/-!
概要：普遍余単位の実 comma の標的射影を、同じ cocone 射影と元の Hom 比較へ同定する。
方針：反対での実閉前合成を戻し、第二射影の準同型性と各次数の切断を使う。
規約：全 Hom の全整数次数を保持。使われ方：標的 nerve の自明 Kan fibration 性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex
variable (R : Type u) [CommRing R] (C E : Type v) [DGCategory R C] [DGCategory R E]
  (F : DGFunctor R C E) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalComma R C E F)
/-- 同じ標的 Hom 射影は、反対 comma の実第二射影そのもの。 -/
lemma dgUniversalCommaTarget_map :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F).map X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R Cᵒᵖ Eᵒᵖ F.op
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaDualLabel R C E F Y.label)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaDualLabel R C E F X.label) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget, EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation,
    DGFunctor.op, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDoubleOppositeDown, Category.id_comp]
  rfl
/-- 同じ普遍余単位の全 Hom 比較から、標的 Hom 射影の準同型性を得る。 -/
lemma dgUniversalCommaTarget_map_quasiIso :
    QuasiIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F).map X Y) := by
  let A := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaDualLabel R C E F Y.label
  let B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaDualLabel R C E F X.label
  let q := F.op.map A.source B.source ≫ eHomWhiskerRight (Complex R) A.augmentation
    (ForgetEnrichment.of (Complex R) (F.op.obj B.source))
  have hq : QuasiIso q := by
    change QuasiIso (F.map X.label.universal.source Y.label.universal.source ≫
      eHomWhiskerRight (Complex R)
        ((forgetEnrichmentOppositeEquivalence (Complex R) E).inverse.map
          Y.label.universal.counit.op)
        (ForgetEnrichment.of (Complex R) (Opposite.op (F.obj X.label.universal.source))))
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOppositePrecomposition_eq_postcomposition]
    have hc := Y.label.universal.quasiIso X.label.universal.source
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn at hc
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition_eq_closed] at hc
    exact hc
  rw [dgUniversalCommaTarget_map]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeProjectionSnd_quasiIso_of_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R Cᵒᵖ Eᵒᵖ F.op A B) q
      (-(eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) A.replacement)
        B.augmentation)) _ hq
  simp only [q, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, biprod.desc_eq,
    Preadditive.comp_neg, sub_eq_add_neg]
  rfl
/-- 同じ実 cocone の切断から、標的 Hom 射影の全整数次数全射性を得る。 -/
lemma dgUniversalCommaTarget_degree_surjective (j : ℤ) :
    Function.Surjective (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F).map X Y).f j) := by
  let A := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaDualLabel R C E F Y.label
  let B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaDualLabel R C E F X.label
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R Cᵒᵖ Eᵒᵖ F.op A B
  let K := homObject R C X.label.universal.source Y.label.universal.source
  let L := homObject R E X.label.target Y.label.target
  let b : L ⟶ K ⊞ L := biprod.inr
  let p : K ⊞ L ⟶ L := biprod.snd
  have hs : b.f j ≫ (mappingCocone.inl d).v j j (add_zero j) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F).map X Y).f j = 𝟙 _ := by
    rw [dgUniversalCommaTarget_map]
    change b.f j ≫ (mappingCocone.inl d).v j j (add_zero j) ≫
      ((mappingCocone.fst d).f j ≫ p.f j) = 𝟙 _
    rw [← Category.assoc ((mappingCocone.inl d).v j j (add_zero j)),
      mappingCocone.inl_v_fst_f, Category.id_comp]
    rw [← HomologicalComplex.comp_f]
    change (biprod.inr ≫ biprod.snd : L ⟶ L).f j = 𝟙 _
    rw [biprod.inr_snd, HomologicalComplex.id_f]
  intro y
  refine ⟨(mappingCocone.inl d).v j j (add_zero j) (b.f j y), ?_⟩
  exact ConcreteCategory.congr_hom hs y
end SerrePositivity.InfinityCategories.Project.DerivedCategories
