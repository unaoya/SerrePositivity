module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentUnderlyingHo
public import SerrePositivity.InfinityCategories.ModelBridge.QuillenCfMixedHom

/-!
概要：cf 対応圏の元の混合射の合成を、元のモデル圏の通常の合成へ戻す。
方針：元の Hom 同型の合成式と、元の通常の置換比較の自然性を使用する。
規約：coherent な cf 置換関手の射との照合は別工程。使われ方：HTT 5.2.4.6。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Coherent
open SerrePositivity.KST.SConstruction
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
  (adj : L ⊣ coherentEnrichedUnderlyingFunctor R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (cofC : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))

/-- 元の上段包含は、豊穣単位からの射の元の像を保持する。 -/
lemma quillenCfTop_eHom_map
    {Y Z : CofibrantFibrantObjects D} (a : Y ⟶ Z) :
    eHomEquiv SSet ((coherentEnrichedUnderlyingFunctor (quillenCfCollageTop R)).map a) =
      eHomEquiv SSet a.hom := by
  apply (SSet.unitHomEquiv _).injective
  exact coherentEnrichedUnderlyingFunctor_vertex (quillenCfCollageTop R) a

/-- 元の下段包含は、豊穣単位からの射の元の像を保持する。 -/
lemma quillenCfBottom_eHom_map
    {X W : CofibrantFibrantObjects C} (a : X ⟶ W) :
    eHomEquiv SSet ((coherentEnrichedUnderlyingFunctor (quillenCfCollageBottom R)).map a) =
      eHomEquiv SSet a.hom := by
  apply (SSet.unitHomEquiv _).injective
  exact coherentEnrichedUnderlyingFunctor_vertex (quillenCfCollageBottom R) a

/-- 下段の元の通常射と混合射の合成は、元の C の合成そのものである。 -/
lemma quillenCfMixedHomEquiv_bottom_comp
    {X W : CofibrantFibrantObjects C} {Y : CofibrantFibrantObjects D}
    (a : X ⟶ W) (b : (quillenCfCollageBottom R).obj W ⟶ (quillenCfCollageTop R).obj Y) :
    quillenCfMixedHomEquiv R X Y
      ((coherentEnrichedUnderlyingFunctor (quillenCfCollageBottom R)).map a ≫ b) =
      a.hom ≫ quillenCfMixedHomEquiv R W Y b := by
  obtain ⟨f, rfl⟩ := (quillenCfMixedHomEquiv R W Y).symm.surjective b
  apply (quillenCfMixedHomEquiv R X Y).symm.injective
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  apply (eHomEquiv SSet (C := QuillenCfCollage R)).injective
  calc
    _ = eHomEquiv SSet ((coherentEnrichedUnderlyingFunctor (quillenCfCollageBottom R)).map a) ≫
        eHomWhiskerLeft SSet ((quillenCfCollageBottom R).obj X)
          ((quillenCfMixedHomEquiv R W Y).symm f) :=
      SerrePositivity.Enriched.eHomEquiv_postcomp _ _
    _ = eHomEquiv SSet a.hom ≫ eHomWhiskerLeft SSet X.obj f :=
      congrArg₂ (fun h k ↦ h ≫ k) (quillenCfBottom_eHom_map R a)
        (quillenCfMixedHomWhiskerLeft R X W Y f)
    _ = eHomEquiv SSet (a.hom ≫ f) :=
      (SerrePositivity.Enriched.eHomEquiv_postcomp a.hom f).symm
    _ = _ := (quillenCfMixedHomEquiv_eHom R X Y (a.hom ≫ f)).symm

/-- 混合射と上段の元の通常射の合成は、元の C の合成と R の通常の作用に一致する。 -/
lemma quillenCfMixedHomEquiv_comp_top
    {X : CofibrantFibrantObjects C} {Y Z : CofibrantFibrantObjects D}
    (b : (quillenCfCollageBottom R).obj X ⟶ (quillenCfCollageTop R).obj Y) (a : Y ⟶ Z) :
    quillenCfMixedHomEquiv R X Z
      (b ≫ (coherentEnrichedUnderlyingFunctor (quillenCfCollageTop R)).map a) =
      quillenCfMixedHomEquiv R X Y b ≫ (coherentEnrichedUnderlyingFunctor R).map a.hom := by
  obtain ⟨f, rfl⟩ := (quillenCfMixedHomEquiv R X Y).symm.surjective b
  apply (quillenCfMixedHomEquiv R X Z).symm.injective
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  apply (eHomEquiv SSet (C := QuillenCfCollage R)).injective
  calc
    _ = (λ_ (𝟙_ SSet.{u})).inv ≫
        (eHomEquiv SSet ((quillenCfMixedHomEquiv R X Y).symm f) ⊗ₘ
          eHomEquiv SSet ((coherentEnrichedUnderlyingFunctor (quillenCfCollageTop R)).map a)) ≫
        eComp SSet ((quillenCfCollageBottom R).obj X) ((quillenCfCollageTop R).obj Y)
          ((quillenCfCollageTop R).obj Z) := eHomEquiv_comp SSet _ _
    _ = (λ_ (𝟙_ SSet.{u})).inv ≫ (eHomEquiv SSet f ⊗ₘ eHomEquiv SSet a.hom) ≫
        eComp SSet ((quillenCfCollageBottom R).obj X) ((quillenCfCollageTop R).obj Y)
          ((quillenCfCollageTop R).obj Z) :=
      congrArg₂ (fun h k ↦ (λ_ (𝟙_ SSet.{u})).inv ≫ (h ⊗ₘ k) ≫
        eComp SSet ((quillenCfCollageBottom R).obj X) ((quillenCfCollageTop R).obj Y)
          ((quillenCfCollageTop R).obj Z))
        (quillenCfMixedHomEquiv_eHom R X Y f) (quillenCfTop_eHom_map R a)
    _ = (λ_ (𝟙_ SSet.{u})).inv ≫ (eHomEquiv SSet f ⊗ₘ eHomEquiv SSet a.hom) ≫
        (𝟙 _ ⊗ₘ R.map Y.obj Z.obj) ≫ eComp SSet X.obj (R.obj Y.obj) (R.obj Z.obj) := rfl
    _ = (λ_ (𝟙_ SSet.{u})).inv ≫
        (eHomEquiv SSet f ⊗ₘ (eHomEquiv SSet a.hom ≫ R.map Y.obj Z.obj)) ≫
        eComp SSet X.obj (R.obj Y.obj) (R.obj Z.obj) := by
      simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id]
    _ = (λ_ (𝟙_ SSet.{u})).inv ≫
        (eHomEquiv SSet f ⊗ₘ
          eHomEquiv SSet ((coherentEnrichedUnderlyingFunctor R).map a.hom)) ≫
        eComp SSet X.obj (R.obj Y.obj) (R.obj Z.obj) :=
      congrArg (fun k ↦ (λ_ (𝟙_ SSet.{u})).inv ≫ (eHomEquiv SSet f ⊗ₘ k) ≫
        eComp SSet X.obj (R.obj Y.obj) (R.obj Z.obj))
        (enrichedUnderlying_eHom_map R a.hom).symm
    _ = eHomEquiv SSet (f ≫ (coherentEnrichedUnderlyingFunctor R).map a.hom) :=
      (eHomEquiv_comp SSet f ((coherentEnrichedUnderlyingFunctor R).map a.hom)).symm
    _ = _ := (quillenCfMixedHomEquiv_eHom R X Z
      (f ≫ (coherentEnrichedUnderlyingFunctor R).map a.hom)).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
