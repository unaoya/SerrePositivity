module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition
public import SerrePositivity.KST.Spectra.StrictEnrichedTransformationNerve
public import SerrePositivity.KST.Spectra.EnrichedTransformationTriangleOuter

/-!
概要：単位パラメータの厳密豊穣自然変換の前後合成と縦合成。
方針：全 Hom の自然性を同じ豊穣合成の各単体で証明する。
規約：点ごとの同型の比較に弱めない。元の変換の全単体を保持する。
使われ方：共通 BF 右射影の構造正方形を厳密豊穣変換として接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra
open EnrichedParameterCylinder
variable {C : Type v} {D : Type w} {E : Type z}
  [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D] [EnrichedCategory SSet.{u} E]

/-- 厳密変換の端点表示だけを等式で正規化する。 -/
def d3GradedOfEq {F G F' G' : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (hf : F = F') (hg : G = G') :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F' G' := by
  subst F' G'
  exact η

/-- 元の全 Hom 自然性を同じ豊穣関手へ前合成する。 -/
def d3GradedPrecomp (K : EnrichedFunctor SSet.{u} C D)
    {F G : EnrichedFunctor SSet.{u} D E}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) (K.comp SSet F) (K.comp SSet G) where
  app X := η.app (K.obj X)
  naturality X Y := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨a, f⟩
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality_app _ F G η (K.obj X) (K.obj Y) d a ((K.map X Y).app d f)

/-- 同じ豊穣関手の全 Hom 作用で、元の厳密変換を後合成する。 -/
def d3GradedPostcomp {F G : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (K : EnrichedFunctor SSet.{u} D E) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) (F.comp SSet K) (G.comp SSet K) where
  app X := η.app X ≫ K.map _ _
  naturality X Y := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨a, f⟩
    change (eComp SSet _ _ _).app d
      ((K.map _ _).app d ((F.map X Y).app d f),
        (K.map _ _).app d ((η.app Y).app d a)) =
      (eComp SSet _ _ _).app d
        ((K.map _ _).app d ((η.app X).app d a),
          (K.map _ _).app d ((G.map X Y).app d f))
    rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality_app]

/-- 元の二つの単位パラメータ変換の、同じ指定成分による縦合成。 -/
def d3GradedComp {F G H : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G H) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F H where
  app X := (λ_ (𝟙_ SSet.{u})).inv ≫
    (η.app X ⊗ₘ θ.app X) ≫ eComp SSet _ _ _
  naturality X Y := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟩, f⟩
    change (eComp SSet _ _ _).app d
      ((F.map X Y).app d f,
        (eComp SSet _ _ _).app d ((η.app Y).app d PUnit.unit,
          (θ.app Y).app d PUnit.unit)) =
      (eComp SSet _ _ _).app d
        ((eComp SSet _ _ _).app d ((η.app X).app d PUnit.unit,
          (θ.app X).app d PUnit.unit), (H.map X Y).app d f)
    rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality_app, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality_app, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app]

section Components
variable {C' D' E' : Type v} [Category.{u} C'] [Category.{u} D'] [Category.{u} E']
  [SimplicialCategory C'] [SimplicialCategory D'] [SimplicialCategory E']
  {F G H : EnrichedFunctor SSet.{u} C' D'}

/-- 端点表示の正規化は、元の指定通常成分を保持する。 -/
lemma d3GradedOfEq_component_heq {F' G' : EnrichedFunctor SSet.{u} C' D'}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (hf : F = F') (hg : G = G') (X : C') :
    HEq (StrictEnrichedTransformation.componentHom F' G' (d3GradedOfEq η hf hg) X)
      (StrictEnrichedTransformation.componentHom F G η X) := by
  subst F' G'
  rfl

/-- 全 Hom 自然性を持つ厳密変換は、指定成分が等しければ同じ変換。 -/
lemma d3Graded_ext
    {η θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G}
    (h : ∀ X, StrictEnrichedTransformation.componentHom F G η X =
      StrictEnrichedTransformation.componentHom F G θ X) : η = θ := by
  apply GradedNatTrans.ext
  funext X
  apply (SSet.unitHomEquiv _).injective
  exact (SimplicialCategory.homEquiv' _ _).symm.injective (h X)

/-- 厳密変換の通常成分を豊穣単位へ戻すと、同じ全単体の成分を回収する。 -/
lemma d3Graded_component_eHomEquiv
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) (X : C') :
    eHomEquiv SSet (StrictEnrichedTransformation.componentHom F G η X) = η.app X := by
  apply (SSet.unitHomEquiv _).injective
  exact (SimplicialCategory.homEquiv' _ _).apply_symm_apply _

/-- 縦合成の指定成分は、元の二成分の通常の合成そのもの。 -/
lemma d3GradedComp_component
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G H) (X : C') :
    StrictEnrichedTransformation.componentHom F H (d3GradedComp η θ) X =
      StrictEnrichedTransformation.componentHom F G η X ≫
        StrictEnrichedTransformation.componentHom G H θ X := by
  apply (eHomEquiv SSet).injective
  rw [eHomEquiv_comp, d3Graded_component_eHomEquiv,
    d3Graded_component_eHomEquiv, d3Graded_component_eHomEquiv]
  rfl

/-- 後合成の指定成分は、同じ豊穣関手の通常の作用そのもの。 -/
lemma d3GradedPostcomp_component
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (K : EnrichedFunctor SSet.{u} D' E') (X : C') :
    StrictEnrichedTransformation.componentHom _ _ (d3GradedPostcomp η K) X =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor K).map
        (StrictEnrichedTransformation.componentHom F G η X) := by
  apply (SimplicialCategory.homEquiv' _ _).injective
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex K
    (StrictEnrichedTransformation.componentHom F G η X)
  refine Eq.trans ?_ h.symm
  simp only [StrictEnrichedTransformation.componentHom, d3GradedPostcomp,
    Equiv.apply_symm_apply]
  rfl

end Components
end SerrePositivity.KST.Spectra
