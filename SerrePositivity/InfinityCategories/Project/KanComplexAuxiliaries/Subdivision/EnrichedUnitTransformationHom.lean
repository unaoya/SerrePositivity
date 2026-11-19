module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterCylinderFunctor

/-!
概要：単位をパラメータとする豊穣自然変換の、全 Hom への合成作用。
方針：評価と後合成を単位子で制限し、自然性・結合律で三つの合成公式を示す。
規約：自然変換の因子分解を成分だけでなく全 Hom に沿い保持する。
使われ方：零対象を中間に持つ三段の coherent な図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedUnitTransformation
end SerrePositivity.KST.Spectra.EnrichedUnitTransformation
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom
open _root_.SerrePositivity.KST.Spectra.EnrichedUnitTransformation

variable {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
  {F G : EnrichedFunctor SSet.{u} C D}

/-- 単位をパラメータとする自然変換と全 Hom の後合成。 -/
def hom (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) (X Y : C) :
    (X ⟶[SSet] Y) ⟶ (F.obj X ⟶[SSet] G.obj Y) :=
  (λ_ (X ⟶[SSet] Y)).inv ≫ (η.app X ⊗ₘ G.map X Y) ≫ eComp SSet _ _ _

/-- 自然変換の作用は左の元の関手の Hom と合成できる。 -/
lemma hom_comp_left (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) (X Y Z : C) :
    eComp SSet X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom η X Z =
      (F.map X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom η Y Z) ≫ eComp SSet (F.obj X) (F.obj Y) (G.obj Z) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g⟩
  change (eComp SSet (F.obj X) (G.obj X) (G.obj Z)).app d
    ((η.app X).app d PUnit.unit, (G.map X Z).app d ((eComp SSet X Y Z).app d (f, g))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app G X Y Z d f g, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app,
    ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality_app (𝟙_ SSet.{u}) F G η X Y d PUnit.unit f]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app (F.obj X) (F.obj Y) (G.obj Y) (G.obj Z) d
    ((F.map X Y).app d f) ((η.app Y).app d PUnit.unit) ((G.map Y Z).app d g)

/-- 自然変換の作用は右の元の関手の Hom と合成できる。 -/
lemma hom_comp_right (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) (X Y Z : C) :
    eComp SSet X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom η X Z =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom η X Y ⊗ₘ G.map Y Z) ≫ eComp SSet (F.obj X) (G.obj Y) (G.obj Z) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g⟩
  change (eComp SSet (F.obj X) (G.obj X) (G.obj Z)).app d
    ((η.app X).app d PUnit.unit, (G.map X Z).app d ((eComp SSet X Y Z).app d (f, g))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app G X Y Z d f g]
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app (F.obj X) (G.obj X) (G.obj Y) (G.obj Z) d
    ((η.app X).app d PUnit.unit) ((G.map X Y).app d f) ((G.map Y Z).app d g)).symm

/-- 成分で与えた因子分解は、任意の二つの Hom の合成にも一致する。 -/
lemma hom_comp_factorization {H : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G H)
    (ζ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F H)
    (hc : ∀ X, ζ.app X = (λ_ (𝟙_ SSet.{u})).inv ≫
      (η.app X ⊗ₘ θ.app X) ≫ eComp SSet (F.obj X) (G.obj X) (H.obj X)) (X Y Z : C) :
    eComp SSet X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom ζ X Z =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom η X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom θ Y Z) ≫ eComp SSet (F.obj X) (G.obj Y) (H.obj Z) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g⟩
  have hz := ConcreteCategory.congr_hom (NatTrans.congr_app (hc X) d) PUnit.unit
  have hn := congrArg (fun k ↦ (eComp SSet (G.obj X) (H.obj Y) (H.obj Z)).app d
    (k, (H.map Y Z).app d g))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality_app (𝟙_ SSet.{u}) G H θ X Y d PUnit.unit f)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app] at hn
  change (eComp SSet (F.obj X) (H.obj X) (H.obj Z)).app d
    ((ζ.app X).app d PUnit.unit, (H.map X Z).app d ((eComp SSet X Y Z).app d (f, g))) = _
  rw [hz, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app H X Y Z d f g]
  change (eComp SSet (F.obj X) (H.obj X) (H.obj Z)).app d
    ((eComp SSet (F.obj X) (G.obj X) (H.obj X)).app d
      ((η.app X).app d PUnit.unit, (θ.app X).app d PUnit.unit),
      (eComp SSet (H.obj X) (H.obj Y) (H.obj Z)).app d
        ((H.map X Y).app d f, (H.map Y Z).app d g)) =
    (eComp SSet (F.obj X) (G.obj Y) (H.obj Z)).app d
      ((eComp SSet (F.obj X) (G.obj X) (G.obj Y)).app d
        ((η.app X).app d PUnit.unit, (G.map X Y).app d f),
        (eComp SSet (G.obj Y) (H.obj Y) (H.obj Z)).app d
          ((θ.app Y).app d PUnit.unit, (H.map Y Z).app d g))
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_assoc_app]
  exact congrArg (fun k ↦ (eComp SSet (F.obj X) (G.obj X) (H.obj Z)).app d
    ((η.app X).app d PUnit.unit, k)) hn.symm

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
