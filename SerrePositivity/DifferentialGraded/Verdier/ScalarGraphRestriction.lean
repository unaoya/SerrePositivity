module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # 係数変更と graph 制限・通常の延長の交換

係数環の平坦性を仮定せず、通常の随伴と実際の制限を先に比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

private lemma scalarGraph_postcompose_id (P Q : Complex A) :
    homPostcompose P (𝟙 Q) = 𝟙 _ := (homFunctor P).map_id Q

private lemma scalarGraph_precompose_id (P Q : Complex A) :
    homPrecompose (𝟙 P) Q = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact CochainComplex.HomComplex.Cochain.id_comp z

/-- 係数制限と dg 関手への制限は、全次数の加群作用も含めて可換する。 -/
def scalarGraphRestrictionIso :
    moduleRestriction A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
        (ScalarExtension.dgFunctor φ F).op ⋙ ScalarExtension.moduleRestriction φ D ≅
      ScalarExtension.moduleRestriction φ E ⋙ moduleRestriction A D E F.op :=
  NatIso.ofComponents (fun M => moduleIsoMk A D (fun _ => Iso.refl _) (by
    intro x y
    dsimp only [Iso.refl_hom]
    rw [scalarGraph_postcompose_id, scalarGraph_precompose_id]
    simp only [Category.comp_id]
    change (ScalarExtension.rightRestriction φ D
      (restrictModule A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
        (ScalarExtension.dgFunctor φ F).op (ForgetEnrichment.to (Complex A') M))).map x y =
      F.op.map x y ≫
        (ScalarExtension.rightRestriction φ E (ForgetEnrichment.to (Complex A') M)).map
          (F.op.obj x) (F.op.obj y)
    rw [ScalarExtension.rightRestriction_map, ScalarExtension.rightRestriction_map]
    change (ScalarExtension.adjunction φ).unit.app _ ≫
        (ScalarExtension.restriction φ).map
          ((ScalarExtension.extension φ).map (F.op.map x y) ≫
            (ForgetEnrichment.to (Complex A') M).map _ _) ≫ _ = _
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    have hn := (ScalarExtension.adjunction φ).unit.naturality (F.op.map x y)
    simp only [Functor.comp_map, Functor.id_map] at hn
    have hh := congrArg (fun t => t ≫
      (ScalarExtension.restriction φ).map
        ((ForgetEnrichment.to (Complex A') M).map (F.op.obj x) (F.op.obj y)) ≫
      ScalarExtension.restrictionHom φ
        ((ForgetEnrichment.to (Complex A') M).obj (F.op.obj x))
        ((ForgetEnrichment.to (Complex A') M).obj (F.op.obj y))) hn.symm
    simp only [Category.assoc] at hh
    convert hh using 1 <;> rfl))
    (by
      intro M N f
      apply moduleMorphism_ext
      intro d
      simp only [Functor.comp_map, CategoryTheory.Functor.map_comp,
        moduleIsoMk_hom_eval, Iso.refl_hom, ScalarExtension.moduleRestriction_eval,
        moduleRestriction_map_eval]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- 両複合随伴の一意性で得る、通常の graph 延長と係数拡大の交換。 -/
def scalarGraphExtensionIso :
    (dgModuleExtension A D E F).onClosed ⋙ ScalarExtension.moduleExtension φ E ≅
      ScalarExtension.moduleExtension φ D ⋙
        (dgModuleExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
          (ScalarExtension.dgFunctor φ F)).onClosed :=
  Adjunction.leftAdjointUniq
    ((dgModuleExtensionRestrictionAdjunction A D E F).comp
      (ScalarExtension.moduleAdjunction φ E))
    (((ScalarExtension.moduleAdjunction φ D).comp
      (dgModuleExtensionRestrictionAdjunction A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.DGBaseChange φ E) (ScalarExtension.dgFunctor φ F))).ofNatIsoRight
      (scalarGraphRestrictionIso φ D E F))
end SerrePositivity.DifferentialGraded
