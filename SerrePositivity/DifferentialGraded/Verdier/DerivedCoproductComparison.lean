module
public import SerrePositivity.DifferentialGraded.Derived.Coproducts
public import SerrePositivity.DifferentialGraded.Module.Colimits
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonColimitQuasiIso
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # 加群の擬同型の余積と導来局所化の余積保存

各評価の exact な余極限と、通常の加群の射影置換を用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma module_colimMap_quasiIso {J : Type w} [Category.{w'} J] [Small.{u} J]
    [HasColimitsOfShape J (ModuleCat.{u} A)] [HasExactColimitsOfShape J (ModuleCat.{u} A)]
    {F G : J ⥤ ModuleCategory A D} (α : F ⟶ G)
    (hα : ∀ j, moduleQuasiIso A D (α.app j)) : moduleQuasiIso A D (colimMap α) := by
  have : HasColimitsOfShape J (Complex A) :=
    ⟨fun H => HasColimit.mk ⟨_, isColimitCoconeOfHasColimitEval H⟩⟩
  intro x
  let E := moduleEvaluation A D x
  have : QuasiIso (colimMap (Functor.whiskerRight α E)) :=
    DGQuotient.complex_colimMap_quasiIso A _ (fun j => hα j x)
  have h := (preservesColimitNatIso E).hom.naturality α
  change E.map (colimMap α) ≫ (preservesColimitIso E G).hom =
    (preservesColimitIso E F).hom ≫ colimMap (Functor.whiskerRight α E) at h
  have : QuasiIso (E.map (colimMap α) ≫ (preservesColimitIso E G).hom) := by
    rw [h]
    infer_instance
  exact quasiIso_of_comp_right (E.map (colimMap α)) (preservesColimitIso E G).hom

variable {I : Type w} [Small.{u} I]

private lemma sigmaMap_eq_colimMap {C : Type*} [Category* C] {J : Type*}
    (M N : J → C) [HasCoproduct M] [HasCoproduct N] (q : ∀ i, M i ⟶ N i) :
    Limits.Sigma.map q = colimMap (Discrete.natTrans (F := Discrete.functor M)
      (G := Discrete.functor N) (fun i => q i.as)) := rfl

/-- 任意の u-small 族の objectwise 擬同型の直和は擬同型。 -/
lemma module_coproductMap_quasiIso {M N : I → ModuleCategory A D}
    (q : ∀ i, M i ⟶ N i) (hq : ∀ i, moduleQuasiIso A D (q i)) :
    moduleQuasiIso A D (Limits.Sigma.map q) := by
  have : HasExactColimitsOfShape (Discrete I) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} I).symm)
  rw [sigmaMap_eq_colimMap M N q]
  exact module_colimMap_quasiIso A D (F := Discrete.functor M) (G := Discrete.functor N)
    (Discrete.natTrans (fun i => q i.as)) (fun i => hq i.as)

/-- 射影性を仮定しない任意の加群族でも、局所化した余積包含は導来圏の余積となる。 -/
def moduleDerivedCofanIsColimit (M : I → ModuleCategory A D) :
    IsColimit (moduleProjectiveDerivedCofan A D M) := by
  let R := fun i => moduleCanonicalProjectiveResolution A D (M i)
  let P := fun i => (R i).obj
  let q := fun i => (R i).π
  let e := moduleDerivedIso A D (Limits.Sigma.map q)
    (module_coproductMap_quasiIso A D q (fun i => (R i).quasiIso))
  let α : Discrete.functor (fun i => (moduleToDerived A D).obj (P i)) ≅
      Discrete.functor (fun i => (moduleToDerived A D).obj (M i)) :=
    Discrete.natIso (fun i => moduleDerivedIso A D (q i.as) (R i.as).quasiIso)
  refine (IsColimit.precomposeHomEquiv α (moduleProjectiveDerivedCofan A D M))
    (IsColimit.ofIsoColimit
      (moduleProjectiveDerivedCofanIsColimit A D P (fun i => (R i).projective)) ?_)
  refine Cocone.ext e ?_
  rintro ⟨i⟩
  change (moduleToDerived A D).map (Sigma.ι P i) ≫
      (moduleToDerived A D).map (Limits.Sigma.map q) =
    (moduleToDerived A D).map (q i) ≫ (moduleToDerived A D).map (Sigma.ι M i)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Sigma.ι_map]

/-- 導来圏の選ばれた余積と、underived 余積の局所化との比較。 -/
def moduleDerivedCoproductIso (M : I → ModuleCategory A D) :
    (∐ fun i => (moduleToDerived A D).obj (M i)) ≅ (moduleToDerived A D).obj (∐ M) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (moduleDerivedCofanIsColimit A D M)

@[reassoc] lemma moduleDerivedCoproductIso_ι (M : I → ModuleCategory A D) (i : I) :
    Sigma.ι (fun i => (moduleToDerived A D).obj (M i)) i ≫
      (moduleDerivedCoproductIso A D M).hom = (moduleToDerived A D).map (Sigma.ι M i) := by
  let hc := colimit.isColimit (Discrete.functor (fun i => (moduleToDerived A D).obj (M i)))
  exact hc.comp_coconePointUniqueUpToIso_hom _ ⟨i⟩

instance moduleToDerived_preservesCoproduct (M : I → ModuleCategory A D) :
    PreservesColimit (Discrete.functor M) (moduleToDerived A D) :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct M)
    ((isColimitMapCoconeCofanMkEquiv (moduleToDerived A D) M (Sigma.ι M)).symm
      (moduleDerivedCofanIsColimit A D M))

instance moduleToDerived_preservesCoproducts :
    PreservesColimitsOfShape (Discrete I) (moduleToDerived A D) :=
  preservesColimitsOfShape_of_discrete _

end SerrePositivity.DifferentialGraded
