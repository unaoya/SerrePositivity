module
public import SerrePositivity.DifferentialGraded.Morita.KernelBasic
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelImage

/-! # U16d：主導来kernel合成比較の主Perfへの制限

U16aの主導来作用族と合成自然同型を明示した入力として使う。
実際の通常kernelのPerf作用とkernelComposeの正しい向き・局所Hom条件を保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (P : Bimodule A E D) (Q : Bimodule A B E)
  (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
    (ForgetEnrichment.of (Complex A) (P.rightAt d))))
  (hQ : ∀ e : E, modulePerfect A B ((moduleToDerived A B).obj
    (ForgetEnrichment.of (Complex A) (Q.rightAt e))))
  (hD : localHomKFlat A D)
  (Action : Kernel A D B ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A B))

def perfectKernelCompositeTarget : DerivedModuleCategory A D ⥤ DerivedModuleCategory A B :=
  Action.obj (kernelCompose A D E B hD
    ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))
    ((bimoduleToDerived A B E).obj (BimoduleCategory.of A B E Q)))

variable (eComp : kernelDerivedTensorOnBimodule A D E P ⋙
  kernelDerivedTensorOnBimodule A E B Q ≅ perfectKernelCompositeTarget A D E B P Q hD Action)
include hP hQ eComp

lemma perfectKernelComposite_preserves {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A B ((perfectKernelCompositeTarget A D E B P Q hD Action).obj X) :=
  (modulePerfect A B).prop_of_iso (eComp.app X)
    (perfectKernelAction_preserves A E B Q hQ (perfectKernelAction_preserves A D E P hP hX))

def perfectKernelCompositeAction : PerfectModuleCategory A D ⥤ PerfectModuleCategory A B :=
  perfectFunctorRestriction A D B (perfectKernelCompositeTarget A D E B P Q hD Action)
    (fun _ h => perfectKernelComposite_preserves A D E B P Q hP hQ hD Action eComp h)

def perfectKernelCompositionComparisonIso :
    perfectKernelAction A D E P hP ⋙ perfectKernelAction A E B Q hQ ≅
      perfectKernelCompositeAction A D E B P Q hP hQ hD Action eComp :=
  perfectFunctorCompositionIso A D E B
      (kernelDerivedTensorOnBimodule A D E P) (kernelDerivedTensorOnBimodule A E B Q)
      (fun _ h => perfectKernelAction_preserves A D E P hP h)
      (fun _ h => perfectKernelAction_preserves A E B Q hQ h) ≪≫
    perfectFunctorIso A D B _ _
      (fun _ h => perfectKernelAction_preserves A E B Q hQ
        (perfectKernelAction_preserves A D E P hP h))
      (fun _ h => perfectKernelComposite_preserves A D E B P Q hP hQ hD Action eComp h) eComp

lemma perfectKernelCompositionComparisonIso_inclusion :
    Functor.whiskerRight
        (perfectKernelCompositionComparisonIso A D E B P Q hP hQ hD Action eComp).hom
        (perfectModuleInclusion A B Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ) eComp.hom := by
  apply NatTrans.ext
  funext X
  change 𝟙 _ ≫ eComp.hom.app X.obj = eComp.hom.app X.obj
  exact Category.id_comp _

end SerrePositivity.DifferentialGraded.Morita
