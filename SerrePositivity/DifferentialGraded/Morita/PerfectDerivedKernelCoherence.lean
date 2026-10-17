module
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelColumns
public import SerrePositivity.DifferentialGraded.Morita.CoherenceIdentity

/-! # 実際の主導来kernelの恒等作用と、明示した合成比較のPerf制限

恒等比較はU16aの公開済みの実際の自然同型を使用する。
合成比較はU16aの型どおりの自然同型を明示して受け取り、局所Hom条件を保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma kernelIdentity_columnsPerfect : kernelColumnsPerfect A D D (kernelIdentity A D) := by
  apply (kernelColumnsPerfect_iff_preservesPerfect A D D _).2
  intro X hX
  exact (modulePerfect A D).prop_of_iso ((kernelIdentityIso A D).app X).symm hX

def perfectDerivedKernelIdentityIso :
    perfectDerivedKernelAction A D D (kernelIdentity A D) (kernelIdentity_columnsPerfect A D) ≅
      𝟭 (PerfectModuleCategory A D) :=
  perfectFunctorIso A D D _ _
      (fun _ h => perfectDerivedKernelAction_preserves A D D _
        (kernelIdentity_columnsPerfect A D) h) (fun _ h => h) (kernelIdentityIso A D) ≪≫
    perfectFunctorIdentityIso A D

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E B)
  (hP : kernelColumnsPerfect A D E P) (hQ : kernelColumnsPerfect A E B Q)
  (eComp : kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E B Q ≅
    kernelDerivedTensor A D B (kernelCompose A D E B hD P Q))
include hP hQ eComp

lemma kernelCompose_columnsPerfect :
    kernelColumnsPerfect A D B (kernelCompose A D E B hD P Q) := by
  apply (kernelColumnsPerfect_iff_preservesPerfect A D B _).2
  intro X hX
  exact (modulePerfect A B).prop_of_iso (eComp.app X)
    (perfectDerivedKernelAction_preserves A E B Q hQ
      (perfectDerivedKernelAction_preserves A D E P hP hX))

def perfectDerivedKernelCompositionIso :
    perfectDerivedKernelAction A D E P hP ⋙ perfectDerivedKernelAction A E B Q hQ ≅
      perfectDerivedKernelAction A D B (kernelCompose A D E B hD P Q)
        (kernelCompose_columnsPerfect A D E B hD P Q hP hQ eComp) :=
  perfectFunctorCompositionIso A D E B _ _
      (fun _ h => perfectDerivedKernelAction_preserves A D E P hP h)
      (fun _ h => perfectDerivedKernelAction_preserves A E B Q hQ h) ≪≫
    perfectFunctorIso A D B _ _
      (fun _ h => perfectDerivedKernelAction_preserves A E B Q hQ
        (perfectDerivedKernelAction_preserves A D E P hP h))
      (fun _ h => perfectDerivedKernelAction_preserves A D B _
        (kernelCompose_columnsPerfect A D E B hD P Q hP hQ eComp) h) eComp

lemma perfectDerivedKernelCompositionIso_inclusion :
    Functor.whiskerRight
        (perfectDerivedKernelCompositionIso A D E B hD P Q hP hQ eComp).hom
        (perfectModuleInclusion A B Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ) eComp.hom := by
  apply NatTrans.ext
  funext X
  change 𝟙 _ ≫ eComp.hom.app X.obj = eComp.hom.app X.obj
  exact Category.id_comp _

lemma perfectDerivedKernelCompositionIso_naturality
    (P' : Kernel A D E) (Q' : Kernel A E B)
    (hP' : kernelColumnsPerfect A D E P') (hQ' : kernelColumnsPerfect A E B Q')
    (eComp' : kernelDerivedTensor A D E P' ⋙ kernelDerivedTensor A E B Q' ≅
      kernelDerivedTensor A D B (kernelCompose A D E B hD P' Q'))
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hNat : NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
        ((kernelDerivedTensorFunctor A E B).map g) ≫ eComp'.hom =
      eComp.hom ≫ (kernelDerivedTensorFunctor A D B).map
        (kernelComposeMap A D E B hD f g)) :
    NatTrans.hcomp (perfectDerivedKernelMap A D E hP hP' f)
        (perfectDerivedKernelMap A E B hQ hQ' g) ≫
        (perfectDerivedKernelCompositionIso A D E B hD P' Q' hP' hQ' eComp').hom =
      (perfectDerivedKernelCompositionIso A D E B hD P Q hP hQ eComp).hom ≫
        perfectDerivedKernelMap A D B
          (kernelCompose_columnsPerfect A D E B hD P Q hP hQ eComp)
          (kernelCompose_columnsPerfect A D E B hD P' Q' hP' hQ' eComp')
          (kernelComposeMap A D E B hD f g) := by
  apply NatTrans.ext
  funext X
  apply (modulePerfect A B).hom_ext
  have h := NatTrans.congr_app hNat X.obj
  simp only [NatTrans.comp_app, NatTrans.hcomp_app] at h
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, perfectDerivedKernelCompositionIso,
    perfectFunctorCompositionIso, perfectFunctorIso, Iso.trans_hom, NatIso.ofComponents,
    ObjectProperty.isoMk, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app]
  change
    ((((kernelDerivedTensorFunctor A E B).map g).app
        ((kernelDerivedTensor A D E P).obj X.obj) ≫
      (kernelDerivedTensor A E B Q').map
        (((kernelDerivedTensorFunctor A D E).map f).app X.obj)) ≫
      𝟙 _ ≫ eComp'.hom.app X.obj) =
    (𝟙 _ ≫ eComp.hom.app X.obj) ≫
      ((kernelDerivedTensorFunctor A D B).map (kernelComposeMap A D E B hD f g)).app X.obj
  simpa only [Category.id_comp, kernelDerivedTensor, Functor.comp_obj] using h

end SerrePositivity.DifferentialGraded.Morita
