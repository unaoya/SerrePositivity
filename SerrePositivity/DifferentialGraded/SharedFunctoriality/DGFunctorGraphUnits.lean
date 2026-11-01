module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphComposition
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionIdentity
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso

/-! # 元の graph 合成比較の恒等入力との両立
概要：入力関手の等号移送を保ち、graph 合成比較と実単位同型を照合する。
方針：閉零双加群射を元の各右加群で判定し、同じ Yoneda 単位を回収する。
規約：等号移送を省略して異なる入力を同一視しない。使われ方：Perf 比較の三角整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} E]

/-- 元の dg 入力の等号による、実 graph 双加群の同型。 -/
def dgFunctorGraphInputIso {F G : DGFunctor A D E} (h : F = G) :
    BimoduleCategory.of A E D (functorGraph A D E F) ≅
      BimoduleCategory.of A E D (functorGraph A D E G) :=
  eqToIso (congrArg (fun H => BimoduleCategory.of A E D (functorGraph A D E H)) h)

/-- 入力等号の graph 移送は、元の各右加群の等号移送を回収する。 -/
lemma dgFunctorGraphInputIso_evaluation {F G : DGFunctor A D E} (h : F = G) (d : D) :
    (BimoduleCategory.evaluation A E D d).mapIso (dgFunctorGraphInputIso A D E h) =
      eqToIso (congrArg (fun H => ForgetEnrichment.of (Complex A)
        ((functorGraph A D E H).rightAt d)) h) := by
  cases h
  simp only [dgFunctorGraphInputIso, eqToIso_refl, Functor.mapIso_refl]
  rfl

variable [Small.{u} D]

/-- graph の恒等入力を対角に置き換える、元の tensor 源の等号移送。 -/
def dgFunctorGraphUnitSourceIso (F : DGFunctor A D E) :
    BimoduleCategory.of A E D
        (BimoduleTensor.compose A E D D (functorGraph A D E F)
          (functorGraph A D D (DGFunctor.id D))) ≅
      BimoduleCategory.of A E D
        (BimoduleTensor.compose A E D D (functorGraph A D E F) (Bimodule.diagonal A D)) :=
  eqToIso (congrArg (fun Q => BimoduleCategory.of A E D
    (BimoduleTensor.compose A E D D (functorGraph A D E F) Q)) (functorGraph_identity A D))

/-- 元の graph 合成比較の恒等入力は、同じ右 tensor 単位を回収する。 -/
lemma dgFunctorGraphCompositionIso_id (F : DGFunctor A D E) :
    dgFunctorGraphCompositionIso A D D E (DGFunctor.id D) F ≪≫
        dgFunctorGraphInputIso A D E (strictDGFunctor_id_comp F) =
      dgFunctorGraphUnitSourceIso A D E F ≪≫
        BimoduleTensor.rightBimoduleUnitIso A E D (functorGraph A D E F) := by
  apply Iso.ext
  apply BimoduleCategory.hom_ext
  intro d
  simp only [Iso.trans_hom, Functor.map_comp, dgFunctorGraphInputIso,
    dgFunctorGraphUnitSourceIso, eqToIso.hom, eqToHom_map]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

end SerrePositivity.KST.SConstruction
