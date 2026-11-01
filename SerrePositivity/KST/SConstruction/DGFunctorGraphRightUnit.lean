module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphUnits
public import SerrePositivity.KST.SConstruction.DGDiagonalUnitAgreement

/-! # 元の graph 比較の右恒等入力
概要：右恒等 dg 入力の graph 比較を、同じ左 tensor 単位と照合する。
方針：対角の左右単位の一致を、入力等号移送と各値での評価に接続する。
規約：元の graph 比較を取り替えない。使われ方：実 Perf 延長のもう一方の単位整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 元の graph 合成射の各値は、同じ元の Yoneda 右単位射。 -/
lemma dgFunctorGraphCompositionIso_hom_value (F : DGFunctor A D E) (G : DGFunctor A E T)
    (t : T) (d : D) :
    (BimoduleCategory.valueEvaluation A T D t d).map
        (dgFunctorGraphCompositionIso A D E T F G).hom =
      (BimoduleTensor.rightUnitValueIso A T E (functorGraph A E T G) t (F.obj d)).hom :=
  BimoduleTensor.rightUnitIso_hom_eval A T E (functorGraph A E T G) t (F.obj d)

/-- 対角への等号移送を含めた、元の右単位から左単位への値の比較。 -/
lemma dgDiagonalRightUnitValue_transport (P : Bimodule A E E)
    (h : P = Bimodule.diagonal A E) (b c : E) :
    (BimoduleTensor.rightUnitValueIso A E E P b c).hom ≫
        eqToHom (congrArg (fun Q => Q.value b c) h) =
      eqToHom (congrArg (fun Q =>
        (BimoduleTensor.compose A E E E Q (Bimodule.diagonal A E)).value b c) h) ≫
        (BimoduleTensor.leftUnitValueIso A E E (Bimodule.diagonal A E) b c).hom := by
  subst P
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact dgDiagonal_rightUnitValue_eq_leftUnit A E b c

/-- 右恒等入力の graph を対角へ移す、同じ元の tensor 源の等号同型。 -/
def dgFunctorGraphRightUnitSourceIso (F : DGFunctor A D E) :
    BimoduleCategory.of A E D
        (BimoduleTensor.compose A E E D (functorGraph A E E (DGFunctor.id E))
          (functorGraph A D E F)) ≅
      BimoduleCategory.of A E D
        (BimoduleTensor.compose A E E D (Bimodule.diagonal A E) (functorGraph A D E F)) :=
  eqToIso (congrArg (fun P => BimoduleCategory.of A E D
    (BimoduleTensor.compose A E E D P (functorGraph A D E F))) (functorGraph_identity A E))

/-- 元の graph 合成比較の右恒等入力は、同じ左 tensor 単位を回収する。 -/
lemma dgFunctorGraphCompositionIso_comp_id (F : DGFunctor A D E) :
    dgFunctorGraphCompositionIso A D E E F (DGFunctor.id E) ≪≫
        dgFunctorGraphInputIso A D E (strictDGFunctor_comp_id F) =
      dgFunctorGraphRightUnitSourceIso A D E F ≪≫
        BimoduleTensor.leftBimoduleUnitIso A E D (functorGraph A D E F) := by
  apply Iso.ext
  apply BimoduleCategory.value_hom_ext
  intro b d
  simp only [Iso.trans_hom, Functor.map_comp, dgFunctorGraphInputIso,
    dgFunctorGraphRightUnitSourceIso, eqToIso.hom, eqToHom_map]
  rw [dgFunctorGraphCompositionIso_hom_value, BimoduleTensor.leftBimoduleUnitIso_hom_value]
  have h := dgDiagonalRightUnitValue_transport A E (functorGraph A E E (DGFunctor.id E))
    (functorGraph_identity A E) b (F.obj d)
  simp only [eqToHom_refl, Category.comp_id] at h ⊢
  convert h using 1 <;> rfl

end SerrePositivity.KST.SConstruction
