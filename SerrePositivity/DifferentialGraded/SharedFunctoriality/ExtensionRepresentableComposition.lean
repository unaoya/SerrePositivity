module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionInputTransport
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionEvaluationTransport
public import SerrePositivity.DifferentialGraded.Tensor.Compose
/-!
概要：実加群延長の合成比較は、代表加群の元の Yoneda 比較と厳密に整合する。
方針：右単位の双加群自然性と結合整合性を graph に適用し、元の代表で評価する。
規約：既存の合成同型・代表同型を変更せず、実閉射の等式として証明する。
使われ方：D-19。D2 の自由 Hom 比較で一回延長と二回延長を同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory BimoduleTensor
open SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (T : Type z) [DGCategory R T] [Small.{u} T]
  (F : DGFunctor R D E) (G : DGFunctor R E T)

lemma dgModuleExtensionCompositionAt_representable (x : D) :
    (dgModuleExtensionCompositionAt R D E T F G (representable R x)).hom ≫
      (dgModuleExtensionRepresentableIso R D T (F.comp G) x).hom =
    (dgModuleExtension R E T G).onClosed.map
      (dgModuleExtensionRepresentableIso R D E F x).hom ≫
        (dgModuleExtensionRepresentableIso R E T G (F.obj x)).hom := by
  let P := functorGraph R E T G
  let Q := functorGraph R D E F
  let H := functorGraph R D T (F.comp G)
  let e := dgFunctorGraphCompositionIso R D E T F G
  have h : (associatorIso R T E D D P Q (Bimodule.diagonal R D)).inv ≫
      composeMap R T D D e.hom (𝟙 (BimoduleCategory.of R D D (Bimodule.diagonal R D))) ≫
        (rightBimoduleUnitIso R T D H).hom =
      composeMap R T E D (𝟙 (BimoduleCategory.of R T E P))
        (rightBimoduleUnitIso R E D Q).hom ≫ e.hom := by
    have hn := rightBimoduleUnitIso_naturality R T D e.hom
    change composeMap R T D D e.hom
        (𝟙 (BimoduleCategory.of R D D (Bimodule.diagonal R D))) ≫
        (rightBimoduleUnitIso R T D H).hom =
      (rightBimoduleUnitIso R T D (BimoduleTensor.compose R T E D P Q)).hom ≫ e.hom at hn
    rw [hn, ← Category.assoc, rightUnit_associator_inv]
  have he := congrArg (BimoduleCategory.evaluation R T D x).map h
  simp only [CategoryTheory.Functor.map_comp] at he
  rw [dgModuleExtension_second_map_evaluation] at he
  apply moduleMorphism_ext R T
  intro t
  have hv := congrArg (moduleEvaluation R T t).map he
  simp only [CategoryTheory.Functor.map_comp] at hv ⊢
  simp only [associatorIso_inv_eval, composeMap_eval] at hv
  simp only [dgModuleExtensionCompositionAt, dgModuleExtensionCompositionTensorIso,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, dgModuleGraphTensorFunctor_map,
    associatorIso_inv_eval, composeMap_eval] at ⊢
  simp only [rightBimoduleUnitIso, BimoduleCategory.isoOfFamily_hom_eval,
    e, dgFunctorGraphCompositionIso, dgFunctorGraphCompositionAt] at hv
  simp only [associatorRightModuleIso_inv_eval, composeRightMap_eval,
    composeValueHom_eq, rightUnitIso_hom_eval] at hv ⊢
  rw [dgTensor_associator_value_evaluation, dgTensor_first_value_evaluation] at hv
  dsimp only [Bimodule.diagonal, dgYoneda, DGFunctor.ofHomMaps] at hv
  simpa only [P, Q, H, Category.assoc, dgModuleExtensionRepresentableIso,
    rightUnitIso_hom_eval, dgFunctorGraphCompositionIso] using hv

end SerrePositivity.DifferentialGraded
