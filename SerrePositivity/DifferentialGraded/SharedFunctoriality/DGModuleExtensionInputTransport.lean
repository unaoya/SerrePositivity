module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionComposition
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphUnits
public import SerrePositivity.DifferentialGraded.Module.FreeSphere

/-! # 実延長の入力等号移送と tensor 射の評価
概要：入力の等号による実延長の比較と、tensor 作用の元の閉零射を固定する。
方針：等号帰納と双加群射の評価から、元の加群上の厳密な式を得る。
規約：移送による同型と新しい比較の選択を区別する。使われ方：実 Perf 比較の三角。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の dg 入力の等号による、同じ実延長の対象別比較。 -/
def dgModuleExtensionInputIso {F G : DGFunctor A D E} (h : F = G)
    (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) ((dgModuleExtension A D E F).obj M) ≅
      ForgetEnrichment.of (Complex A) ((dgModuleExtension A D E G).obj M) :=
  eqToIso (congrArg (fun H => ForgetEnrichment.of (Complex A)
    ((dgModuleExtension A D E H).obj M)) h)

/-- graph の入力等号を tensor 作用後に評価すると、元の実延長の入力等号を回収する。 -/
lemma dgModuleExtensionInputIso_tensor_evaluation {F G : DGFunctor A D E} (h : F = G)
    (M : RightModule A D) :
    (BimoduleCategory.evaluation A E (RightModule A D) M).map
        ((dgModuleGraphTensorFunctor A D E).map (dgFunctorGraphInputIso A D E h).hom) =
      (dgModuleExtensionInputIso A D E h M).hom := by
  cases h
  simp only [dgFunctorGraphInputIso, dgModuleExtensionInputIso, eqToIso_refl,
    Iso.refl_hom]
  exact (congrArg (BimoduleCategory.evaluation A E (RightModule A D) M).map
    ((dgModuleGraphTensorFunctor A D E).map_id
      (BimoduleCategory.of A E D (functorGraph A D E F)))).trans
    ((BimoduleCategory.evaluation A E (RightModule A D) M).map_id _)

variable (F : DGFunctor A D E) (C : Type z) [DGCategory A C]

/-- tensor の後因子の射は、評価後に同じ元の実延長の閉零射作用を回収する。 -/
lemma dgModuleExtension_second_map_evaluation {Q Q' : BimoduleCategory A D C}
    (a : Q ⟶ Q') (c : C) :
    (BimoduleCategory.evaluation A E C c).map
        (BimoduleTensor.composeMap A E D C
          (𝟙 (BimoduleCategory.of A E D (functorGraph A D E F))) a) =
      (dgModuleExtension A D E F).onClosed.map ((BimoduleCategory.evaluation A D C c).map a) := by
  apply moduleMorphism_ext
  intro e
  change (BimoduleCategory.valueEvaluation A E C e c).map
      (BimoduleTensor.composeMap A E D C
        (𝟙 (BimoduleCategory.of A E D (functorGraph A D E F))) a) = _
  rw [BimoduleTensor.composeMap_value_eval, dgModuleExtension_map_eval]
  unfold BimoduleTensor.composeValueMap
  exact congrArg (fun k => BalancedTensor.map A D
    ((BimoduleCategory.evaluation A D C c).map a) k)
    ((BimoduleCategory.leftEvaluation A E D e).map_id
      (BimoduleCategory.of A E D (functorGraph A D E F)))

end SerrePositivity.KST.SConstruction
