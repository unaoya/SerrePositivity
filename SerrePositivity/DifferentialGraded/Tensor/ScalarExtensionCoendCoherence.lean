module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionRing
public import SerrePositivity.DifferentialGraded.Tensor.Yoneda
public import SerrePositivity.DifferentialGraded.Tensor.LeftYoneda
public import SerrePositivity.DifferentialGraded.Tensor.TensorModuleIso

/-! # 係数変更と相対 tensor の評価単位・パラメータ結合比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 係数変更した右 representable の相対 tensor 評価単位。 -/
def yonedaBaseChangeIso (z : D) (N : LeftModule A D) :
    BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D (representable A z)) (leftModule φ D N) ≅
      (extension φ).obj (N.obj z) :=
  (balancedIso φ D (representable A z) N).symm ≪≫
    (extension φ).mapIso (BalancedTensor.yonedaIso A D z N)

@[reassoc (attr := simp)]
lemma ι_yonedaBaseChangeIso (z : D) (N : LeftModule A D) (x : D) :
    BalancedTensor.ι A' (DGBaseChange φ D)
        (rightModule φ D (representable A z)) (leftModule φ D N) x ≫
      (yonedaBaseChangeIso φ D z N).hom =
      BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x z := by
  simp only [yonedaBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, BalancedTensor.yonedaIso]
  rw [balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp,
    BalancedTensor.ι_yonedaEvaluation, leftAction_comparison φ D N x z,
    Iso.inv_hom_id_assoc]

@[reassoc]
lemma yonedaBaseChange_comparison (z : D) (N : LeftModule A D) :
    (balancedIso φ D (representable A z) N).hom ≫ (yonedaBaseChangeIso φ D z N).hom =
      (extension φ).map (BalancedTensor.yonedaIso A D z N).hom := by
  simp only [yonedaBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, CategoryTheory.Functor.mapIso_hom]

/-- 係数変更した左 representable の相対 tensor 評価単位。 -/
def leftYonedaBaseChangeIso (z : D) (M : RightModule A D) :
    BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D M) (leftModule φ D (leftRepresentable A z)) ≅
      (extension φ).obj (M.obj (op z)) :=
  (balancedIso φ D M (leftRepresentable A z)).symm ≪≫
    (extension φ).mapIso (BalancedTensor.leftYonedaIso A D z M)

@[reassoc (attr := simp)]
lemma ι_leftYonedaBaseChangeIso (z : D) (M : RightModule A D) (x : D) :
    BalancedTensor.ι A' (DGBaseChange φ D)
        (rightModule φ D M) (leftModule φ D (leftRepresentable A z)) x ≫
      (leftYonedaBaseChangeIso φ D z M).hom =
      BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) z x := by
  simp only [leftYonedaBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, BalancedTensor.leftYonedaIso]
  rw [balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp,
    BalancedTensor.ι_leftYonedaEvaluation, rightAction_comparison φ D M z x]
  change (tensorIso φ (M.obj (op x)) (homObject A D z x)).inv ≫
    (tensorIso φ (M.obj (op x)) (homObject A D z x)).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

@[reassoc]
lemma leftYonedaBaseChange_comparison (z : D) (M : RightModule A D) :
    (balancedIso φ D M (leftRepresentable A z)).hom ≫
        (leftYonedaBaseChangeIso φ D z M).hom =
      (extension φ).map (BalancedTensor.leftYonedaIso A D z M).hom := by
  simp only [leftYonedaBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, CategoryTheory.Functor.mapIso_hom]

/-- 複体パラメータを相対 tensor の外へ出す結合同型の係数変更。 -/
def tensorModuleBaseChangeIso (K : Complex A) (M : RightModule A D) (N : LeftModule A D) :
    BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D (tensorModule K M)) (leftModule φ D N) ≅
      (extension φ).obj K ⊗
        BalancedTensor.obj A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) :=
  (balancedIso φ D (tensorModule K M) N).symm ≪≫
    (extension φ).mapIso (BalancedTensor.tensorModuleIso A D K M N) ≪≫
      tensorIso φ K (BalancedTensor.obj A D M N) ≪≫
        cochainTensorIso (Iso.refl _) (balancedIso φ D M N)

@[reassoc]
lemma ι_tensorModuleBaseChangeIso (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (x : D) :
    BalancedTensor.ι A' (DGBaseChange φ D)
        (rightModule φ D (tensorModule K M)) (leftModule φ D N) x ≫
      (tensorModuleBaseChangeIso φ D K M N).hom =
    (tensorIso φ K (M.obj (op x))).hom ▷ (extension φ).obj (N.obj x) ≫
      (α_ ((extension φ).obj K) ((extension φ).obj (M.obj (op x)))
        ((extension φ).obj (N.obj x))).hom ≫
      (extension φ).obj K ◁
        BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) x := by
  simp only [tensorModuleBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, cochainTensorIso, MonoidalCategory.tensorIso_hom,
    Iso.refl_hom,
    id_tensorHom, BalancedTensor.tensorModuleIso]
  rw [balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    BalancedTensor.ι_tensorModuleHom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := tensorIso_naturality φ (𝟙 K) (BalancedTensor.ι A D M N x)
  simp only [CategoryTheory.Functor.map_id, id_tensorHom] at hn
  rw [← Category.assoc ((extension φ).map (K ◁ BalancedTensor.ι A D M N x))
    (tensorIso φ K (BalancedTensor.obj A D M N)).hom
    ((extension φ).obj K ◁ (balancedIso φ D M N).hom), hn]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp, balancedIso_ι, whiskerLeft_comp]
  have ha := congrArg (fun f => (tensorIso φ (K ⊗ M.obj (op x)) (N.obj x)).inv ≫ f ≫
      (extension φ).obj K ◁
        BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) x)
    (tensorIso_associator φ K (M.obj (op x)) (N.obj x)).symm
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at ha
  convert ha using 1

@[reassoc]
lemma tensorModuleBaseChange_comparison (K : Complex A) (M : RightModule A D)
    (N : LeftModule A D) :
    (balancedIso φ D (tensorModule K M) N).hom ≫
        (tensorModuleBaseChangeIso φ D K M N).hom =
      (extension φ).map (BalancedTensor.tensorModuleIso A D K M N).hom ≫
        (tensorIso φ K (BalancedTensor.obj A D M N)).hom ≫
          (extension φ).obj K ◁ (balancedIso φ D M N).hom := by
  simp only [tensorModuleBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, cochainTensorIso, MonoidalCategory.tensorIso_hom,
    Iso.refl_hom, id_tensorHom, Iso.hom_inv_id_assoc]

end SerrePositivity.DifferentialGraded.ScalarExtension
