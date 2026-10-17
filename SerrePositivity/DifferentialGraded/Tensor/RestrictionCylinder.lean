module
public import SerrePositivity.DifferentialGraded.Tensor.TensorModuleNaturality
public import SerrePositivity.DifferentialGraded.Module.RestrictionTensor

/-! # 制限された加群cylinder射影のbalanced tensor後の準同型性

## 概要
制限された加群cylinder射影のbalanced tensor後の準同型性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

lemma moduleRestrictionTensorIso_hom_eval (K : Complex A) (M : ModuleCategory A E) (d : D) :
    (moduleEvaluation A D d).map (moduleRestrictionTensorIso A D E F K M).hom = 𝟙 _ := by
  simp only [moduleRestrictionTensorIso, eqToIso.hom, CategoryTheory.Functor.map_id,
    eqToHom_refl]

/-- 制限された標準cylinderの射影は、同じintervalを使った制限加群の射影と可換。 -/
lemma moduleRestriction_precylinderProjection (M : ModuleCategory A E) :
    (moduleRestriction A D E F).map (modulePrecylinder A E M).π =
      (moduleRestrictionTensorIso A D E F (dgInterval A) M).hom ≫
        (modulePrecylinder A D ((moduleRestriction A D E F).obj M)).π := by
  apply moduleMorphism_ext
  intro d
  rw [moduleRestriction_map_eval, CategoryTheory.Functor.map_comp,
    moduleRestrictionTensorIso_hom_eval]
  refine Eq.trans ?_ (Category.id_comp ((moduleEvaluation A D d).map
    (modulePrecylinder A D ((moduleRestriction A D E F).obj M)).π)).symm
  change (moduleEvaluation A E (F.obj (op d)).unop).map
      (tensorModuleMap (HomologicalComplex.cylinder.π (𝟙_ (Complex A)))
          (ForgetEnrichment.to (Complex A) M) ≫
        (moduleTensorUnitIso A E (ForgetEnrichment.to (Complex A) M)).hom) =
    (moduleEvaluation A D d).map
      (tensorModuleMap (HomologicalComplex.cylinder.π (𝟙_ (Complex A)))
          (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M)) ≫
        (moduleTensorUnitIso A D
          (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M))).hom)
  simp only [CategoryTheory.Functor.map_comp, tensorModuleMap_eval, moduleTensorUnitIso_hom_eval]
  rfl

/-- 制限後の相対K-flat性を要求せず、cylinder射影のtensor像は準同型。 -/
lemma rightTensor_restrictedPrecylinderProjection_quasiIso (M : ModuleCategory A E)
    (N : LeftModule A D) :
    QuasiIso ((BalancedTensor.rightTensorFunctor A D N).map
      ((moduleRestriction A D E F).map (modulePrecylinder A E M).π)) := by
  have := BalancedTensor.rightTensor_precylinderProjection_quasiIso A D
    ((moduleRestriction A D E F).obj M) N
  rw [moduleRestriction_precylinderProjection, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.DifferentialGraded
