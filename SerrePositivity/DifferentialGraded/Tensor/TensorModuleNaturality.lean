module
public import SerrePositivity.DifferentialGraded.Tensor.TensorModuleIso
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunction
public import SerrePositivity.DifferentialGraded.Module.Cylinder

/-! # balanced tensorの外へ出す同型の生成複体に関する自然性とcylinder射影

## 概要
balanced tensorの外へ出す同型の生成複体に関する自然性とcylinder射影。

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
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma tensorModuleHom_naturality {K L : Complex A} (f : K ⟶ L)
    (M : RightModule A D) (N : LeftModule A D) :
    (rightTensorFunctor A D N).map (tensorModuleMap f M) ≫ tensorModuleHom A D L M N =
      tensorModuleHom A D K M N ≫ (f ⊗ₘ 𝟙 (obj A D M N)) := by
  apply hom_ext
  intro x
  have h := ι_map A D (tensorModuleMap f M) (𝟙 (ForgetEnrichment.of (Complex A) N)) x
  rw [tensorModuleMap_eval, CategoryTheory.Functor.map_id] at h
  have hL := ι_tensorModuleHom A D L M N x
  have hK := ι_tensorModuleHom_assoc A D K M N x (f ⊗ₘ 𝟙 (obj A D M N))
  have hm : ((f ⊗ₘ 𝟙 (M.obj (Opposite.op x))) ⊗ₘ 𝟙 (N.obj x)) ≫
      (α_ L (M.obj (Opposite.op x)) (N.obj x)).hom ≫ L ◁ ι A D M N x =
    (α_ K (M.obj (Opposite.op x)) (N.obj x)).hom ≫
      K ◁ ι A D M N x ≫ (f ⊗ₘ 𝟙 (obj A D M N)) := by
    simp only [tensorHom_id]
    rw [associator_naturality_left_assoc, whisker_exchange]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ tensorModuleHom A D L M N) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => ((f ⊗ₘ 𝟙 (M.obj (Opposite.op x))) ⊗ₘ 𝟙 (N.obj x)) ≫ k) hL).trans
          (hm.trans hK.symm))))

/-- interval射影は任意の固定左因子とのbalanced tensor後も準同型。 -/
lemma rightTensor_intervalProjection_quasiIso (M : RightModule A D) (N : LeftModule A D) :
    QuasiIso ((rightTensorFunctor A D N).map
      (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) M)) := by
  have h := tensorModuleHom_naturality A D (cylinder.π (𝟙_ (Complex A))) M N
  have : IsIso (tensorModuleHom A D (dgInterval A) M N) :=
    (tensorModuleIso A D (dgInterval A) M N).isIso_hom
  have : IsIso (tensorModuleHom A D (𝟙_ (Complex A)) M N) :=
    (tensorModuleIso A D (𝟙_ (Complex A)) M N).isIso_hom
  have : QuasiIso (cylinder.π (𝟙_ (Complex A)) ⊗ₘ 𝟙 (obj A D M N)) :=
    (tensorIntervalHomotopyEquiv A (obj A D M N)).quasiIso_hom
  have : QuasiIso ((rightTensorFunctor A D N).map
      (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) M) ≫
        tensorModuleHom A D (𝟙_ (Complex A)) M N) := h.symm ▸ (quasiIso_comp _ _)
  exact quasiIso_of_comp_right _ (tensorModuleHom A D (𝟙_ (Complex A)) M N)

lemma rightTensor_precylinderProjection_quasiIso (M : ModuleCategory A D)
    (N : LeftModule A D) :
    QuasiIso ((rightTensorFunctor A D N).map (modulePrecylinder A D M).π) := by
  have := rightTensor_intervalProjection_quasiIso A D (ForgetEnrichment.to (Complex A) M) N
  change QuasiIso ((rightTensorFunctor A D N).map
    (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M) ≫
      (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.DifferentialGraded.BalancedTensor
