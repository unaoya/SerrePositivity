module
public import SerrePositivity.DifferentialGraded.Tensor.ParameterTensorFamilies

/-! # 生成複体とのtensorをbalanced tensorの外へ出す同型

## 概要
生成複体とのtensorをbalanced tensorの外へ出す同型。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/ModuleCylinderKFlat.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (K : Complex A) (M : RightModule A D) (N : LeftModule A D)

def tensorModuleHom : obj A D (tensorModule K M) N ⟶ K ⊗ obj A D M N :=
  desc A D (tensorModule K M) N
    (paramTensorFamily A D (paramRestrict A D M N (𝟙 (K ⊗ obj A D M N))))

def tensorModuleInv : K ⊗ obj A D M N ⟶ obj A D (tensorModule K M) N :=
  paramDesc A D M N (tensorParamFamily A D
    (homEquiv A D (tensorModule K M) N _ (𝟙 (obj A D (tensorModule K M) N))))

@[reassoc]
lemma ι_tensorModuleHom (x : D) :
    ι A D (tensorModule K M) N x ≫ tensorModuleHom A D K M N =
      (α_ K (M.obj (Opposite.op x)) (N.obj x)).hom ≫ K ◁ ι A D M N x := by
  rw [tensorModuleHom, ι_desc]
  change (α_ K (M.obj (Opposite.op x)) (N.obj x)).hom ≫
    ((K ◁ ι A D M N x) ≫ 𝟙 _) = _
  rw [Category.comp_id]

@[reassoc]
lemma ι_tensorModuleInv (x : D) :
    (K ◁ ι A D M N x) ≫ tensorModuleInv A D K M N =
      (α_ K (M.obj (Opposite.op x)) (N.obj x)).inv ≫ ι A D (tensorModule K M) N x := by
  rw [tensorModuleInv, ι_paramDesc]
  change (α_ K (M.obj (Opposite.op x)) (N.obj x)).inv ≫
    (ι A D (tensorModule K M) N x ≫ 𝟙 _) = _
  rw [Category.comp_id]

def tensorModuleIso : obj A D (tensorModule K M) N ≅ K ⊗ obj A D M N where
  hom := tensorModuleHom A D K M N
  inv := tensorModuleInv A D K M N
  hom_inv_id := by
    apply hom_ext A D (tensorModule K M) N
    intro x
    rw [ι_tensorModuleHom_assoc, ι_tensorModuleInv, Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply param_hom_ext A D M N
    intro x
    rw [ι_tensorModuleInv_assoc, ι_tensorModuleHom, Iso.inv_hom_id_assoc, Category.comp_id]

end SerrePositivity.DifferentialGraded.BalancedTensor
