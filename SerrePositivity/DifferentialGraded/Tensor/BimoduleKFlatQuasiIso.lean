module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleQuasiIso
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComparison

/-! # 右相対K-flat因子間の準同型をbimodule合成が保存する

## 概要
右相対K-flat因子間の準同型をbimodule合成が保存する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensorKFlatComparison.lean。
局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeMap_second_kFlat_quasiIso (P : BimoduleCategory A B C)
    {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E (𝟙 P) g) := by
  intro b e
  rw [composeMap_value_eval]
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  exact BalancedTensor.rightTensor_relativeKFlat_quasiIso A C
    ((BimoduleCategory.underlying A B C P).leftAt b) (hQ e) (hQ' e)
    ((BimoduleCategory.evaluation A C E e).map g)
    (BimoduleCategory.quasiIso_evaluation A C E hg e)

lemma composeMap_kFlat_quasiIso {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hf : BimoduleCategory.quasiIso A B C f) (hg : BimoduleCategory.quasiIso A C E g) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E f g) := by
  have h₁ := composeMap_first_quasiIso A B C E Q hQ f hf
  have h₂ := composeMap_second_kFlat_quasiIso A B C E P' hQ hQ' g hg
  have he := composeMap_comp A B C E f (𝟙 P') (𝟙 Q) g
  simp only [Category.comp_id, Category.id_comp] at he
  rw [he]
  exact (BimoduleCategory.quasiIso A B E).comp_mem _ _ h₁ h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
