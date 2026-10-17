module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorComparison
public import SerrePositivity.DifferentialGraded.Bimodule.ValueActions

/-! # 閉零bimodule射の積dg圏上の全Hom自然性

## 概要
閉零bimodule射の積dg圏上の全Hom自然性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleFull.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 右作用と左作用に自然な閉零射は、積の全Homにも自然である。 -/
lemma valueMap_uncurry_naturality {M N : BimoduleCategory A B C} (a : M ⟶ N)
    (x y : DGTensorCategory A Bᵒᵖ C) :
    (underlying A B C M).uncurryHom x y ≫
      homPostcompose ((underlying A B C M).value x.1.unop x.2)
        ((valueEvaluation A B C y.1.unop y.2).map a) =
    (underlying A B C N).uncurryHom x y ≫
      homPrecompose ((valueEvaluation A B C x.1.unop x.2).map a)
        ((underlying A B C N).value y.1.unop y.2) := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (homPostcompose _ _).f n
    (((underlying A B C M).uncurryHom x y).f n (dgTensorElement A f g hn)) =
    (homPrecompose _ _).f n
      (((underlying A B C N).uncurryHom x y).f n (dgTensorElement A f g hn))
  rw [Bimodule.uncurryHom_apply, Bimodule.uncurryHom_apply]
  simp only [Units.smul_def, map_zsmul]
  apply congrArg (((p * q).negOnePow : ℤ) • ·)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply,
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega)]
  change ((valueEvaluation A B C y.1.unop y.2).map a).f j
    (leftAction A ((underlying A B C M).leftAt y.1.unop) g
      (moduleAction A ((underlying A B C M).rightAt x.2) f z rfl) (by omega)) =
    leftAction A ((underlying A B C N).leftAt y.1.unop) g
      (moduleAction A ((underlying A B C N).rightAt x.2) f
        (((valueEvaluation A B C x.1.unop x.2).map a).f i z) rfl) (by omega)
  rw [valueMap_leftAction, valueMap_rightAction]

end SerrePositivity.DifferentialGraded.BimoduleCategory
