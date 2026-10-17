module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorModuleFunctor
public import SerrePositivity.DifferentialGraded.Bimodule.QuasiIso

/-! # 積dg圏上の加群比較の本質的全射性と準同型の保存・反映

## 概要
積dg圏上の加群比較の本質的全射性と準同型の保存・反映。

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
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def objectPreimage (M : BimoduleCategory A B C) : BimoduleTensorModuleCategory A B C :=
  ForgetEnrichment.of (Complex A) (BimoduleCategory.underlying A B C M).toTensorFunctor

def objectPreimageIso (M : BimoduleCategory A B C) :
    (functor A B C).obj (objectPreimage A B C M) ≅ M :=
  eqToIso (by
    exact congrArg (BimoduleCategory.of A B C)
      (Bimodule.toTensorFunctor_toBimodule (BimoduleCategory.underlying A B C M)))

instance essSurj : (functor A B C).EssSurj where
  mem_essImage M := ⟨objectPreimage A B C M, ⟨objectPreimageIso A B C M⟩⟩

/-- 元の二つの閉零圏で指定した準同型のクラスは、値の評価により一致する。 -/
lemma functor_quasiIso_iff {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) :
    BimoduleCategory.quasiIso A B C ((functor A B C).map f) ↔
      leftModuleQuasiIso A (DGTensorCategory A Bᵒᵖ C) f := by
  constructor
  · intro hf
    apply (leftModuleQuasiIso_iff A (DGTensorCategory A Bᵒᵖ C) f).2
    intro x
    rcases x with ⟨b, c⟩
    have hh := hf b.unop c
    rw [functor_map_value] at hh
    exact hh
  · intro hf b c
    rw [functor_map_value]
    exact (leftModuleQuasiIso_iff A (DGTensorCategory A Bᵒᵖ C) f).1 hf (op b, c)

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
