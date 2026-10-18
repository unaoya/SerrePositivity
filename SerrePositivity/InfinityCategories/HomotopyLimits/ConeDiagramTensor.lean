module

public import SerrePositivity.InfinityCategories.Core.JoinTensorInterval

/-!
概要：join と直積の標準比較が、図式の因子の射と可換であることを示す。
方針：join の切断を保ち、補った直積の単体で二成分を比較する。
規約：パラメータの直積因子は固定する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6 の錐の模型の図式制限の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：補った直積の左因子への射は二成分表示を保つ。
方針：空次数と正次数に分けて定義を計算する。
規約：r は頂点数。
使われ方：Kerodon §4.6.6 の右パラメータの比較の自然性。 -/
lemma augTensorEquiv_symm_homLeft {B D : SSet.{u}} (f : B ⟶ D) (A : SSet.{u})
    (r : ℕ) (b : Join.augObj B r) (a : Join.augObj A r) :
    Join.augHom (f ▷ A) r ((Join.augTensorEquiv B A r).symm (b, a)) =
      (Join.augTensorEquiv D A r).symm (Join.augHom f r b, a) := by
  cases r <;> rfl

/-- 概要：join の右側の直積への比較は、右図式の射と可換。
方針：切断と左単体を保ち、右の直積の成分を比較する。
規約：パラメータ A は共通。
使われ方：Kerodon 7.4.1.6 の切断側の比較と図式の制限の可換性。 -/
lemma joinTensorRight_diagram {B D : SSet.{u}} (f : B ⟶ D) (C A : SSet.{u}) :
    (joinMap (𝟙 C) f ▷ A) ≫ joinTensorRight C D A =
      joinTensorRight C B A ≫ joinMap (𝟙 C) (f ▷ A) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨ℓ, c, b⟩, a⟩
  change (⟨ℓ, Join.augHom (𝟙 C) ℓ.val c,
      (Join.augTensorEquiv D A (n + 1 - ℓ.val)).symm
        (Join.augHom f (n + 1 - ℓ.val) b,
          Join.augMap A (Join.suffixIncl (n + 1) ℓ.val _) a)⟩ :
      Join.Simplex C (D ⊗ A) n) =
    ⟨ℓ, Join.augHom (𝟙 C) ℓ.val c,
      Join.augHom (f ▷ A) (n + 1 - ℓ.val)
        ((Join.augTensorEquiv B A (n + 1 - ℓ.val)).symm
          (b, Join.augMap A (Join.suffixIncl (n + 1) ℓ.val _) a))⟩
  rw [augTensorEquiv_symm_homLeft]

/-- 概要：join の左側の直積への比較は、右図式の射と可換。
方針：切断と左側の直積を保ち、右単体だけに射を適用する。
規約：直積のパラメータ A と左因子 C は共通。
使われ方：Kerodon 7.4.1.6 の slice 側の比較と図式の制限の可換性。 -/
lemma joinTensorLeft_diagram {B D : SSet.{u}} (f : B ⟶ D) (A C : SSet.{u}) :
    (A ◁ joinMap (𝟙 C) f) ≫ joinTensorLeft A C D =
      joinTensorLeft A C B ≫ joinMap (𝟙 (A ⊗ C)) f := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, ⟨ℓ, c, b⟩⟩
  change (⟨ℓ, (Join.augTensorEquiv A C ℓ.val).symm
      (Join.augMap A (Join.prefixIncl (n + 1) ℓ.val _) a,
        Join.augHom (𝟙 C) ℓ.val c), Join.augHom f (n + 1 - ℓ.val) b⟩ :
      Join.Simplex (A ⊗ C) D n) =
    ⟨ℓ, Join.augHom (𝟙 (A ⊗ C)) ℓ.val
      ((Join.augTensorEquiv A C ℓ.val).symm
        (Join.augMap A (Join.prefixIncl (n + 1) ℓ.val _) a, c)),
      Join.augHom f (n + 1 - ℓ.val) b⟩
  rw [Join.augHom_id, Join.augHom_id]

end SerrePositivity.InfinityCategories.HomotopyLimits
