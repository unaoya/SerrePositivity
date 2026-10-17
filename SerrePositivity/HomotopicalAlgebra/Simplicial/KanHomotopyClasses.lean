module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyExtension

/-!
# Kan値の区間ホモトピー類への前合成はanodyne射を全単射へ送る

## 概要
Kan値の区間ホモトピー類への前合成はanodyne射を全単射へ送る。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。
[棚卸し m0413][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0413
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Kan valued homotopy classes invert every anodyne extension

An inverse is constructed by extension. Homotopy extension proves that this
construction descends to classes and is independent of the selected extensions.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.SimplicialModel.KanHomotopyClasses
open HomotopyClasses
variable {A B K : SSet.{v}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

def extension (f : A ⟶ K) : B ⟶ K :=
  (KanHomotopyExtension.exists_extension i hi hK f).choose

@[simp] lemma extension_fac (f : A ⟶ K) : i ≫ extension i hi hK f = f :=
  (KanHomotopyExtension.exists_extension i hi hK f).choose_spec

def inverse : obj A K → obj B K :=
  Quot.lift (fun f => mk (extension i hi hK f)) (by
    intro f g h
    obtain ⟨H⟩ := h
    apply Quot.sound
    apply KanHomotopyExtension.exists_homotopy i hi hK
    simpa only [extension_fac] using H)

lemma inverse_right (x : obj A K) : pre i (inverse i hi hK x) = x := by
  refine Quot.inductionOn x (fun f => ?_)
  exact congrArg mk (extension_fac i hi hK f)

lemma inverse_left (x : obj B K) : inverse i hi hK (pre i x) = x := by
  refine Quot.inductionOn x (fun f => ?_)
  apply Quot.sound
  apply KanHomotopyExtension.exists_homotopy i hi hK
  rw [extension_fac]
  exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (i ≫ f))

include hi hK in
/-- Kan値の区間ホモトピー類への前合成はanodyne射を全単射へ送る。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。
-/
lemma pre_bijective : Function.Bijective (pre i (K := K)) :=
  ⟨Function.LeftInverse.injective (inverse_left i hi hK),
    Function.RightInverse.surjective (inverse_right i hi hK)⟩

lemma functor_inverts (K : SSet.{v})
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    SSet.anodyneExtensions.op.IsInvertedBy (functor K) := by
  intro X Y f hf
  exact (isIso_iff_bijective _).mpr (pre_bijective f.unop hf hK)

lemma rightOp_inverts (K : SSet.{v})
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    SSet.anodyneExtensions.IsInvertedBy (functor K).rightOp :=
  (functor_inverts K hK).rightOp

end SerrePositivity.SimplicialModel.KanHomotopyClasses
