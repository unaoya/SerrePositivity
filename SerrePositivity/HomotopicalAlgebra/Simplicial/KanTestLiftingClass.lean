module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRestrictionLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRelativeLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoStrictExtension
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# 局所化可逆な単射を固定した左持ち上げクラスとの交わりとして特徴付ける

## 概要
局所化可逆な単射を固定した左持ち上げクラスとの交わりとして特徴付ける。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0438][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0438
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Localized mono equivalences as a fixed left lifting class intersected with monos

The fixed right tests are terminal maps of Kan objects and their actual
path restrictions to the two endpoints. No model structure is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.KanTestLiftingClass

abbrev pathRestriction (K : SSet.{v}) :=
  Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom
    (SSet.boundary 1).ι (terminal.from K) terminalIsTerminal

inductive RightTests : ∀ {A B : SSet.{v}}, (A ⟶ B) → Prop
  | terminal (K : SSet.{v}) (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
      RightTests (terminal.from K)
  | paths (K : SSet.{v}) (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
      RightTests (pathRestriction K).π

abbrev rightTests : MorphismProperty SSet.{v} := @RightTests

def localizedMonos : MorphismProperty SSet.{v} :=
  fun _ _ i => Mono i ∧ IsIso (AnodyneHomotopy.anodyneQ.map i)

variable {A B K : SSet.{v}} (i : A ⟶ B)

lemma path_lifting_of_boundaryProduct
    (hl : HasLiftingProperty (KanRelativeLifting.boundaryProduct i).ι (terminal.from K)) :
    HasLiftingProperty i (pathRestriction K).π := by
  let pp := KanRelativeLifting.boundaryProduct i
  have hf : HasLiftingProperty pp.flipTensor.ι (terminal.from K) :=
    (HasLiftingProperty.iff_of_arrow_iso_left
      (show Arrow.mk pp.ι ≅ Arrow.mk pp.flipTensor.ι from
        Arrow.isoMk (Iso.refl _) (β_ _ _)) (terminal.from K)).mp hl
  exact (internalHomAdjunction₂.hasLiftingProperty_iff pp.flipTensor
    (pathRestriction K)).mp hf

lemma boundaryProduct_lifting_of_path
    (hl : HasLiftingProperty i (pathRestriction K).π) :
    HasLiftingProperty (KanRelativeLifting.boundaryProduct i).ι (terminal.from K) := by
  let pp := KanRelativeLifting.boundaryProduct i
  have hf : HasLiftingProperty pp.flipTensor.ι (terminal.from K) :=
    (internalHomAdjunction₂.hasLiftingProperty_iff pp.flipTensor (pathRestriction K)).mpr hl
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (show Arrow.mk pp.ι ≅ Arrow.mk pp.flipTensor.ι from
      Arrow.isoMk (Iso.refl _) (β_ _ _)) (terminal.from K)).mpr hf

lemma localizedMono_le_llp : localizedMonos.{v} ≤ rightTests.llp := by
  intro A B i hi E T p hp
  have : Mono i := hi.1
  cases hp with
  | terminal K hK => exact KanMonoStrictExtension.terminal_lifting i hK hi.2
  | paths K hK =>
    apply path_lifting_of_boundaryProduct
    have hr : HasLiftingProperty (SSet.boundary.{v} 1).ι
        ((MonoidalClosed.pre i).app K) :=
      KanRestrictionLifting.all_mono_rlp i hi.2 hK _ inferInstance
    exact (internalHomAdjunction₂.hasLiftingProperty_iff
      (KanRelativeLifting.boundaryProduct i)
      (Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom
        i (terminal.from K) terminalIsTerminal)).mpr hr

lemma tests_of_llp (hi : rightTests.llp i) : KanTestDetection.Tests i := by
  intro K hK
  constructor
  · intro x y h
    obtain ⟨f, rfl⟩ := Quot.exists_rep x
    obtain ⟨g, rfl⟩ := Quot.exists_rep y
    obtain ⟨H⟩ := KanActualHomotopy.of_class_eq hK h
    have hl := boundaryProduct_lifting_of_path i (hi _ (RightTests.paths K hK))
    obtain ⟨V, _⟩ := KanRelativeLifting.exists_extension i hl f g H
    exact HomotopyClasses.sound V
  · intro x
    obtain ⟨f, rfl⟩ := Quot.exists_rep x
    have : HasLiftingProperty i (terminal.from K) := hi _ (RightTests.terminal K hK)
    let sq : CommSq f i (terminal.from K) (terminal.from B) := ⟨by simp⟩
    exact ⟨HomotopyClasses.mk sq.lift, congrArg HomotopyClasses.mk sq.fac_left⟩

lemma localized_isIso_of_llp (hi : rightTests.llp i) :
    IsIso (AnodyneHomotopy.anodyneQ.map i) :=
  (KanTestDetection.anodyneQ_isIso_iff_tests i).mpr (tests_of_llp i hi)

/-- 局所化可逆な単射を固定した左持ち上げクラスとの交わりとして特徴付ける。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
lemma localizedMonos_eq : localizedMonos.{v} =
    MorphismProperty.monomorphisms SSet.{v} ⊓ rightTests.llp := by
  funext A B i
  apply propext
  constructor
  · intro hi
    exact ⟨hi.1, localizedMono_le_llp i hi⟩
  · intro hi
    exact ⟨hi.1, localized_isIso_of_llp i hi.2⟩

end SerrePositivity.SimplicialModel.KanTestLiftingClass
