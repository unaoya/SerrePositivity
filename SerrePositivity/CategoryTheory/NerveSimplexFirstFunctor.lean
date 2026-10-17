module

public import SerrePositivity.CategoryTheory.NerveSimplexStart
public import SerrePositivity.CategoryTheory.ElementsChainLifting
public import SerrePositivity.CategoryTheory.NerveHomotopyUniverse
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveAugmentation

/-!
# 先頭単体を取る関手が元のnerve augmentationを回収する

## 概要
先頭単体を取る関手が元のnerve augmentationを回収する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
単体を表す合成可能射列の先頭または終端を評価する。
単体圏の射と射列の制限を照合し、関手の法則とaugmentationの式を確認する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0015][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#m0015
[plan]: ../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The first-simplex functor recovers the actual nerve augmentation

All original simplex operators and their prefix maps are used. The
identity is an equality of whole simplicial maps, before localization.
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.NerveSimplexFirstFunctor
variable (D : Type u) [Category.{v} D]

def first : (nerve D).Elements ⥤ D where
  obj s := s.val.obj 0
  map f := NerveSimplexStart.startMap f.op
  map_id s := NerveSimplexStart.startMap_id (Opposite.op s)
  map_comp f g := NerveSimplexStart.startMap_comp g.op f.op

lemma canonical_chain {n : ℕ} (δ : ComposableArrows SimplexCategoryᵒᵖ n)
    (z : (nerve D).obj (δ.obj 0)) :
    LabelledChain.lift (nerve D) δ z ⋙ first D =
      (SimplexCategory.toCat.map (SimplexChainParameter.parameter δ)).toFunctor ⋙ z := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have he : δ.map (homOfLE (Fin.zero_le i)) ≫ δ.map h =
      δ.map (homOfLE (Fin.zero_le j)) := (δ.map_comp _ _).symm
  have hi := congrArg (fun f => f.unop.toOrderHom 0) he
  change z.map (homOfLE ((δ.map (homOfLE (Fin.zero_le i))).unop.toOrderHom.monotone
      (Fin.zero_le ((δ.map h).unop.toOrderHom 0)))) ≫
      eqToHom (congrArg z.obj hi) = _
  rw [← eqToHom_map z hi, ← z.map_comp]
  apply congrArg z.map
  exact Subsingleton.elim _ _

lemma chain_augmentation {n : ℕ} (c : ComposableArrows (nerve D).Elements n) :
    c ⋙ first D =
      (SimplicialModel.SimplexNerveAugmentation.augmentation (nerve D)).app
        (Opposite.op (SimplexCategory.mk n)) c := by
  calc
    _ = LabelledChain.lift (nerve D)
        (c ⋙ Functor.Elements.π (nerve D)) (c.obj 0).val ⋙ first D :=
      congrArg (fun e => e ⋙ first D) (LabelledChain.reconstruct (nerve D) c).symm
    _ = _ := canonical_chain D _ _

/-- 先頭単体を取る関手が元のnerve augmentationを回収する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
単体を表す合成可能射列の先頭または終端を評価する。
単体圏の射と射列の制限を照合し、関手の法則とaugmentationの式を確認する。
-/
lemma augmentation_eq : NerveHomotopyUniverse.map (first D) =
    SSet.uliftFunctor.{max u v, max u v}.map
      (SimplicialModel.SimplexNerveAugmentation.augmentation (nerve D)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply ULift.ext
  exact chain_augmentation D c.down

end SerrePositivity.NerveSimplexFirstFunctor
