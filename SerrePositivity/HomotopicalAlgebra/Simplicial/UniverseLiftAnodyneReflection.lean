module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneModelDetection

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyClasses
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# 宇宙liftの前後でanodyne局所化の可逆性が同値となる

## 概要
宇宙liftの前後でanodyne局所化の可逆性が同値となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0589][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0589
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reflection of anodyne localization across simplicial universes

Kan valued homotopy classes detect the comparison. Replacements use only the
horn small-object argument, with no model structure in either universe.
-/

@[expose] public section
universe w v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.SimplicialModel.UniverseLift
open AnodyneHomotopy

instance preservesTerminal : PreservesLimitsOfShape (Discrete PEmpty) SSet.uliftFunctor.{w, v} := by
  apply preservesLimitsOfShape_of_evaluation
  intro n
  change PreservesLimitsOfShape (Discrete PEmpty)
    ((evaluation SimplexCategoryᵒᵖ (Type v)).obj n ⋙ CategoryTheory.uliftFunctor.{w, v})
  infer_instance

lemma horn_terminal_map {K : SSet.{v}}
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)) := by
  let e := (terminalIsTerminal.isTerminalObj SSet.uliftFunctor).uniqueUpToIso
    terminalIsTerminal
  let a : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (terminal.from K)) ≅ Arrow.mk (terminal.from (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)) :=
    Arrow.isoMk (Iso.refl _) e (by apply terminal.hom_ext)
  exact (SSet.modelCategoryQuillen.J.rlp.arrow_iso_iff a).mp
    ((horn_rightClass_iff (terminal.from K)).mpr hK)

lemma kan_test_bijective {X Y K : SSet.{v}} (f : X ⟶ Y)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
    (hf : IsIso (anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f))) :
    Function.Bijective (HomotopyClasses.pre f (K := K)) := by
  have h := map_isIso_of_anodyneQ_isIso (HomotopyClasses.functor (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)).rightOp
    (KanHomotopyClasses.rightOp_inverts _ (horn_terminal_map hK)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map f) hf
  have hp : IsIso ((HomotopyClasses.functor (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)).map ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f).op)) :=
    (isIso_op_iff _).mp h
  have hb : Function.Bijective (HomotopyClasses.pre (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f) (K := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)) :=
    (isIso_iff_bijective ((HomotopyClasses.functor (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)).map ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f).op))).mp hp
  have he : HomotopyClasses.pre f (K := K) =
      (homotopyClassEquiv.{w} X K).symm ∘
        HomotopyClasses.pre (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map f) ∘ homotopyClassEquiv Y K := by
    funext x
    exact (Equiv.eq_symm_apply _).mpr (homotopyClassEquiv_pre f x)
  rw [he]
  exact (homotopyClassEquiv X K).symm.bijective.comp
    (hb.comp (homotopyClassEquiv Y K).bijective)

lemma anodyneQ_map_isIso_reflect_of_kan {X Y : SSet.{v}} (f : X ⟶ Y)
    (hX : SSet.modelCategoryQuillen.J.rlp (terminal.from X))
    (hY : SSet.modelCategoryQuillen.J.rlp (terminal.from Y))
    (hf : IsIso (anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f))) : IsIso (anodyneQ.map f) :=
  HomotopyClasses.map_isIso_of_tests anodyneQ (Localization.inverts _ _)
    f (kan_test_bijective f hX hf).surjective (kan_test_bijective f hY hf).injective

/- 旧宣言の技術注記：
Reflection for every small map. The auxiliary Kan replacements are obtained
from the horn small-object argument, without assuming any model structure.
-/
/-- 宇宙lift後のanodyne局所化可逆性から元の局所化可逆性を反映する。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
lemma anodyneQ_map_isIso_reflect {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f))) : IsIso (anodyneQ.map f) := by
  let J := SSet.modelCategoryQuillen.J.{v}
  let dx := MorphismProperty.factorizationData J.rlp.llp J.rlp (terminal.from X)
  let dy := MorphismProperty.factorizationData J.rlp.llp J.rlp (terminal.from Y)
  have hix : SSet.anodyneExtensions dx.i := dx.hi
  have hiy : SSet.anodyneExtensions dy.i := dy.hi
  have hx : J.rlp (terminal.from dx.Z) := by
    rw [← terminal.hom_ext dx.p (terminal.from dx.Z)]
    exact dx.hp
  have hy : J.rlp (terminal.from dy.Z) := by
    rw [← terminal.hom_ext dy.p (terminal.from dy.Z)]
    exact dy.hp
  obtain ⟨g, hg⟩ := KanHomotopyExtension.exists_extension dx.i hix hy (f ≫ dy.i)
  let F := SSet.uliftFunctor.{w, v} ⋙ anodyneQ
  have hFx : IsIso (F.map dx.i) := anodyneQ_lift_inverts dx.i hix
  have hFy : IsIso (F.map dy.i) := anodyneQ_lift_inverts dy.i hiy
  have hf' : IsIso (F.map f) := hf
  have hs : F.map dx.i ≫ F.map g = F.map f ≫ F.map dy.i :=
    (F.map_comp _ _).symm.trans ((congrArg F.map hg).trans (F.map_comp _ _))
  have hFg : IsIso (F.map g) := by
    rw [← isIso_comp_left_iff (F.map dx.i), hs]
    infer_instance
  have hQg : IsIso (anodyneQ.map g) := anodyneQ_map_isIso_reflect_of_kan g hx hy hFg
  have hQx : IsIso (anodyneQ.map dx.i) := Localization.inverts _ _ _ hix
  have hQy : IsIso (anodyneQ.map dy.i) := Localization.inverts _ _ _ hiy
  have hs' : anodyneQ.map dx.i ≫ anodyneQ.map g = anodyneQ.map f ≫ anodyneQ.map dy.i :=
    (anodyneQ.map_comp _ _).symm.trans
      ((congrArg anodyneQ.map hg).trans (anodyneQ.map_comp _ _))
  rw [← isIso_comp_right_iff (anodyneQ.map f) (anodyneQ.map dy.i), ← hs']
  infer_instance

/-- 宇宙liftの前後でanodyne局所化の可逆性が同値となる。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
lemma anodyneQ_map_isIso_iff {X Y : SSet.{v}} (f : X ⟶ Y) :
    IsIso (anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f)) ↔ IsIso (anodyneQ.map f) :=
  ⟨anodyneQ_map_isIso_reflect f, anodyneQ_map_isIso_of_small f⟩

open HomotopicalAlgebra in
/-- The comparison detects precisely the original small model weak equivalences. -/
lemma weakEquivalences_iff_lift_anodyneQ_isIso [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {X Y : SSet.{v}} (f : X ⟶ Y) :
    weakEquivalences SSet.{v} f ↔ IsIso (anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f)) :=
  (weakEquivalences_iff_anodyneQ_isIso hcof hfib f).trans (anodyneQ_map_isIso_iff f).symm

open HomotopicalAlgebra in
/-- An entire natural comparison can be tested after lifting and localizing,
while its components remain weak equivalences in the original small model. -/
lemma natural_weakEquivalences_iff_lift_isIso [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{v}} (α : F ⟶ G) :
    (∀ d, weakEquivalences SSet.{v} (α.app d)) ↔
      IsIso (Functor.whiskerRight α (SSet.uliftFunctor.{w, v} ⋙ anodyneQ)) := by
  constructor
  · intro hα
    have (d : D) : IsIso ((Functor.whiskerRight α
        (SSet.uliftFunctor.{w, v} ⋙ anodyneQ)).app d) :=
      (weakEquivalences_iff_lift_anodyneQ_isIso hcof hfib (α.app d)).mp (hα d)
    exact NatIso.isIso_of_isIso_app _
  · intro hα d
    have : IsIso (Functor.whiskerRight α (SSet.uliftFunctor.{w, v} ⋙ anodyneQ)) := hα
    exact (weakEquivalences_iff_lift_anodyneQ_isIso hcof hfib (α.app d)).mpr
      (inferInstanceAs (IsIso ((Functor.whiskerRight α
        (SSet.uliftFunctor.{w, v} ⋙ anodyneQ)).app d)))

end SerrePositivity.SimplicialModel.UniverseLift
