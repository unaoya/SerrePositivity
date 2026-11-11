module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection

/-!
# 小さいKan値のlift間の局所化射の等式を元の実ホモトピーで判定する

## 概要
小さいKan値のlift間の局所化射の等式を元の実ホモトピーで判定する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。
[棚卸し m0598][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0598
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Small homotopy classes compute localized Hom between lifted small Kan values

This controls Hom size after localization. It does not shrink the simplices
of the original large space or construct a strict small replacement diagram.
-/

@[expose] public section
universe w v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.UniverseLift
variable {D : Type uD} [Category.{vD} D] (L : SSet.{max w v} ⥤ D)
  [L.IsLocalization SSet.anodyneExtensions]
  (X K : SSet.{v}) (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

/-- The small source of the equivalence is the original homotopy-class type. -/
def smallLocalizedHomEquiv : HomotopyClasses.obj X K ≃
    (L.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X) ⟶ L.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)) :=
  (homotopyClassEquiv.{w} X K).trans
    (KanLocalizedRepresentatives.homEquiv L (horn_terminal_map hK) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj X))

@[simp] lemma smallLocalizedHomEquiv_mk (f : X ⟶ K) :
    smallLocalizedHomEquiv L X K hK (HomotopyClasses.mk f) = L.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f) := rfl

include hK in
lemma small_localizedHom : Small.{v} (L.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X) ⟶ L.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)) :=
  small_map (smallLocalizedHomEquiv L X K hK).symm

/-- Every localized arrow between lifted small values has an original small
map as representative. The target is Kan in the original small universe. -/
def localizedRepresentative (φ : L.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X) ⟶ L.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)) : X ⟶ K :=
  (Quot.exists_rep ((smallLocalizedHomEquiv L X K hK).symm φ)).choose

lemma localizedRepresentative_map (φ : L.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X) ⟶ L.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)) :
    L.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (localizedRepresentative L X K hK φ)) = φ := by
  change smallLocalizedHomEquiv L X K hK
    (HomotopyClasses.mk (localizedRepresentative L X K hK φ)) = φ
  exact (congrArg (smallLocalizedHomEquiv L X K hK)
    (Quot.exists_rep ((smallLocalizedHomEquiv L X K hK).symm φ)).choose_spec).trans
      ((smallLocalizedHomEquiv L X K hK).apply_symm_apply φ)

include hK in
/-- 小さいKan値のlift間の局所化射の等式を元の実ホモトピーで判定する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
lemma localized_map_eq_iff_homotopy (f g : X ⟶ K) :
    L.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f) = L.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} g) ↔ Nonempty (SSet.Homotopy f g) :=
  ⟨fun he => KanActualHomotopy.of_class_eq hK
      ((smallLocalizedHomEquiv L X K hK).injective he),
    fun ⟨H⟩ => AnodyneHomotopy.map_homotopy_eq L (Localization.inverts L _) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.homotopy H)⟩

end SerrePositivity.SimplicialModel.UniverseLift
