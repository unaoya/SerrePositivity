module

public import SerrePositivity.InfinityCategories.F2.BousfieldKanTerminalCylinder

/-!
概要：終対象による coend の脚上の円柱は dinatural。
方針：重みの収縮の自然性、tensor の交換則、普遍脚の dinaturality を組み合わせる。
規約：全ての高次単体を同時に比較する。
使われ方：脚上のホモトピーを coend 全体へ降下させる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I] {t : I}

/-- 概要：終対象からの収縮円柱は coend の同一視と整合する。
方針：結合子で時間を移し、重みの自然性の後に coend の関係を使う。
規約：元の円柱を変更しない。使われ方：global な収縮ホモトピーの構成。 -/
lemma terminalWeightLegHomotopy_naturality (F : I ⥤ SSet.{u}) (ht : IsTerminal t)
    {i j : I} (f : i ⟶ j) :
    ((F.obj i ◁ (bousfieldKanWeight Iᵒᵖ).map f.op) ▷ (Δ[1] : SSet.{u})) ≫
      (terminalWeightLegHomotopy F ht i).h =
        ((F.map f ▷ (bousfieldKanWeight Iᵒᵖ).obj (Opposite.op j)) ▷ (Δ[1] : SSet.{u})) ≫
          (terminalWeightLegHomotopy F ht j).h := by
  let W := bousfieldKanWeight Iᵒᵖ
  change ((F.obj i ◁ W.map f.op) ▷ (Δ[1] : SSet.{u})) ≫
    (α_ (F.obj i) (W.obj (Opposite.op i)) (Δ[1] : SSet.{u})).hom ≫
      (F.obj i ◁ (terminalWeightHomotopy ht i).h) ≫ weightedColimitι W F i =
    ((F.map f ▷ W.obj (Opposite.op j)) ▷ (Δ[1] : SSet.{u})) ≫
      (α_ (F.obj j) (W.obj (Opposite.op j)) (Δ[1] : SSet.{u})).hom ≫
        (F.obj j ◁ (terminalWeightHomotopy ht j).h) ≫ weightedColimitι W F j
  have h₁ : ((F.obj i ◁ W.map f.op) ▷ (Δ[1] : SSet.{u})) ≫
      (α_ (F.obj i) (W.obj (Opposite.op i)) (Δ[1] : SSet.{u})).hom =
        (α_ (F.obj i) (W.obj (Opposite.op j)) (Δ[1] : SSet.{u})).hom ≫
          (F.obj i ◁ (W.map f.op ▷ (Δ[1] : SSet.{u}))) := rfl
  have h₂ : ((F.map f ▷ W.obj (Opposite.op j)) ▷ (Δ[1] : SSet.{u})) ≫
      (α_ (F.obj j) (W.obj (Opposite.op j)) (Δ[1] : SSet.{u})).hom =
        (α_ (F.obj i) (W.obj (Opposite.op j)) (Δ[1] : SSet.{u})).hom ≫
          (F.map f ▷ (W.obj (Opposite.op j) ⊗ (Δ[1] : SSet.{u}))) := rfl
  rw [reassoc_of% h₁, reassoc_of% h₂, ← whiskerLeft_comp_assoc,
    terminalWeightHomotopy_naturality, whiskerLeft_comp_assoc, weightedColimit_condition]
  rfl

end SerrePositivity.InfinityCategories.F2
