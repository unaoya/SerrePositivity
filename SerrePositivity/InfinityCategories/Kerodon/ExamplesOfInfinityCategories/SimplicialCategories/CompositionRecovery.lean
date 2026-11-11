module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.IntervalChoice

/-!
# ホーンの合成面上の写像の回収

概要：真部分区間の Hom 回収を C の合成で結び、合成面上の写像を構成する。
方針：pathThroughIso の逆で二つの Hom に分割し、回収写像と sHomComp を適用する。
規約：外側区間が全区間でも、両脚が真部分区間なら構成できる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の空洞立方体の合成面。
零座標面との整合性は FullFaceCompatibility、合成面どうしは CompositionCompatibility に置く。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：両脚が真部分区間である合成面上に C の Hom への写像を構成する。
方針：合成面を二つの Path Hom の直積へ分割し、回収後に C の合成を取る。
規約：外側区間の真部分性を仮定しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の合成面の既知データ。 -/
def hornCompositionHom {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b c : Fin (n + 3))
    (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (hpbc : b ≠ 0 ∨ c ≠ Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{v} a) (c := ULift.up c) (ULift.up b) : SSet) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up a) (ULift.up b) (ULift.up c)).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a b hab hpab ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn b c hbc hpbc) ≫
        SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c)

/-- 概要：合成面上の回収を二つの Hom で前合成すると C における回収写像の合成になる。
方針：pathThroughIso と逆同型を消去する。
規約：等式は native な Path Hom の直積上の写像の等式。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の合成面の貼合せの検査。 -/
lemma hornCompositionHom_on_product {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b c : Fin (n + 3))
    (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (hpbc : b ≠ 0 ∨ c ≠ Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up.{v} a) (ULift.up b) (ULift.up c)).hom ≫
      hornCompositionHom σ h0 hn a b c hab hbc hpab hpbc =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a b hab hpab ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn b c hbc hpbc) ≫
        SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) := by
  simp [hornCompositionHom]

/-- 概要：外側も真部分区間なら合成面上の回収は標準 Hom 回収の制限に等しい。
方針：合成面への同型で前合成し、真部分区間の合成則を使う。
規約：両脚と外側の真部分性をそれぞれ明示する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornCompositionHom_eq_proper {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b c : Fin (n + 3))
    (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (hpbc : b ≠ 0 ∨ c ≠ Fin.last (n + 2))
    (hpac : a ≠ 0 ∨ c ≠ Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{v} a) (c := ULift.up c) (ULift.up b)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a c (hab.trans hbc) hpac =
        hornCompositionHom σ h0 hn a b c hab hbc hpab hpbc := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up.{v} a) (ULift.up b) (ULift.up c)).hom).mp
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι]
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a b hab hpab ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn b c hbc hpbc) ≫
          SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom_comp σ h0 hn a b c hab hbc hpab hpbc hpac
    _ = _ := by simp [hornCompositionHom]

/-- 概要：全区間の任意の内部切断点に対して合成面上の写像を構成する。
方針：両脚の真部分性を切断点の内部性から得て一般の合成面回収を適用する。
規約：全区間の未構成の Hom 写像や Kan 充填を仮定しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の空洞立方体の全ての合成面。 -/
def hornInnerCompositionHom {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (b : Fin (n + 3))
    (hb0 : 0 < b) (hbn : b < Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{v} (0 : Fin (n + 3)))
      (c := ULift.up (Fin.last (n + 2))) (ULift.up b) : SSet) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))) :=
  hornCompositionHom σ h0 hn 0 b (Fin.last (n + 2)) (Fin.zero_le b) (Fin.le_last b)
    (Or.inr (ne_of_lt hbn)) (Or.inl (ne_of_gt hb0))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
