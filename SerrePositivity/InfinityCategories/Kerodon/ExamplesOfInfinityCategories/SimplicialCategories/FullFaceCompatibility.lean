module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FaceCompatibilityEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionCompatibility

/-!
# 全区間での零座標面と合成面の整合性

概要：全区間の端点を固定し、空洞部分の面上の写像と全ての重なりの一致を得る。
方針：端点に依存しない整合性を特殊化し、同じ座標の混合した交わりは空として扱う。
規約：端点 Hom の全体への延長を仮定しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の空洞部分への貼合せ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：全区間の既知の内部零座標面上に Hom 写像を定義する。
方針：部分単体集合の包含の後にその面からの Hom 候補を合成する。
規約：除外点 j は両端点とホーンの欠ける面 i を避ける。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の既知データ。 -/
def hornInnerZeroHom {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} (0 : Fin (n + 3)))
      (b := ULift.up (Fin.last (n + 2))) (ULift.up j) : SSet) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj 0 (Fin.last (n + 2))
    (ne_of_lt hj0) (ne_of_gt hjn)

/-- 概要：全区間の二つの既知零座標面の写像は交わりで一致する。
方針：包含の合成を消去し、任意の端点での零座標面の一致を適用する。
規約：二つの座標は同じでもよい。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の零座標面の貼合せ。 -/
lemma hornInnerZeroHom_overlap {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i)
    (hj0 : 0 < j) (hjn : j < Fin.last (n + 2))
    (hk0 : 0 < k) (hkn : k < Fin.last (n + 2)) :
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} (0 : Fin (n + 3)))
        (b := ULift.up (Fin.last (n + 2))) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up k) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j) from inf_le_left) ≫ hornInnerZeroHom σ j hj hj0 hjn =
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} (0 : Fin (n + 3)))
        (b := ULift.up (Fin.last (n + 2))) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up k) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up k) from inf_le_right) ≫ hornInnerZeroHom σ k hk hk0 hkn := by
  simp only [hornInnerZeroHom, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_zero_overlap_general σ j k hj hk 0 (Fin.last (n + 2))
    (ne_of_lt hj0) (ne_of_gt hjn) (ne_of_lt hk0) (ne_of_gt hkn)

/-- 概要：全区間の零座標面と任意の内部合成面の写像は交わりで一致する。
方針：座標が違えば一般の整合性を使い、同じなら交わりの空性を使う。
規約：切断点はホーンの欠ける面の頂点でもよい。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9（Tag 00LS） の全ての混合した重なりの貼合せ。 -/
lemma hornInnerZeroHom_composition_overlap {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (j b : Fin (n + 3)) (hj : j ≠ i)
    (hj0 : 0 < j) (hjn : j < Fin.last (n + 2))
    (hb0 : 0 < b) (hbn : b < Fin.last (n + 2)) :
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} (0 : Fin (n + 3)))
        (b := ULift.up (Fin.last (n + 2))) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j) from inf_le_left) ≫ hornInnerZeroHom σ j hj hj0 hjn =
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} (0 : Fin (n + 3)))
        (b := ULift.up (Fin.last (n + 2))) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) from inf_le_right) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerCompositionHom σ h0 hn b hb0 hbn := by
  by_cases hbj : b = j
  · subst b
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathMixed_self_hom_ext _ _ _ _ _
  simp only [hornInnerZeroHom, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCompositionHom_zero_overlap_general σ h0 hn j hj 0 b (Fin.last (n + 2))
    (ne_of_lt hj0) hbj (ne_of_gt hjn) (Fin.zero_le b) (Fin.le_last b)
    (Or.inr (ne_of_lt hbn)) (Or.inl (ne_of_gt hb0))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
