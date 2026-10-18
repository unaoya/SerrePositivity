module

public import SerrePositivity.InfinityCategories.Coherent.ZeroFaceCompatibility
public import SerrePositivity.InfinityCategories.Coherent.MixedCompatibility

/-!
# 面の重なりにおける任意の端点

概要：零座標面の整合性の端点を面の像という表示から解放する。
方針：除外点を避ける頂点を succAbove の像で表し、既存の整合性へ帰着する。
規約：元の端点の共通対象間の厳密な等式を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.9 の全区間への貼合せ。
-/

@[expose] public section

universe v u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Coherent

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：任意の共通端点に対し二つの零座標面上の候補は交わりで一致する。
方針：除外点と端点を二重の succAbove で表示して既存の整合性を適用する。
規約：二つの除外点の一致も許す。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9 の零座標面の貼合せ。 -/
lemma hornHomViaFace_zero_overlap_general {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (a b : Fin (n + 3))
    (haj : a ≠ j) (hbj : b ≠ j) (hak : a ≠ k) (hbk : b ≠ k) :
    (pathAvoids (a := ULift.up.{v} a) (b := ULift.up b) (ULift.up j) ⊓
      pathAvoids (ULift.up k)).ι ≫ hornHomViaFace σ j hj a b haj hbj =
    (pathAvoids (a := ULift.up.{v} a) (b := ULift.up b) (ULift.up j) ⊓
      pathAvoids (ULift.up k)).ι ≫ hornHomViaFace σ k hk a b hak hbk := by
  by_cases hkj : k = j
  · subst k
    rfl
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hkj
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq haj
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hbj
  have hak' : a ≠ k := fun h ↦ hak (congrArg j.succAbove h)
  have hbk' : b ≠ k := fun h ↦ hbk (congrArg j.succAbove h)
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hak'
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hbk'
  exact hornHomViaFace_zero_overlap σ j k hj hk a b

/-- 概要：任意の端点と切断点で零座標面候補と合成面の回収は交わり上で一致する。
方針：三点を一つの面の像として表し、順序を反映して既存の整合性を適用する。
規約：切断点は零座標面の除外点を避ける。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9 の全区間での混合した重なり。 -/
lemma hornCompositionHom_zero_overlap_general {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (j : Fin (n + 3)) (hj : j ≠ i)
    (a b c : Fin (n + 3)) (haj : a ≠ j) (hbj : b ≠ j) (hcj : c ≠ j)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (hpbc : b ≠ 0 ∨ c ≠ Fin.last (n + 2)) :
    (pathAvoids (a := ULift.up.{v} a) (b := ULift.up c) (ULift.up j) ⊓
      pathThrough (ULift.up b)).ι ≫ hornHomViaFace σ j hj a c haj hcj =
    SSet.Subcomplex.homOfLE
      (show pathAvoids (a := ULift.up.{v} a) (b := ULift.up c) (ULift.up j) ⊓
        pathThrough (ULift.up b) ≤ pathThrough (ULift.up b) from inf_le_right) ≫
      hornCompositionHom σ h0 hn a b c hab hbc hpab hpbc := by
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq haj
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hbj
  obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hcj
  exact hornCompositionHom_zero_overlap σ h0 hn j hj a b c
    ((Fin.strictMono_succAbove j).le_iff_le.mp hab)
    ((Fin.strictMono_succAbove j).le_iff_le.mp hbc) hpab hpbc

end SerrePositivity.InfinityCategories.Coherent
