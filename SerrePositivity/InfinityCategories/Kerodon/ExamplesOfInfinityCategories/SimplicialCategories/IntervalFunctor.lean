module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HornFunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FaceHom

/-!
# 既知面からの真部分区間上の豊穣関手

概要：内部ホーンの真部分閉区間上に単位と合成を保つ豊穣関手を回収する。
方針：区間外の既知面に沿って引き戻し、対象を共通の頂点対象へ移す。
規約：閉区間は ULift した有限順序の部分型で表す。全区間は除く。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の構成。
区間の包含による Hom の同定は IntervalHom、面の選択の比較は IntervalChoice に置く。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {J : Type v} [LinearOrder J]
/-- 概要：既知面を避ける任意の線形順序の対象族上に実際の豊穣関手を構成する。
方針：対象族と面の退化に沿って既知面を引き戻し、共通の頂点対象へ移す。
規約：Mathlib の native な thickening を使い、局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面への Hom の回収。 -/
def hornFunctorViaFace {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (f : J →o ULift.{v} (Fin (n + 3)))
    (hf : ∀ x, (f x).down ≠ j) : EnrichedFunctor SSet (SimplicialThickening J) C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor
    ((SimplicialThickening.functor f).comp SSet
      ((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction j).toOrderHom.uliftMap).comp SSet
        (σ.app _ (SSet.horn.face i j hj))))
    (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (f p.as).down) (fun p ↦ by
      change (σ.app _ (SSet.horn.face i j hj)).obj
        ⟨⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction j).toOrderHom (f p.as).down⟩⟩ = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.horn_face_obj, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction_point j (f p.as).down (hf p.as)])
set_option backward.isDefEq.respectTransparency false in
/-- 概要：既知面から作った豊穣関手の Hom は対象族の Path 写像と面候補の合成に等しい。
方針：対象の移送を消去し、豊穣関手の合成の定義を比較する。
規約：Mathlib の native な thickening を使い、局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面への Hom の回収。 -/
lemma hornFunctorViaFace_map {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (f : J →o ULift.{v} (Fin (n + 3)))
    (hf : ∀ x, (f x).down ≠ j) (x y : SimplicialThickening J) :
    (hornFunctorViaFace σ j hj f hf).map x y =
      (SimplicialThickening.functor f).map x y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj (f x.as).down (f y.as).down (hf x.as) (hf y.as) := by
  apply eq_of_heq
  simp only [hornFunctorViaFace, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell,
    ← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  rfl
/-- 概要：既知面からの豊穣関手の対象は共通の頂点対象である。
方針：対象の置き換えの定義を使う。
規約：Mathlib の native な thickening を使い、局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面への Hom の回収。 -/
lemma hornFunctorViaFace_obj {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (f : J →o ULift.{v} (Fin (n + 3)))
    (hf : ∀ x, (f x).down ≠ j) (x : SimplicialThickening J) :
    (hornFunctorViaFace σ j hj f hf).obj x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (f x.as).down := rfl

/-- 概要：区間外の既知面から閉区間上の実際の豊穣関手を構成する。
方針：閉区間の包含を用い、その像が除外頂点を避けることを順序の不等式で確認する。
規約：Mathlib の native な thickening を使い、局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面への Hom の回収。 -/
def hornIntervalViaFace {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 3)) (hout : j < a ∨ b < j) :
    EnrichedFunctor SSet
      (SimplicialThickening (Set.Icc (ULift.up.{v} a) (ULift.up.{v} b))) C :=
  hornFunctorViaFace σ j hj ⟨Subtype.val, fun _ _ h ↦ h⟩ (fun x h ↦ by
    have hx := x.property
    change a ≤ x.val.down ∧ x.val.down ≤ b at hx
    change x.val.down = j at h
    rcases hout with hja | hbj
    · exact (ne_of_gt (lt_of_lt_of_le hja hx.1)) h
    · exact (ne_of_lt (lt_of_le_of_lt hx.2 hbj)) h)

/-- 概要：閉区間上の豊穣関手の対象は元のホーンの同じ頂点の対象である。
方針：区間の包含と対象の置き換えの定義を使う。
規約：Mathlib の native な thickening を使い、局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面への Hom の回収。 -/
lemma hornIntervalViaFace_obj {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 3)) (hout : j < a ∨ b < j)
    (x : SimplicialThickening (Set.Icc (ULift.up.{v} a) (ULift.up.{v} b))) :
    (hornIntervalViaFace σ j hj a b hout).obj x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ x.as.val.down := rfl

/-- 概要：内部ホーンの任意の真部分閉区間上に豊穣関手を構成する。
方針：左端点が 0 でなければ面 0、そうでなければ最後の面を選ぶ。
規約：Mathlib の native な thickening を使い、局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面への Hom の回収。 -/
def hornProperIntervalFunctor {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b : Fin (n + 3))
    (hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    EnrichedFunctor SSet
      (SimplicialThickening (Set.Icc (ULift.up.{v} a) (ULift.up.{v} b))) C := by
  let j : Fin (n + 3) := if a = 0 then Fin.last (n + 2) else 0
  have hj : j ≠ i := by
    by_cases ha : a = 0
    · simpa only [j, ite_eq_left ha] using ne_of_gt hn
    · simpa only [j, ite_eq_right ha] using ne_of_lt h0
  have hout : j < a ∨ b < j := by
    by_cases ha : a = 0
    · simp only [j, ite_eq_left ha]
      exact Or.inr (lt_of_le_of_ne (Fin.le_last b) (hp.resolve_left (fun h ↦ h ha)))
    · simp only [j, ite_eq_right ha]
      exact Or.inl (lt_of_le_of_ne (Fin.zero_le a) (Ne.symm ha))
  exact hornIntervalViaFace σ j hj a b hout

/-- 概要：真部分区間から回収した豊穣関手は共通の頂点対象を持つ。
方針：共通対象への置き換えの定義を使う。
規約：Mathlib の native な thickening を使い、局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面への Hom の回収。 -/
lemma hornProperIntervalFunctor_obj {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b : Fin (n + 3))
    (hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (x : SimplicialThickening (Set.Icc (ULift.up.{v} a) (ULift.up.{v} b))) :
    (hornProperIntervalFunctor σ h0 hn a b hp).obj x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ x.as.val.down := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
