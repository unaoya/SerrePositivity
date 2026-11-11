module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FunctorReindex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.IntervalClamp
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.IntervalRecovery

/-!
# 真部分区間の回収の選択独立性と合成則

概要：既知面からの回収の選択独立性と真部分区間での合成の整合性を準備する。
方針：閉区間への射影、ホーンの自然性、豊穣関手の構造則を使う。
規約：追加の充填仮定や局所 Kan 性を用いない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS）。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：閉区間上の豊穣関手は区間外の既知面の選択によらない。
方針：射影した同じ単体上で比較してから区間へ制限する。空の区間は対象が存在しないことを使う。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornIntervalViaFace_independent {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (a b : Fin (n + 3)) (j k : Fin (n + 3))
    (hj : j ≠ i) (hk : k ≠ i) (houtj : j < a ∨ b < j) (houtk : k < a ∨ b < k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalViaFace σ j hj a b houtj = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalViaFace σ k hk a b houtk := by
  by_cases hab : a ≤ b
  · let θ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClampSimplex a b
    let e : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) →o ULift.{v} (Fin (n + 3)) :=
      ⟨Subtype.val, fun _ _ h ↦ h⟩
    have he : θ.toOrderHom.uliftMap.comp e = e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClampSimplex_ulift_inclusion a b
    have hc (f g : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) →o ULift.{v} (Fin (n + 3)))
        (h : f = g) (j : Fin (n + 3)) (hj : j ≠ i)
        (hf : ∀ x, (f x).down ≠ j) (hg : ∀ x, (g x).down ≠ j) :
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ j hj f hf = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ j hj g hg := by
      subst g
      rfl
    have hr (j : Fin (n + 3)) (hj : j ≠ i) (hout : j < a ∨ b < j) :
        (SimplicialThickening.functor e).comp SSet
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ j hj θ.toOrderHom.uliftMap
            (fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClampSimplex_avoids j a b hab hout x.down)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalViaFace σ j hj a b hout := by
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace_comp σ j hj θ.toOrderHom.uliftMap
        (fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClampSimplex_avoids j a b hab hout x.down) e).trans
          (hc _ _ he j hj _ _)
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace_simplex_eq σ θ j k hj hk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClampSimplex_avoids j a b hab houtj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClampSimplex_avoids k a b hab houtk)
    exact (hr j hj houtj).symm.trans
      ((congrArg (fun F ↦ (SimplicialThickening.functor e).comp SSet F) h).trans (hr k hk houtk))
  · refine EnrichedFunctor.ext SSet (fun x ↦ ?_) ?_
    · exact (hab (x.as.property.1.trans x.as.property.2)).elim
    · intro x y
      exact (hab (x.as.property.1.trans x.as.property.2)).elim
/-- 概要：閉区間から周囲の Hom 上への回収も面の選択によらない。
方針：回収豊穣関手の等式を Hom の同型に沿って評価する。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornIntervalHom_independent {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (a b : Fin (n + 3)) (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i)
    (houtj : j < a ∨ b < j) (houtk : k < a ∨ b < k)
    (x y : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom σ j hj a b houtj x y = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom σ k hk a b houtk x y := by
  have hm (F G : EnrichedFunctor SSet
      (SimplicialThickening (Set.Icc (ULift.up.{v} a) (ULift.up.{v} b))) C) (h : F = G) :
      HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalHomMap F x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalHomMap G x y) := by
    subst G
    rfl
  exact eq_of_heq (hm _ _ (hornIntervalViaFace_independent σ a b j k hj hk houtj houtk))

/-- 概要：標準の真部分区間の豊穣関手は任意の区間外の既知面からの構成に等しい。
方針：標準の面の選択を展開し、選択独立性を適用する。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornProperIntervalFunctor_eq_viaFace {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b : Fin (n + 3))
    (hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) (j : Fin (n + 3)) (hj : j ≠ i)
    (hout : j < a ∨ b < j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalFunctor σ h0 hn a b hp = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalViaFace σ j hj a b hout := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalFunctor
  exact hornIntervalViaFace_independent σ a b _ j _ hj _ hout

/-- 概要：標準の真部分区間の Hom は任意の区間外の既知面の区間 Hom に等しい。
方針：豊穣関手の選択独立性を両端で評価する。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornProperIntervalHom_eq_interval {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b : Fin (n + 3))
    (hab : a ≤ b) (hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (j : Fin (n + 3)) (hj : j ≠ i) (hout : j < a ∨ b < j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a b hab hp = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom σ j hj a b hout
      ⟨ULift.up.{v} a, le_rfl, hab⟩ ⟨ULift.up.{v} b, hab, le_rfl⟩ := by
  let x : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) := ⟨ULift.up.{v} a, le_rfl, hab⟩
  let y : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) := ⟨ULift.up.{v} b, hab, le_rfl⟩
  have hm (F G : EnrichedFunctor SSet
      (SimplicialThickening (Set.Icc (ULift.up.{v} a) (ULift.up.{v} b))) C) (h : F = G) :
      HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalHomMap F x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalHomMap G x y) := by
    subst G
    rfl
  exact eq_of_heq (hm _ _ (hornProperIntervalFunctor_eq_viaFace σ h0 hn a b hp j hj hout))

/-- 概要：標準の真部分区間の Hom は任意の区間外の面候補に等しい。
方針：区間からの回収の比較と面候補との比較を合成する。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornProperIntervalHom_eq_viaFace {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b : Fin (n + 3))
    (hab : a ≤ b) (hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (j : Fin (n + 3)) (hj : j ≠ i) (hout : j < a ∨ b < j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a b hab hp = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj a b
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalVertex_ne_outside j a b hout ⟨ULift.up.{v} a, le_rfl, hab⟩)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalVertex_ne_outside j a b hout ⟨ULift.up.{v} b, hab, le_rfl⟩) :=
  (hornProperIntervalHom_eq_interval σ h0 hn a b hab hp j hj hout).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom_eq_viaFace σ j hj a b hout _ _)
/-- 概要：大きい区間上の回収を小さい真部分区間の二対象で評価すると標準回収に等しい。
方針：大きい区間の外の面を両方に共通に選ぶ。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornProperIntervalHom_on_subinterval {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b : Fin (n + 3))
    (j : Fin (n + 3)) (hj : j ≠ i) (hout : j < a ∨ b < j)
    (x y : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b)) (hxy : x ≤ y)
    (hp : x.val.down ≠ 0 ∨ y.val.down ≠ Fin.last (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn x.val.down y.val.down hxy hp =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom σ j hj a b hout x y := by
  have ho : j < x.val.down ∨ y.val.down < j := by
    rcases hout with hja | hbj
    · exact Or.inl (lt_of_lt_of_le hja x.property.1)
    · exact Or.inr (lt_of_le_of_lt y.property.2 hbj)
  rw [hornProperIntervalHom_eq_viaFace σ h0 hn x.val.down y.val.down hxy hp j hj ho,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom_eq_viaFace]

/-- 概要：標準の真部分区間の自己 Hom 回収は単位を保つ。
方針：区間上の豊穣関手の単位則を周囲へ移す。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornProperIntervalHom_id {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a : Fin (n + 3))
    (hp : a ≠ 0 ∨ a ≠ Fin.last (n + 2)) :
    eId SSet (SimplicialThickening.mk (ULift.up.{v} a)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a a le_rfl hp = eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalHomMap_id (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalFunctor σ h0 hn a a hp)
    ⟨ULift.up a, le_rfl, le_rfl⟩

/-- 概要：外側も真部分区間である三対象では標準 Hom 回収は合成を保つ。
方針：同じ外側区間の外の面を選び、三つの Hom を同じ豊穣関手で比較する。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornProperIntervalHom_comp {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b c : Fin (n + 3))
    (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (hpbc : b ≠ 0 ∨ c ≠ Fin.last (n + 2))
    (hpac : a ≠ 0 ∨ c ≠ Fin.last (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{v} a) (ULift.up.{v} b) (ULift.up.{v} c) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a c (hab.trans hbc) hpac =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a b hab hpab ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn b c hbc hpbc) ≫
        SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) := by
  let x : Set.Icc (ULift.up.{v} a) (ULift.up.{v} c) := ⟨ULift.up a, le_rfl, hab.trans hbc⟩
  let y : Set.Icc (ULift.up.{v} a) (ULift.up.{v} c) := ⟨ULift.up b, hab, hbc⟩
  let z : Set.Icc (ULift.up.{v} a) (ULift.up.{v} c) := ⟨ULift.up c, hab.trans hbc, le_rfl⟩
  have go (j : Fin (n + 3)) (hj : j ≠ i) (hout : j < a ∨ c < j) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{v} a) (ULift.up.{v} b) (ULift.up.{v} c) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a c (hab.trans hbc) hpac =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a b hab hpab ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn b c hbc hpbc) ≫
          SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) := by
    have hxz := hornProperIntervalHom_on_subinterval σ h0 hn a c j hj hout x z
      (hab.trans hbc) hpac
    have hxy := hornProperIntervalHom_on_subinterval σ h0 hn a c j hj hout x y hab hpab
    have hyz := hornProperIntervalHom_on_subinterval σ h0 hn a c j hj hout y z hbc hpbc
    rw [hxz, hxy, hyz]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom_comp σ j hj a c hout x y z
  by_cases ha : a = 0
  · exact go (Fin.last (n + 2)) (ne_of_gt hn)
      (Or.inr (lt_of_le_of_ne (Fin.le_last c) (hpac.resolve_left (fun h ↦ h ha))))
  · exact go 0 (ne_of_lt h0) (Or.inl (lt_of_le_of_ne (Fin.zero_le a) (Ne.symm ha)))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
