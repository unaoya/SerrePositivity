module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.IntervalHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.IntervalFunctor

/-!
# 真部分区間から周囲の Hom 上への回収

概要：区間上の豊穣関手から native な Path Hom 上の単位・合成を保つ写像を回収する。
方針：区間の Hom 同型に沿って写像を移し、同型と豊穣関手の構造則を用いる。
規約：内部ホーンの真部分区間には追加の充填仮定や局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の構成。
異なる区間や既知面の選択との比較は IntervalChoice と FaceIntervalRestriction に置く。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {J : Type v} [LinearOrder J] {l r : J}
/-- 概要：閉区間上の豊穣関手の Hom 写像を周囲の Path Hom の上で読む。
方針：閉区間の Hom 同型の逆と元の Hom 写像を合成する。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
def intervalHomMap
    (F : EnrichedFunctor SSet (SimplicialThickening (Set.Icc l r)) C)
    (x y : Set.Icc l r) :
    nerve (SimplicialThickening.Path x.val y.val) ⟶
      SimplicialCategory.sHom (F.obj (.mk x)) (F.obj (.mk y)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso x y).inv ≫ F.map (.mk x) (.mk y)
/-- 概要：周囲へ移した Hom 写像を区間内へ制限すると元の写像に等しい。
方針：Hom 同型と逆同型を消去する。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
lemma intervalHomMap_on_interval
    (F : EnrichedFunctor SSet (SimplicialThickening (Set.Icc l r)) C)
    (x y : Set.Icc l r) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso x y).hom ≫ intervalHomMap F x y = F.map (.mk x) (.mk y) := by
  simp [intervalHomMap]
/-- 概要：周囲へ移した Hom 写像は native な合成を保つ。
方針：二つの Hom 同型の直積で前合成し、区間内の豊穣関手の合成則に戻す。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
lemma intervalHomMap_comp
    (F : EnrichedFunctor SSet (SimplicialThickening (Set.Icc l r)) C)
    (x y z : Set.Icc l r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap x.val y.val z.val ≫ intervalHomMap F x z =
      (intervalHomMap F x y ⊗ₘ intervalHomMap F y z) ≫
        SimplicialCategory.sHomComp (F.obj (.mk x)) (F.obj (.mk y)) (F.obj (.mk z)) := by
  apply (cancel_epi ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso x y).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso y z).hom)).mp
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso_comp]
  simp only [Category.assoc, intervalHomMap_on_interval]
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    intervalHomMap_on_interval, intervalHomMap_on_interval]
  exact F.map_comp (.mk x) (.mk y) (.mk z)
/-- 概要：周囲へ移した Hom 写像は native な単位を保つ。
方針：包含の単位との整合性と元の豊穣関手の単位則を使う。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
lemma intervalHomMap_id
    (F : EnrichedFunctor SSet (SimplicialThickening (Set.Icc l r)) C)
    (x : Set.Icc l r) :
    eId SSet (SimplicialThickening.mk x.val) ≫ intervalHomMap F x x =
      eId SSet (F.obj (.mk x)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso_id x, Category.assoc, intervalHomMap_on_interval]
  exact F.map_id (.mk x)
/-- 概要：区間外の既知面から周囲の native な Hom 上の写像を回収する。
方針：閉区間上の豊穣関手の Hom を周囲へ移す。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
def hornIntervalHom {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 3)) (hout : j < a ∨ b < j)
    (x y : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b)) :
    nerve (SimplicialThickening.Path x.val y.val) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ x.val.down) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ y.val.down) :=
  intervalHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalViaFace σ j hj a b hout) x y

/-- 概要：内部ホーンの真部分区間の両端の間の native な Hom 写像を回収する。
方針：区間外の端の面からの豊穣関手を両端で評価し、Hom の同型で移す。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
def hornProperIntervalHom {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b : Fin (n + 3))
    (hab : a ≤ b) (hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    nerve (SimplicialThickening.Path (ULift.up.{v} a) (ULift.up.{v} b)) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) :=
  intervalHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalFunctor σ h0 hn a b hp)
    ⟨ULift.up a, le_rfl, hab⟩ ⟨ULift.up b, hab, le_rfl⟩

/-- 概要：真部分区間の Hom 回収を区間内へ制限すると区間の豊穣関手の Hom に等しい。
方針：区間の Hom 同型を消去する。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
lemma hornProperIntervalHom_on_interval {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b : Fin (n + 3))
    (hab : a ≤ b) (hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso (⟨ULift.up a, le_rfl, hab⟩ : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b))
      ⟨ULift.up b, hab, le_rfl⟩).hom ≫ hornProperIntervalHom σ h0 hn a b hab hp =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalFunctor σ h0 hn a b hp).map
          ⟨⟨ULift.up a, le_rfl, hab⟩⟩ ⟨⟨ULift.up b, hab, le_rfl⟩⟩ :=
  intervalHomMap_on_interval _ _ _
/-- 概要：閉区間内の頂点は区間外の頂点と異なる。
方針：区間の両端の不等式と区間外の不等式を組み合わせる。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
lemma intervalVertex_ne_outside {n : ℕ} (j a b : Fin (n + 3))
    (hout : j < a ∨ b < j) (x : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b)) :
    x.val.down ≠ j := by
  intro h
  have hx := x.property
  change a ≤ x.val.down ∧ x.val.down ≤ b at hx
  rcases hout with hja | hbj
  · exact (ne_of_gt (lt_of_lt_of_le hja hx.1)) h
  · exact (ne_of_lt (lt_of_le_of_lt hx.2 hbj)) h
set_option backward.isDefEq.respectTransparency false in
/-- 概要：指定した面からの区間 Hom 回収は既存の面候補に厳密に等しい。
方針：包含の Hom 写像と Hom 同型の逆を消去し、対象の移送を比較する。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
lemma hornIntervalHom_eq_viaFace {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 3)) (hout : j < a ∨ b < j)
    (x y : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b)) :
    hornIntervalHom σ j hj a b hout x y = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj x.val.down y.val.down
      (intervalVertex_ne_outside j a b hout x) (intervalVertex_ne_outside j a b hout y) := by
  dsimp only [hornIntervalHom, intervalHomMap, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalViaFace]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace_map, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso_hom,
    Iso.inv_hom_id, Category.id_comp]
  rfl
/-- 概要：指定した同じ面から区間内で回収した Hom 写像は native な合成を保つ。
方針：周囲へ移した豊穣関手の Hom の合成則を適用する。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
lemma hornIntervalHom_comp {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 3)) (hout : j < a ∨ b < j)
    (x y z : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap x.val y.val z.val ≫ hornIntervalHom σ j hj a b hout x z =
      (hornIntervalHom σ j hj a b hout x y ⊗ₘ hornIntervalHom σ j hj a b hout y z) ≫
        SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ x.val.down)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ y.val.down) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ z.val.down) :=
  intervalHomMap_comp _ _ _ _
/-- 概要：指定した同じ面から区間内で回収した Hom 写像は native な単位を保つ。
方針：周囲へ移した豊穣関手の Hom の単位則を適用する。
規約：元の Mathlib Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面と整合性。 -/
lemma hornIntervalHom_id {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 3)) (hout : j < a ∨ b < j)
    (x : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b)) :
    eId SSet (SimplicialThickening.mk x.val) ≫ hornIntervalHom σ j hj a b hout x x =
      eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ x.val.down) := intervalHomMap_id _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
