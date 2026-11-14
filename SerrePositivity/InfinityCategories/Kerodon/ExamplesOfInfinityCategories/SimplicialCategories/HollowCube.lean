module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SubcomplexIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Cube
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HollowCylinder

/-!
# 空洞立方体の所属条件と Kan 複体への延長

概要：coherent nerve の内部ホーン充填に必要な立方体の計算を行う。
方針：冪集合の nerve と一座標の分離を使う。
規約：Mathlib の包含順序を保つ。Kerodon の逆包含では上下が逆になる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV）。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {T : Type u}


/-- 概要：Λ[1,1] の単体はすべての頂点で座標 1 を持つ。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
lemma mem_upperEndpoint_iff {n : SimplexCategoryᵒᵖ} (s : (Δ[1] : SSet.{u}).obj n) :
    s ∈ (Λ[1, (1 : Fin 2)] : (Δ[1] : SSet.{u}).Subcomplex).obj n ↔
      ∀ t, s.down.toOrderHom t = 1 := by
  rcases n with ⟨⟨n⟩⟩
  rw [SSet.mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨j, hj, h⟩ t
    fin_cases j
    · have ht : s.down.toOrderHom t ≠ 0 := fun ht ↦ h ⟨t, ht⟩
      exact Fin.eq_last_of_not_lt (by simpa using ht)
    · exact False.elim (hj rfl)
  · intro h
    refine ⟨0, by decide, ?_⟩
    rintro ⟨t, ht⟩
    change s.down.toOrderHom t = 0 at ht
    exact (by decide : (1 : Fin 2) ≠ 0) ((h t).symm.trans ht)


/-- 概要：いずれかの座標が常に 0 または常に 1 となる単体を境界とする。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
def cubeBoundary (T : Type u) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).Subcomplex where
  obj _ := {F | ∃ x, (∀ t, x ∈ F.obj t) ∨ ∀ t, x ∉ F.obj t}
  map f F h := by
    obtain ⟨x, h | h⟩ := h
    · exact ⟨x, Or.inl (fun t ↦ h (f.unop.toOrderHom t))⟩
    · exact ⟨x, Or.inr (fun t ↦ h (f.unop.toOrderHom t))⟩


/-- 概要：指定座標の下面だけを欠く立方体境界を定義する。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
noncomputable def hollowCube (i : T) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).Subcomplex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCylinder
    (cubeBoundary {x : T // x ≠ i})).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplit i)

set_option backward.isDefEq.respectTransparency false in

/-- 概要：空洞立方体への所属を一定の 1 座標または指定外の一定の 0 座標で特徴付ける。
方針：空洞柱の二つの部分と座標の指示関数を比較する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
lemma mem_hollowCube_iff (i : T) {n : SimplexCategoryᵒᵖ} (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).obj n) :
    F ∈ (hollowCube i).obj n ↔
      (∃ x, ∀ t, x ∈ F.obj t) ∨ ∃ x, x ≠ i ∧ ∀ t, x ∉ F.obj t := by
  classical
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplit i).app n F ∈
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCylinder
      (cubeBoundary {x : T // x ≠ i})).obj n ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCylinder,
    SSet.Subcomplex.mem_unionProd_iff]
  rw [mem_upperEndpoint_iff]
  change (∀ t, ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeCoordinateMap i).app n F).down.toOrderHom t = 1) ∨
    (∃ x : {x : T // x ≠ i}, (∀ t, x.1 ∈ F.obj t) ∨ ∀ t, x.1 ∉ F.obj t) ↔ _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeCoordinateMap_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeCoordinate, OrderHom.coe_mk,
    Fin.zero_ne_one, ite_eq_left_iff,
    imp_false, not_not]
  constructor
  · rintro (h | ⟨x, h | h⟩)
    · exact Or.inl ⟨i, h⟩
    · exact Or.inl ⟨x.1, h⟩
    · exact Or.inr ⟨x.1, x.2, h⟩
  · rintro (⟨x, h⟩ | ⟨x, hx, h⟩)
    · by_cases hx : x = i
      · exact Or.inl (hx ▸ h)
      · exact Or.inr ⟨⟨x, hx⟩, Or.inl h⟩
    · exact Or.inr ⟨⟨x, hx⟩, Or.inr h⟩


/-- 概要：空洞立方体を残りの境界から作る空洞柱へ同型で移す。
方針：座標分離の同型を部分単体集合へ制限する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
noncomputable def hollowCubeIso (i : T) :
    (hollowCube i : SSet.{u}) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCylinder
        (cubeBoundary {x : T // x ≠ i}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.subcomplexPreimageIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplitIso i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCylinder (cubeBoundary {x : T // x ≠ i}))

/-- 概要：空洞立方体の包含は anodyne である。
方針：空洞柱への同型と pushout-product の anodyne 性を用いる。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
lemma hollowCube_anodyne (i : T) : SSet.anodyneExtensions (hollowCube i).ι := by
  let e : Arrow.mk (hollowCube i).ι ≅
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCylinder
        (cubeBoundary {x : T // x ≠ i})).ι :=
    Arrow.isoMk (hollowCubeIso i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplitIso i) (by rfl)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff e).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCylinder_anodyne _)


/-- 概要：空洞立方体への所属は増大列の最初と最後の部分集合だけで判定できる。
方針：増大列の包含を最初と最後の頂点へ適用する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
lemma mem_hollowCube_endpoints_iff (i : T) {n : SimplexCategoryᵒᵖ}
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).obj n) :
    F ∈ (hollowCube i).obj n ↔
      (∃ x, x ∈ F.obj 0) ∨ ∃ x, x ≠ i ∧ x ∉ F.obj (Fin.last n.unop.len) := by
  rw [mem_hollowCube_iff]
  constructor
  · rintro (⟨x, hx⟩ | ⟨x, hxi, hx⟩)
    · exact Or.inl ⟨x, hx 0⟩
    · exact Or.inr ⟨x, hxi, hx _⟩
  · rintro (⟨x, hx⟩ | ⟨x, hxi, hx⟩)
    · exact Or.inl ⟨x, fun t ↦ (F.map (homOfLE (Fin.zero_le t))).le hx⟩
    · exact Or.inr ⟨x, hxi, fun t ht ↦ hx ((F.map (homOfLE (Fin.le_last t))).le ht)⟩


/-- 概要：Kan 複体への空洞立方体上の写像は全立方体へ延長する。
方針：anodyne 包含に対する終対象への Kan fibration の持ち上げを使う。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
lemma hollowCube_extension (i : T) {X : SSet.{u}} [SSet.KanComplex X]
    (f : (hollowCube i : SSet) ⟶ X) :
    ∃ g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ X, (hollowCube i).ι ≫ g = f := by
  have : HasLiftingProperty (hollowCube i).ι (CategoryTheory.Limits.terminal.from X) :=
    hollowCube_anodyne i _ (by rwa [← HomotopicalAlgebra.fibration_iff])
  let sq : CommSq f (hollowCube i).ι (CategoryTheory.Limits.terminal.from X)
      (CategoryTheory.Limits.terminal.from _) :=
    ⟨CategoryTheory.Limits.terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.1.5.1" (partial := component) "仮定：座標集合 T（Lean は任意の集合を取り、HA の場合は Fin n を取る）。結論：包含順序の冪集合の神経、座標を一つ分離した ∆¹ との積同型、いずれかの座標が一定となる境界を与える（立方体と境界の定義に一致）。全 n 座標を同時に並べる積との同型は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeBoundary
