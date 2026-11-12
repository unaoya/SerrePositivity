module

public import Mathlib.AlgebraicTopology.SimplicialNerve
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 冪集合の nerve と立方体の座標分離

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


/-- 概要：任意の座標集合 T の立方体をその冪集合の nerve で定義する。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
@[kerodon 00LK]
abbrev cube (T : Type u) : SSet.{u} := nerve (Set T)

/-- 概要：部分集合の一つの所属座標を 0 または 1 として取り出す。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
noncomputable def cubeCoordinate (i : T) : Set T →o Fin 2 := by
  classical
  exact ⟨fun S ↦ if i ∈ S then 1 else 0, by
    intro S U h
    by_cases hi : i ∈ S
    · simp [hi, h hi]
    · simp [hi]⟩

/-- 概要：所属座標を ULift した二点の順序圏への関手にする。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
noncomputable def cubeCoordinateFunctor (i : T) : Set T ⥤ ULift.{u} (Fin 2) :=
  (ULift.orderIso.symm.monotone.comp (cubeCoordinate i).monotone).functor

/-- 概要：立方体の一座標を標準 1 単体へ写す。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
noncomputable def cubeCoordinateMap (i : T) : cube T ⟶ Δ[1] :=
  nerveMap (cubeCoordinateFunctor i) ≫ (SSet.stdSimplex.isoNerve 1).inv

/-- 概要：指定座標以外の部分集合を取り出す関手を作る。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
def cubeRestFunctor (i : T) : Set T ⥤ Set {x : T // x ≠ i} :=
  (show Monotone (fun S : Set T ↦ {x : {x : T // x ≠ i} | x.1 ∈ S}) from
    fun _ _ h _ hx ↦ h hx).functor

/-- 概要：一座標への写像は各頂点で所属の指示関数になる。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
lemma cubeCoordinateMap_apply (i : T) {n : SimplexCategoryᵒᵖ} (F : (cube T).obj n)
    (t : Fin (n.unop.len + 1)) :
    ((cubeCoordinateMap i).app n F).down.toOrderHom t = (cubeCoordinate i) (F.obj t) := by
  rcases n with ⟨⟨n⟩⟩
  change ((SSet.stdSimplex.isoNerve 1).inv.app _
    ((nerveMap (cubeCoordinateFunctor i)).app _ F)) t = _
  rw [SSet.stdSimplex.isoNerve_inv_app_apply]
  rfl

/-- 概要：残りの座標の増大列と 1 単体から全座標の増大列を復元する。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
noncomputable def cubeCombineSimplex (i : T) {n : SimplexCategoryᵒᵖ}
    (z : (cube {x : T // x ≠ i} ⊗ (Δ[1] : SSet.{u})).obj n) :
    (cube T).obj n := by
  classical
  exact (show Monotone (fun t : Fin (n.unop.len + 1) ↦
    {x : T | x = i ∧ z.2.down.toOrderHom t = 1 ∨
      ∃ h : x ≠ i, (⟨x, h⟩ : {x : T // x ≠ i}) ∈ z.1.obj t}) from by
      intro t r htr x hx
      rcases hx with ⟨rfl, hi⟩ | ⟨hx, ht⟩
      · exact Or.inl ⟨rfl, le_antisymm (Fin.le_last _) (hi ▸ z.2.down.toOrderHom.monotone htr)⟩
      · exact Or.inr ⟨hx, (z.1.map (homOfLE htr)).le ht⟩).functor

/-- 概要：立方体から残りの座標と指定座標の直積への写像を作る。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
noncomputable def cubeSplit (i : T) : cube T ⟶ cube {x : T // x ≠ i} ⊗ (Δ[1] : SSet.{u}) where
  app n := ↾fun F ↦ ⟨(nerveMap (cubeRestFunctor i)).app n F, (cubeCoordinateMap i).app n F⟩

/-- 概要：残りの座標と指定座標の直積から立方体への写像を作る。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
noncomputable def cubeUnsplit (i : T) : cube {x : T // x ≠ i} ⊗ (Δ[1] : SSet.{u}) ⟶ cube T where
  app _ := ↾cubeCombineSimplex i
  naturality := by
    intro n m f
    apply ConcreteCategory.hom_ext
    intro z
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- 概要：座標分離後の復元は恒等写像である。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
lemma cubeSplit_comp_cubeUnsplit (i : T) : cubeSplit i ≫ cubeUnsplit i = 𝟙 (cube T) := by
  classical
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  ext x
  change (x = i ∧ (if i ∈ F.obj t then (1 : Fin 2) else 0) = 1 ∨
    ∃ h : x ≠ i, x ∈ F.obj t) ↔ x ∈ F.obj t
  by_cases hx : x = i
  · subst x; simp
  · simp [hx]

/-- 概要：座標復元後の分離は直積の恒等写像である。
方針：部分集合の所属と包含を各頂点で計算する。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
lemma cubeUnsplit_comp_cubeSplit (i : T) :
    cubeUnsplit i ≫ cubeSplit i = 𝟙 (cube {x : T // x ≠ i} ⊗ (Δ[1] : SSet.{u})) := by
  classical
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  rcases n with ⟨⟨n⟩⟩
  apply Prod.ext
  · refine CategoryTheory.Functor.ext (fun t ↦ ?_)
    ext x
    change (x.1 = i ∧ z.2.down.toOrderHom t = 1 ∨ ∃ h : x.1 ≠ i,
      (⟨x.1, h⟩ : {x : T // x ≠ i}) ∈ z.1.obj t) ↔ x ∈ z.1.obj t
    simp [x.2]
  · apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext t
    change ((cubeCoordinateMap i).app _
      (cubeCombineSimplex i z)).down.toOrderHom t = z.2.down.toOrderHom t
    rw [cubeCoordinateMap_apply]
    dsimp only [cubeCoordinate, cubeCombineSimplex, OrderHom.coe_mk, Monotone.functor_obj]
    generalize ht : z.2.down.toOrderHom t = k
    fin_cases k <;> simp

/-- 概要：立方体を残りの座標の立方体と Δ[1] の直積へ分解する。
方針：所属座標の抽出と復元が単体的に互いに逆であることを用いる。
規約：包含順序の座標を使い、点の所属を 1 とする。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）–2.4.5.12（Tag 00LV） の内部ホーンの立方体への帰着。 -/
@[kerodon 00LK]
noncomputable def cubeSplitIso (i : T) : cube T ≅ cube {x : T // x ≠ i} ⊗ (Δ[1] : SSet.{u}) where
  hom := cubeSplit i
  inv := cubeUnsplit i
  hom_inv_id := cubeSplit_comp_cubeUnsplit i
  inv_hom_id := cubeUnsplit_comp_cubeSplit i


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
