module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HornData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFace

/-!
# 共通対象上のホーンの豊穣関手

概要：共通の頂点対象へ移した Hom 写像が単位と合成を保つことを証明する。
方針：豊穣関手の対象を点ごとの等式で置き換える一般構成を使う。
規約：追加の整合性仮定や局所 Kan 性を用いない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の貼合せ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u w

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {D : Type w} [EnrichedCategory SSet.{v} D]
/-- 概要：対象を点ごとの等しい対象へ置き換えた豊穣関手を構成する。
方針：対象関数の等式で移送を消去し、元の単位と合成の法則を用いる。
規約：Mathlib の SSet 豊穣関手と ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
def reobjectFunctor (F : EnrichedFunctor SSet D C) (g : D → C)
    (h : ∀ x, F.obj x = g x) : EnrichedFunctor SSet D C where
  obj := g
  map x y := F.map x y ≫ eqToHom (by rw [h x, h y])
  map_id x := by
    have ho : F.obj = g := funext h
    subst g
    simp
  map_comp x y z := by
    have ho : F.obj = g := funext h
    subst g
    simp

/-- 概要：ホーンの単体上の豊穣関手を共通の頂点対象で表す。
方針：元の豊穣関手の対象を hornObj へ点ごとの等式で移す。
規約：Mathlib の SSet 豊穣関手と ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
def hornFunctorOnCell {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    {m : ℕ} (x : (Λ[n + 2, i] : SSet.{max u v}) _⦋m⦌) :
    EnrichedFunctor SSet (SimplicialThickening (ULift.{v} (Fin (m + 1)))) C :=
  reobjectFunctor (σ.app _ x) (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (x.1.down.toOrderHom p.as.down))
    (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.horn_simplex_obj σ x p.as.down)
/-- 概要：対象を共通化した豊穣関手の Hom 写像は既存の回収写像に等しい。
方針：両方の型の移送の定義と証明の一意性を使う。
規約：Mathlib の SSet 豊穣関手と ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornFunctorOnCell_map {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    {m : ℕ} (x : (Λ[n + 2, i] : SSet.{max u v}) _⦋m⦌) (a b : Fin (m + 1)) :
    (hornFunctorOnCell σ x).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ x a b := rfl
/-- 概要：ホーンの各単体から回収した Hom 写像は native な Path の合成を保つ。
方針：共通対象上の豊穣関手の合成の法則を適用する。
規約：Mathlib の SSet 豊穣関手と ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornHomOnCell_comp {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    {m : ℕ} (x : (Λ[n + 2, i] : SSet.{max u v}) _⦋m⦌) (a b c : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{v} a) (ULift.up.{v} b) (ULift.up.{v} c) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ x a c =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ x a b ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ x b c) ≫
      SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (x.1.down.toOrderHom a))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (x.1.down.toOrderHom b)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (x.1.down.toOrderHom c)) :=
  (hornFunctorOnCell σ x).map_comp ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ⟨⟨c⟩⟩
/-- 概要：対象を置き換えた Hom 写像は元の写像と異種等号で一致する。
方針：等式による合成移送を消去する。
規約：Mathlib の SSet 豊穣関手と ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma reobjectFunctor_map_heq (F : EnrichedFunctor SSet D C) (g : D → C)
    (h : ∀ x, F.obj x = g x) (x y : D) :
    HEq ((reobjectFunctor F g h).map x y) (F.map x y) := comp_eqToHom_heq _ _
/-- 概要：ホーンの各単体から回収した Hom 写像は native な Path の単位を保つ。
方針：共通対象上の豊穣関手の単位の法則を適用する。
規約：Mathlib の SSet 豊穣関手と ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の合成面の整合性。 -/
lemma hornHomOnCell_id {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    {m : ℕ} (x : (Λ[n + 2, i] : SSet.{max u v}) _⦋m⦌) (a : Fin (m + 1)) :
    eId SSet (SimplicialThickening.mk (ULift.up.{v} a)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ x a a =
      eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (x.1.down.toOrderHom a)) :=
  (hornFunctorOnCell σ x).map_id ⟨⟨a⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
