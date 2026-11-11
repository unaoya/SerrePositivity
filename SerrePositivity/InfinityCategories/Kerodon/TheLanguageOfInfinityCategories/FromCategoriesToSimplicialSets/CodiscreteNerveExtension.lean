module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
# 点を持つcodiscrete圏のnerveは全hornを充填できるKan複体である

## 概要
点を持つcodiscrete圏のnerveは全hornを充填できるKan複体である。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0363][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0363
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17

対応節は Kerodon 1.3（Tag 002L）。
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Vertex functions extend uniquely to maps into a codiscrete nerve

For an inhabited label type this nerve is injective against all simplicial
monomorphisms, and in particular Kan, in any value universe without a model.
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets
variable {I : Type u} {X : SSet.{u}}

abbrev zero : SimplexCategoryᵒᵖ := op (SimplexCategory.mk 0)

abbrev vertex (n : SimplexCategoryᵒᵖ) (j : Fin (n.unop.len + 1)) : n ⟶ zero :=
  (SimplexCategory.const (SimplexCategory.mk 0) n.unop j).op

def fromVertices (v : X.obj zero → I) : X ⟶ nerve (Codiscrete I) where
  app n := ↾fun x => Codiscrete.functor (fun j => v (X.map (vertex n j) x))
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Codiscrete.equivFun.injective
    funext j
    exact congrArg v ((types_congr_hom (X.map_comp θ (vertex m j)) x).symm)

def vertices (f : X ⟶ nerve (Codiscrete I)) : X.obj zero → I :=
  fun x => ((f.app zero x).obj 0).as

lemma vertices_fromVertices (v : X.obj zero → I) : vertices (fromVertices v) = v := by
  funext x
  change v (X.map (vertex zero 0) x) = v x
  have he : vertex zero 0 = 𝟙 zero := by
    apply Quiver.Hom.unop_inj
    ext j
    change (0 : ℕ) = j.val
    have hj : j.val < 1 := j.isLt
    omega
  rw [he, X.map_id]
  rfl

lemma fromVertices_vertices (f : X ⟶ nerve (Codiscrete I)) :
    fromVertices (vertices f) = f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Codiscrete.equivFun.injective
  funext j
  exact congrArg (fun c => (c.obj 0).as)
    (types_congr_hom (f.naturality (vertex n j)) x)

def homEquiv : (X ⟶ nerve (Codiscrete I)) ≃ (X.obj zero → I) where
  toFun := vertices
  invFun := fromVertices
  left_inv := fromVertices_vertices
  right_inv := vertices_fromVertices

lemma exists_extension {A B : SSet.{u}} (j : A ⟶ B) [Mono j]
    (f : A ⟶ nerve (Codiscrete I)) (i : I) :
    ∃ g : B ⟶ nerve (Codiscrete I), j ≫ g = f := by
  have hj : Function.Injective (j.app zero) :=
    (mono_iff_injective _).mp inferInstance
  let v : B.obj zero → I := Function.extend (j.app zero) (vertices f) (fun _ => i)
  refine ⟨fromVertices v, homEquiv.injective ?_⟩
  funext x
  change vertices (fromVertices v) (j.app zero x) = vertices f x
  rw [vertices_fromVertices]
  exact hj.extend_apply _ _ _

lemma terminal_mono_rlp (i : I) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (terminal.from (nerve (Codiscrete I))) := by
  intro A B j hj
  have : Mono j := hj
  refine ⟨fun {f g} _ => ?_⟩
  obtain ⟨l, hl⟩ := exists_extension j f i
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := terminal.hom_ext _ _ }⟩⟩

lemma terminal_horn_rlp (i : I) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (nerve (Codiscrete I))) := by
  intro A B j hj
  exact terminal_mono_rlp i j (SSet.modelCategoryQuillen.J_le_monomorphisms j hj)

/-- 点を持つcodiscrete圏のnerveは全hornを充填できるKan複体である。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。
-/
lemma kanComplex (i : I) : SSet.KanComplex (nerve (Codiscrete I)) :=
  (SSet.modelCategoryQuillen.fibration_iff _).mpr (terminal_horn_rlp i)

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets
