module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Elements

/-!
# nerveの単体圏から終端頂点を評価する関手を構成する

## 概要
nerveの単体圏から終端頂点を評価する関手を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
単体を表す合成可能射列の先頭または終端を評価する。
単体圏の射と射列の制限を照合し、関手の法則とaugmentationの式を確認する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0014][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#m0014
[plan]: ../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Endpoint evaluation on the actual category of nerve simplices

The last vertex changes along a simplex operator by the actual tail of
the chain. This includes the face deleting the old last vertex. It is
not merely evaluation on a fixed degree or an endpoint-preserving map.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.NerveSimplexEndpoint
variable {D : Type u} [Category.{v} D]

abbrev Index (D : Type u) [Category.{v} D] := (nerve D).Elementsᵒᵖ
abbrev dimension (s : Index D) := s.unop.obj.unop.len
abbrev chain (s : Index D) : Fin (dimension s + 1) ⥤ D := s.unop.val
abbrev endpoint (s : Index D) : D := (chain s).obj (Fin.last (dimension s))
abbrev operator {s t : Index D} (f : s ⟶ t) :
    SimplexCategory.mk (dimension s) ⟶ SimplexCategory.mk (dimension t) := f.unop.hom.unop

lemma chain_eq {s t : Index D} (f : s ⟶ t) :
    (SimplexCategory.toCat.map (operator f)).toFunctor ⋙ chain t = chain s := f.unop.map_val

lemma endpoint_eq {s t : Index D} (f : s ⟶ t) : endpoint s =
    (chain t).obj ((operator f).toOrderHom (Fin.last (dimension s))) :=
  congrArg (fun q : Fin (dimension s + 1) ⥤ D => q.obj (Fin.last (dimension s)))
    (chain_eq f).symm

def tail {n m : ℕ} (c : Fin (n + 1) ⥤ D) (d : Fin (m + 1) ⥤ D)
    (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (h : (SimplexCategory.toCat.map θ).toFunctor ⋙ d = c) :
    c.obj (Fin.last n) ⟶ d.obj (Fin.last m) :=
  eqToHom (congrArg (fun q : Fin (n + 1) ⥤ D => q.obj (Fin.last n)) h.symm) ≫
    d.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last n))))

lemma tail_comp {n m k : ℕ} (c : Fin (n + 1) ⥤ D) (d : Fin (m + 1) ⥤ D)
    (e : Fin (k + 1) ⥤ D) (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (ψ : SimplexCategory.mk m ⟶ SimplexCategory.mk k)
    (hθ : (SimplexCategory.toCat.map θ).toFunctor ⋙ d = c)
    (hψ : (SimplexCategory.toCat.map ψ).toFunctor ⋙ e = d)
    (h : (SimplexCategory.toCat.map (θ ≫ ψ)).toFunctor ⋙ e = c) :
    tail c e (θ ≫ ψ) h = tail c d θ hθ ≫ tail d e ψ hψ := by
  subst c
  subst d
  simp only [tail, eqToHom_refl, Category.id_comp]
  exact e.map_comp _ _

def endpointMap {s t : Index D} (f : s ⟶ t) : endpoint s ⟶ endpoint t :=
  tail (chain s) (chain t) (operator f) (chain_eq f)

lemma endpointMap_id (s : Index D) : endpointMap (𝟙 s) = 𝟙 (endpoint s) := by
  simp [endpointMap, tail]

lemma endpointMap_comp {s t r : Index D} (f : s ⟶ t) (g : t ⟶ r) :
    endpointMap (f ≫ g) = endpointMap f ≫ endpointMap g :=
  tail_comp (chain s) (chain t) (chain r) (operator f) (operator g)
    (chain_eq f) (chain_eq g) (chain_eq (f ≫ g))

/-- A named chain as an object of the actual nerve simplex category. -/
abbrev ofChain {n : ℕ} (c : ComposableArrows D n) : Index D :=
  Opposite.op ((nerve D).elementsMk (Opposite.op (SimplexCategory.mk n)) c)

/-- The actual simplex-category arrow for any reindexing, including the last face. -/
def reindexArrow {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ⟶ ofChain c :=
  Quiver.Hom.op (Functor.Elements.homMk θ.op rfl)

lemma reindexArrow_endpoint {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    endpointMap (reindexArrow c θ) =
      c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))) := by
  simp only [endpointMap, tail, eqToHom_refl, Category.id_comp]

/- 旧宣言の技術注記：
Evaluate each actual nerve simplex at its last object and each operator at its tail.
-/
/-- nerveの単体圏から終端頂点を評価する関手を構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
単体を表す合成可能射列の先頭または終端を評価する。
単体圏の射と射列の制限を照合し、関手の法則とaugmentationの式を確認する。
-/
def functor (D : Type u) [Category.{v} D] : Index D ⥤ D where
  obj s := endpoint s
  map f := endpointMap f
  map_id s := endpointMap_id s
  map_comp f g := endpointMap_comp f g

end SerrePositivity.NerveSimplexEndpoint
