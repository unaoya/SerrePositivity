module

public import SerrePositivity.CategoryTheory.ArrowFactorizationCategory
public import SerrePositivity.CategoryTheory.AnchoredChainSimplicial
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 中断した任意モデル源への一般化：AnchoredChainNerve

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All anchored chains are the nerve of the factorization category。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0003][inventory]を参照する。

[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#m0003
[plan]: ../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All anchored chains are the nerve of the factorization category

This identifies every degree and all simplicial operators at once. The
nerve uses the maximum of the independent object and Hom universes.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.AnchoredChain
variable {D : Type u} [Category.{v} D] {Y V : D} {g : Y ⟶ V} {n m : ℕ}

/-- Every intermediate object of a chain is its actual cut factorization. -/
def cutDiagram (c : AnchoredChain g n) : Fin (n + 1) ⥤ ArrowFactorization g where
  obj k := c.cut k
  map {i j} h :=
    { hom := c.diagram.map h
      left_comm := by
        change (c.left ≫ c.diagram.map _) ≫ c.diagram.map _ = c.left ≫ c.diagram.map _
        rw [Category.assoc, ← c.diagram.map_comp]
        rfl
      right_comm := by
        change c.diagram.map _ ≫ (c.diagram.map _ ≫ c.right) = c.diagram.map _ ≫ c.right
        rw [← Category.assoc, ← c.diagram.map_comp]
        rfl }
  map_id k := ArrowFactorization.Hom.ext (c.diagram.map_id k)
  map_comp h k := ArrowFactorization.Hom.ext (c.diagram.map_comp h k)

/-- A diagram of factorizations supplies the surrounding arrows and their composite. -/
def fromDiagram (F : Fin (n + 1) ⥤ ArrowFactorization g) : AnchoredChain g n where
  diagram := F ⋙ ArrowFactorization.forget g
  left := (F.obj 0).left
  right := (F.obj (Fin.last n)).right
  fac := by
    change ((F.obj 0).left ≫ (F.map (homOfLE (Fin.zero_le (Fin.last n)))).hom) ≫
      (F.obj (Fin.last n)).right = g
    rw [ArrowFactorization.left_comp]
    exact (F.obj (Fin.last n)).fac

lemma fromDiagram_cutDiagram (c : AnchoredChain g n) : fromDiagram (cutDiagram c) = c := by
  cases c with
  | mk F a b h =>
    unfold fromDiagram cutDiagram cut before after
    congr 1 <;> simp

lemma cutDiagram_fromDiagram_obj (F : Fin (n + 1) ⥤ ArrowFactorization g) (k : Fin (n + 1)) :
    (cutDiagram (fromDiagram F)).obj k = F.obj k := by
  change ArrowFactorization.mk (F.obj k).middle
    ((F.obj 0).left ≫ (F.map (homOfLE (Fin.zero_le k))).hom)
    ((F.map (homOfLE (Fin.le_last k))).hom ≫ (F.obj (Fin.last n)).right) _ = F.obj k
  calc
    _ = ArrowFactorization.mk (F.obj k).middle (F.obj k).left (F.obj k).right (F.obj k).fac := by
      congr 1
      · exact (F.map (homOfLE (Fin.zero_le k))).left_comm
      · exact (F.map (homOfLE (Fin.le_last k))).right_comm
    _ = F.obj k := ArrowFactorization.eta _

lemma cutDiagram_fromDiagram (F : Fin (n + 1) ⥤ ArrowFactorization g) :
    cutDiagram (fromDiagram F) = F := by
  refine CategoryTheory.Functor.ext (cutDiagram_fromDiagram_obj F) ?_
  intro i j h
  apply ArrowFactorization.Hom.ext
  simp only [ArrowFactorization.comp_hom, ArrowFactorization.eqToHom_hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma fromDiagram_reindex (F : Fin (n + 1) ⥤ ArrowFactorization g)
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    fromDiagram (θ.monotone.functor ⋙ F) = (fromDiagram F).reindex θ := by
  unfold fromDiagram reindex
  congr 1
  · exact (F.map (homOfLE (Fin.zero_le (θ 0)))).left_comm.symm
  · exact (F.map (homOfLE (Fin.le_last (θ (Fin.last m))))).right_comm.symm

variable (g)

def degreeEquiv (n : ℕ) : (Fin (n + 1) ⥤ ArrowFactorization g) ≃ AnchoredChain g n where
  toFun := fromDiagram
  invFun := cutDiagram
  left_inv := cutDiagram_fromDiagram
  right_inv := fromDiagram_cutDiagram

/-- The degreewise equivalence commutes with every ordinal operator. -/
def fromNerve : nerve (ArrowFactorization g) ⟶ simplicial g where
  app _ := ↾fromDiagram
  naturality {a b} θ := by
    ext F
    exact fromDiagram_reindex F θ.unop.toOrderHom

instance fromNerve_isIso : IsIso (fromNerve g) := by
  have : ∀ n, IsIso ((fromNerve g).app n) := fun n =>
    (CategoryTheory.isIso_iff_bijective _).mpr (degreeEquiv g n.unop.len).bijective
  exact NatIso.isIso_of_isIso_app _

def nerveIso : nerve (ArrowFactorization g) ≅ simplicial g := asIso (fromNerve g)

end SerrePositivity.AnchoredChain
