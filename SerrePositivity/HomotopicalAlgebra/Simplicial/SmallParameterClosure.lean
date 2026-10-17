module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Logic.Small.Set

/-!
# 中断した任意モデル源への一般化：SmallParameterClosure

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A small subcomplex closed under a whole simplicial parameter operation。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0574][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0574
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A small subcomplex closed under a whole simplicial parameter operation

Countably many images suffice. Smallness is proved in the original universe
degree by degree; the ambient simplicial set may live in a larger universe.
-/

@[expose] public section
universe v w
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.SmallParameterClosure
variable {X P : SSet.{w}}

def IsSmall (A : X.Subcomplex) : Prop := ∀ n, Small.{v} (A.obj n)

def step (t : X ⊗ P ⟶ X) (A : X.Subcomplex) : X.Subcomplex :=
  A ⊔ Subfunctor.range (A.ι ▷ P ≫ t)

def stage (t : X ⊗ P ⟶ X) (A : X.Subcomplex) : ℕ → X.Subcomplex
  | 0 => A
  | n + 1 => step t (stage t A n)

def closure (t : X ⊗ P ⟶ X) (A : X.Subcomplex) : X.Subcomplex :=
  ⨆ n, stage t A n

lemma le_closure (t : X ⊗ P ⟶ X) (A : X.Subcomplex) : A ≤ closure t A :=
  le_iSup (fun n => stage t A n) 0

lemma step_small (t : X ⊗ P ⟶ X) (A : X.Subcomplex)
    (hP : ∀ n, Small.{v} (P.obj n)) (hA : IsSmall.{v} A) : IsSmall.{v} (step t A) := by
  intro n
  have := hP n
  have := hA n
  change Small.{v} ↥(A.obj n ∪ Set.range ((A.ι ▷ P ≫ t).app n))
  have : Small.{v} ((A.toSSet ⊗ P).obj n) :=
    inferInstanceAs (Small.{v} (A.obj n × P.obj n))
  infer_instance

lemma stage_small (t : X ⊗ P ⟶ X) (A : X.Subcomplex)
    (hP : ∀ n, Small.{v} (P.obj n)) (hA : IsSmall.{v} A) (k : ℕ) :
    IsSmall.{v} (stage t A k) := by
  induction k with
  | zero => exact hA
  | succ k hk => exact step_small t _ hP hk

lemma closure_small (t : X ⊗ P ⟶ X) (A : X.Subcomplex)
    (hP : ∀ n, Small.{v} (P.obj n)) (hA : IsSmall.{v} A) : IsSmall.{v} (closure t A) := by
  intro n
  have (k : ℕ) : Small.{v} ((stage t A k).obj n) := stage_small t A hP hA k n
  change Small.{v} ((⨆ k, stage t A k).obj n)
  rw [Subfunctor.iSup_obj]
  infer_instance

/-- Every parameter value is retained; this is not merely closure at the vertices. -/
lemma closed (t : X ⊗ P ⟶ X) (A : X.Subcomplex) :
    Subfunctor.range ((closure t A).ι ▷ P ≫ t) ≤ closure t A := by
  intro n y hy
  obtain ⟨⟨x, p⟩, rfl⟩ := hy
  have hx : ∃ k, x.val ∈ (stage t A k).obj n := by
    simpa only [closure, Subfunctor.iSup_obj, Set.mem_iUnion] using x.property
  obtain ⟨k, hk⟩ := hx
  apply (le_iSup (fun j => stage t A j) (k + 1)) n
  apply (le_sup_right : Subfunctor.range ((stage t A k).ι ▷ P ≫ t) ≤
    step t (stage t A k)) n
  exact ⟨(⟨x.val, hk⟩, p), rfl⟩

end SerrePositivity.SimplicialModel.SmallParameterClosure
