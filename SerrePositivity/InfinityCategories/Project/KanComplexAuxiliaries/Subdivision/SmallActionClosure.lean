module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Logic.Small.Set

/-!
# 小さい部分単体集合の作用による閉包

## 概要
小さいパラメータの作用で小さい部分単体集合を閉じる。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
像を加える操作を可算回反復し、その和の小ささと作用に対する閉性を示す。
既存の構成を同じ公開名と証明のまま一般層に切り出す。

## 規約と注意
宇宙と仮定は各宣言に明示したものを用いる。
専用の比較図式・正規化充填・選択の整合性は仮定しない。

## 使われ方
一般入口GeneralToolsおよび共有Foundationsから利用する。
旧パスの互換importを通して中断中の厳密化からも利用する。
今後のS-構成・ホモトピー比較・局所化の基礎として使える。
詳細はformalization-plans/archive/k-theory-generalization-inventory.mdの配置実施記録を参照。
-/

@[expose] public section
universe v w
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure
variable {X P : SSet.{w}}

def IsSmall (A : X.Subcomplex) : Prop := ∀ n, Small.{v} (A.obj n)

def step (t : X ⊗ P ⟶ X) (A : X.Subcomplex) : X.Subcomplex :=
  A ⊔ Subfunctor.range (A.ι ▷ P ≫ t)

def stage (t : X ⊗ P ⟶ X) (A : X.Subcomplex) : ℕ → X.Subcomplex
  | 0 => A
  | n + 1 => step t (stage t A n)

/-- 小さい部分単体集合を指定したパラメータ作用に関して閉じる。
作用の像を加える操作の可算反復の上限を取り、小ささと閉性は後続の補題で示す。 -/
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

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure
