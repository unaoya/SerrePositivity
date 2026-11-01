module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LiftSuccessor

/-!
# 指定済みの低次数の持ち上げを保持するReedy持ち上げを構成する

## 概要
指定済みの低次数の持ち上げを保持するReedy持ち上げを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0268][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0268
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reedy lifting retaining an entire prescribed lower-degree lift

The existing successor construction can start at any degree and retain
all old components. The resulting single natural lift agrees exactly
with the supplied natural lift below the starting degree.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.RelativeLifting
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {A B X Y : J ⥤ C} {i : A ⟶ B} {p : X ⟶ Y}
  [∀ j, HasLiftingProperty (relativeLatchingMap r j i) (relativeMatchingMap r j p)]
  {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a i p b)
  (n : ℕ) (initial : LiftBelow r sq n)

lemma degreeZero_identities {j k : J} (f : j ⟶ k) (hj : r.deg j = 0) (hk : r.deg k = 0) :
    MorphismProperty.identities J f := by
  let q := r.mapFactorizationData f
  have hz : r.deg q.Z = 0 := Nat.eq_zero_of_le_zero (hj ▸ r.le₁ q.i q.hi)
  have hi := r.identities_of_prop₁_of_eq q.hi (hj.trans hz.symm)
  have hp := r.identities_of_prop₂_of_eq q.hp (hz.trans hk.symm)
  exact q.fac ▸ (MorphismProperty.identities J).comp_mem q.i q.p hi hp

def tower : (k : ℕ) → LiftBelow r sq (n + k)
  | 0 => initial
  | k + 1 => (tower k).successor

lemma tower_app_mono {k l : ℕ} (hkl : k ≤ l) (j : J) (hj : r.deg j < n + k) :
    (tower r sq n initial l).hom.app ⟨j, lt_of_lt_of_le hj (Nat.add_le_add_left hkl n)⟩ =
      (tower r sq n initial k).hom.app ⟨j, hj⟩ := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    exact ((tower r sq n initial l).successor_app_old j
      (lt_of_lt_of_le hj (Nat.add_le_add_left hkl n))).trans ih

abbrev app (j : J) : B.obj j ⟶ X.obj j :=
  (tower r sq n initial (r.deg j + 1)).hom.app
    ⟨j, lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_left _ _)⟩

lemma app_eq_tower (k : ℕ) (j : J) (hj : r.deg j < n + k) :
    app r sq n initial j = (tower r sq n initial k).hom.app ⟨j, hj⟩ := by
  exact (tower_app_mono r sq n initial (le_max_right k (r.deg j + 1)) j _).symm.trans
    (tower_app_mono r sq n initial (le_max_left k (r.deg j + 1)) j hj)

lemma naturality {j k : J} (f : j ⟶ k) :
    B.map f ≫ app r sq n initial k = app r sq n initial j ≫ X.map f := by
  let l := max (r.deg j) (r.deg k) + 1
  have hj : r.deg j < n + l := lt_of_lt_of_le
    (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)) (Nat.le_add_left _ _)
  have hk : r.deg k < n + l := lt_of_lt_of_le
    (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)) (Nat.le_add_left _ _)
  rw [app_eq_tower r sq n initial l j hj, app_eq_tower r sq n initial l k hk]
  exact (tower r sq n initial l).hom.naturality (ObjectProperty.homMk f : ⟨j, hj⟩ ⟶ ⟨k, hk⟩)

def lift : B ⟶ X where
  app := app r sq n initial
  naturality {_ _} f := naturality r sq n initial f

lemma fac_left : i ≫ lift r sq n initial = a := by
  apply NatTrans.ext
  funext j
  exact congr_app (tower r sq n initial (r.deg j + 1)).fac_left
    ⟨j, lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_left _ _)⟩

lemma fac_right : lift r sq n initial ≫ p = b := by
  apply NatTrans.ext
  funext j
  exact congr_app (tower r sq n initial (r.deg j + 1)).fac_right
    ⟨j, lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_left _ _)⟩

lemma restrict : Functor.whiskerLeft (lowerInclusion r n) (lift r sq n initial) = initial.hom := by
  apply NatTrans.ext
  funext j
  exact app_eq_tower r sq n initial 0 j.obj j.property

/-- 指定済みの低次数の持ち上げを保持するReedy持ち上げを構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。
-/
def liftStruct : sq.LiftStruct where
  l := lift r sq n initial
  fac_left := fac_left r sq n initial
  fac_right := fac_right r sq n initial

end SerrePositivity.Reedy.RelativeLifting
