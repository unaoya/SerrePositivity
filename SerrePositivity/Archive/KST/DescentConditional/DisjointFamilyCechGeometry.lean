module

public import SerrePositivity.Archive.KST.DescentConditional.FiniteFamilyCech
public import Mathlib.CategoryTheory.Extensive

/-!
# 非交和の被覆族の多重交叉

## 概要
非交和の包含の被覆族について、同じ成分の多重交叉と異なる成分を含む交叉を計算する。

## 方針
単射の同じ成分の交叉では指定射影と対角を逆にする。
異なる成分を含む交叉は、互いに素な二つの包含の引き戻しである厳密な始対象へ写す。

## 規約
元の圏内の実際の wide pullback の指定射を使う。前層の非交和保存は仮定しない。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の非交和被覆。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {ι : Type w} {Y : C} (X : ι → C) (cover : ∀ i, X i ⟶ Y)

/-- 概要：単射の同じ成分の多重交叉とその成分の指定同型（公理 (1)）。
方針：零番目の射影と全ての座標が恒等となる対角を互いに逆にする。
規約：選んだ成分の被覆射の mono 性だけを使用。使われ方：非交和被覆の定数添字の列。 -/
def familyCechDiagonalIso (n : SimplexCategory) (i : ι) [Mono (cover i)] :
    familyCechTerm X cover n (fun _ ↦ i) ≅ X i where
  hom := WidePullback.π (fun _ : Fin (n.len + 1) ↦ cover i) 0
  inv := WidePullback.lift (cover i) (fun _ ↦ 𝟙 (X i)) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, WidePullback.lift_π, Category.comp_id]
      apply (cancel_mono (cover i)).mp
      simp
    · simp
  inv_hom_id := by simp

/-- 概要：同じ成分の指定対角同型は単体射で保持される（公理 (1)）。
方針：指定射影を被覆射と合成し、mono 性で二つの座標を同定する。
規約：元の幾何射の等式。使われ方：定数の値の図式への自然な射。 -/
theorem familyCechDiagonalIso_naturality {n m : SimplexCategory} (f : n ⟶ m)
    (i : ι) [Mono (cover i)] :
    familyCechMap X cover f (fun _ ↦ i) ≫ (familyCechDiagonalIso X cover n i).hom =
      (familyCechDiagonalIso X cover m i).hom := by
  apply (cancel_mono (cover i)).mp
  simp [familyCechMap, familyCechDiagonalIso]

/-- 概要：同じ成分の指定対角も単体射で保持される（公理 (1)）。
方針：射影との逆関係と指定射影の自然性で同定する。
規約：元の幾何の合成の等式。使われ方：前層で写した定数図式への自然性。 -/
theorem familyCechDiagonalIso_inv_naturality {n m : SimplexCategory} (f : n ⟶ m)
    (i : ι) [Mono (cover i)] :
    (familyCechDiagonalIso X cover m i).inv ≫ familyCechMap X cover f (fun _ ↦ i) =
      (familyCechDiagonalIso X cover n i).inv := by
  apply (cancel_mono (familyCechDiagonalIso X cover n i).hom).mp
  rw [Category.assoc, familyCechDiagonalIso_naturality]
  simp

variable [Finite ι] [FinitaryExtensive C]

/-- 概要：異なる成分を含む非交和被覆族の多重交叉は始対象（公理 (1)）。
方針：異なる二成分の互いに素な引き戻しへ指定座標で写し、始対象の厳密性を使う。
規約：元の有限型の圏に適用できる圏論的計算。使われ方：空の交叉の値の弱可縮性。 -/
def disjointFamilyCech_isInitial (n : SimplexCategory) (a : Fin (n.len + 1) → ι)
    (j k : Fin (n.len + 1)) (h : a j ≠ a k) :
    IsInitial (familyCechTerm X (fun i ↦ Sigma.ι X i) n a) := by
  let p := pullback (Sigma.ι X (a j)) (Sigma.ι X (a k))
  have hp : IsInitial p := initialIsInitial.ofIso
    (FinitaryExtensive.isPullback_initial_to_sigma_ι X (a j) (a k) h).isoPullback
  let q : familyCechTerm X (fun i ↦ Sigma.ι X i) n a ⟶ p :=
    pullback.lift (WidePullback.π (fun t ↦ Sigma.ι X (a t)) j)
      (WidePullback.π (fun t ↦ Sigma.ι X (a t)) k) (by simp)
  exact hp.ofStrict q

end SerrePositivity.KST.Descent
