module

public import SerrePositivity.KST.Descent.DiagramTransfer
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# 有限の成分ごとに異なる正 rank 作用の可逆性

## 概要
極限を保つ関手の自然な射の可逆性を各成分で検査し、成分ごとに異なる正の有理 rank 倍へ適用する。

## 方針
各成分の指定同型から極限点の同型を構成し、元の自然変換の成分と同一であることを自然性で示す。

## 規約
ここで使う極限は値域の通常の有限積などであり、Tot とは呼ばない。

## 使われ方
論文 補題 3.2 の有限 Zariski Čech の各段の非交和と、変動する局所 rank の可逆性。
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Linear

namespace SerrePositivity.KST.Descent

/-- 概要：極限を保つ関手間の自然な射の可逆性は成分で反映（補題 3.2）。
方針：成分の同型による極限点の指定同型と自然性の式を比較する。
規約：有限積の場合に元の非交和の成分を検査できる。使われ方：局所 rank の異なる各成分の貼り合わせ。 -/
theorem naturalMap_isIso_of_isLimit
    {C V J : Type*} [Category* C] [Category* V] [Category* J]
    {D : J ⥤ C} {c : Cone D} (hc : IsLimit c)
    {F G : C ⥤ V} [PreservesLimit D F] [PreservesLimit D G]
    (a : F ⟶ G) (ha : ∀ j, IsIso (a.app (D.obj j))) : IsIso (a.app c.pt) := by
  let τ := Functor.whiskerLeft D a
  have : ∀ j, IsIso (τ.app j) := ha
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  let e := (isLimitOfPreserves F hc).conePointsIsoOfNatIso
    (isLimitOfPreserves G hc) (asIso τ)
  have he : a.app c.pt = e.hom := by
    apply (isLimitOfPreserves G hc).hom_ext
    intro j
    exact (a.naturality (c.π.app j)).symm.trans
      ((isLimitOfPreserves F hc).conePointsIsoOfNatIso_hom_comp
        (isLimitOfPreserves G hc) (asIso τ) j).symm
  rw [he]
  exact e.isIso_hom

/-- 概要：正の整数 rank 倍の恒等射の指定逆（補題 3.2）。
方針：有理線形な値域で rank の有理逆数倍を使う。
規約：対象は一般の有理線形圏。使われ方：成分ごとに異なる局所 rank 作用の検査。 -/
def positiveRankIdentityIso {V : Type*} [Category* V] [Preadditive V] [Linear ℚ V]
    (X : V) (rank : ℕ) (positive : 0 < rank) : X ≅ X where
  hom := (rank : ℚ) • 𝟙 X
  inv := (rank : ℚ)⁻¹ • 𝟙 X
  hom_inv_id := by
    simp only [smul_comp, comp_smul, Category.id_comp, smul_smul]
    rw [inv_mul_cancel₀ (by exact_mod_cast positive.ne'), one_smul]
  inv_hom_id := by
    simp only [smul_comp, comp_smul, Category.id_comp, smul_smul]
    rw [mul_inv_cancel₀ (by exact_mod_cast positive.ne'), one_smul]

/-- 概要：成分ごとに異なる正 rank の自然な作用は極限点でも可逆（補題 3.2）。
方針：各成分で正の有理 rank の指定同型を使い、極限保存で反映する。
規約：全成分の rank が同じとは要求しない。使われ方：有限非交和の Čech 各段での rank 作用。 -/
theorem naturalEndomorphism_isIso_of_positiveRanks
    {C V J : Type*} [Category* C] [Category* V] [Category* J]
    [Preadditive V] [Linear ℚ V]
    {D : J ⥤ C} {c : Cone D} (hc : IsLimit c)
    {F : C ⥤ V} [PreservesLimit D F] (a : F ⟶ F)
    (rank : J → ℕ) (positive : ∀ j, 0 < rank j)
    (hlocal : ∀ j, a.app (D.obj j) = (rank j : ℚ) • 𝟙 (F.obj (D.obj j))) :
    IsIso (a.app c.pt) :=
  naturalMap_isIso_of_isLimit hc a (fun j ↦ by
    rw [hlocal j]
    exact (positiveRankIdentityIso (F.obj (D.obj j)) (rank j) (positive j)).isIso_hom)

end SerrePositivity.KST.Descent
