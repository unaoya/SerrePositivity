module
public import SerrePositivity.KST.ProExcision.ChainHomotopySquare
public import Mathlib.Algebra.Homology.Linear

/-!
# 鎖ホモトピーの自然な正方形の加法と整数倍

概要：構成済みホモトピーの成分の自然性を和・整数倍・恒等比較へ移す。
方針：合成を成分の和と scalar に分配する。
規約：KST Construction A.5 の augmentation 補正。
使われ方：二つの比較の差から復元する実区間の同変性。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {C C' D D' : ChainComplex A ℕ}

/-- 概要：恒等比較の零ホモトピーは任意の二つの鎖写像に自然。
方針：等式からのホモトピーの零成分を使う。
規約：KST A.5。使われ方：比較の差に足す第二の始点の恒等比較。 -/
lemma ChainHomotopySquare.refl (a : C ⟶ C') (b : D ⟶ D') (f : C ⟶ D) (f' : C' ⟶ D') :
    ChainHomotopySquare a b (Homotopy.refl f) (Homotopy.refl f') :=
  ChainHomotopySquare.ofEq a b rfl rfl

/-- 概要：二つの自然なホモトピーの和は自然。
方針：成分の和へ合成を分配する。
規約：KST A.5。使われ方：三項の augmentation 補正の比較の合成。 -/
lemma ChainHomotopySquare.add
    {f g k l : C ⟶ D} {f' g' k' l' : C' ⟶ D'} {a : C ⟶ C'} {b : D ⟶ D'}
    {H : Homotopy f g} {H' : Homotopy f' g'} {K : Homotopy k l} {K' : Homotopy k' l'}
    (hH : ChainHomotopySquare a b H H') (hK : ChainHomotopySquare a b K K') :
    ChainHomotopySquare a b (H.add K) (H'.add K') := by
  intro n
  simp only [Homotopy.add_hom, Preadditive.comp_add, Preadditive.add_comp, hH n, hK n]

/-- 概要：自然なホモトピーの整数倍は自然。
方針：合成と整数 scalar の可換性を使う。
規約：KST A.5、実線形圏の構造を用いる。
使われ方：第二の比較の負と第三項の負の同変性。 -/
lemma ChainHomotopySquare.smul [Linear ℤ A]
    {f g : C ⟶ D} {f' g' : C' ⟶ D'} {a : C ⟶ C'} {b : D ⟶ D'}
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ChainHomotopySquare a b H H') (s : ℤ) :
    ChainHomotopySquare a b (H.smul s) (H'.smul s) := by
  intro n
  simp only [Homotopy.smul_hom, Linear.comp_smul, Linear.smul_comp, hH n]

end SerrePositivity.KST.ProExcision
