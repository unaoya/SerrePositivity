module
public import Mathlib.Algebra.Homology.Homotopy

/-!
# 鎖ホモトピーの成分の自然な正方形

概要：一段上の鎖ホモトピーの成分が二つの鎖写像に可換であることを表し、合成則を証明する。
方針：和・負号・前後の鎖写像の合成に分配する。
規約：KST Construction A.5、対象は ℕ 次数の鎖複体。
使われ方：構成済みの標準比較の自然性を各合成段階から導く。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {C C' D D' E E' : ChainComplex A ℕ}

/-- 概要：二つの鎖ホモトピーの一段上の成分が作る自然な正方形。
方針：各次数の実写像の可換性を述べる。
規約：KST A.5、存在を仮定する界面ではなく構成済みホモトピーの性質。
使われ方：自然性を前後合成と連結へ分解する。 -/
def ChainHomotopySquare {f g : C ⟶ D} {f' g' : C' ⟶ D'}
    (a : C ⟶ C') (b : D ⟶ D') (H : Homotopy f g) (H' : Homotopy f' g') : Prop :=
  ∀ n, a.f n ≫ H'.hom n (n + 1) = H.hom n (n + 1) ≫ b.f (n + 1)

/-- 概要：等式から作る零成分のホモトピーは任意の二つの鎖写像に自然。
方針：成分が零であることを使う。
規約：KST A.5。使われ方：比較の等式による端点同定。 -/
lemma ChainHomotopySquare.ofEq {f g : C ⟶ D} {f' g' : C' ⟶ D'}
    (a : C ⟶ C') (b : D ⟶ D') (h : f = g) (h' : f' = g') :
    ChainHomotopySquare a b (Homotopy.ofEq h) (Homotopy.ofEq h') := by
  intro n
  simp only [Homotopy.ofEq_hom, Pi.zero_apply, Limits.comp_zero, Limits.zero_comp]

/-- 概要：自然なホモトピーの連結は自然。
方針：二つの成分の和へ合成を分配する。
規約：KST A.5。使われ方：標準比較の連結。 -/
lemma ChainHomotopySquare.trans {f g k : C ⟶ D} {f' g' k' : C' ⟶ D'}
    {a : C ⟶ C'} {b : D ⟶ D'} {H : Homotopy f g} {H' : Homotopy f' g'}
    {K : Homotopy g k} {K' : Homotopy g' k'}
    (hH : ChainHomotopySquare a b H H') (hK : ChainHomotopySquare a b K K') :
    ChainHomotopySquare a b (H.trans K) (H'.trans K') := by
  intro n
  simp only [Homotopy.trans_hom, Preadditive.comp_add, Preadditive.add_comp, hH n, hK n]

/-- 概要：自然なホモトピーの逆向きも自然。
方針：成分の負号を合成の外へ出す。
規約：KST A.5。使われ方：Moore 収縮の向きの反転。 -/
lemma ChainHomotopySquare.symm {f g : C ⟶ D} {f' g' : C' ⟶ D'}
    {a : C ⟶ C'} {b : D ⟶ D'} {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ChainHomotopySquare a b H H') : ChainHomotopySquare a b H.symm H'.symm := by
  intro n
  simp only [Homotopy.symm_hom, Preadditive.comp_neg, Preadditive.neg_comp, hH n]

/-- 概要：可換な前合成はホモトピーの自然な正方形を保つ。
方針：前合成の正方形とホモトピーの正方形を次数ごとに合成する。
規約：KST A.5。使われ方：Moore 包含や AW の前合成。 -/
lemma ChainHomotopySquare.compLeft {f g : C ⟶ D} {f' g' : C' ⟶ D'}
    {a : C ⟶ C'} {b : D ⟶ D'} {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ChainHomotopySquare a b H H') (e : E ⟶ C) (e' : E' ⟶ C') (c : E ⟶ E')
    (he : c ≫ e' = e ≫ a) : ChainHomotopySquare c b (H.compLeft e) (H'.compLeft e') := by
  intro n
  have hn := congrArg (fun t ↦ t.f n) he
  change c.f n ≫ e'.f n = e.f n ≫ a.f n at hn
  simp only [Homotopy.compLeft_hom]
  rw [← Category.assoc, hn, Category.assoc, hH n, ← Category.assoc]

/-- 概要：可換な後合成はホモトピーの自然な正方形を保つ。
方針：ホモトピーの正方形と後合成の正方形を次数ごとに合成する。
規約：KST A.5。使われ方：shuffle や Moore 射影の後合成。 -/
lemma ChainHomotopySquare.compRight {f g : C ⟶ D} {f' g' : C' ⟶ D'}
    {a : C ⟶ C'} {b : D ⟶ D'} {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ChainHomotopySquare a b H H') (e : D ⟶ E) (e' : D' ⟶ E') (c : E ⟶ E')
    (he : b ≫ e' = e ≫ c) : ChainHomotopySquare a c (H.compRight e) (H'.compRight e') := by
  intro n
  have hn := congrArg (fun t ↦ t.f (n + 1)) he
  change b.f (n + 1) ≫ e'.f (n + 1) = e.f (n + 1) ≫ c.f (n + 1) at hn
  simp only [Homotopy.compRight_hom]
  rw [← Category.assoc, hH n, Category.assoc, hn, ← Category.assoc]

end SerrePositivity.KST.ProExcision
