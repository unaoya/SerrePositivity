module

public import SerrePositivity.KST.ProExcision.IntervalGradeBoundary
public import SerrePositivity.KST.ProExcision.KoszulDifferential

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 有限 Koszul 初頁の係数微分

概要：補助初頁を共通係数次数のテンソルで表し、その微分を Koszul 微分へ同定する。
方針：実際の区間の商比較に、下端を正規化した隣接商のホモロジー比較を合成する。
規約：Mathlib の頁 2 は KST の E₁。
使われ方：KST Lemma 4.10 の次頁を Koszul ホモロジーとして計算する。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：有限 Koszul 補助初頁を指定した係数次数のテンソルへ同定する。
方針：実際の商模型と下端正規化を使い、Koszul 項の自由性で平坦比較を適用する。
規約：位置 (s,p) の係数次数は s+2p。使われ方：KST Lemma 4.10 の微分に適合する初頁模型。 -/
def koszulFirstPageCoefficientIsoAt {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (pq : ℤ × Fin (e + 1))
    (t : ℤ) (ht : pq.1 + 2 * (pq.2.val : ℤ) = t) :
    ((koszulFilteredSpectralSequence z K).page 2).X pq ≅
      (tensorLeft ((koszulComplex z).X (-(pq.2.val : ℤ)))).obj (K.homology t) := by
  let : Module.Free R ((koszulComplex z).X (-(pq.2.val : ℤ))) :=
    (koszulComplex_free_finite_X z (-(pq.2.val : ℤ))).1
  refine koszulFirstPageQuotientIso z K pq ≪≫
    intervalTensorGradeHomologyIso (koszulComplex z) K
      (-((koszulFiltrationIndex e).obj pq.2.castSucc))
      (-((koszulFiltrationIndex e).obj pq.2.succ))
      (-(pq.2.val : ℤ)) (pq.1 + (pq.2.val : ℤ)) t _ ?_ ?_ (by omega)
  · dsimp [koszulFiltrationIndex]
    omega
  · dsimp [koszulFiltrationIndex]
    omega

/-- 概要：有限 Koszul 補助初頁の微分は、係数ホモロジーと Koszul 微分のテンソル。
方針：商模型の初頁微分に区間境界のホモロジー比較を合成する。
規約：源 (s,p+1) と標的 (s+2,p) は共通係数次数 t を持つ。
使われ方：KST Lemma 4.10 の E₂ の Koszul ホモロジー同定。 -/
theorem koszulFirstPage_d_coefficient {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : Fin e) (s t : ℤ)
    (ht : s + 2 * ((p.val : ℤ) + 1) = t) :
    ((koszulFilteredSpectralSequence z K).page 2).d (s, p.succ) (s + 2, p.castSucc) ≫
      (koszulFirstPageCoefficientIsoAt z K (s + 2, p.castSucc) t (by dsimp; omega)).hom =
      (koszulFirstPageCoefficientIsoAt z K (s, p.succ) t (by dsimp; omega)).hom ≫
        ((koszulComplex z).d (-(p.succ.val : ℤ)) (-(p.val : ℤ)) ▷ K.homology t) := by
  let P := koszulComplex z
  let index := koszulFiltrationIndex e
  let i : Fin (e + 2) := p.castSucc.castSucc
  let j : Fin (e + 2) := p.succ.castSucc
  let k : Fin (e + 2) := p.succ.succ
  let f : i ⟶ j := homOfLE (Fin.le_iff_val_le_val.mpr (by
    change p.val ≤ p.val + 1
    omega))
  let g : j ⟶ k := homOfLE (Fin.le_iff_val_le_val.mpr (by
    change p.val + 1 ≤ p.val + 1 + 1
    omega))
  let A := -index.obj i
  let B := -index.obj j
  let C := -index.obj k
  let c := -(p.succ.val : ℤ)
  let d := -(p.val : ℤ)
  let n := s + (p.succ.val : ℤ)
  let n' := s + 2 + (p.val : ℤ)
  let hab := neg_le_neg (index.map f).le
  let hbc := neg_le_neg (index.map g).le
  have ha : A = d + 1 := by dsimp [A, index, i, d, koszulFiltrationIndex]; omega
  have hb : B = d := by dsimp [B, index, j, d, koszulFiltrationIndex]; omega
  have hc : C = c := by dsimp [C, index, k, c, koszulFiltrationIndex]; omega
  have hd : c + 1 = d := by dsimp [c, d]; omega
  have hn : n + 1 = n' := by dsimp [n, n']; omega
  have hs : n - c = t := by dsimp [n, c]; omega
  let : Module.Free R (P.X c) := (koszulComplex_free_finite_X z c).1
  let : Module.Free R (P.X d) := (koszulComplex_free_finite_X z d).1
  let src := intervalTensorGradeHomologyIso P K B C c n t hbc (by omega) hc hs
  let tgt := intervalTensorGradeHomologyIso P K A B d n' t hab ha hb (by omega)
  let S := tensorFiltrationInterval P K index f
  let b := tensorFiltrationBoundary P K index g
  let H := homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  let D := ((koszulFilteredSpectralSequence z K).page 2).d (s, p.succ) (s + 2, p.castSucc)
  let qsrc := (koszulFirstPageQuotientIso z K (s, p.succ)).hom
  let qtgt := (koszulFirstPageQuotientIso z K (s + 2, p.castSucc)).hom
  have hcoef : H.shiftMap (intervalTensorGradeBoundary P K A B C hab hbc)
      n n' (by omega) ≫ tgt.hom = src.hom ≫ (P.d c d ▷ K.homology t) :=
    intervalTensorGradeHomology_differential P K A B C c d n n' t
      hab hbc ha hb hc hd hn hs
  have hshift : H.shiftMap b n n' (by omega) ≫ homologyMap S.g n' =
      H.shiftMap (intervalTensorGradeBoundary P K A B C hab hbc) n n' (by omega) := by
    erw [← H.shiftMap_comp b S.g n n' (by omega)]
    rfl
  change D ≫ (qtgt ≫ tgt.hom) = (qsrc ≫ src.hom) ≫ (P.d c d ▷ K.homology t)
  calc
    _ = (D ≫ qtgt) ≫ tgt.hom := (Category.assoc _ _ _).symm
    _ = (qsrc ≫ H.shiftMap b n n' (by omega) ≫ homologyMap S.g n') ≫ tgt.hom :=
      congrArg (fun f ↦ f ≫ tgt.hom) (koszulFirstPage_d_quotient z K p s)
    _ = qsrc ≫ ((H.shiftMap b n n' (by omega) ≫ homologyMap S.g n') ≫ tgt.hom) := by
      simp only [Category.assoc]
    _ = qsrc ≫ (H.shiftMap (intervalTensorGradeBoundary P K A B C hab hbc)
        n n' (by omega) ≫ tgt.hom) :=
      congrArg (fun f ↦ qsrc ≫ (f ≫ tgt.hom)) hshift
    _ = qsrc ≫ (src.hom ≫ (P.d c d ▷ K.homology t)) :=
      congrArg (fun f ↦ qsrc ≫ f) hcoef
    _ = _ := (Category.assoc _ _ _).symm

end SerrePositivity.KST.ProExcision
