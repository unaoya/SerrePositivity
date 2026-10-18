module

public import SerrePositivity.KST.ProExcision.IntervalCut

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Koszul 補助初頁の商モデルにおける微分

概要：有限 Koszul 濾過の初頁微分を実際の商短完全列の分裂境界で表す。
方針：Mathlib の初頁計算と、再添字項濾過の δ の商比較を合成する。
規約：Mathlib の頁 2 は KST の E₁ であり、次頁の同定とは区別する。
使われ方：KST Lemma 4.10 の初頁微分と Koszul 微分の比較。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：Koszul 補助初頁を、実際の濾過区間の商ホモロジーで表す。
方針：初頁の区間同型に、cone から商への擬同型を合成する。
規約：標準の商射を使う。使われ方：KST Lemma 4.10 の微分の商モデル。 -/
def koszulFirstPageQuotientIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (pq : ℤ × Fin (e + 1)) :
    ((koszulFilteredSpectralSequence z K).page 2).X pq ≅
      (tensorFiltrationInterval (koszulComplex z) K (koszulFiltrationIndex e)
        (homOfLE (show pq.2.castSucc ≤ pq.2.succ by
          simp [Fin.le_iff_val_le_val]))).X₃.homology (pq.1 + (pq.2.val : ℤ)) :=
  koszulFirstPageXIso z K pq ≪≫
    tensorFiltrationIntervalHomologyIso (koszulComplex z) K (koszulFiltrationIndex e) _ _

/-- 概要：補助初頁の二つの隣接行の微分は、区間の分裂境界と左の商射のホモロジー写像。
方針：初頁微分の δ 表示を商ホモロジー同型で移し、実際の区間境界公式を使う。
規約：源は (s,p+1)、標的は (s+2,p)。使われ方：KST Lemma 4.10 の E₁ 微分。 -/
theorem koszulFirstPage_d_quotient {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : Fin e) (s : ℤ) :
    let i : Fin (e + 2) := p.castSucc.castSucc
    let j : Fin (e + 2) := p.succ.castSucc
    let k : Fin (e + 2) := p.succ.succ
    let f : i ⟶ j := homOfLE (Fin.le_iff_val_le_val.mpr (by
      change p.val ≤ p.val + 1
      omega))
    let g : j ⟶ k := homOfLE (Fin.le_iff_val_le_val.mpr (by
      change p.val + 1 ≤ p.val + 1 + 1
      omega))
    let S := tensorFiltrationInterval (koszulComplex z) K (koszulFiltrationIndex e) f
    ((koszulFilteredSpectralSequence z K).page 2).d (s, p.succ) (s + 2, p.castSucc) ≫
      (koszulFirstPageQuotientIso z K (s + 2, p.castSucc)).hom =
      (koszulFirstPageQuotientIso z K (s, p.succ)).hom ≫
        (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
          (tensorFiltrationBoundary (koszulComplex z) K (koszulFiltrationIndex e) g)
          (s + (p.succ.val : ℤ)) (s + 2 + (p.val : ℤ)) (by simp; omega) ≫
        homologyMap S.g (s + 2 + (p.val : ℤ)) := by
  dsimp only
  let X := koszulFilteredSpectralObject z K
  let data := Abelian.SpectralObject.coreE₂CohomologicalFin (e + 1)
  have hpq : (ComplexShape.spectralSequenceFin (e + 1) (2, 1 - 2)).Rel
      (s, p.succ) (s + 2, p.castSucc) := by
    simp only [ComplexShape.spectralSequenceFin_rel_iff, Fin.val_succ, Fin.val_castSucc]
    constructor <;> push_cast <;> omega
  erw [X.spectralSequence_first_page_d_eq data _ _ hpq
    p.castSucc.castSucc p.succ.castSucc p.succ.succ rfl rfl rfl
    (s + (p.succ.val : ℤ)) (s + 2 + (p.val : ℤ)) rfl (by simp; omega)]
  simp only [koszulFirstPageQuotientIso, koszulFirstPageXIso, Iso.trans_hom, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  congr 1
  exact tensorFiltration_delta_quotientIso (koszulComplex z) K (koszulFiltrationIndex e)
    (homOfLE (show p.castSucc.castSucc ≤ p.succ.castSucc by
      simp [Fin.le_iff_val_le_val]))
    (homOfLE (show p.succ.castSucc ≤ p.succ.succ by
      simp [Fin.le_iff_val_le_val]))
    (s + (p.succ.val : ℤ)) (s + 2 + (p.val : ℤ)) (by simp; omega)

end SerrePositivity.KST.ProExcision
