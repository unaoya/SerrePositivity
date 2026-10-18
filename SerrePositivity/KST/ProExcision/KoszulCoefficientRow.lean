module

public import SerrePositivity.KST.ProExcision.FiniteKoszulShape
public import SerrePositivity.KST.ProExcision.SupportedRestriction

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 有限 Koszul 初頁の一行と次頁

概要：係数次数を固定した初頁の一行を、係数付き Koszul 複体の有限制限へ同定する。
方針：微分に適合する初頁係数同型を成分とし、閉じた行への制限ホモロジーを使う。
規約：Mathlib の頁 3 が KST の E₂ に対応する。
使われ方：KST Lemma 4.10 の Koszul ホモロジーによる次頁計算。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：係数付き Koszul 複体を実際に残る有限次数へ制限する。
方針：項ごとの右テンソル関手を適用し、有限整数埋め込みへ制限する。
規約：行 p は整数次数 -p。使われ方：KST Lemma 4.10 の有限な係数複体。 -/
def koszulCoefficientFiniteComplex {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) :
    HomologicalComplex (ModuleCat.{u} R) (finiteKoszulShape e) :=
  (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj (koszulComplex z)).restriction
    (finiteKoszulIntEmbedding e)

/-- 概要：固定係数次数の補助初頁の一行を複体として取り出す。
方針：微分元・微分先について閉じた形状埋め込みに制限する。
規約：係数次数 t の位置は (t-2p,p)。使われ方：KST Lemma 4.10 の次頁の計算。 -/
def koszulFirstPageFiniteRow {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (t : ℤ) :
    HomologicalComplex (ModuleCat.{u} R) (finiteKoszulShape e) :=
  ((koszulFilteredSpectralSequence z K).page 2).restriction (finiteKoszulSpectralEmbedding e t)

/-- 概要：初頁微分の係数比較を、等しい標的第一座標の任意表示へ移す。
方針：標的座標の等式で置換し、既証の微分比較を使う。
規約：係数次数の証明も同時に移す。使われ方：KST Lemma 4.10 の有限行の複体同型。 -/
theorem koszulFirstPage_d_coefficient_of_eq {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : Fin e) (s s' t : ℤ)
    (h : s + 2 = s') (ht : s + 2 * ((p.val : ℤ) + 1) = t)
    (ht' : s' + 2 * (p.val : ℤ) = t) :
    ((koszulFilteredSpectralSequence z K).page 2).d (s, p.succ) (s', p.castSucc) ≫
      (koszulFirstPageCoefficientIsoAt z K (s', p.castSucc) t ht').hom =
      (koszulFirstPageCoefficientIsoAt z K (s, p.succ) t (by dsimp; omega)).hom ≫
        ((koszulComplex z).d (-(p.succ.val : ℤ)) (-(p.val : ℤ)) ▷ K.homology t) := by
  subst s'
  exact koszulFirstPage_d_coefficient z K p s t ht

/-- 概要：固定係数次数の初頁の一行は、係数付き Koszul 複体の有限制限と同型。
方針：初頁係数同型を成分とし、実際の初頁微分の Koszul 微分比較を使う。
規約：端に存在しない微分は形状が扱う。使われ方：KST Lemma 4.10 の E₂ 同定。 -/
def koszulFirstPageFiniteRowIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (t : ℤ) :
    koszulFirstPageFiniteRow z K t ≅ koszulCoefficientFiniteComplex z (K.homology t) := by
  refine Hom.isoOfComponents
    (fun p ↦ koszulFirstPageCoefficientIsoAt z K (t - 2 * (p.val : ℤ), p) t (by dsimp; omega)) ?_
  intro i j hij
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  change j + 1 = i at hij
  subst i
  let p : Fin e := ⟨j, by omega⟩
  let s := t - 2 * ((j + 1 : ℕ) : ℤ)
  have htgt : t - 2 * (j : ℤ) = s + 2 := by dsimp [s]; omega
  symm
  change ((koszulFilteredSpectralSequence z K).page 2).d
      (s, p.succ) (t - 2 * (j : ℤ), p.castSucc) ≫
      (koszulFirstPageCoefficientIsoAt z K (t - 2 * (j : ℤ), p.castSucc) t (by dsimp [p]; omega)).hom =
    (koszulFirstPageCoefficientIsoAt z K (s, p.succ) t (by dsimp [p, s]; omega)).hom ≫
      ((koszulComplex z).d (-(p.succ.val : ℤ)) (-(p.val : ℤ)) ▷ K.homology t)
  exact koszulFirstPage_d_coefficient_of_eq z K p s (t - 2 * (j : ℤ)) t htgt.symm
    (by dsimp [s, p]; omega) (by dsimp [p]; omega)

/-- 概要：補助頁 3 の項は、固定係数次数の有限 Koszul 係数複体のホモロジー。
方針：スペクトル系列の頁間同型、閉じた行への制限、初頁の複体同型を合成する。
規約：これは KST E₂ の有限次数模型であり、全 Koszul 複体への比較は別段階。
使われ方：KST Lemma 4.10 の次頁計算。 -/
def koszulSecondPageFiniteIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (t : ℤ) (p : Fin (e + 1)) :
    ((koszulFilteredSpectralSequence z K).page 3).X (t - 2 * (p.val : ℤ), p) ≅
      (koszulCoefficientFiniteComplex z (K.homology t)).homology p :=
  ((koszulFilteredSpectralSequence z K).iso 2 3 (t - 2 * (p.val : ℤ), p)).symm ≪≫
    (closedRestrictionHomologyIso ((koszulFilteredSpectralSequence z K).page 2)
      (finiteKoszulSpectralEmbedding e t) p).symm ≪≫
    (homologyFunctor (ModuleCat.{u} R) (finiteKoszulShape e) p).mapIso
      (koszulFirstPageFiniteRowIso z K t)

/-- 概要：補助頁 3、すなわち KST E₂ は、係数付き全 Koszul 複体のホモロジー。
方針：有限模型の次頁同型に、項の台から得た全複体へのホモロジー比較を続ける。
規約：係数は H_t(K)、整数 Koszul 次数は -p。使われ方：KST Lemma 4.10 の E₂ 計算。 -/
def koszulSecondPageIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (t : ℤ) (p : Fin (e + 1)) :
    ((koszulFilteredSpectralSequence z K).page 3).X (t - 2 * (p.val : ℤ), p) ≅
      ((((tensorRight (K.homology t)).mapHomologicalComplex (.up ℤ)).obj
        (koszulComplex z)).homology (-(p.val : ℤ))) :=
  koszulSecondPageFiniteIso z K t p ≪≫
    supportedRestrictionHomologyIso
      (((tensorRight (K.homology t)).mapHomologicalComplex (.up ℤ)).obj (koszulComplex z))
      (finiteKoszulIntEmbedding e) p

end SerrePositivity.KST.ProExcision
