module

public import SerrePositivity.KST.ProExcision.FiniteKoszulShape
public import Mathlib.Algebra.Homology.Embedding.HomEquiv

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 台の上への制限と零延長の比較

概要：埋め込みの像の外で項が零の複体は、像への制限を零延長すると元に戻る。
方針：既存の liftExtend を恒等射へ適用し、各成分の同型性を証明する。
規約：埋め込みの像が前後の微分について閉じる必要はない。
使われ方：KST Lemma 4.10 の有限 Koszul 係数複体の全体への比較。
-/

universe u v w

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- 概要：像の外で項が零の複体と、その制限の零延長は同型。
方針：下端境界から入る射は零対象を通るため、恒等射を零延長へ持ち上げられる。
規約：複体の台は項ごとの零性で指定する。使われ方：KST Lemma 4.10 の端を含む有限制限。 -/
def supportedRestrictionExtendIso
    {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
    {C : Type v} [Category.{w} C] [Abelian C]
    (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]
    [K.IsStrictlySupported e] : K ≅ (K.restriction e).extend e := by
  have hφ : e.HasLift (𝟙 (K.restriction e)) := by
    intro j hj i' hi'
    exact (K.isZero_X_of_isStrictlySupported e i' (hj.notMem hi')).eq_of_src _ _
  let f := e.liftExtend (𝟙 (K.restriction e)) hφ
  have hf (i' : J) : IsIso (f.f i') := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      exact (e.isIso_liftExtend_f_iff (𝟙 (K.restriction e)) hφ hi).mpr (by infer_instance)
    · exact (K.isZero_X_of_isStrictlySupported e i' (fun i hi ↦ hi' ⟨i, hi⟩)).isIso
        ((K.restriction e).isZero_extend_X e i' (fun i hi ↦ hi' ⟨i, hi⟩)) (f.f i')
  have := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

/-- 概要：像の外で項が零の複体は、像への制限で対応するホモロジーを保つ。
方針：零延長ホモロジーの同型と、台から得た零延長との同型を合成する。
規約：端で前後の添字が像の外へ出る場合も含む。
使われ方：KST Lemma 4.10 の有限 Koszul 行から全 Koszul ホモロジーへの移行。 -/
def supportedRestrictionHomologyIso
    {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
    {C : Type v} [Category.{w} C] [Abelian C]
    (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]
    [K.IsStrictlySupported e] (p : I) :
    (K.restriction e).homology p ≅ K.homology (e.f p) :=
  ((K.restriction e).extendHomologyIso e rfl).symm ≪≫
    (homologyFunctor C c' (e.f p)).mapIso (supportedRestrictionExtendIso K e).symm

/-- 概要：有限 Koszul 整数埋め込みの像は整数区間 [-e,0]。
方針：有限行の値の上下界を使い、逆向きには -q の自然数化を行う。
規約：両端を含む。使われ方：KST Lemma 4.10 の Koszul 複体の台の指定。 -/
theorem finiteKoszulIntEmbedding_mem_iff (e : ℕ) (q : ℤ) :
    (∃ p, (finiteKoszulIntEmbedding e).f p = q) ↔ -(e : ℤ) ≤ q ∧ q ≤ 0 := by
  constructor
  · rintro ⟨p, hp⟩
    change -(p.val : ℤ) = q at hp
    have := p.isLt
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨⟨(-q).toNat, by omega⟩, ?_⟩
    change -(((-q).toNat : ℕ) : ℤ) = q
    omega

variable {R : Type u} [CommRing R]

/-- 概要：項ごとに係数をテンソルした Koszul 複体の台は有限整数区間に含まれる。
方針：元の Koszul 項の上下界とテンソル関手の零対象保存を使う。
規約：係数の平坦性・有限性は不要。使われ方：KST Lemma 4.10 の有限係数複体の比較。 -/
instance koszulCoefficientComplex_isStrictlySupported
    {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) :
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex (.up ℤ)).obj
      (koszulComplex z)).IsStrictlySupported (finiteKoszulIntEmbedding e) where
  isZero q hq := by
    have hn : ¬ (∃ p, (finiteKoszulIntEmbedding e).f p = q) := by
      rintro ⟨p, hp⟩
      exact hq p hp
    have hz : IsZero ((koszulComplex z).X q) := by
      by_cases hpos : 0 < q
      · exact koszulComplex_isZero_X_of_pos z q hpos
      · exact koszulComplex_isZero_X_of_lt z q (by
          have := mt (finiteKoszulIntEmbedding_mem_iff e q).mpr hn
          omega)
    exact (CategoryTheory.MonoidalCategory.tensorRight M).map_isZero hz

end SerrePositivity.KST.ProExcision
