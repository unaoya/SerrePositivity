module

public import SerrePositivity.KST.ProExcision.ParameterQuotient
public import SerrePositivity.KST.ProExcision.KoszulConeVanishing

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# Koszul ホモロジーの通常冪商との pro 比較

概要：通常の生成イデアル商から Koszul 複体のホモロジーへの比較を完成する。
方針：通常商と反復商の自然同型、列長帰納法による cone 比較を合成する。
規約：複体の各ホモロジーが有限生成。複体の各項の有限性は要求しない。
使われ方：KST Lemma 4.10 の複体模型。単体環の π との同定は K-L9 の界面で供給する。
原典のスペクトル系列証明とは異なり、cone 長完全列と対角の共終性を用いる。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- 概要：通常のパラメータ冪イデアル商から実 Koszul cone ホモロジーへの標準比較。
方針：始域を反復商へ自然に同定し、cone 長完全列による比較と合成する。
規約：全ての冪遷移と可換するレベル射。
使われ方：KST Lemma 4.10。単体環の π への移送には K-L9 の模型同定を使う。 -/
def koszul_comparison {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    LevelHom (parameterQuotientTower z (K.homology i))
      ((koszulConeTower z K).map (homologyFunctor _ _ i)) :=
  LevelHom.comp (parameterQuotientComparison z (K.homology i)) (koszulConeComparison z K i)

/-- 概要：通常のパラメータ冪商と Koszul ホモロジーは pro 同型。
方針：通常商の自然同型と、長完全列による列長帰納法の比較を合成する。
規約：Noether 環、次数ごとに有限な係数ホモロジー。有界性・項の平坦性は不要。
使われ方：KST Lemma 4.10 の複体模型。原典のスペクトル系列 API は使用しない。 -/
theorem koszul_comparison_isProIso [IsNoetherianRing R] {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, Module.Finite R (K.homology i)) (i : ℤ) : IsProIso (koszul_comparison z K i) :=
  IsProIso.comp (parameterQuotientComparison_isProIso z (K.homology i))
    (koszulConeComparison_isProIso z K hK i)

end SerrePositivity.KST.ProExcision
