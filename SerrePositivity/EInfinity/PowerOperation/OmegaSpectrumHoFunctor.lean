module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyComparison

/-!
# 元の Ω スペクトルの通常関手と native Sp の整数 π 関手の比較

DAG XIII §2.2 の実 π/H 比較の補助。BF 射の同じ coherent な辺の類を使う。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants

/-- 元の BF 対象と射を、native Sp の実際のホモトピー圏へ送る関手。 -/
def omegaSpectrumHoFunctor : OmegaSpectrum.{u} ⥤ hoFunctor.obj Sp.{u} where
  obj := SpectrumHo.obj
  map f := SpectrumHo.hom f
  map_id X := SpectrumHo.hom_id X
  map_comp f g := SpectrumHo.hom_comp f g

/-- native Sp の π_j と、元の BF 整数次数群の全関手の自然同型。 -/
def omegaSpectrumHoPiComparison (j : ℤ) :
    omegaSpectrumHoFunctor.{u} ⋙ SpectrumHo.piFunctor j ≅ OmegaSpectrum.homotopyFunctor j :=
  NatIso.ofComponents (fun X => SpectrumHo.piComparison X j)
    (fun f => SpectrumHo.piComparison_naturality f j)

end SerrePositivity.EInfinity.PowerOperation
