module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingSourceFunctor
public import SerrePositivity.KST.Spectra.RawSpectrumCotensorSourceNaturality

/-!
概要：元の cotensor 交換を、BF 源全体の点つき前層の自然同型にまとめる。
方針：元の前合成から作った前層と、証明済みの源変数の可換式を使う。
規約：通常の圏上の自然同型。豊穣な自然性は別工程。使われ方：Hom-end 比較の表現可能性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 全 BF 源について自然な、元の点つき Hom と cotensor の交換同型。 -/
def sourceCotensorNatIso (Z : KanSequence.{u}) (A : PointedSimplicialSet.{u}) :
    sourceFunctor (KanSequence.mapping A Z) ≅ sourceFunctor Z ⋙ ihom A :=
  NatIso.ofComponents (fun X ↦ cotensorIso X.unop Z A)
    (fun f ↦ cotensorComparison_pre_source f.unop Z A)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
