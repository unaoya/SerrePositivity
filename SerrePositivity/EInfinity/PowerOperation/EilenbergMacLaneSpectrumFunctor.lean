module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneOmegaSequence

/-!
# 全複体と厳密な鎖写像からの指定 Eilenberg–Mac Lane スペクトル関手

DAG XIII §2.2、BF 1978 §2 の前段。同じ Ω 列と既存の単射置換を使う。
ここでは通常の圏の関手とその nerve 上の図式を作り、D(A) からの降下は後続とする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (KanPiIsomorphism)
variable (A : Type u) [CommRing A]

/-- 指定 Kan 列の全関手を、証明済みの Ω 条件を持つ充満部分圏へ上げる。 -/
def eilenbergMacLaneOmegaSequenceFunctor : Complex A ⥤ KanOmegaSequence.{u} :=
  kanOmegaSequenceProperty.lift (eilenbergMacLaneSequenceFunctor A)
    (eilenbergMacLaneSequence_omega A)

/-- 同じ逐次単射置換による、全複体上の実スペクトル関手。 -/
def eilenbergMacLaneSpectrumFunctor : Complex A ⥤ KST.Spectra.OmegaSpectrum.{u} :=
  eilenbergMacLaneOmegaSequenceFunctor A ⋙ omegaSequenceReplacementFunctor

/-- 準同型の像は、指定実スペクトルの全段で π 同型。 -/
lemma eilenbergMacLaneSpectrumMap_piIsomorphism {M N : Complex A} (f : M ⟶ N)
    [QuasiIso f] (r : ℕ) :
    KanPiIsomorphism (((eilenbergMacLaneSpectrumFunctor A).map f).app r).right :=
  omegaSequenceReplacementFunctor_piIsomorphism
    ((eilenbergMacLaneOmegaSequenceFunctor A).map f)
    (fun n => levelMap_kanPiIsomorphism f n) r

/-- 通常の複体圏の nerve の厳密な図式を、同じ native Sp へ送る。 -/
def eilenbergMacLaneOrdinaryNative : nerve (Complex A) ⟶ KST.Spectra.Sp.{u} :=
  nerveMap (eilenbergMacLaneOmegaSequenceFunctor A) ≫ omegaSequenceNative

end SerrePositivity.EInfinity.PowerOperation
