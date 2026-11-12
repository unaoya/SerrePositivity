module

public import SerrePositivity.EInfinity.PowerOperation.OmegaSpectrumHoFunctor
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSpectrumHomologyIso

/-!
# 元の実 EM スペクトルの native Sp の π/H 自然同型

DAG XIII §2.2 の π/H 比較。全複体の通常関手上で、native Sp の実際の π 関手に
BF の整数次数群の比較をつなぐ。既存 D(A) 上への比較は後続とする。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
variable (A : Type u) [CommRing A]

/-- 同じ実 EM スペクトルを native Sp で読んだ π_j/H^{-j} の全自然同型。 -/
def eilenbergMacLaneNativeHomologyIso (j : ℤ) :
    (eilenbergMacLaneSpectrumFunctor A ⋙ omegaSpectrumHoFunctor) ⋙ SpectrumHo.piFunctor j ≅
      complexMultiplicativeCohomology A j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (eilenbergMacLaneSpectrumFunctor A) (omegaSpectrumHoPiComparison j) ≪≫
      eilenbergMacLaneSpectrumHomologyIso A j

end SerrePositivity.EInfinity.PowerOperation
