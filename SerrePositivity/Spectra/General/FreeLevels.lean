module

public import SerrePositivity.Spectra.SymmetricSequence.FreeConvolution
public import SerrePositivity.Spectra.General.Evaluation

/-! # 自由対称スペクトルの各段の表示と零になる範囲

F_n Xの各段をSym(K)と自由対称列の分解図式で表す。
直和の全単射で添字付けた生成元上の値が射を決定し、n未満の段は零対象となる。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.GeneralSymmetricSpectrum

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] {K : C}

/-- 自由スペクトルの第m段の分解図式。 -/
def freeAtLevelDiagram (n : ℕ) (X : C) (m : ℕ) :
    CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m) ⥤
      C := SymmetricSequence.freeConvolutionDiagram (SymmetricSequence.tensorPowerSequence K) n X m

/-- Sym(K)の段とXから、直和の全単射で指定する自由スペクトルの生成元。 -/
def freeAtLevelGenerator (n : ℕ) (X : C) (m : ℕ)
    (a : FiniteBijection) (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶
      FiniteBijection.of m) :
    (SymmetricSequence.tensorPowerSequence K).obj a ⊗ X ⟶ level ((freeAt (K := K) n).obj X) m :=
  SymmetricSequence.freeConvolutionGenerator (SymmetricSequence.tensorPowerSequence K) n X m a h

/-- n未満の段は始対象。 -/
def freeAtLevelInitial (n : ℕ) (X : C) (m : ℕ) (hm : m < n) :
    IsInitial (level ((freeAt (K := K) n).obj X) m) :=
  SymmetricSequence.freeConvolutionLevelInitial (SymmetricSequence.tensorPowerSequence K) n X m hm

end SerrePositivity.GeneralSymmetricSpectrum
