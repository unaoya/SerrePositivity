module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInduction
public import SerrePositivity.Spectra.General.FreeLevels

/-! # 自由対称スペクトルの各段の誘導図式による表示

第二ブロックをnに固定し、Sym(K)側の全単射の作用を余極限で同一視する。
各項のSym(K)の次数はm−nであり、比較同型の両方向を生成元と比較する。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.GeneralSymmetricSpectrum

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] {K : C}

/-- 自由スペクトルの第m段を表す、第二ブロックnの誘導図式。 -/
def freeAtLevelInductionDiagram (n : ℕ) (X : C) (m : ℕ) :
    CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m) ⥤
      C :=
  SymmetricSequence.freeInductionDiagram (SymmetricSequence.tensorPowerSequence K) n X m

/-- 自由スペクトルの各段は誘導図式の余極限。 -/
def freeAtLevelIsoInduction (n : ℕ) (X : C) (m : ℕ) :
    level ((freeAt (K := K) n).obj X) m ≅ colimit (freeAtLevelInductionDiagram (K := K) n X m) :=
  SymmetricSequence.freeConvolutionLevelIsoInduction (SymmetricSequence.tensorPowerSequence K) n X m

end SerrePositivity.GeneralSymmetricSpectrum
