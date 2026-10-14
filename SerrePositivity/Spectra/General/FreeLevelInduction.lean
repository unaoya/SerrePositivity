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

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 誘導図式の各項は、m−n次Sym(K)とXのtensor。 -/
lemma freeAtLevelInductionDiagram_obj (n : ℕ) (X : C) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    (freeAtLevelInductionDiagram (K := K) n X m).obj d = TensorPowers.power K (m - n) ⊗ X :=
  SymmetricSequence.freeInductionDiagram_obj (SymmetricSequence.tensorPowerSequence K) n X m d

/-- 自由スペクトルの各段は誘導図式の余極限。 -/
def freeAtLevelIsoInduction (n : ℕ) (X : C) (m : ℕ) :
    level ((freeAt (K := K) n).obj X) m ≅ colimit (freeAtLevelInductionDiagram (K := K) n X m) :=
  SymmetricSequence.freeConvolutionLevelIsoInduction (SymmetricSequence.tensorPowerSequence K) n X m

/-- 比較同型は生成元を誘導図式の標準包含へ送る。 -/
@[reassoc (attr := simp)] lemma freeAtLevelIsoInduction_generator
    (n : ℕ) (X : C) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    freeAtLevelGenerator (K := K) n X m d.left d.hom ≫
      (freeAtLevelIsoInduction (K := K) n X m).hom =
      colimit.ι (freeAtLevelInductionDiagram (K := K) n X m) d :=
  SymmetricSequence.freeConvolutionLevelIsoInduction_generator
    (SymmetricSequence.tensorPowerSequence K) n X m d

/-- 逆同型は誘導図式の標準包含を自由スペクトルの生成元へ戻す。 -/
@[reassoc (attr := simp)] lemma freeAtLevelIsoInduction_inclusion
    (n : ℕ) (X : C) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    colimit.ι (freeAtLevelInductionDiagram (K := K) n X m) d ≫
      (freeAtLevelIsoInduction (K := K) n X m).inv =
      freeAtLevelGenerator (K := K) n X m d.left d.hom :=
  SymmetricSequence.freeConvolutionLevelIsoInduction_inclusion
    (SymmetricSequence.tensorPowerSequence K) n X m d

/-- 射の決定にはm−n次Sym(K)からの生成元だけで十分。 -/
lemma freeAtLevel_hom_ext_standard (n : ℕ) (X : C) (m : ℕ)
    {Y : C} (f g : level ((freeAt (K := K) n).obj X) m ⟶ Y)
    (h : ∀ k : FiniteBijection.sumObj (FiniteBijection.of (m - n))
        (FiniteBijection.of n) ⟶ FiniteBijection.of m,
      freeAtLevelGenerator (K := K) n X m (FiniteBijection.of (m - n)) k ≫ f =
        freeAtLevelGenerator (K := K) n X m (FiniteBijection.of (m - n)) k ≫ g) : f = g :=
  SymmetricSequence.freeConvolutionLevel_hom_ext_standard
    (SymmetricSequence.tensorPowerSequence K) n X m f g h

end SerrePositivity.GeneralSymmetricSpectrum
