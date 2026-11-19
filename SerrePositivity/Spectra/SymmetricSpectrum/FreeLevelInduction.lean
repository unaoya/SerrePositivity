module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInduction
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeLevels

/-! # 自由対称スペクトルの各段の誘導図式による表示

第二ブロックをnに固定し、球面側の全単射の作用を余極限で同一視する。
各項の球面の次数はm−nであり、比較同型の両方向を生成元と比較する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 自由スペクトルの第m段を表す、第二ブロックnの誘導図式。 -/
def freeAtLevelInductionDiagram (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m) ⥤
      PointedSimplicialSet.{u} :=
  SymmetricSequence.freeInductionDiagram sphereSequence n X m

/-- 誘導図式の各項は、m−n次球面とXのsmash。 -/
lemma freeAtLevelInductionDiagram_obj (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    (freeAtLevelInductionDiagram n X m).obj d = spherePower.{u} (m - n) ⊗ X :=
  SymmetricSequence.freeInductionDiagram_obj sphereSequence n X m d

/-- 自由スペクトルの各段は誘導図式の余極限。 -/
def freeAtLevelIsoInduction (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    level ((freeAt n).obj X) m ≅ colimit (freeAtLevelInductionDiagram n X m) :=
  SymmetricSequence.freeConvolutionLevelIsoInduction sphereSequence n X m

/-- 比較同型は生成元を誘導図式の標準包含へ送る。 -/
@[reassoc (attr := simp)] lemma freeAtLevelIsoInduction_generator
    (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    freeAtLevelGenerator n X m d.left d.hom ≫ (freeAtLevelIsoInduction n X m).hom =
      colimit.ι (freeAtLevelInductionDiagram n X m) d :=
  SymmetricSequence.freeConvolutionLevelIsoInduction_generator sphereSequence n X m d

/-- 逆同型は誘導図式の標準包含を自由スペクトルの生成元へ戻す。 -/
@[reassoc (attr := simp)] lemma freeAtLevelIsoInduction_inclusion
    (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    colimit.ι (freeAtLevelInductionDiagram n X m) d ≫ (freeAtLevelIsoInduction n X m).inv =
      freeAtLevelGenerator n X m d.left d.hom :=
  SymmetricSequence.freeConvolutionLevelIsoInduction_inclusion sphereSequence n X m d

/-- 射の決定にはm−n次球面からの生成元だけで十分。 -/
lemma freeAtLevel_hom_ext_standard (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    {Y : PointedSimplicialSet.{u}} (f g : level ((freeAt n).obj X) m ⟶ Y)
    (h : ∀ k : FiniteBijection.sumObj (FiniteBijection.of (m - n))
        (FiniteBijection.of n) ⟶ FiniteBijection.of m,
      freeAtLevelGenerator n X m (FiniteBijection.of (m - n)) k ≫ f =
        freeAtLevelGenerator n X m (FiniteBijection.of (m - n)) k ≫ g) : f = g :=
  SymmetricSequence.freeConvolutionLevel_hom_ext_standard sphereSequence n X m f g h

end SerrePositivity.SymmetricSpectrum
