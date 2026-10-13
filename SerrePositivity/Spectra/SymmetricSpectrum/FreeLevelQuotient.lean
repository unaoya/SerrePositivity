module

public import SerrePositivity.Spectra.SymmetricSequence.FreeBlockQuotient
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeLevelAction

/-! # 自由対称スペクトルの各段のブロック商表示

全単射で添字付けたm−n次球面とXのsmashの余積を、第一ブロックの対称群の関係式で割る。
その余等化子を自由スペクトルの第m段と比較する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- m−n次球面とXのsmashの余積を、球面側の対称群の関係式で割った商。 -/
def freeAtLevelBlockQuotient (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    PointedSimplicialSet.{u} :=
  SymmetricSequence.freeBlockQuotient sphereSequence.{u} n X m

/-- 全単射の添字に対応する、ブロック商の生成元。 -/
def freeAtLevelBlockGenerator (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    (h : SymmetricSequence.FreeBlockIndex n m) :
    spherePower.{u} (m - n) ⊗ X ⟶ freeAtLevelBlockQuotient n X m :=
  SymmetricSequence.freeBlockQuotientGenerator sphereSequence.{u} n X m h

/-- 商の関係式は球面の置換作用と、添字へのブロック置換の前合成を同一視する。 -/
@[reassoc] lemma freeAtLevelBlockGenerator_relation (n : ℕ) (X : PointedSimplicialSet.{u})
    (m : ℕ) (σ : Equiv.Perm (Fin (m - n))) (h : SymmetricSequence.FreeBlockIndex n m) :
    (spherePermutationAction.{u} (m - n) σ).asIso.hom ▷ X ≫
        freeAtLevelBlockGenerator n X m h =
      freeAtLevelBlockGenerator n X m
        (FiniteBijection.sumMap (FiniteBijection.permutation (m - n) σ) (𝟙 _) ≫ h) := by
  exact SymmetricSequence.freeBlockQuotientGenerator_relation sphereSequence.{u} n X m σ h

/-- 自由スペクトルの第m段と、球面側のブロック作用で割った余等化子との比較。 -/
def freeAtLevelIsoBlockQuotient (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    level ((freeAt n).obj X) m ≅ freeAtLevelBlockQuotient n X m :=
  SymmetricSequence.freeConvolutionLevelIsoBlockQuotient sphereSequence.{u} n X m

/-- 比較同型は自由スペクトルの生成元を商の生成元へ送る。 -/
@[reassoc] lemma freeAtLevelIsoBlockQuotient_generator (n : ℕ) (X : PointedSimplicialSet.{u})
    (m : ℕ) (h : SymmetricSequence.FreeBlockIndex n m) :
    freeAtLevelGenerator n X m (FiniteBijection.of (m - n)) h ≫
        (freeAtLevelIsoBlockQuotient n X m).hom = freeAtLevelBlockGenerator n X m h :=
  SymmetricSequence.freeConvolutionLevelIsoBlockQuotient_generator sphereSequence.{u} n X m h

/-- 比較同型の逆は商の生成元を自由スペクトルの生成元へ戻す。 -/
@[reassoc] lemma freeAtLevelIsoBlockQuotient_inverse (n : ℕ) (X : PointedSimplicialSet.{u})
    (m : ℕ) (h : SymmetricSequence.FreeBlockIndex n m) :
    freeAtLevelBlockGenerator n X m h ≫ (freeAtLevelIsoBlockQuotient n X m).inv =
      freeAtLevelGenerator n X m (FiniteBijection.of (m - n)) h :=
  SymmetricSequence.freeConvolutionLevelIsoBlockQuotient_inverse sphereSequence.{u} n X m h

/-- 明示的なブロック商と、既存の誘導図式の余極限との比較。 -/
def freeAtLevelBlockQuotientIsoInduction (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    freeAtLevelBlockQuotient n X m ≅ colimit (freeAtLevelInductionDiagram n X m) :=
  SymmetricSequence.freeBlockQuotientIsoInduction sphereSequence.{u} n X m

/-- n未満の段では、ブロック商も零対象となる。 -/
lemma freeAtLevelBlockQuotient_isZero (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    (hm : m < n) : IsZero (freeAtLevelBlockQuotient n X m) :=
  (freeAtLevel_isZero n X m hm).of_iso (freeAtLevelIsoBlockQuotient n X m).symm

end SerrePositivity.SymmetricSpectrum
