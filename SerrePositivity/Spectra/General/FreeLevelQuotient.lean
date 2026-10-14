module

public import SerrePositivity.Spectra.SymmetricSequence.FreeBlockQuotient
public import SerrePositivity.Spectra.General.FreeLevelInduction

/-! # 自由対称スペクトルの各段のブロック商表示

全単射で添字付けたm−n次Sym(K)とXのtensorの余積を、第一ブロックの対称群の関係式で割る。
その余等化子を自由スペクトルの第m段と比較する。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.GeneralSymmetricSpectrum

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] {K : C}

/-- m−n次Sym(K)とXのtensorの余積を、Sym(K)側の対称群の関係式で割った商。 -/
def freeAtLevelBlockQuotient (n : ℕ) (X : C) (m : ℕ) :
    C :=
  SymmetricSequence.freeBlockQuotient (SymmetricSequence.tensorPowerSequence K) n X m

/-- 全単射の添字に対応する、ブロック商の生成元。 -/
def freeAtLevelBlockGenerator (n : ℕ) (X : C) (m : ℕ)
    (h : SymmetricSequence.FreeBlockIndex n m) :
    TensorPowers.power K (m - n) ⊗ X ⟶ freeAtLevelBlockQuotient (K := K) n X m :=
  SymmetricSequence.freeBlockQuotientGenerator (SymmetricSequence.tensorPowerSequence K) n X m h

omit [MonoidalClosed C] in
/-- 商の関係式はSym(K)の置換作用と、添字へのブロック置換の前合成を同一視する。 -/
@[reassoc] lemma freeAtLevelBlockGenerator_relation (n : ℕ) (X : C)
    (m : ℕ) (σ : Equiv.Perm (Fin (m - n))) (h : SymmetricSequence.FreeBlockIndex n m) :
    (SymmetricSequence.tensorPowerSequence K).map
        (FiniteBijection.permutation (m - n) σ) ▷ X ≫
        freeAtLevelBlockGenerator (K := K) n X m h =
      freeAtLevelBlockGenerator (K := K) n X m
        (FiniteBijection.sumMap (FiniteBijection.permutation (m - n) σ) (𝟙 _) ≫ h) := by
  exact SymmetricSequence.freeBlockQuotientGenerator_relation
    (SymmetricSequence.tensorPowerSequence K) n X m σ h

/-- 自由スペクトルの第m段と、Sym(K)側のブロック作用で割った余等化子との比較。 -/
def freeAtLevelIsoBlockQuotient (n : ℕ) (X : C) (m : ℕ) :
    level ((freeAt (K := K) n).obj X) m ≅ freeAtLevelBlockQuotient (K := K) n X m :=
  SymmetricSequence.freeConvolutionLevelIsoBlockQuotient
    (SymmetricSequence.tensorPowerSequence K) n X m

/-- 比較同型は自由スペクトルの生成元を商の生成元へ送る。 -/
@[reassoc] lemma freeAtLevelIsoBlockQuotient_generator (n : ℕ) (X : C)
    (m : ℕ) (h : SymmetricSequence.FreeBlockIndex n m) :
    freeAtLevelGenerator (K := K) n X m (FiniteBijection.of (m - n)) h ≫
        (freeAtLevelIsoBlockQuotient (K := K) n X m).hom =
        freeAtLevelBlockGenerator (K := K) n X m h :=
  SymmetricSequence.freeConvolutionLevelIsoBlockQuotient_generator
    (SymmetricSequence.tensorPowerSequence K) n X m h

/-- 比較同型の逆は商の生成元を自由スペクトルの生成元へ戻す。 -/
@[reassoc] lemma freeAtLevelIsoBlockQuotient_inverse (n : ℕ) (X : C)
    (m : ℕ) (h : SymmetricSequence.FreeBlockIndex n m) :
    freeAtLevelBlockGenerator (K := K) n X m h ≫ (freeAtLevelIsoBlockQuotient (K := K) n X m).inv =
      freeAtLevelGenerator (K := K) n X m (FiniteBijection.of (m - n)) h :=
  SymmetricSequence.freeConvolutionLevelIsoBlockQuotient_inverse
    (SymmetricSequence.tensorPowerSequence K) n X m h

/-- 明示的なブロック商と、既存の誘導図式の余極限との比較。 -/
def freeAtLevelBlockQuotientIsoInduction (n : ℕ) (X : C) (m : ℕ) :
    freeAtLevelBlockQuotient (K := K) n X m ≅
      colimit (freeAtLevelInductionDiagram (K := K) n X m) :=
  SymmetricSequence.freeBlockQuotientIsoInduction (SymmetricSequence.tensorPowerSequence K) n X m

/-- n未満の段では、ブロック商も零対象となる。 -/
lemma freeAtLevelBlockQuotient_isZero [HasZeroObject C] (n : ℕ) (X : C) (m : ℕ)
    (hm : m < n) : IsZero (freeAtLevelBlockQuotient (K := K) n X m) :=
  (freeAtLevel_isZero (K := K) n X m hm).of_iso (freeAtLevelIsoBlockQuotient (K := K) n X m).symm

end SerrePositivity.GeneralSymmetricSpectrum
