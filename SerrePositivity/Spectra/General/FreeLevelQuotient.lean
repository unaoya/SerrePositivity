module

public import SerrePositivity.Spectra.SymmetricSequence.FreePermutationAction

public import SerrePositivity.Spectra.General.FreeLevelNaturality

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

/-- 自由スペクトルの作用付き各段と明示的な商表示との自然同型。 -/
def freeAtLevelActionNatIsoBlockQuotient (n m : ℕ) :
    freeAt (K := K) n ⋙ forget K ⋙ SymmetricSequence.levelActionFunctor m ≅
      SymmetricSequence.freeBlockQuotientActionFunctor
        (SymmetricSequence.tensorPowerSequence K) n m :=
  NatIso.ofComponents
    (fun X => SymmetricSequence.freeConvolutionLevelActionIsoBlockQuotient
      (SymmetricSequence.tensorPowerSequence K) n X m) (by
    intro X Y f
    apply Action.hom_ext
    change ((freeAt (K := K) n).map f).hom.app (FiniteBijection.of m) ≫ _ = _
    rw [freeAt_map_underlying]
    exact SymmetricSequence.freeConvolutionLevelIsoBlockQuotient_input
      (SymmetricSequence.tensorPowerSequence K) n f m)

/-- 商を経由した作用付き自然同型は、元の誘導表示との自然同型に一致する。 -/
lemma freeAtLevelActionNatIsoBlockQuotient_trans (n m : ℕ) :
    freeAtLevelActionNatIsoBlockQuotient (K := K) n m ≪≫
        SymmetricSequence.freeBlockQuotientActionNatIsoInduction
          (SymmetricSequence.tensorPowerSequence K) n m =
      freeAtLevelActionNatIsoInduction (K := K) n m := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact congrArg Iso.hom
    (SymmetricSequence.freeConvolutionLevelActionIsoBlockQuotient_trans
      (SymmetricSequence.tensorPowerSequence K) n X m)

/-- 自由スペクトルの第m段と、Σ_mで添字付けた誘導商との比較同型。 -/
def freeAtLevelIsoPermutation (n : ℕ) (X : C) (m : ℕ) (hm : n ≤ m) :
    level ((freeAt (K := K) n).obj X) m ≅
      SymmetricSequence.freePermutationQuotient
        (SymmetricSequence.tensorPowerSequence K) n X m hm :=
  freeAtLevelIsoBlockQuotient (K := K) n X m ≪≫
    SymmetricSequence.freeBlockQuotientIsoPermutation
      (SymmetricSequence.tensorPowerSequence K) n X m hm

/-- 比較同型は全単射の生成元を、対応する置換の生成元へ送る。 -/
@[reassoc] lemma freeAtLevelIsoPermutation_generator (n : ℕ)
    (X : C) (m : ℕ) (hm : n ≤ m)
    (h : SymmetricSequence.FreeBlockIndex n m) :
    freeAtLevelGenerator (K := K) n X m (FiniteBijection.of (m - n)) h ≫
        (freeAtLevelIsoPermutation (K := K) n X m hm).hom =
      SymmetricSequence.freePermutationQuotientGenerator
        (SymmetricSequence.tensorPowerSequence K) n X m hm
        (SymmetricSequence.freePermutationIndex n m hm h) := by
  change freeAtLevelGenerator (K := K) n X m (FiniteBijection.of (m - n)) h ≫
    (freeAtLevelIsoBlockQuotient (K := K) n X m).hom ≫
      SymmetricSequence.freeBlockToPermutationQuotient
        (SymmetricSequence.tensorPowerSequence K) n X m hm = _
  erw [freeAtLevelIsoBlockQuotient_generator_assoc (K := K) n X m h]
  exact SymmetricSequence.freeBlockToPermutationQuotient_generator
    (SymmetricSequence.tensorPowerSequence K) n X m hm h

/-- 自由スペクトルの作用付き各段と、対称群の誘導商との自然同型。 -/
def freeAtLevelActionNatIsoPermutation (n m : ℕ) (hm : n ≤ m) :
    freeAt (K := K) n ⋙ forget K ⋙ SymmetricSequence.levelActionFunctor m ≅
      SymmetricSequence.freePermutationActionFunctor
        (SymmetricSequence.tensorPowerSequence K) n m hm :=
  freeAtLevelActionNatIsoBlockQuotient (K := K) n m ≪≫
    SymmetricSequence.freeBlockActionNatIsoPermutation
      (SymmetricSequence.tensorPowerSequence K) n m hm

/-- 作用付き自然同型は、基礎対象の誘導商への比較同型を持ち上げる。 -/
lemma freeAtLevelActionNatIsoPermutation_hom (n m : ℕ) (hm : n ≤ m)
    (X : C) :
    ((freeAtLevelActionNatIsoPermutation (K := K) n m hm).app X).hom.hom =
      (freeAtLevelIsoPermutation (K := K) n X m hm).hom := rfl

end SerrePositivity.GeneralSymmetricSpectrum
