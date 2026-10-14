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

omit [MonoidalClosed C] in
/-- 分解の各項は、Sym(K)と全単射で添字付けたXの余積とのtensor。 -/
lemma freeAtLevelDiagram_obj (n : ℕ) (X : C) (m : ℕ)
    (d : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m)) :
    (freeAtLevelDiagram (K := K) n X m).obj d =
      TensorPowers.power K (FiniteBijection.card d.left.1) ⊗
      ∐ (fun _ : FiniteBijection.of n ⟶ d.left.2 => X) := rfl

/-- 自由スペクトルの各段の余極限表示。 -/
def freeAtLevelIsoColimit (n : ℕ) (X : C) (m : ℕ) :
    level ((freeAt (K := K) n).obj X) m ≅ colimit (freeAtLevelDiagram (K := K) n X m) :=
  SymmetricSequence.freeConvolutionLevelIsoColimit (SymmetricSequence.tensorPowerSequence K) n X m

/-- Sym(K)の段とXから、直和の全単射で指定する自由スペクトルの生成元。 -/
def freeAtLevelGenerator (n : ℕ) (X : C) (m : ℕ)
    (a : FiniteBijection) (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶
      FiniteBijection.of m) :
    (SymmetricSequence.tensorPowerSequence K).obj a ⊗ X ⟶ level ((freeAt (K := K) n).obj X) m :=
  SymmetricSequence.freeConvolutionGenerator (SymmetricSequence.tensorPowerSequence K) n X m a h

/-- 出力の全単射による作用は生成元の添字への後合成。 -/
@[reassoc] lemma freeAtLevelGenerator_map (n : ℕ) (X : C)
    (m m' : ℕ) (a : FiniteBijection)
    (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m)
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m') :
    freeAtLevelGenerator (K := K) n X m a h ≫ ((freeAt (K := K) n).obj X).X.map k =
      freeAtLevelGenerator (K := K) n X m' a (h ≫ k) :=
  SymmetricSequence.freeConvolutionGenerator_map
    (SymmetricSequence.tensorPowerSequence K) n X m m' a h k

/-- Sym(K)側のブロックの作用と、生成元の添字の同一視の関係。 -/
@[reassoc] lemma freeAtLevelGenerator_left_relation (n : ℕ) (X : C)
    (m : ℕ) {a b : FiniteBijection} (k : a ⟶ b)
    (h : FiniteBijection.sumObj b (FiniteBijection.of n) ⟶ FiniteBijection.of m) :
    (SymmetricSequence.tensorPowerSequence K).map k ▷ X ≫ freeAtLevelGenerator (K := K) n X m b h =
      freeAtLevelGenerator (K := K) n X m a
        (FiniteBijection.sumMap k (𝟙 (FiniteBijection.of n)) ≫ h) :=
  SymmetricSequence.freeConvolutionGenerator_left_relation
    (SymmetricSequence.tensorPowerSequence K) n X m k h

/-- 自由スペクトルの各段からの射は、この生成元上の値で決まる。 -/
lemma freeAtLevel_hom_ext (n : ℕ) (X : C) (m : ℕ)
    {Y : C} (f g : level ((freeAt (K := K) n).obj X) m ⟶ Y)
    (h : ∀ (a : FiniteBijection)
      (k : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m),
      freeAtLevelGenerator (K := K) n X m a k ≫ f =
        freeAtLevelGenerator (K := K) n X m a k ≫ g) : f = g :=
  SymmetricSequence.freeConvolutionLevel_hom_ext
    (SymmetricSequence.tensorPowerSequence K) n X m f g h

/-- n未満の段は始対象。 -/
def freeAtLevelInitial (n : ℕ) (X : C) (m : ℕ) (hm : m < n) :
    IsInitial (level ((freeAt (K := K) n).obj X) m) :=
  SymmetricSequence.freeConvolutionLevelInitial (SymmetricSequence.tensorPowerSequence K) n X m hm

/-- n未満の段は零対象である。 -/
lemma freeAtLevel_isZero [HasZeroObject C] (n : ℕ) (X : C) (m : ℕ) (hm : m < n) :
    IsZero (level ((freeAt (K := K) n).obj X) m) :=
  (isZero_zero C).of_iso
    ((freeAtLevelInitial (K := K) n X m hm).uniqueUpToIso (isZero_zero _).isInitial)

end SerrePositivity.GeneralSymmetricSpectrum
