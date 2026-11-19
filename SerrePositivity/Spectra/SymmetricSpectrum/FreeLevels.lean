module

public import SerrePositivity.Spectra.SymmetricSequence.FreeConvolution
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation

/-! # 自由対称スペクトルの各段の表示と零になる範囲

F_n Xの各段を球面と自由対称列の分解図式で表す。
直和の全単射で添字付けた生成元上の値が射を決定し、n未満の段は零対象となる。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 自由スペクトルの第m段の分解図式。 -/
def freeAtLevelDiagram (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m) ⥤
      PointedSimplicialSet.{u} := SymmetricSequence.freeConvolutionDiagram sphereSequence n X m

/-- 分解の各項は、球面と全単射で添字付けたXの余積とのsmash。 -/
lemma freeAtLevelDiagram_obj (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    (d : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m)) :
    (freeAtLevelDiagram n X m).obj d = spherePower.{u} (FiniteBijection.card d.left.1) ⊗
      ∐ (fun _ : FiniteBijection.of n ⟶ d.left.2 => X) := rfl

/-- 自由スペクトルの各段の余極限表示。 -/
def freeAtLevelIsoColimit (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    level ((freeAt n).obj X) m ≅ colimit (freeAtLevelDiagram n X m) :=
  SymmetricSequence.freeConvolutionLevelIsoColimit sphereSequence n X m

/-- 球面の段とXから、直和の全単射で指定する自由スペクトルの生成元。 -/
def freeAtLevelGenerator (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    (a : FiniteBijection) (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶
      FiniteBijection.of m) : sphereSequence.{u}.obj a ⊗ X ⟶ level ((freeAt n).obj X) m :=
  SymmetricSequence.freeConvolutionGenerator sphereSequence n X m a h

/-- 出力の全単射による作用は生成元の添字への後合成。 -/
@[reassoc] lemma freeAtLevelGenerator_map (n : ℕ) (X : PointedSimplicialSet.{u})
    (m m' : ℕ) (a : FiniteBijection)
    (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m)
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m') :
    freeAtLevelGenerator n X m a h ≫ ((freeAt n).obj X).X.map k =
      freeAtLevelGenerator n X m' a (h ≫ k) :=
  SymmetricSequence.freeConvolutionGenerator_map sphereSequence n X m m' a h k

/-- 球面側のブロックの作用と、生成元の添字の同一視の関係。 -/
@[reassoc] lemma freeAtLevelGenerator_left_relation (n : ℕ) (X : PointedSimplicialSet.{u})
    (m : ℕ) {a b : FiniteBijection} (k : a ⟶ b)
    (h : FiniteBijection.sumObj b (FiniteBijection.of n) ⟶ FiniteBijection.of m) :
    sphereSequence.{u}.map k ▷ X ≫ freeAtLevelGenerator n X m b h =
      freeAtLevelGenerator n X m a
        (FiniteBijection.sumMap k (𝟙 (FiniteBijection.of n)) ≫ h) :=
  SymmetricSequence.freeConvolutionGenerator_left_relation sphereSequence n X m k h

/-- 自由スペクトルの各段からの射は、この生成元上の値で決まる。 -/
lemma freeAtLevel_hom_ext (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    {Y : PointedSimplicialSet.{u}} (f g : level ((freeAt n).obj X) m ⟶ Y)
    (h : ∀ (a : FiniteBijection)
      (k : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m),
      freeAtLevelGenerator n X m a k ≫ f = freeAtLevelGenerator n X m a k ≫ g) : f = g :=
  SymmetricSequence.freeConvolutionLevel_hom_ext sphereSequence n X m f g h

/-- n未満の段は始対象。 -/
def freeAtLevelInitial (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) (hm : m < n) :
    IsInitial (level ((freeAt n).obj X) m) :=
  SymmetricSequence.freeConvolutionLevelInitial sphereSequence n X m hm

/-- n未満の段は零対象である。 -/
lemma freeAtLevel_isZero (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) (hm : m < n) :
    IsZero (level ((freeAt n).obj X) m) :=
  (isZero_zero PointedSimplicialSet.{u}).of_iso
    ((freeAtLevelInitial n X m hm).uniqueUpToIso (isZero_zero _).isInitial)

end SerrePositivity.SymmetricSpectrum
