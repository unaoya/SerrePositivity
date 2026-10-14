module

public import SerrePositivity.Spectra.SymmetricSequence.FreePairConvolution
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreePair

/-! # 自由スペクトルのテンソル積と和次数の自由生成

F_m XとF_n Yの球面上のテンソル積をF_(m+n)(X⊗Y)へ比較する。
入力のテンソル積は基点付き単体的集合の通常のsmashである。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- F_m XとF_n Yの積は、和次数からXとYのsmashを生成する自由スペクトルと同型。 -/
def sphereTensorFreeAtSum (m n : ℕ) (X Y : PointedSimplicialSet.{u}) :
    sphereTensor ((freeAt m).obj X) ((freeAt n).obj Y) ≅ (freeAt (m + n)).obj (X ⊗ Y) :=
  sphereTensorFreeAtPair m n X Y ≪≫
    freeFunctor.mapIso (SymmetricSequence.freePairConvolutionIso m n X Y)

/-- 和次数への比較は、前回の自由加群の比較と自由対称列の和次数比較の合成。 -/
lemma sphereTensorFreeAtSum_eq (m n : ℕ) (X Y : PointedSimplicialSet.{u}) :
    sphereTensorFreeAtSum m n X Y = sphereTensorFreeAtPair m n X Y ≪≫
      freeFunctor.mapIso (SymmetricSequence.freePairConvolutionIso m n X Y) := rfl

/-- 和次数への自由スペクトルの比較は両方の入力の射に関して自然。 -/
lemma sphereTensorFreeAtSum_naturality (m n : ℕ) {X X' Y Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    sphereTensorMap ((freeAt m).map f) ((freeAt n).map g) ≫
        (sphereTensorFreeAtSum m n X' Y').hom =
      (sphereTensorFreeAtSum m n X Y).hom ≫ (freeAt (m + n)).map (f ⊗ₘ g) := by
  change sphereTensorMap ((freeAt m).map f) ((freeAt n).map g) ≫
      (sphereTensorFreeAtPair m n X' Y').hom ≫
        freeFunctor.map (SymmetricSequence.freePairConvolutionIso m n X' Y').hom =
    ((sphereTensorFreeAtPair m n X Y).hom ≫
      freeFunctor.map (SymmetricSequence.freePairConvolutionIso m n X Y).hom) ≫
        freeFunctor.map ((SymmetricSequence.freeAt (m + n)).map (f ⊗ₘ g))
  rw [← Category.assoc, sphereTensorFreeAtPair_naturality, Category.assoc,
    ← freeFunctor.map_comp, SymmetricSequence.freePairConvolutionIso_naturality,
    freeFunctor.map_comp, Category.assoc]

/-- 第m段と第n段から作る自由スペクトルをテンソルする二変数関手。 -/
def sphereTensorFreeAtBifunctor (m n : ℕ) :
    PointedSimplicialSet.{u} × PointedSimplicialSet.{u} ⥤ SymmetricSpectrum.{u} :=
  (freeAt m).prod (freeAt n) ⋙ sphereTensorBifunctor

/-- 二つの入力をsmashして和次数から自由スペクトルを作る二変数関手。 -/
def freeAtSmashBifunctor (m n : ℕ) :
    PointedSimplicialSet.{u} × PointedSimplicialSet.{u} ⥤ SymmetricSpectrum.{u} :=
  tensor PointedSimplicialSet.{u} ⋙ freeAt (m + n)

/-- F_mとF_nのテンソル積とF_(m+n)の二変数の自然比較。 -/
def sphereTensorFreeAtSumNatIso (m n : ℕ) :
    sphereTensorFreeAtBifunctor.{u} m n ≅ freeAtSmashBifunctor.{u} m n :=
  NatIso.ofComponents (fun XY => sphereTensorFreeAtSum m n XY.1 XY.2)
    (fun fg => sphereTensorFreeAtSum_naturality m n fg.1 fg.2)

end SerrePositivity.SymmetricSpectrum
