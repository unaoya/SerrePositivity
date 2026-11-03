module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorPairFaces
public import SerrePositivity.DifferentialGraded.Category.Basic

/-! # 元の左右 Hom 鎖射の実 tensor 合成
概要：元の左右 cube の Hom 鎖射を、元の実 tensor 比較と豊穣合成で連結する。
方針：元の全斉次元対で実 tensor 比較と tensor 鎖射を評価する。
規約：元の実鎖射・因子順を保持。使われ方：内部一面の左右復元からの実鎖射。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の左右 Hom 鎖射の、元の同じ左右連結 cube からの実豊穣順合成鎖射。 -/
def serreCubeTensorComposition {x y z : D} (n m : ℕ)
    (F : serreCubeComplex A n ⟶ homObject A D x y)
    (G : serreCubeComplex A m ⟶ homObject A D y z) :
    serreCubeComplex A (n + m) ⟶ homObject A D x z :=
  (serreCubeTensorIso A n m).hom.hom ≫ (F ⊗ₘ G) ≫ eComp (Complex A) x y z

/-- 元の実合成鎖射は、全斉次元対で同じ元の豊穣順合成を回収する。 -/
lemma serreCubeTensorComposition_apply {x y z : D} (n m : ℕ)
    (F : serreCubeComplex A n ⟶ homObject A D x y)
    (G : serreCubeComplex A m ⟶ homObject A D y z)
    (p q k : ℤ) (hk : p + q = k)
    (f : (serreCubeComplex A n).X p) (g : (serreCubeComplex A m).X q) :
    (serreCubeTensorComposition A n m F G).f k (serreCubeTensorPair A n m p q k hk f g) =
      forward A (F.f p f) (G.f q g) hk := by
  have h := congrArg (fun w => (eComp (Complex A) x y z).f k ((F ⊗ₘ G).f k w))
    (serreCubeTensorPair_hom A n m p q k hk f g)
  exact h.trans (congrArg (fun w => (eComp (Complex A) x y z).f k w)
    (tensorMap_apply F G p q k hk f g))

end SerrePositivity.KST.SConstruction
