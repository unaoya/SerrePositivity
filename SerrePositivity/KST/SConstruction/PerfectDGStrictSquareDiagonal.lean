module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionFactorization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size

/-! # 元の標準 dg 対角の実 Perf 延長
概要：元の小さい dg gluing への標準対角を、同じ実 Perf 延長で送る。
方針：元の左右射影の厳密回収を、実合成比較と入力等号を保つ比較同型へ移す。
規約：Small Perf を仮定しない。lax pullback との同定は未主張。
使われ方：Milnor 四角形の対角像とその完備商の具体化。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (D : Type z) [DGCategory R D] [Small.{u} D]
  (E : Type t) [DGCategory R E]
  (L : DGFunctor R P C) (G : DGFunctor R P D)
  (p : DGFunctor R C E) (q : DGFunctor R D E) (h : L.comp p = G.comp q)

/-- 元の標準対角を、元の小さい gluing の実 Perf へ延長した同じ dg 関手。 -/
def perfectDGStrictSquareDiagonal :
    DGFunctor R (PerfectDGModule R P)
      (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))) :=
  perfectDGExtension R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
    (dgStrictSquareDiagonal R C D E p q L G h)

/-- 左 Perf 射影は、元の合成比較と厳密な左射影回収を通って元の延長と同型。 -/
def perfectDGStrictSquareDiagonalLeftAt (X : PerfectDGModule R P) :
    ForgetEnrichment.of (Complex R)
      (((perfectDGStrictSquareDiagonal R P C D E L G p q h).comp
        (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) C
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)))).obj X) ≅
    ForgetEnrichment.of (Complex R) ((perfectDGExtension R P C L).obj X) :=
  perfectDGExtensionFactorizationAt R P
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) C
    (dgStrictSquareDiagonal R C D E p q L G h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)) L
    (dgStrictSquareDiagonal_left R C D E p q L G h) X

/-- 右 Perf 射影も、元の合成比較と厳密な右射影回収を通って元の延長と同型。 -/
def perfectDGStrictSquareDiagonalRightAt (X : PerfectDGModule R P) :
    ForgetEnrichment.of (Complex R)
      (((perfectDGStrictSquareDiagonal R P C D E L G p q h).comp
        (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) D
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)))).obj X) ≅
    ForgetEnrichment.of (Complex R) ((perfectDGExtension R P D G).obj X) :=
  perfectDGExtensionFactorizationAt R P
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) D
    (dgStrictSquareDiagonal R C D E p q L G h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)) G
    (dgStrictSquareDiagonal_right R C D E p q L G h) X

/-- 同じ左 Perf 射影の指定比較は、全 Hom 複体上で自然。 -/
lemma perfectDGStrictSquareDiagonalLeftAt_naturality (X Y : PerfectDGModule R P) :
    ((perfectDGStrictSquareDiagonal R P C D E L G p q h).comp
      (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)))).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R)
          (((perfectDGStrictSquareDiagonal R P C D E L G p q h).comp
            (perfectDGExtension R
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) C
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)))).obj X))
        (perfectDGStrictSquareDiagonalLeftAt R P C D E L G p q h Y).hom =
    (perfectDGExtension R P C L).map X Y ≫ eHomWhiskerRight (Complex R)
      (perfectDGStrictSquareDiagonalLeftAt R P C D E L G p q h X).hom
      (ForgetEnrichment.of (Complex R) ((perfectDGExtension R P C L).obj Y)) :=
  perfectDGExtensionFactorizationAt_naturality R P
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) C
    (dgStrictSquareDiagonal R C D E p q L G h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)) L
    (dgStrictSquareDiagonal_left R C D E p q L G h) X Y

/-- 同じ右 Perf 射影の指定比較は、全 Hom 複体上で自然。 -/
lemma perfectDGStrictSquareDiagonalRightAt_naturality (X Y : PerfectDGModule R P) :
    ((perfectDGStrictSquareDiagonal R P C D E L G p q h).comp
      (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) D
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)))).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R)
          (((perfectDGStrictSquareDiagonal R P C D E L G p q h).comp
            (perfectDGExtension R
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) D
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)))).obj X))
        (perfectDGStrictSquareDiagonalRightAt R P C D E L G p q h Y).hom =
    (perfectDGExtension R P D G).map X Y ≫ eHomWhiskerRight (Complex R)
      (perfectDGStrictSquareDiagonalRightAt R P C D E L G p q h X).hom
      (ForgetEnrichment.of (Complex R) ((perfectDGExtension R P D G).obj Y)) :=
  perfectDGExtensionFactorizationAt_naturality R P
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) D
    (dgStrictSquareDiagonal R C D E p q L G h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)) G
    (dgStrictSquareDiagonal_right R C D E p q L G h) X Y

end SerrePositivity.KST.SConstruction
