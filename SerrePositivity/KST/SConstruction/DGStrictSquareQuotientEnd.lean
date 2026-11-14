module
public import SerrePositivity.KST.SConstruction.DGHomGluingStrictSquare
public import SerrePositivity.KST.SConstruction.DGLaxQuotientEnd

/-! # 元の厳密 dg 四角形の標準対角商と指定 End
概要：構成済みの標準対角を使い、元の (0,b,0) の実商 End を具体化する。
方針：元の閉零対象と右対象を保持し、指定 ε による対角像の収縮へ接続する。
規約：生成性・Morita・lax pullback との同定は未主張。使われ方：LT の ⊙ の dg 模型。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  {P : Type t} [DGCategory R P] (L : DGFunctor R P C) (G : DGFunctor R P D)
  (h : L.comp p = G.comp q) (z₀ : C)
  (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z₀)) (b : D)

/-- 元の厳密四角形から構成した標準対角を使う、指定商 End の実入力。 -/
def dgStrictSquareQuotientInput :
    DGLaxQuotientEndInput R C D (dgHomGluingBimodule R C D E p q) P :=
  DGLaxQuotientEndInput.ofClosedZero
    (dgStrictSquareDiagonal R C D E p q L G h) z₀ hz b

/-- 同じ標準対角像の実商における、元の (0,b,0) の全 dg End。 -/
abbrev dgStrictSquareQuotientEnd :=
  (dgStrictSquareQuotientInput R C D E p q L G h z₀ hz b).endObject

/-- 同じ実商の全 Hom は、元の標準対角像を消す同じ path 商複体。 -/
lemma dgStrictSquareQuotientEnd_hom
    (x y : dgStrictSquareQuotientEnd R C D E p q L G h z₀ hz b) :
    homObject R (dgStrictSquareQuotientEnd R C D E p q L G h z₀ hz b) x y =
      DGQuotient.quotientHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
        (dgQuotientImage R (dgStrictSquareDiagonal R C D E p q L G h))
        (dgStrictSquareQuotientInput R C D E p q L G h z₀ hz b).point
        (dgStrictSquareQuotientInput R C D E p q L G h z₀ hz b).point := rfl

/-- 元の標準対角の像は、指定 ε により同じ実商の dg nerve 内で零対象となる。 -/
lemma dgStrictSquareQuotient_diagonal_isZero (x : P) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex
      (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgStrictSquareQuotientInput R C D E p q L G h z₀ hz b).quotientObject)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
        ((dgStrictSquareQuotientInput R C D E p q L G h z₀ hz b).projection.obj
          ((dgStrictSquareDiagonal R C D E p q L G h).obj x))) :=
  (dgStrictSquareQuotientInput R C D E p q L G h z₀ hz b).diagonal_isZero x

end SerrePositivity.KST.SConstruction
