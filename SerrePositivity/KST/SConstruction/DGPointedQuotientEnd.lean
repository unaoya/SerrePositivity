module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic

/-! # 対角像を消す実 dg 商の指定対象 End
概要：実 dg 関手の対象像を収縮する Drinfeld 商と、指定対象の全 dg End を構成する。
方針：元の path 商・指定 ε・forward 合成をそのまま保持する。
規約：生成性・Morita 同定・nerve の局所化性は未主張。使われ方：dg ⊙ の実模型。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] {P : Type v} {G : Type w}
  [DGCategory R P] [DGCategory R G] [Small.{u} G] (i : DGFunctor R P G)

/-- 消す対角 dg 関手の、元の対象像そのもの。 -/
def dgQuotientImage : Set G := Set.range i.obj

/-- 対角像を指定 ε で収縮する、元の実 path 商の対象。 -/
abbrev PointedDGQuotientObject := DGQuotient.QuotientObject G (dgQuotientImage R i)

/-- 元の対角像を消す、同じ実 dg 商射。 -/
def pointedDGQuotientProjection : DGFunctor R G (PointedDGQuotientObject R i) :=
  DGQuotient.inclusion R G (dgQuotientImage R i)

/-- 元の指定対象 b を、そのまま同じ商の対象にする。 -/
def pointedDGQuotientVertex (b : G) : PointedDGQuotientObject R i :=
  (pointedDGQuotientProjection R i).obj b

/-- 元の指定対象の商での全 dg End を持つ、一対象の実 dg 圏。 -/
abbrev PointedDGQuotientEndObject (b : G) :=
  EndomorphismObject (pointedDGQuotientVertex R i b)

/-- 指定対象の実 dg End から、元の実 dg 商への包含。 -/
def pointedDGQuotientEndInclusion (b : G) :
    DGFunctor R (PointedDGQuotientEndObject R i b) (PointedDGQuotientObject R i) :=
  endomorphismInclusion R (pointedDGQuotientVertex R i b)

/-- 元の対象の End から、その同じ商の対象の End への実 dg 射。 -/
def pointedDGQuotientEndUnitMap (b : G) :
    DGFunctor R (EndomorphismObject b) (PointedDGQuotientEndObject R i b) :=
  endomorphismMap R (pointedDGQuotientProjection R i) b

/-- 指定 End と商の包含の正方形は、全 Hom 複体を保って厳密に可換。 -/
lemma pointedDGQuotientEndUnitMap_inclusion (b : G) :
    (pointedDGQuotientEndUnitMap R i b).comp (pointedDGQuotientEndInclusion R i b) =
      (endomorphismInclusion R b).comp (pointedDGQuotientProjection R i) :=
  endomorphismMap_comp_inclusion R (pointedDGQuotientProjection R i) b

/-- 指定 End の全 Hom は、元の指定対象の同じ path 商の全複体。 -/
lemma pointedDGQuotientEnd_hom (b : G) (x y : PointedDGQuotientEndObject R i b) :
    homObject R (PointedDGQuotientEndObject R i b) x y =
      DGQuotient.quotientHom R G (dgQuotientImage R i) b b := rfl

/-- 指定 End の各次数は、元の全 path 直和の同じ次数。 -/
lemma pointedDGQuotientEnd_X (b : G) (x y : PointedDGQuotientEndObject R i b) (n : ℤ) :
    (homObject R (PointedDGQuotientEndObject R i b) x y).X n =
      (DGQuotient.internalHom R G (dgQuotientImage R i) b b).X n := rfl

/-- 指定 End の微分は、元の内部微分と指定 ε 消去の和。 -/
lemma pointedDGQuotientEnd_d (b : G) (x y : PointedDGQuotientEndObject R i b) (n : ℤ) :
    (homObject R (PointedDGQuotientEndObject R i b) x y).d n (n + 1) =
      (DGQuotient.internalHom R G (dgQuotientImage R i) b b).d n (n + 1) +
        (DGQuotient.erasure R G (dgQuotientImage R i) b b).v n (n + 1) rfl :=
  DGQuotient.quotientHom_d R G (dgQuotientImage R i) b b n

/-- 指定 End の乗法は、元の実商の forward 豊穣合成そのもの。 -/
lemma pointedDGQuotientEnd_multiplication (b : G)
    (x y z : PointedDGQuotientEndObject R i b) :
    eComp (Complex R) x y z =
      DGQuotient.quotientComposition R G (dgQuotientImage R i) b b b := rfl

/-- 対角像の元の対象に、同じ商の指定次数 −1 の ε を与える。 -/
def pointedDGQuotientDiagonalEpsilon (a : P) :
    GradedHom R (pointedDGQuotientVertex R i (i.obj a))
      (pointedDGQuotientVertex R i (i.obj a)) (-1) :=
  DGQuotient.epsilonElement R G (dgQuotientImage R i) ⟨i.obj a, ⟨a, rfl⟩⟩

/-- 同じ ε は、元の対角像の恒等を実 dg 商で収縮する。 -/
lemma pointedDGQuotientDiagonalEpsilon_d (a : P) :
    (homObject R (PointedDGQuotientObject R i)
      (pointedDGQuotientVertex R i (i.obj a))
      (pointedDGQuotientVertex R i (i.obj a))).d (-1) 0
        (pointedDGQuotientDiagonalEpsilon R i a) =
    (unitElement R (pointedDGQuotientVertex R i (i.obj a))).val :=
  DGQuotient.differential_epsilonElement R G (dgQuotientImage R i) ⟨i.obj a, ⟨a, rfl⟩⟩

end SerrePositivity.KST.SConstruction
