module
public import SerrePositivity.KST.SConstruction.DGPointedQuotientEnd
public import SerrePositivity.InfinityCategories.Derived.ContractingZeroVertex

/-! # 指定 ε による対角像とその指定 End の dg nerve 内の零化
概要：実商の対角像とその一対象 End の頂点が、実 dg nerve の零対象になると示す。
方針：同じ指定 ε の微分方程式を、全写像空間の初終対象判定へ渡す。
規約：H⁰ の恒等の零性だけでは代用しない。使われ方：dg ⊙ の商での対角の零化。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGNerve
variable (R : Type u) [CommRing R] {P : Type v} {G : Type w}
  [DGCategory R P] [DGCategory R G] [Small.{u} G] (i : DGFunctor R P G)

/-- 元の対角像は、同じ ε により実商の dg nerve の零対象になる。 -/
lemma pointedDGQuotientDiagonal_isZero (a : P) :
    IsZeroVertex (X := dgNerve R (PointedDGQuotientObject R i))
      (Simplex.vertex (pointedDGQuotientVertex R i (i.obj a))) :=
  dgNerve_contractingElement_isZeroVertex _ (pointedDGQuotientDiagonalEpsilon R i a)
    (pointedDGQuotientDiagonalEpsilon_d R i a)

/-- 対角像の指定 End の頂点も、同じ ε により実 dg nerve の零対象になる。 -/
lemma pointedDGQuotientDiagonalEnd_isZero (a : P)
    (x : PointedDGQuotientEndObject R i (i.obj a)) :
    IsZeroVertex (X := dgNerve R (PointedDGQuotientEndObject R i (i.obj a)))
      (Simplex.vertex x) :=
  dgNerve_contractingElement_isZeroVertex x (pointedDGQuotientDiagonalEpsilon R i a)
    (pointedDGQuotientDiagonalEpsilon_d R i a)

end SerrePositivity.KST.SConstruction
