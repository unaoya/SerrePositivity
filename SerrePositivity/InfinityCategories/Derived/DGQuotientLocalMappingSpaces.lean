module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorQuasiIsoFullyFaithful
public import SerrePositivity.InfinityCategories.Derived.DGQuotientNerve
public import SerrePositivity.InfinityCategories.DGNerve.FullSubcategory
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness

/-! # dg 商の局所対象における実写像空間

概要：片側 K-flat 条件の下で、局所対象への／からの商の実写像空間は元と同値。
方針：path 長 filtration による Hom 準同型を、全射性を要求しない実 pinched 比較へ渡す。
規約：H⁰ の Hom だけで済ませない。使われ方：β3 の局所化の coherent 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定対象に右直交する標的への、実商の pinched 写像空間の比較は同値。 -/
theorem dgQuotient_pinchedHomMap_equivalence_into (S : Set D)
    (h : DGQuotient.homIntoKFlat A D S) (x y : D)
    (hy : ∀ b : S, (homObject A D b.val y).Acyclic) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap (dgQuotientNerveProjection A D S) (Simplex.vertex x) (Simplex.vertex y)) :=
  dgFunctor_pinchedHomMap_quasiIso_equivalence (DGQuotient.inclusion A D S) x y
    (DGQuotient.originalHomInclusion_quasiIso_into A D S h x y hy)

/-- 指定対象に左直交する始点からの、実商の pinched 写像空間の比較は同値。 -/
theorem dgQuotient_pinchedHomMap_equivalence_outOf (S : Set D)
    (h : DGQuotient.homOutOfKFlat A D S) (x y : D)
    (hx : ∀ b : S, (homObject A D x b.val).Acyclic) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap (dgQuotientNerveProjection A D S) (Simplex.vertex x) (Simplex.vertex y)) :=
  dgFunctor_pinchedHomMap_quasiIso_equivalence (DGQuotient.inclusion A D S) x y
    (DGQuotient.originalHomInclusion_quasiIso_outOf A D S h x y hx)

/-- 商で零化する指定対象に、全次数で右直交する実 dg 対象。 -/
def dgQuotientRightLocal (S : Set D) (y : D) : Prop :=
  ∀ b : S, (homObject A D b.val y).Acyclic

/-- 右局所対象の充満 dg 部分圏から実商への関手。 -/
def dgQuotientRightLocalFunctor (S : Set D) :
    DGFunctor A (DGFullSubcategory D (dgQuotientRightLocal A D S))
      (DGQuotient.QuotientObject D S) :=
  (dgFullSubcategoryInclusion A D (dgQuotientRightLocal A D S)).comp
    (DGQuotient.inclusion A D S)

/-- 右局所対象の実部分圏から商への native nerve は実充満忠実。 -/
theorem dgQuotientRightLocalNerve_isFullyFaithful (S : Set D)
    (h : DGQuotient.homIntoKFlat A D S) :
    IsFullyFaithful (dgNerve.map (dgQuotientRightLocalFunctor A D S)) := by
  apply dgNerve_map_isFullyFaithful_of_quasiIso
  intro x y
  change QuasiIso (𝟙 _ ≫ DGQuotient.originalHomInclusion A D S x.val y.val)
  rw [Category.id_comp]
  exact DGQuotient.originalHomInclusion_quasiIso_into A D S h x.val y.val y.property

end SerrePositivity.InfinityCategories
