module
public import SerrePositivity.KST.SConstruction.DGGluingAxesYonedaCofiber
public import SerrePositivity.KST.SConstruction.DGGluingClosedZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareTopMiddleIso

/-! # 全四角が元の代表加群である実二軸 cofiber
概要：実 gluing 零対象の代表加群を零角に置き、元の二軸 cofiber 四角形を保つ。
方針：元の零角変更ホモトピーと両零角の実零性で押し出し性を移す。
規約：下側三対象と元の二射を保持。使われ方：元の dg nerve への四角形の反映。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "Z" => ForgetEnrichment.of (Complex R)
  (representable R (dgGluingRightAxisObject R C D M zc zd))
local notation "L" => ForgetEnrichment.of (Complex R)
  (representable R (dgGluingLeftAxisObject R C D M zd X.left))
local notation "s" => dgGluingAxesYonedaCofiberData R C D M zc hc zd hd X

/-- 元の標準零加群から指定 gluing 零代表への零射は、元の零上辺を因子分解する。 -/
lemma dgGluingAxesRepresentableCofiber_top_factor :
    (0 : moduleZero R G ⟶ Z) ≫ (0 : Z ⟶ L) = (s).top := by
  change (0 : moduleZero R G ⟶ Z) ≫ (0 : Z ⟶ L) =
    (0 : moduleZero R G ⟶ moduleCone R G (dgGluingAxesYonedaRightMap R C D M zc hc X)) ≫
      dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X
  rw [zero_comp, zero_comp]

/-- 同じ下側三対象・二射を保持し、零角だけを元の gluing 零代表へ移す。 -/
def dgGluingAxesRepresentableCofiberData :=
  (s).changeTopMiddle (0 : moduleZero R G ⟶ Z) (0 : Z ⟶ L)
    (dgGluingAxesRepresentableCofiber_top_factor R C D M zc hc zd hd X)

/-- 元の四代表加群を四頂点とする実二軸四角形。 -/
def dgGluingAxesRepresentableCofiberSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) (max v w)}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R G :=
  (dgGluingAxesRepresentableCofiberData R C D M zc hc zd hd X).square

/-- 同じ代表加群零角は、実 ∞ 圏の零頂点。 -/
lemma dgGluingAxesRepresentableCofiberSquare_zero :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex
      (dgGluingAxesRepresentableCofiberSquare R C D M zc hc zd hd X) 0 1) := by
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex
    (dgGluingAxesRepresentableCofiberData R C D M zc hc zd hd X).square 0 1)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.square_vertex01]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_of_closed_isZero _
    (dgGluingClosedZero_representable_isZero R C D M zc hc zd hd)

/-- 零角変更は、元の二軸 cofiber 四角形全体の実関手同型となる。 -/
def dgGluingAxesRepresentableCofiberFunctorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgGluingAxesYonedaCofiberSquare R C D M zc hc zd hd X)
      (dgGluingAxesRepresentableCofiberSquare R C D M zc hc zd hd X) :=
  (s).changeTopMiddleFunctorIso _ _
    (dgGluingAxesRepresentableCofiber_top_factor R C D M zc hc zd hd X)
    (dgGluingAxesYonedaCofiberSquare_zero R C D M zc hc zd hd X)
    (dgGluingAxesRepresentableCofiberSquare_zero R C D M zc hc zd hd X)

/-- 元の四代表加群と二射を持つ同じ実四角形も、∞ 押し出しとなる。 -/
lemma dgGluingAxesRepresentableCofiberSquare_isPushout :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgGluingAxesRepresentableCofiberSquare R C D M zc hc zd hd X) :=
  (dgGluingAxesYonedaCofiberSquare_isPushout R C D M zc hc zd hd X).of_functorIso
    (dgGluingAxesRepresentableCofiberFunctorIso R C D M zc hc zd hd X)

/-- 零角変更後も、右辺は元の左軸射影の Yoneda 像そのもの。 -/
lemma dgGluingAxesRepresentableCofiberSquare_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgGluingAxesRepresentableCofiberSquare R C D M zc hc zd hd X =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R G
        (dgGluingAxesYonedaLeftMap R C D M zd hd X)).edge := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫
    (dgGluingAxesRepresentableCofiberData R C D M zc hc zd hd X).square = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.square_right]
  exact congrArg (fun k => SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R G k).edge)
    (dgGluingAxesYonedaCofiberData_right R C D M zc hc zd hd X)

end SerrePositivity.KST.SConstruction
