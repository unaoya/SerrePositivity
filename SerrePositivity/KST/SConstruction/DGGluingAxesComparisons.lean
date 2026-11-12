module
public import SerrePositivity.KST.SConstruction.DGGluingAxesHomNaturality
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedComparison

/-! # 元の二軸への二射の全次数自然変換
概要：同じ二射の全 Hom 自然性を、単位パラメータの豊穣自然変換へ束ねる。
方針：元の比較射を成分に使い、閉零圏の自然変換にも同じ成分で制限する。
規約：同じ二射と全次数作用を保持。使われ方：元の短複体と Yoneda 円錐の関手性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 元の右軸からの同じ二成分閉射を持つ、全 Hom 自然な単位パラメータ比較。 -/
def dgGluingAxisRightComparison (z : C)
    (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z)) :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).comp (dgGluingRightAxis R C D M z hz))
      (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) :=
  dgFunctorClosedComparison R _ _ (dgGluingAxisRightInclusion R C D M z hz)
    (dgGluingAxisRightInclusion_hom_naturality R C D M z hz)

/-- 元の左軸への同じ二成分閉射を持つ、全 Hom 自然な単位パラメータ比較。 -/
def dgGluingAxisLeftComparison (z : D)
    (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z)) :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R)))
      (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).comp (dgGluingLeftAxis R C D M z hz)) :=
  dgFunctorClosedComparison R _ _ (dgGluingAxisLeftProjection R C D M z hz)
    (dgGluingAxisLeftProjection_hom_naturality R C D M z hz)

/-- 元の右軸比較の閉零制限も、同じ元の成分で自然。 -/
def dgGluingAxisRightClosedComparison (z : C)
    (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z)) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).comp (dgGluingRightAxis R C D M z hz)).onClosed ⟶
      (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed where
  app X := dgGluingAxisRightInclusion R C D M z hz (ForgetEnrichment.to (Complex R) X)
  naturality _ _ f := dgFunctorClosedComparison_naturality R
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).comp (dgGluingRightAxis R C D M z hz))
    (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
    (dgGluingAxisRightInclusion R C D M z hz)
    (dgGluingAxisRightInclusion_hom_naturality R C D M z hz) f

/-- 元の左軸比較の閉零制限も、同じ元の成分で自然。 -/
def dgGluingAxisLeftClosedComparison (z : D)
    (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z)) :
    (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed ⟶
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).comp (dgGluingLeftAxis R C D M z hz)).onClosed where
  app X := dgGluingAxisLeftProjection R C D M z hz (ForgetEnrichment.to (Complex R) X)
  naturality _ _ f := dgFunctorClosedComparison_naturality R
    (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).comp (dgGluingLeftAxis R C D M z hz))
    (dgGluingAxisLeftProjection R C D M z hz)
    (dgGluingAxisLeftProjection_hom_naturality R C D M z hz) f

end SerrePositivity.KST.SConstruction
