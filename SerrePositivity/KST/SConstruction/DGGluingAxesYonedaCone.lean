module
public import SerrePositivity.KST.SConstruction.DGGluingAxesComplex
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Size

/-! # 元の二軸短複体の Yoneda 円錐比較
概要：元の右軸射の代表加群円錐から、同じ左軸の代表加群への比較射を作る。
方針：同じ二射と合成零を Yoneda で送り、元の moduleConeDesc を使う。
規約：同じ比較射を保持。準同型性は DGGluingAxesYonedaQuasiIso で証明する。
使われ方：元の二軸列の cofiber 性の判定。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))

/-- 元の同じ右軸射を代表加群の閉射へ送る。 -/
def dgGluingAxesYonedaRightMap (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ForgetEnrichment.of (Complex R)
      (representable R (dgGluingRightAxisObject R C D M zc X.right)) ⟶
    ForgetEnrichment.of (Complex R) (representable R X) :=
  (dgYoneda R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map
    (dgGluingAxisRightInclusion R C D M zc hc X)

/-- 元の同じ左軸射を代表加群の閉射へ送る。 -/
def dgGluingAxesYonedaLeftMap (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ForgetEnrichment.of (Complex R) (representable R X) ⟶
    ForgetEnrichment.of (Complex R)
      (representable R (dgGluingLeftAxisObject R C D M zd X.left)) :=
  (dgYoneda R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map
    (dgGluingAxisLeftProjection R C D M zd hd X)

/-- 同じ二つの Yoneda 像の合成は、元の合成零を保って厳密に零。 -/
lemma dgGluingAxesYoneda_comp_zero (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingAxesYonedaRightMap R C D M zc hc X ≫
      dgGluingAxesYonedaLeftMap R C D M zd hd X = 0 :=
  ((dgYoneda R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map_comp
    (dgGluingAxisRightInclusion R C D M zc hc X)
    (dgGluingAxisLeftProjection R C D M zd hd X)).symm.trans
      ((congrArg ((dgYoneda R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map)
        (dgGluingAxes_comp_zero R C D M zc hc zd hd X)).trans
          ((dgYoneda R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map_zero _ _))

/-- 元の右軸射の同じ代表円錐から、同じ左軸代表への実 dg 自然な比較射。 -/
def dgGluingAxesYonedaConeComparison (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    moduleCone R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (dgGluingAxesYonedaRightMap R C D M zc hc X) ⟶
    ForgetEnrichment.of (Complex R)
      (representable R (dgGluingLeftAxisObject R C D M zd X.left)) :=
  moduleConeDesc R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (dgGluingAxesYonedaRightMap R C D M zc hc X) (dgGluingAxesYonedaLeftMap R C D M zd hd X)
    (dgGluingAxesYoneda_comp_zero R C D M zc hc zd hd X)

/-- 同じ代表円錐比較は、元の左軸射の Yoneda 像を厳密に回収する。 -/
lemma dgGluingAxesYonedaConeComparison_inr (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    moduleConeInr R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (dgGluingAxesYonedaRightMap R C D M zc hc X) ≫
      dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X =
    dgGluingAxesYonedaLeftMap R C D M zd hd X :=
  moduleConeDesc_inr R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _ _ _

/-- 同じ実代表円錐比較の各評価は、元の二つの評価鎖写像からの円錐比較。 -/
lemma dgGluingAxesYonedaConeComparison_eval (X T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (moduleEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) T).map
      (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X) =
    complexConeDesc
      ((moduleEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) T).map
        (dgGluingAxesYonedaRightMap R C D M zc hc X))
      ((moduleEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) T).map
        (dgGluingAxesYonedaLeftMap R C D M zd hd X))
      (moduleCompZero_eval R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _ _
        (dgGluingAxesYoneda_comp_zero R C D M zc hc zd hd X) (Opposite.op T)) :=
  moduleConeDesc_eval R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _ _ _ T

end SerrePositivity.KST.SConstruction
