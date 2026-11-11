module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConeNativePathDown
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackHomotopyPoint

/-!
概要：元の coherent cospan 錐から、native 余極限写像の値の引き戻しへの比較射を作る。
方針：元の指定可換同型の円柱を両脚とともに path 引き戻しへ入れる。
規約：両脚と全 path 座標を保持。使われ方：全空間 Kan 比較との照合と交換の普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cl" =>
  coherentTotalMapNativeValueDown F X (coherentTransformationTotalMap F X C.toLeft)
local notation "cr" =>
  coherentTotalMapNativeValueDown F Y (coherentTransformationTotalMap F Y C.toRight)
local notation "cf" =>
  coherentTotalMapNativeValueDown X Z (coherentTransformationTotalMap X Z C.fromLeft)
local notation "cg" =>
  coherentTotalMapNativeValueDown Y Z (coherentTransformationTotalMap Y Z C.fromRight)

/-- 概要：元の指定可換同型の元の宇宙での円柱代表。
方針：同じ指定同型の射の代表。規約：類を保持。使われ方：引き戻し比較の全 path。 -/
def coherentCospanConeNativeComparisonHomotopy : SSet.Homotopy (cl ≫ cf) (cr ≫ cg) :=
  functorHomHomotopy (coherentCospanConeNativePathDownIso F X Y Z C).hom

/-- 概要：比較の円柱の類は元の下降した指定可換同型の射。
方針：同じ指定同型の代表の仕様。規約：元の類を保持。使われ方：指定 path の識別。 -/
lemma coherentCospanConeNativeComparisonHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (coherentCospanConeNativeComparisonHomotopy F X Y Z C)) =
        (coherentCospanConeNativePathDownIso F X Y Z C).hom := functorHomHomotopy_hom _

/-- 概要：元の両脚と指定可換 path を持つ、native 余極限値からの引き戻し比較射。
方針：同じ円柱と両脚を path 引き戻しへ入れる。
規約：元の宇宙の実際の射。使われ方：filtered 引き戻し交換の比較候補。 -/
def coherentCospanConeNativeComparison :
    (spaceInfinityObject (coherentDiagramTotalVertex F)).obj ⟶ intervalPullback cf cg :=
  intervalPullbackHomotopyPoint cf cg cl cr (coherentCospanConeNativeComparisonHomotopy F X Y Z C)

/-- 概要：比較射は元の第一脚を厳密に保持。
方針：第一座標。規約：射の等式。使われ方：元の二射影の照合。 -/
lemma coherentCospanConeNativeComparison_left :
    coherentCospanConeNativeComparison F X Y Z C ≫ intervalPullbackLeft cf cg = cl :=
  intervalPullbackHomotopyPoint_left _ _ _ _ _

/-- 概要：比較射は元の第二脚を厳密に保持。
方針：第二座標。規約：射の等式。使われ方：元の二射影の照合。 -/
lemma coherentCospanConeNativeComparison_right :
    coherentCospanConeNativeComparison F X Y Z C ≫ intervalPullbackRight cf cg = cr :=
  intervalPullbackHomotopyPoint_right _ _ _ _ _

/-- 概要：比較射の全 path 座標は元の指定可換同型の同じ円柱。
方針：元の円柱の curry を回収。
規約：全単体の厳密な等式。使われ方：元の指定 path との最終照合。 -/
lemma coherentCospanConeNativeComparison_path :
    coherentCospanConeNativeComparison F X Y Z C ≫ intervalPullbackPath cf cg =
      curry ((β_ (Δ[1] : SSet.{u})
        (spaceInfinityObject (coherentDiagramTotalVertex F)).obj).hom ≫
          (coherentCospanConeNativeComparisonHomotopy F X Y Z C).h) :=
  intervalPullbackHomotopyPoint_path _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
