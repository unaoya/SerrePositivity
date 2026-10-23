module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconePointHomComposition
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCoconeTotalComparison

/-!
概要：元の余錐の全 Hom 比較を、小さい全空間の内部 Hom 内で実際の相対合成と比較する。
方針：三角形の合成同型を、定値標的の fiber 表示と宇宙の同型で写す。
規約：元の余錐と元の標準比較を保持する。
使われ方：全空間の単位の前合成との残る作用比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B : SSet.{u}}

/-- 概要：定値 unstraightening への相対写像を小さい全空間から元の値への写像にする。
方針：定値 fiber 表示・値の比較・小さい内部 Hom の同型を続ける。
規約：実際の射。使われ方：元の相対合成の値の表示への移送。 -/
def coherentTotalRelativeComparison
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    relativeFunctorSpace (leftUnstraighteningProjection (SSet.const z))
      (leftUnstraighteningProjection F) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
        ((ihom (smallLeftUnstraightening F)).obj (spaceInfinityObject z).obj) :=
  (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom ≫
    (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z).hom ≫
      (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).hom

/-- 概要：相対表示の比較を続けると元の小さい定値標的比較そのもの。
方針：元の定義を展開する。規約：厳密な式。使われ方：標準比較の追跡。 -/
lemma coherentTotalRelativeComparison_factor
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    leftUnstraighteningMappingSpaceMap F (SSet.const z) ≫ coherentTotalRelativeComparison F z =
      coherentSmallConstantTargetMap F z := by
  simp only [coherentTotalRelativeComparison, coherentSmallConstantTargetMap,
    coherentConstantTargetMap, Category.assoc]

/-- 概要：元の全 Hom の標準全空間比較は、元の二つの比較の相対合成の像と同型。
方針：両端固定の対角比較と三角形の合成同型を元の標的の比較射で写す。
規約：全 Hom の族全体での同型。使われ方：単位の前合成への最後の作用比較。 -/
def coherentCoconeCompositionIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso (coconePointHomFamily c z ≫ coherentCoconeTotalComparison F z)
      (coconePointHomRelativeComposite c z ≫ coherentTotalRelativeComparison F z) := by
  have e := (coconePointHomNativeCompositionIso c z).postcomp (coherentTotalRelativeComparison F z)
  simpa only [Category.assoc, coherentTotalRelativeComparison_factor,
    coherentCoconeTotalComparison] using e

end SerrePositivity.InfinityCategories.F2
