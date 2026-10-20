module

public import SerrePositivity.InfinityCategories.F2.CoherentCoconeComposition
public import SerrePositivity.InfinityCategories.F2.CoconeFiberHomComparison

/-!
概要：元の native 余錐の全 Hom 比較を元の pointed-space 輸送の作用へ移す。
方針：相対合成の比較と fiber の輸送比較を、同じ全 Hom パラメータで合成する。
規約：実際の比較射と輸送族を保持。使われ方：native 余極限写像と具体的 Kan 射の照合。
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
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌)

/-- 概要：元の余錐の全 Hom の輸送作用を元の全空間・値で表示。
方針：元の fiber 輸送の後で余錐の fiber 写像の前合成と値への後合成。
規約：全高次パラメータを保持。使われ方：指定した射の値の照合。 -/
def coherentCoconeTransportAction : pinchedHomLeft c.vertex z ⟶
    (ihom (leftUnstraightening F)).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj) :=
  (pointedIntervalTransport (pinchedHomLeftToIntervalMappingSpace c.vertex z)).map ≫
    (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z) ≫
      (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z).hom

/-- 概要：元の全 Hom の標準全空間比較は元の輸送作用と指定同型で結ばれる。
方針：相対合成の二つの比較を合成し、内部 Hom の縮小同型を消去する。
規約：全族の関手同型。使われ方：native 写像の元の作用を具体的な射へ比較。 -/
def coherentCoconeTransportActionIso :
    FunctorIso
      ((coconePointHomFamily c z ≫ coherentCoconeTotalComparison F z) ≫
        (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv)
      (coherentCoconeTransportAction F c z) := by
  let d := (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z).hom
  have e := (coconePointHomNativeCompositionIso c z).postcomp
    ((constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom ≫ d)
  have e' := (coconeFiberHomComparisonIso c z).postcomp d
  have he : FunctorIso
      ((coconePointHomFamily c z ≫ coherentCoconeTotalComparison F z) ≫
        (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv)
      ((coconePointHomRelativeComposite c z ≫
        (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom) ≫ d) := by
    simpa only [coherentCoconeTotalComparison, coherentSmallConstantTargetMap,
      coherentConstantTargetMap, Category.assoc, Iso.hom_inv_id, Category.comp_id] using e
  exact he ≪≫ e'

end SerrePositivity.InfinityCategories.F2
