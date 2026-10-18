module

public import SerrePositivity.InfinityCategories.F1B.UnitComparisonFiberForwardData
public import SerrePositivity.InfinityCategories.F1B.UnitCommaReconstructionParameters

/-!
概要：comma 写像空間から導来 fiber へ進んで戻る合成を恒等射に結ぶ。
方針：普遍標的・普遍ホモトピーの厳密な回収を、元の輸送の前合成の復元比較へ渡す。
規約：普遍族で選んだ輸送を制限し、パラメータ上で選び直した輸送とは同一視しない。
使われ方：B1 の各点の単位比較から comma 写像空間の可縮性へ進む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：comma の区間写像空間の恒等射は、導来 fiber へ進んで戻る合成にホモトピック。
方針：普遍正方形に、順方向比較で引き戻した普遍データと制限した輸送の比較を適用する。
規約：単位比較の同値性は仮定しない。逆向きのもう一方の合成はここでは主張しない。
使われ方：導来 fiber の可縮性を comma の写像空間へ移すための戻る合成。 -/
lemma unitCommaMappingToComparisonFiber_comp_return_homotopy {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    Nonempty (SSet.Homotopy (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w))
      (unitCommaMappingToComparisonFiber η x w ≫ unitComparisonFiberToCommaMapping η x w)) := by
  have h := unitCommaSquare_reconstruction_precomp_homotopy η x w
    (unitCommaFiberMappingSquare (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w)))
    (unitCommaMappingToComparisonFiber η x w) (unitComparisonFiberSource η x w)
    (unitComparisonFiberHomotopy η x w) (unitCommaMappingToComparisonFiber_source η x w)
    (unitCommaMappingToComparisonFiber_homotopy η x w)
  simpa only [unitCommaFiberMappingSquare_family, unitComparisonFiberToCommaMapping] using h

end SerrePositivity.InfinityCategories
