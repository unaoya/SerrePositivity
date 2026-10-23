module

public import SerrePositivity.InfinityCategories.F1.Coherent.LeftIntervalNaturality
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedLeftIntervalComparison

/-!
概要：Kan 値豊穣図式の左 Hom 作用を、標準 Kan 頂点での pointed 区間族へ移す。
方針：左区間族の豊穣自然性を、同じ端点表示の正規化後に curry する。
規約：Hom の反転と宇宙持ち上げを保ち、実際の豊穣 Hom の作用を使う。
使われ方：Hom 関手の大域比較の pointed 輸送を、恒等射への Kan 作用へ結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の全左 Hom の区間作用は、標準頂点上の同じ pointed Kan 区間作用に厳密に一致。 -/
lemma coherentKanLeftHomIntervalMap_naturality
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C KanObject.{u}) (X Y : C) :
    ((HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom X Y)).inv ≫
      HomotopyLimits.coherentCosliceFiberComparison X Y ≫
        cosliceFiberToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y)) ≫
      intervalMappingPostOfEq (coherentNerveMap F) (coherentNerveVertex X) (coherentNerveVertex Y)
        ((coherentNerveMap_vertex F X).trans (spaceInfinityVertex_eq_coherent (F.obj X)).symm)
        ((coherentNerveMap_vertex F Y).trans (spaceInfinityVertex_eq_coherent (F.obj Y)).symm) =
    SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map (F.map X Y)) ≫
      intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval (F.obj X) (F.obj Y))
        (pointedReverseKanHomInterval_zero (F.obj X) (F.obj Y))
        (pointedReverseKanHomInterval_one (F.obj X) (F.obj Y)) := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingPostOfEq_uncurry,
    intervalMappingUncurry_precomp
      (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map (F.map X Y)))
      (intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval (F.obj X) (F.obj Y))
        (pointedReverseKanHomInterval_zero (F.obj X) (F.obj Y))
        (pointedReverseKanHomInterval_one (F.obj X) (F.obj Y))),
    intervalMappingUncurry_curryOfEndpoints, pointedReverseKanHomInterval_eq_left]
  exact coherentLeftHomInterval_enriched_naturality F X Y

end SerrePositivity.InfinityCategories
