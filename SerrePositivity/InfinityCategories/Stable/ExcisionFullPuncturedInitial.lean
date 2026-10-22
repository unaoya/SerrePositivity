module
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullPuncturedRetraction
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.F2.ConeValEquality
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionCorePuncturedToFull_nerve_mono :
    Mono (nerveMap excisionCorePuncturedToFull.{u}.toFunctor) :=
  nerveMap_mono_of_thin_of_obj_injective _ excisionFullPuncturedToCore_section.injective

lemma excisionCorePuncturedToFull_leftAnodyne :
    leftAnodyneExtensions (nerveMap excisionCorePuncturedToFull.{u}.toFunctor) :=
  orderRetraction_leftAnodyne _ _ excisionFullPuncturedToCore_section
    excisionFullPuncturedToCore_le

lemma excisionCorePuncturedToFull_projection :
    nerveMap excisionCorePuncturedToFull.{u}.toFunctor ≫
      nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) =
        nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫
          nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion := by
  apply thinNerveHom_ext_of_vertices
  intro v
  rfl

end SerrePositivity.InfinityCategories
