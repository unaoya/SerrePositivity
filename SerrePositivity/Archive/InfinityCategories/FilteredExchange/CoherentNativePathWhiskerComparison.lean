module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativePathDownComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeCompositeDownWhisker
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange

/-!
概要：小宇宙の native 可換式を四つの元の値比較の指定正方形として表示する。
方針：合成比較の下降を二比較の水平合成へ戻し、前後合成の交換則で順序を揃える。
規約：四射・元の可換同型の指定値を保持。使われ方：左右の脚の底の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight

/-- 元の四つの値比較の正方形は、元の小宇宙の可換 path と同じ指定値で整合する。 -/
lemma coherentCospanConeNativePathDownIso_whisker :
    (coherentTotalMapNativeValueDownIso X Z cf).precomp
        (coherentTotalMapNativeValueDown F X cl) ≪≫
      (coherentTotalMapNativeValueDownIso F X cl).postcomp (coherentTotalVertexMap X Z cf) ≪≫
        coherentCospanConeValuePathIso F X Y Z C =
    coherentCospanConeNativePathDownIso F X Y Z C ≪≫
      (coherentTotalMapNativeValueDownIso Y Z cg).precomp
        (coherentTotalMapNativeValueDown F Y cr) ≪≫
      (coherentTotalMapNativeValueDownIso F Y cr).postcomp (coherentTotalVertexMap Y Z cg) := by
  have h := coherentCospanConeNativePathDownIso_comparison F X Y Z C
  rw [coherentTotalMapNativeCompositeDownIso_eq_whisker,
    coherentTotalMapNativeCompositeDownIso_eq_whisker,
    functorIso_whisker_exchange, functorIso_whisker_exchange] at h
  simpa only [Iso.trans_assoc] using h

end SerrePositivity.InfinityCategories.F2
