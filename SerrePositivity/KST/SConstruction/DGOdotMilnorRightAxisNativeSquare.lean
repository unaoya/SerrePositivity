module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphNativeSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleDerivedFunctor

/-!
概要：元右軸 graph の増大比較を同じ resolved 商の native 導来加群値へ移す。
方針：同じ全関手射と二つの増大同型を元商包含の実導来延長で後合成する。
規約：固定 ν の小模型・実 lax 中央射との比較は別工程。
使われ方：d④ の同じ resolved 商上の native 増大境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "P" => DGCategoryCellResolution.Source R (B)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) (Q) (dgOdotMilnorResolvedInclusion R d)
local notation "F" => dgOdotMilnorRightAxisEndofunctor R d
local notation "τ" => dgOdotMilnorRightAxisComparison R d

/-- 概要：同じ cell graph の native 全関手射を同じ resolved 商上で読む。
方針：元商包含の実導来延長を全関手圏で後合成する。
規約：元の指定包含を保持。使われ方：中央比較 square の実 native 値域。 -/
def dgOdotMilnorRightAxisNativeFunctor : BimoduleCategory R (P) (P) ⥤
    hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R (Q))) :=
  dgCellGraphNativeFunctor.{u, u} R (B) ⋙
    SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).map (E))

/-- 概要：元右軸 graph 増大の同じ resolved 商値の全関手同型。
方針：元の指定増大を同じ実導来延長で後合成する。
規約：元全単体を保持。使われ方：中央比較の第一縦辺。 -/
def dgOdotMilnorRightAxisNativeSourceAugmentation :=
  (dgCellResolvedGraphAugmentationNativeComparison.{u, u} R (B) (F)).postcomp (E)

/-- 概要：元恒等 graph 増大の同じ resolved 商値の全関手同型。
方針：元の指定増大を同じ実導来延長で後合成する。
規約：元全単体を保持。使われ方：中央比較の第二縦辺。 -/
def dgOdotMilnorRightAxisNativeTargetAugmentation :=
  (dgCellResolvedGraphAugmentationNativeComparison.{u, u} R (B) (DGFunctor.id (B))).postcomp (E)

/-- 概要：元右軸から恒等への比較と二増大は同じ商値の全関手圏で可換。
方針：元 native square を同じ商包含の実導来延長で写す。
規約：同じ解像度比較・同じ増大を保持。使われ方：native 中央辺の全自然性。 -/
lemma dgOdotMilnorRightAxisNativeSquare :
    (dgOdotMilnorRightAxisNativeFunctor R d).map
        (dgCellResolvedGraphMap R (B) (F) (DGFunctor.id (B)) τ) ≫
      (dgOdotMilnorRightAxisNativeFunctor R d).map
        (dgCellResolvedGraphResolution R (B) (DGFunctor.id (B))).π =
    (dgOdotMilnorRightAxisNativeFunctor R d).map (dgCellResolvedGraphResolution R (B) (F)).π ≫
      (dgOdotMilnorRightAxisNativeFunctor R d).map
        (dgCellRestrictedGraphMap R (B) (F) (DGFunctor.id (B)) τ) := by
  let H := SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).map (E))
  exact (H.map_comp _ _).symm.trans
    ((congrArg H.map (dgCellResolvedGraphNativeSquare.{u, u} R (B) (F) (DGFunctor.id (B)) τ)).trans
      (H.map_comp _ _))

end SerrePositivity.KST.SConstruction
