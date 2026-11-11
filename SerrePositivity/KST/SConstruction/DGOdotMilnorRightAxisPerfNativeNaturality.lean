module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisPerfNativeComparison
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphPerfectNativeNaturality

/-!
概要：元右軸の二つの実 Perf 商延長比較を同じ中央比較射に自然に接続する。
方針：共通比較族の全自然性を同じ元二 graph・同じ解像度射へ特殊化する。
規約：元比較射・同じ resolved 商包含・二成分を保持。
使われ方：固定 ν への移送と native 増大 square の主接続。
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
local notation "F" => dgOdotMilnorRightAxisEndofunctor R d
local notation "τ" => dgOdotMilnorRightAxisComparison R d
local notation "q" => dgOdotMilnorResolvedInclusion R d
/-- 概要：同じ resolved 商と元包含先の native 全関手作用。
方針：同じ実延長作用を特殊化する。規約：元二 graph を保持。
使われ方：中央比較と増大 square の共通作用。 -/
abbrev dgOdotMilnorRightAxisPerfNativeFunctor : BimoduleCategory R (P) (P) ⥤
    hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R (Q)))) :=
  dgCellGraphExtendedNativeFunctor.{u, u} R (B) (Q) (q)
local notation "N" => dgOdotMilnorRightAxisPerfNativeFunctor R d

/-- 概要：元右軸中央射の実 Perf 商延長後の同じ全 native 比較射。
方針：元の解像度比較を同じ実 Perf 延長と包含で写す。
規約：元射を選び直さない。使われ方：二成分比較の実終端辺。 -/
abbrev dgOdotMilnorRightAxisPerfNativeArrow :=
  dgCellResolvedGraphPerfectExtendedNerveArrow.{u, u} R (B) (Q)
    (F) (DGFunctor.id (B)) (τ) (q)

/-- 概要：保存済み二成分の全比較は同じ中央比較射を保って自然。
方針：元の同じ二 graph・同じ商包含で一般の全自然性を適用する。
規約：二つの指定比較値と実 Perf 比較射を保持。
使われ方：native square と実中央射の固定 ν 接続。 -/
lemma dgOdotMilnorRightAxisPerfNativeComparison_naturality :
    (N).map (dgCellResolvedGraphMap R (B) (F) (DGFunctor.id (B)) (τ)) ≫
      (dgOdotMilnorRightAxisPerfNativeTargetComparison R d).hom =
    (dgOdotMilnorRightAxisPerfNativeSourceComparison R d).hom ≫
      dgOdotMilnorRightAxisPerfNativeArrow R d :=
  dgCellResolvedGraphPerfectExtendedNativeComparison_naturality.{u, u} R (B) (Q)
    (F) (DGFunctor.id (B)) (τ) (q)

/-- 概要：同じ元 graph の native 増大 square を同じ実包含先で回収する。
方針：元 square を同じ商延長と生包含で写す。規約：同じ中央射を保持。
使われ方：二成分比較と増大の四辺の同時照合。 -/
lemma dgOdotMilnorRightAxisPerfNativeAugmentationSquare :
    (N).map (dgCellResolvedGraphMap R (B) (F) (DGFunctor.id (B)) (τ)) ≫
      (N).map (dgCellResolvedGraphResolution R (B) (DGFunctor.id (B))).π =
    (N).map (dgCellResolvedGraphResolution R (B) (F)).π ≫
      (N).map (dgCellRestrictedGraphMap R (B) (F) (DGFunctor.id (B)) (τ)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R (Q)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R (Q))
  let H := SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) (Q) (q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I))
  exact (H.map_comp _ _).symm.trans
    ((congrArg H.map (dgCellResolvedGraphNativeSquare.{u, u} R (B) (F) (DGFunctor.id (B)) (τ))).trans
      (H.map_comp _ _))

end SerrePositivity.KST.SConstruction
