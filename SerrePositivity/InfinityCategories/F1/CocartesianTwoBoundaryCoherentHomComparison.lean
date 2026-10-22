module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundaryTargetPresentation
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundaryCoherentPullbackComparison

/-!
概要：共有境界の大域指定像と整合する、実際の二次元標準境界の Hom 比較同値。
方針：両側の同じ pullback 表示で、構成済みの厳密 cospan 比較を戻す。
規約：元の境界と両補正比較の指定 path を保持する。
使われ方：高次境界と有限セルによる Hom 比較の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "N" => cocartesianPullbackNativeLiftCoreFunctor p.val.hom q.val.hom
local notation "T" => intervalDiagramLiftOverFunctor
  (cocartesianStrictTransportCoherentDiagram p.val.hom)
  (cocartesianStrictTransportCoherentDiagram q.val.hom)

local instance (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex ((N).obj (Opposite.op z)) :=
  cocartesianNativeLiftCoreFunctor_obj_kan p.val.hom q.val.hom z
local instance (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex ((T).obj (Opposite.op z)) :=
  cocartesianIntervalLiftOverFunctor_obj_kan p q z

/-- 元の実際の二次元境界上の全 native Hom を、同じ分類先 Hom へ写す比較。 -/
def cocartesianTwoBoundaryCoherentHomComparison :
    (N).obj (Opposite.op (HornBoundaryOver.apex 1 σ)) ⟶
      (T).obj (Opposite.op (HornBoundaryOver.apex 1 σ)) :=
  (cocartesianTwoBoundaryNativePresentationIso p q).hom ≫
    cocartesianTwoBoundaryCoherentPullbackComparison j p q ≫
      (cocartesianTwoBoundaryTargetPresentationIso p q).inv

/-- 構成した同じ実際の二次元境界比較自体は、追加仮定なしに同値。 -/
lemma cocartesianTwoBoundaryCoherentHomComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTwoBoundaryCoherentHomComparison j p q) :=
  (qCatEquivalenceOfIso (cocartesianTwoBoundaryNativePresentationIso p q)).isQCatEquivalence.comp
    ((cocartesianTwoBoundaryCoherentPullbackComparison_isQCatEquivalence j p q).comp
      (qCatEquivalenceOfIso (cocartesianTwoBoundaryTargetPresentationIso p q).symm).isQCatEquivalence)

/-- 同じ比較を分類先の pullback 表示へ戻すと、元の厳密 pullback 比較。 -/
lemma cocartesianTwoBoundaryCoherentHomComparison_presentation :
    cocartesianTwoBoundaryCoherentHomComparison j p q ≫
      (cocartesianTwoBoundaryTargetPresentationIso p q).hom =
    (cocartesianTwoBoundaryNativePresentationIso p q).hom ≫
      cocartesianTwoBoundaryCoherentPullbackComparison j p q := by
  simp only [cocartesianTwoBoundaryCoherentHomComparison, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end SerrePositivity.InfinityCategories
