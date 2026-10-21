module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSectionIso
public import SerrePositivity.InfinityCategories.Derived.QCatEquivalenceAdjunction
/-!
概要：元の実入力切断と入力射影を、指定の両向き写像を持つ ∞ 圏同値へ包装する。
方針：厳密切断の全関手同値と、普遍余単位からの随伴を合成する。
規約：生の出力の射影性と大きい分解圏の Small 性は仮定しない。
使われ方：一般 RHom の実 ∞ 関手と三角恒等式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ実入力切断と元の射影による、両比較同型付き ∞ 圏同値。 -/
def dgModuleResolvedSourceSectionEquivalence :
    QCatEquivalence (dgNerve R C) (dgNerve R (DGModuleFunctorResolutionObject R C E F)) where
  hom := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  inv := dgNerve.map (dgModuleFunctorResolutionSource R C E F)
  homInvIso := by
    rw [dgModuleResolvedSourceSection_comp_source]
  invHomIso := dgModuleResolvedProjectionSectionIso R C E F
end SerrePositivity.InfinityCategories
