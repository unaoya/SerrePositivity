module
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedYonedaCommonExact
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorCommonExact
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorYonedaCommonIso
/-!
概要：前三角な小 dg 圏から独立の宇宙の全加群圏への任意の dg 関手は完全。
方針：共通宇宙の Yoneda と kernel tensor を合成し、実関手同型で元の作用へ移送する。
規約：Small は始域と係数圏だけ。対象宇宙の持ち上げ以外は変更しない。
使われ方：D2 G-1 e の混在宇宙の第二脚 M.toFunctor を直接接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) (C : Type w)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]

theorem dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor
    [IsDGPretriangulated R D] (F : DGFunctor R D (RightModule R C)) :
    IsExactFunctor (dgNerveCommonMap.{u, v, max (u + 1) w, max (u + 1) v w t} F) := by
  let P : Bimodule R C D := F
  let := dgPretriangulatedYonedaCommon_isExactFunctor.{u, v, max w t} R D
  let := dgModuleFunctorCommonNerve_isExactFunctor.{u, v, w, max (u + 1) v w t}
    R D C (Morita.kernelTensor R D C P)
  exact isExactFunctor_of_functorIso (dgKernelTensorYonedaCommonIso.{u, v, w, t} R D C P)

/-- 始域と全加群終域の対象だけを同じ宇宙へ上げた native nerve の完全性。 -/
theorem dgPretriangulatedModuleValuedFunctorLifted_isExactFunctor
    [IsDGPretriangulated R D] (F : DGFunctor R D (RightModule R C)) :
    IsExactFunctor (dgNerve.map (dgUniverseLiftFunctor.{u, v, max (u + 1) w,
      max (u + 1) v w t, max (u + 1) v w t} F)) := by
  let d := dgNerveUniverseLiftIso.{u, v, max (u + 1) v w t} R D
  let e := dgNerveUniverseLiftIso.{u, max (u + 1) w, max (u + 1) v w t}
    R (RightModule R C)
  let := dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor.{u, v, w, t} R D C F
  let := isExactFunctor_of_isQCatEquivalence (qCatEquivalenceOfIso d.symm).isQCatEquivalence
  let := isExactFunctor_of_isQCatEquivalence (qCatEquivalenceOfIso e).isQCatEquivalence
  have h : IsExactFunctor (d.inv ≫
      dgNerveCommonMap.{u, v, max (u + 1) w, max (u + 1) v w t} F ≫ e.hom) :=
    inferInstance
  rw [dgNerveCommonMap_lifted] at h
  simpa only [d, e, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h

end SerrePositivity.InfinityCategories
