module
public import SerrePositivity.InfinityCategories.Derived.DGNerveCommonLiftIso
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.Stable.UniverseExactFunctorLift
/-!
概要：前三角な小 dg 圏の Yoneda は任意の共通対象宇宙の nerve 上で完全。
方針：既存の共通宇宙 Yoneda をさらに持ち上げ、始域の上げ下げの実同型で移送する。
規約：全加群圏の Small 仮定を課さず、既存の完全性宣言を保持する。
使われ方：混在宇宙の加群値 dg 関手を kernel tensor と比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v t
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

theorem dgPretriangulatedYonedaCommon_isExactFunctor [IsDGPretriangulated R D] :
    IsExactFunctor (dgNerveCommonMap.{u, v, max (u + 1) v, max (u + 1) v t}
      (dgYoneda R D)) := by
  let L := (dgUniverseLiftDown.{u, v, max (u + 1) v} R D).comp (dgYoneda R D)
  let I := dgNerveCommonLiftIso.{u, v, max (u + 1) v, t} R D
  let := isExactFunctor_of_isQCatEquivalence (qCatEquivalenceOfIso I).isQCatEquivalence
  let := isExactFunctor_ulift.{max (u + 1) v, max (u + 1) v t}
    (dgNerve.map L) (dgPretriangulatedYoneda_isExactFunctor R D)
  have hf : (dgUniverseLiftUp.{u, v, max (u + 1) v} R D).comp L = dgYoneda R D := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [L, EnrichedFunctor.comp_map, dgUniverseLiftUp, dgUniverseLiftDown,
      dgObjectImageEvaluation, Category.id_comp, Category.comp_id, eqToHom_refl]
  have hc := dgNerveCommonMap_comp.{u, v, max (u + 1) v, max (u + 1) v, t}
    (dgUniverseLiftUp.{u, v, max (u + 1) v} R D) L
  rw [hf] at hc
  have h : IsExactFunctor (I.hom ≫
      (SSet.uliftFunctor.{max (u + 1) v t, max (u + 1) v}).map (dgNerve.map L)) :=
    inferInstance
  change IsExactFunctor
    (dgNerveCommonMap.{u, v, max (u + 1) v, max (u + 1) v t}
      (dgUniverseLiftUp.{u, v, max (u + 1) v} R D) ≫
        dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) v, max (u + 1) v t} L) at h
  rwa [hc] at h

end SerrePositivity.InfinityCategories
