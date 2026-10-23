module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IntervalMappingFibration
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CorePullbackIso

/-!
概要：一次元の元の輸送図式の Hom の core は、同じ二成分の core の pullback。
方針：元の strict Hom の表示を、後合成の inner fibration に沿う core の交換に渡す。
規約：core が任意の pullback を保存するとは仮定しない。
使われ方：一次元セルの実際の coherent な Hom との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))

/-- 元の一次元変換空間の core を、元の二成分上の pullback と同型にする。 -/
def cocartesianIntervalMappingCorePullbackIso :
    (quasicategoryCore (strictDiagramMappingSpace F.val G.val) : SSet.{u}) ≅
      pullback
        (quasicategoryCoreMap ((ihom (F.val.obj (ULift.up 0))).map
          (G.val.map strictIntervalIndexArrow)))
        (quasicategoryCoreMap ((pre (F.val.map strictIntervalIndexArrow)).app
          (G.val.obj (ULift.up 1)))) := by
  letI : InnerFibration ((ihom (F.val.obj (ULift.up 0))).map
      (G.val.map strictIntervalIndexArrow)) :=
    F1B.KanEquivalenceLifting.innerFibration
      (kanEquivalenceLifting_cocartesianIntervalPostHom G (F.val.obj (ULift.up 0)))
  exact quasicategoryCoreFunctor.mapIso (strictIntervalMappingPullbackIso F.val G.val) ≪≫
    F2.corePullbackIso _ _

/-- 同じ core の比較の第一射影は、元の零成分の評価の core。 -/
lemma cocartesianIntervalMappingCorePullbackIso_fst :
    (cocartesianIntervalMappingCorePullbackIso F G).hom ≫ pullback.fst _ _ =
      quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0)) := by
  dsimp only [cocartesianIntervalMappingCorePullbackIso, Iso.trans_hom, Functor.mapIso_hom,
    F2.corePullbackIso]
  rw [Category.assoc, F2.corePullbackMap_fst]
  change quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _ = _
  rw [← Functor.map_comp, strictIntervalMappingPullbackIso_fst]
  rfl

/-- 同じ core の比較の第二射影は、元の一成分の評価の core。 -/
lemma cocartesianIntervalMappingCorePullbackIso_snd :
    (cocartesianIntervalMappingCorePullbackIso F G).hom ≫ pullback.snd _ _ =
      quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 1)) := by
  dsimp only [cocartesianIntervalMappingCorePullbackIso, Iso.trans_hom, Functor.mapIso_hom,
    F2.corePullbackIso]
  rw [Category.assoc, F2.corePullbackMap_snd]
  change quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _ = _
  rw [← Functor.map_comp, strictIntervalMappingPullbackIso_snd]
  rfl

/-- 元の二成分の core 上の評価は、同じ後合成・前合成の pullback。 -/
lemma cocartesianIntervalMappingCore_isPullback :
    IsPullback
      (quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0)))
      (quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 1)))
      (quasicategoryCoreMap ((ihom (F.val.obj (ULift.up 0))).map
        (G.val.map strictIntervalIndexArrow)))
      (quasicategoryCoreMap ((pre (F.val.map strictIntervalIndexArrow)).app
        (G.val.obj (ULift.up 1)))) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (cocartesianIntervalMappingCorePullbackIso F G)
    (cocartesianIntervalMappingCorePullbackIso_fst F G)
    (cocartesianIntervalMappingCorePullbackIso_snd F G)
  change quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _ =
    quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _
  rw [← Functor.map_comp, ← Functor.map_comp,
    strictDiagramMappingComponent_naturality F.val G.val strictIntervalIndexArrow]

open HomotopicalAlgebra SSet.modelCategoryQuillen in
/-- 元の一次元 Hom の一成分を固定する射は Kan fibration。 -/
lemma cocartesianIntervalMappingCore_one_fibration :
    Fibration (quasicategoryCoreMap
      (strictDiagramMappingComponent F.val G.val (ULift.up 1))) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  exact (SSet.modelCategoryQuillen.J.rlp).of_isPullback
    (cocartesianIntervalMappingCore_isPullback F G)
    ((SSet.modelCategoryQuillen.fibration_iff _).mp
      (core_cocartesianIntervalPostHom_fibration G _))

end SerrePositivity.InfinityCategories
