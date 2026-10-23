module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.InnerTwoHornDetection
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackAnodyneRestriction

/-!
概要：二次内ホーンへの元の cocartesian Hom の制限も自明 Kan fibration。
方針：欠ける長辺の保存を三角形分解で反映し、元の全相対 Hom の自明 Kan 性を移す。
規約：長辺が制限先に含まれるとは仮定しない。
使われ方：区間の貼り合わせから高次単体の Hom 比較へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {E F : SSet.{u}}
variable (p : E ⟶ (Δ[2] : SSet.{u})) [CocartesianFibration p]
variable (q : F ⟶ (Δ[2] : SSet.{u})) [CocartesianFibration q]

/-- 二次内ホーンへの指定辺保存 Hom の制限は、元の関手のままで自明 Kan。 -/
lemma cocartesianPullbackHomRestriction_innerTwoHorn_trivialKanFibration :
    TrivialKanFibration (cocartesianPullbackHomRestriction p q (Over.mk (horn 2 1).ι)) := by
  let a : Over (Δ[2] : SSet.{u}) := Over.mk (horn 2 1).ι
  let i : Over.mk (pullback.snd a.hom p ≫ p) ⟶ Over.mk p :=
    Over.homMk (pullback.snd a.hom p) rfl
  letI : Mono a.hom := by
    change Mono (horn 2 1).ι
    infer_instance
  letI : Mono i.left := by
    change Mono (pullback.snd a.hom p)
    infer_instance
  let V := {e | IsCocartesianEdge (pullback.fst a.hom p) e}
  let W := {e | IsCocartesianEdge p e}
  let hi := fun e he ↦ (isCocartesianEdge_overPullback_iff p a e).mp he
  have hr (v : (relativeFunctorSpace q p) _⦋0⦌)
      (hv : markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p) V
        ((relativeFunctorOverPre q i).app (Opposite.op ⦋0⦌) v)) :
      markedCocartesianFunctorPredicate q p W v := by
    obtain ⟨H, hH, rfl⟩ := exists_relativeFunctorVertex q p v
    have hv' := (congrArg
      (markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p) V)
      (relativeFunctorOverPre_vertex q i H hH)).mp hv
    have hv'' := (markedCocartesianFunctorPredicate_vertex q
      (pullback.snd a.hom p ≫ p) V (pullback.snd a.hom p ≫ H)
      (by rw [Category.assoc, hH])).mp hv'
    rw [markedCocartesianFunctorPredicate_vertex]
    apply preservesCocartesianEdges_of_innerTwoHorn p q H hH
    intro e he hb
    obtain ⟨d, hd, hde⟩ := exists_cocartesianPullbackEdge_of_base_edge p a e he
      ⟨p.app (Opposite.op ⦋1⦌) e, hb⟩ rfl
    have h := hv'' d hd
    change IsCocartesianEdge q
      (H.app (Opposite.op ⦋1⦌) ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) d)) at h
    rwa [hde] at h
  letI := relativeFunctorOverPre_trivialKanFibration_of_cocartesian q i
    (cocartesianPullback_snd_isPrecompositionEquivalence_of_innerAnodyne p a.hom
      (innerAnodyneExtensions.horn_ι (by decide) (by decide)))
  change TrivialKanFibration (markedCocartesianFunctorPre q i V W hi)
  exact fullRestriction_trivialKanFibration _ _ _ _ (markedCocartesianFunctorPre_ι q i V W hi) hr

/-- 二次内ホーンへの同じ指定辺保存 Hom の core の制限も自明 Kan。 -/
lemma core_cocartesianPullbackHomRestriction_innerTwoHorn_trivialKanFibration :
    TrivialKanFibration (quasicategoryCoreMap
      (cocartesianPullbackHomRestriction p q (Over.mk (horn 2 1).ι))) := by
  letI := cocartesianPullbackHomRestriction_innerTwoHorn_trivialKanFibration p q
  letI : Quasicategory (cocartesianPullbackHomSpace p q (Over.mk (horn 2 1).ι)) := by
    unfold cocartesianPullbackHomSpace
    infer_instance
  exact F2.coreMap_trivialKanFibration _

/-- 両射影を底変換した元の Hom の core への二次内ホーン制限も自明 Kan。 -/
lemma core_cocartesianPullbackNativeRestriction_innerTwoHorn_trivialKanFibration :
    TrivialKanFibration (quasicategoryCoreMap
      (cocartesianPullbackNativeRestriction p q (Over.mk (horn 2 1).ι))) := by
  let a : Over (Δ[2] : SSet.{u}) := Over.mk (horn 2 1).ι
  change TrivialKanFibration (quasicategoryCoreFunctor.map
    (cocartesianPullbackHomRestriction p q a ≫ (cocartesianPullbackHomIso p q a).inv))
  rw [Functor.map_comp]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (core_cocartesianPullbackHomRestriction_innerTwoHorn_trivialKanFibration p q).mem
    (trivialKanFibrations.of_isIso _)⟩

end SerrePositivity.InfinityCategories
