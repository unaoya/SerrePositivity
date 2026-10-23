module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TriangleImageDetection
public import SerrePositivity.InfinityCategories.F1.ScaffoldNerveBridgeTriangles
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackAnodyneRestriction

/-!
概要：最初の辺と尾部への元の指定辺保存 Hom の制限は、全次元で自明 Kan。
方針：欠ける辺の三角形分解で辺保存を反映し、全相対 Hom の自明 Kan 制限から移す。
規約：元の全空間と全関手を固定する。
使われ方：元の分類 Hom 作用の高次単体への帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {E F : SSet.{u}}
  (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [CocartesianFibration p]
  (q : F ⟶ nerve (ULift.{u} (Fin (n + 2)))) [CocartesianFibration q]

/-- 同じ最初の辺と尾部への元の全指定辺保存 Hom の制限は自明 Kan。 -/
lemma cocartesianPullbackHomRestriction_scaffoldBridge_trivialKanFibration :
    TrivialKanFibration
      (cocartesianPullbackHomRestriction p q (Over.mk (scaffoldFiniteNerveBridge n))) := by
  let a : Over (nerve (ULift.{u} (Fin (n + 2)))) := Over.mk (scaffoldFiniteNerveBridge n)
  let i : Over.mk (pullback.snd a.hom p ≫ p) ⟶ Over.mk p :=
    Over.homMk (pullback.snd a.hom p) rfl
  letI : Mono a.hom :=
    mono_of_innerAnodyne a.hom (scaffoldFiniteNerveBridge_innerAnodyne n)
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
    apply preservesCocartesianEdges_of_triangleImage (scaffoldFiniteNerveBridge n)
      (scaffoldFiniteNerveBridge_missing_edge_triangle n) p q H hH
    rintro e he ⟨b, hb⟩
    obtain ⟨d, hd, hde⟩ := exists_cocartesianPullbackEdge_of_base_edge p a e he b hb
    have h := hv'' d hd
    change IsCocartesianEdge q
      (H.app (Opposite.op ⦋1⦌) ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) d)) at h
    rwa [hde] at h
  letI := relativeFunctorOverPre_trivialKanFibration_of_cocartesian q i
    (cocartesianPullback_snd_isPrecompositionEquivalence_of_innerAnodyne p a.hom
      (scaffoldFiniteNerveBridge_innerAnodyne n))
  change TrivialKanFibration (markedCocartesianFunctorPre q i V W hi)
  exact fullRestriction_trivialKanFibration _ _ _ _ (markedCocartesianFunctorPre_ι q i V W hi) hr

end SerrePositivity.InfinityCategories
