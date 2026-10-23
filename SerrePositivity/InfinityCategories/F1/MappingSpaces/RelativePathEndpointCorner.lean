module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RelativePathEquivalenceFibration

/-!
概要：path 置換で指定された元の端点を保つ比較の全境界持ち上げ。
方針：相対可逆 path 写像の実際の pullback として比較を表示する。
規約：指定端点は零・一のいずれでもよい。
使われ方：比較四角形の同時解像の一方の射を trivial Kan fibration にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 端点の元の対象を固定し、path を次の射で写す比較。 -/
def relativePathEndpointCorner {A X Y : SSet.{u}} (u : A ⟶ X) (q : X ⟶ Y) (j : Fin 2) :
    relativeEquivalencePathTargetAt u j ⟶ relativeEquivalencePathTargetAt (u ≫ q) j :=
  relativePathSquareTargetMap u (u ≫ q) (𝟙 A) q (by simp) j

/-- 端点を元の射で写し、path を固定する比較。 -/
def relativePathEndpointCornerBase {A X Y : SSet.{u}}
    (u : A ⟶ X) (q : X ⟶ Y) (j : Fin 2) :
    relativeEquivalencePathTargetAt (u ≫ q) j ⟶ relativeEquivalencePathTargetAt q j :=
  relativePathSquareTargetMap (u ≫ q) q u (𝟙 Y) (by simp) j

/-- 元の端点を保つ比較は、相対可逆 path の写像の実際の pullback。 -/
lemma relativePathEndpointCorner_isPullback {A X Y : SSet.{u}}
    (u : A ⟶ X) (q : X ⟶ Y) (j : Fin 2) :
    IsPullback (pullback.fst (equivalencePathEndpoint X j) u)
      (relativePathEndpointCorner u q j) (relativeEquivalencePathMapAt q j)
      (relativePathEndpointCornerBase u q j) := by
  have hrf : relativePathEndpointCorner u q j ≫
      pullback.fst (equivalencePathEndpoint Y j) (u ≫ q) =
        pullback.fst (equivalencePathEndpoint X j) u ≫ equivalencePathMap q :=
    relativePathSquareTargetMap_fst _ _ _ _ _ _
  have hrs : relativePathEndpointCorner u q j ≫
      pullback.snd (equivalencePathEndpoint Y j) (u ≫ q) =
        pullback.snd (equivalencePathEndpoint X j) u := by
    simpa only [relativePathEndpointCorner, Category.comp_id] using
      (relativePathSquareTargetMap_snd u (u ≫ q) (𝟙 A) q (by simp) j)
  have hbf : relativePathEndpointCornerBase u q j ≫
      pullback.fst (equivalencePathEndpoint Y j) q =
        pullback.fst (equivalencePathEndpoint Y j) (u ≫ q) := by
    simpa only [relativePathEndpointCornerBase, equivalencePathMap_id, Category.comp_id] using
      (relativePathSquareTargetMap_fst (u ≫ q) q u (𝟙 Y) (by simp) j)
  have hbs : relativePathEndpointCornerBase u q j ≫
      pullback.snd (equivalencePathEndpoint Y j) q =
        pullback.snd (equivalencePathEndpoint Y j) (u ≫ q) ≫ u :=
    relativePathSquareTargetMap_snd _ _ _ _ _ _
  have hw : pullback.fst (equivalencePathEndpoint X j) u ≫
      relativeEquivalencePathMapAt q j =
        relativePathEndpointCorner u q j ≫ relativePathEndpointCornerBase u q j := by
    apply pullback.hom_ext
    · rw [Category.assoc, relativeEquivalencePathMapAt_fst, Category.assoc, hbf, hrf]
    · rw [Category.assoc, relativeEquivalencePathMapAt_snd, Category.assoc, hbs,
        ← Category.assoc, hrs, pullback.condition]
  refine IsPullback.mk' hw ?_ ?_
  · intro T f g hf hg
    apply pullback.hom_ext hf
    have he := congrArg (fun m : T ⟶ relativeEquivalencePathTargetAt (u ≫ q) j ↦
      m ≫ pullback.snd (equivalencePathEndpoint Y j) (u ≫ q)) hg
    simpa only [Category.assoc, hrs] using he
  · intro T f b hb
    have hc : f ≫ equivalencePathEndpoint X j =
        b ≫ pullback.snd (equivalencePathEndpoint Y j) (u ≫ q) ≫ u := by
      have he := congrArg (fun m : T ⟶ relativeEquivalencePathTargetAt q j ↦
        m ≫ pullback.snd (equivalencePathEndpoint Y j) q) hb
      simpa only [Category.assoc, relativeEquivalencePathMapAt_snd, hbs] using he
    refine ⟨pullback.lift f
      (b ≫ pullback.snd (equivalencePathEndpoint Y j) (u ≫ q)) hc, pullback.lift_fst _ _ _, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hrf, ← Category.assoc, pullback.lift_fst]
      have he := congrArg (fun m : T ⟶ relativeEquivalencePathTargetAt q j ↦
        m ≫ pullback.fst (equivalencePathEndpoint Y j) q) hb
      simpa only [Category.assoc, relativeEquivalencePathMapAt_fst, hbf] using he
    · rw [Category.assoc, hrs, pullback.lift_snd]

/-- 相対可逆 path の持ち上げを持つ射の端点比較は trivial Kan fibration。 -/
instance relativePathEndpointCorner_trivialKanFibration {A X Y : SSet.{u}}
    (u : A ⟶ X) (q : X ⟶ Y) (j : Fin 2)
    [TrivialKanFibration (relativeEquivalencePathMapAt q j)] :
    TrivialKanFibration (relativePathEndpointCorner u q j) :=
  ⟨trivialKanFibrations.of_isPullback (relativePathEndpointCorner_isPullback u q j)
    (TrivialKanFibration.mem (p := relativeEquivalencePathMapAt q j))⟩

end SerrePositivity.InfinityCategories
