module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteEvaluationOuterProjections
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTrianglePointEvaluation
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：元の反復射影の全評価 Kan 脚を、元の反復 Kan 積の全射影とホモトピーで比較する。
方針：後続脚の元の選択三角形を評価し、snd と帰納仮定を同じ向きで続ける。
規約：元の頂点・脚の辺・選択済み合成三角形を保持する。
使われ方：元の評価錐の点ごとの極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の後続評価脚は、元の snd と元の tail 評価脚の合成へ同じ三角形で比較される。 -/
def finiteFunctorEvaluationKanLeg_succ_homotopy (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1 + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) (j : Fin (n + 1)) :
    SSet.Homotopy (finiteFunctorEvaluationKanLeg (n + 1) F b (Discrete.mk (ULift.up j.succ)))
      (snd (finiteFunctorKanValues (n + 1) F b 0).obj
        (finiteKanProductObject n (finiteFunctorKanValues n (fun i ↦ F i.succ) b)).obj ≫
          finiteFunctorEvaluationKanLeg n (fun i ↦ F i.succ) b (Discrete.mk (ULift.up j))) := by
  let G := finiteCoherentSpaceProduct n (fun i ↦ F i.succ)
  let x := coherentSpaceTensorProductSndVertex (F 0) G
  let y := finiteCoherentProjectionVertex n (fun i ↦ F i.succ) j
  let T := F2.coherentTransformationVertexTriangle (finiteCoherentSpaceProduct (n + 1) F)
    G (F j.succ) x y
  refine coherentTransformationTriangleAtHomotopy _ G (F j.succ) x y T b
    (show finiteKanProductObject (n + 1) (finiteFunctorKanValues (n + 1) F b) ⟶
      finiteKanProductObject n (finiteFunctorKanValues n (fun i ↦ F i.succ) b) from
        snd (finiteFunctorKanValues (n + 1) F b 0).obj
          (finiteKanProductObject n (finiteFunctorKanValues n (fun i ↦ F i.succ) b)).obj)
    (finiteFunctorEvaluationKanLeg n (fun i ↦ F i.succ) b (Discrete.mk (ULift.up j)))
    (finiteFunctorEvaluationKanLeg (n + 1) F b (Discrete.mk (ULift.up j.succ))) ?_ ?_ ?_
  · exact finiteFunctorTailSnd_edge n F b
  · exact (finiteFunctorEvaluationKanLeg_edge n (fun i ↦ F i.succ) b
      (Discrete.mk (ULift.up j))).symm
  · exact (finiteFunctorEvaluationKanLeg_edge (n + 1) F b
      (Discrete.mk (ULift.up j.succ))).symm

/-- 元の全評価 Kan 脚は、元の反復 Kan 積の各射影にホモトピック。 -/
lemma finiteFunctorEvaluationKanLeg_projection_homotopy (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌)
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    Nonempty (SSet.Homotopy (finiteFunctorEvaluationKanLeg n F b i)
      (nonemptyFiniteSSetProjection n (fun j ↦ (finiteFunctorKanValues n F b j).obj)
        i.as.down)) := by
  rcases i with ⟨⟨i⟩⟩
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rw [finiteFunctorEvaluationKanLeg_zero]
    exact ⟨functorHomotopyRefl _⟩
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [finiteFunctorEvaluationKanLeg_first]
      exact ⟨functorHomotopyRefl _⟩
    · let a := snd (finiteFunctorKanValues (n + 1) F b 0).obj
        (finiteKanProductObject n (finiteFunctorKanValues n (fun k ↦ F k.succ) b)).obj
      let H := finiteFunctorEvaluationKanLeg_succ_homotopy n F b j
      let L := functorHomotopyPrecomp (Classical.choice (ih (fun k ↦ F k.succ) j)) a
      have e : FunctorIso
          (finiteFunctorEvaluationKanLeg (n + 1) F b (Discrete.mk (ULift.up j.succ)))
          (nonemptyFiniteSSetProjection (n + 1)
            (fun k ↦ (finiteFunctorKanValues (n + 1) F b k).obj) j.succ) :=
        (functorIsoOfSimplicialHomotopy H) ≪≫ functorIsoOfSimplicialHomotopy L
      exact ⟨e.simplicialHomotopy⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
