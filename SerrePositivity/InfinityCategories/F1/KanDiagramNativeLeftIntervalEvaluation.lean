module

public import SerrePositivity.InfinityCategories.F1.KanEnrichedLeftHomIntervalEvaluation
public import SerrePositivity.InfinityCategories.F1.KanDiagramNativeOppositeParameterEvaluation

/-!
概要：native な左区間の各対象での値を、元の変換の Kan 作用で表す。
方針：共同評価の公式に係数反転の厳密な式を入れ、同じ右端パラメーターを保持する。
規約：pointed prism の存在は主張せず、その底に必要な全区間の等式を証明する。
使われ方：共通 weighted 始域からの prism と元の作用との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 左区間の全パラメーターでの対象評価は、元の変換の評価からの標準反転作用。 -/
lemma kanDiagramOppositeLeftHomInterval_evaluate_action
    {I : Type u} [SmallCategory I] (F G : KanDiagramObject I) (i : I) :
    intervalMappingUncurry (kanDiagramOppositeLeftHomInterval F G) ≫
        evaluateFunctorAt (ULift.up (nerveVertex i)) =
      (Δ[1] ◁ ((SSet.uliftFunctor.{u + 1, u}).map
        (edgewiseRight (SimplicialCategory.sHom F G)) ≫
        leftPointHomReverseParameter (uncurry (strictDiagramMappingComponent
          (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i)))) ≫
      coherentLeftHomInterval (kanObjectOpFunctor.obj (F.val.obj i))
        (kanObjectOpFunctor.obj (G.val.obj i)) := by
  let F' : KanDiagramObject I := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩
  let G' : KanDiagramObject I := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩
  let c := strictDiagramMappingComponent
    (F'.val ⋙ kanObjectForget) (G'.val ⋙ kanObjectForget) i
  have hn : (uliftOppositeIso (SimplicialCategory.sHom F' G')).hom ≫
      SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map c) =
      (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map c) ≫
        (uliftOppositeIso ((ihom (F'.val.obj i).obj).obj (G'.val.obj i).obj)).hom := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [kanDiagramOppositeLeftHomInterval_eq_native]
  simp only [intervalMappingUncurry_precomp, Category.assoc]
  rw [kanEnrichedDiagramLeftHomInterval_evaluate_action]
  have hp := kanDiagramNativeOppositeHomParameter_pointwise F G i
  have hp' : (SSet.uliftFunctor.{u + 1, u}).map
      (kanDiagramNativeOppositeHomParameter F G) ≫
      ((uliftOppositeIso (SimplicialCategory.sHom F' G')).hom ≫
        SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map c)) =
      leftPointHomReverseParameter (uncurry (strictDiagramMappingComponent
        (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i)) :=
    (congrArg (fun k => (SSet.uliftFunctor.{u + 1, u}).map
      (kanDiagramNativeOppositeHomParameter F G) ≫ k) hn).trans hp
  have h := congrArg (fun k => (Δ[1] ◁ k) ≫
    coherentLeftHomInterval (kanObjectOpFunctor.obj (F.val.obj i))
      (kanObjectOpFunctor.obj (G.val.obj i))) hp'
  have h' := congrArg (fun k => (Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseRight (SimplicialCategory.sHom F G))) ≫ k) h
  simp only [whiskerLeft_comp, Category.assoc] at h' ⊢
  convert h' using 1 <;> rfl

end SerrePositivity.InfinityCategories
