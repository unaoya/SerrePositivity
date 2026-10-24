module
public import SerrePositivity.KST.Fibration.PullbackStrictEvaluation
public import SerrePositivity.KST.Fibration.IntervalPrismCancellation
public import SerrePositivity.KST.Fibration.CocartesianKanDiagram
public import SerrePositivity.KST.LocalizingInvariants.IntervalPostcompositionFamily

/-! # 元の区間上の両側 fibration が与える同じ strict transport の可逆性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の圏の射の区間は、同じ始点の nerve 頂点を持つ。 -/
theorem nerveInterval_source_vertex {I : Type u} [Category.{u} I]
    {c d : I} (f : c ⟶ d) :
    (yonedaEquiv.symm (nerve.edgeMk f).edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = nerveVertex c := by
  rw [← intervalMap_source, Equiv.apply_symm_apply]
  exact ComposableArrows.ext₀ rfl

/-- 元の圏の射の区間は、同じ終点の nerve 頂点を持つ。 -/
theorem nerveInterval_target_vertex {I : Type u} [Category.{u} I]
    {c d : I} (f : c ⟶ d) :
    (yonedaEquiv.symm (nerve.edgeMk f).edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = nerveVertex d := by
  rw [← intervalMap_target, Equiv.apply_symm_apply]
  exact ComposableArrows.ext₀ rfl

/-- 元の辺の区間上で両側なら、同じ全 section の輸送は局所化で可逆。 -/
theorem pullbackStrictTransportMap_bilateralEdge_localized_isIso
    {I : Type u} [Category.{u} I] {F B : SSet.{u}}
    (q : F ⟶ B) (k : nerve I ⟶ B) [CocartesianFibration (pullback.snd q k)]
    {c d : I} (f : c ⟶ d)
    [CartesianFibration (pullback.snd q (yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k))]
    [CocartesianFibration (pullback.snd q (yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k))] :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (SerrePositivity.InfinityCategories.cocartesianStrictTransportMap (pullback.snd q k) f)) := by
  let b := yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k
  have hc : k.app (Opposite.op ⦋0⦌) (nerveVertex c) =
      b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
    (congrArg (k.app (Opposite.op ⦋0⦌)) (nerveInterval_source_vertex f)).symm
  have hd : k.app (Opposite.op ⦋0⦌) (nerveVertex d) =
      b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
    (congrArg (k.app (Opposite.op ⦋0⦌)) (nerveInterval_target_vertex f)).symm
  let u := pullbackStrictEvaluationAt q k c _ hc
  let v := pullbackStrictEvaluationAt q k d _ hd
  let t := SerrePositivity.InfinityCategories.cocartesianStrictTransportMap (pullback.snd q k) f
  let H := strictTransportEvaluationPrism (pullback.snd q k) f ≫ pullback.fst q k
  have hp : H ≫ q = fst (Δ[1] : SSet.{u}) _ ≫ b := by
    dsimp only [H, b]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      strictTransportEvaluationPrism_projection, Category.assoc]
  have h₀ : prismEndpoint 0 _ ≫ H = u ≫ vertexFiberι q _ := by
    dsimp only [H]
    rw [← Category.assoc, strictTransportEvaluationPrism_zero, Category.assoc]
    exact (pullbackStrictEvaluationAt_ι q k c _ hc).symm
  have h₁ : prismEndpoint 1 _ ≫ H = (t ≫ v) ≫ vertexFiberι q _ := by
    dsimp only [H]
    rw [← Category.assoc, strictTransportEvaluationPrism_one, Category.assoc, Category.assoc]
    exact (congrArg (fun m => t ≫ m) (pullbackStrictEvaluationAt_ι q k d _ hd).symm).trans
      (Category.assoc _ _ _).symm
  have hu := pullbackStrictEvaluationAt_localized_isIso q k c _ hc
  have hv : IsIso (AnodyneHomotopy.anodyneQ.map v) :=
    pullbackStrictEvaluationAt_localized_isIso q k d _ hd
  have ht := intervalPrism_target_localized_isIso q b u (t ≫ v) H h₀ h₁ hp hu
  rw [Functor.map_comp] at ht
  exact (isIso_comp_right_iff _ _).mp ht

/-- 同じ厳密 Kan 図式の遷移も、両側となる元の区間を実際の同値に送る。 -/
theorem cocartesianKanDiagram_map_bilateralEdge_isQCatEquivalence
    {I : Type u} [Category.{u} I] {F B : SSet.{u}}
    (q : F ⟶ B) (k : nerve I ⟶ B) [CocartesianFibration (pullback.snd q k)]
    {c d : I} (f : c ⟶ d)
    [CartesianFibration (pullback.snd q (yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k))]
    [CocartesianFibration (pullback.snd q (yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k))] :
    IsQCatEquivalence ((cocartesianKanDiagram (pullback.snd q k)).map f) :=
  strictKanCompletion_map_isQCatEquivalence _
    (pullbackStrictTransportMap_bilateralEdge_localized_isIso q k f)

end SerrePositivity.KST.Fibration
