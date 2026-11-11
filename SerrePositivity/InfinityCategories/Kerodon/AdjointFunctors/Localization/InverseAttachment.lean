module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WalkingEquivalenceUniversal
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ParametricDiagramGluing
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization

/-!
概要：任意の辺集合に可逆区間を一斉に貼り、元の全ての指定辺を反転する実射を作る。
方針：指定辺の余積と Kan 区間の余積の pushout を取る。
規約：貼合せ先の quasicategory 性と局所化普遍性は後続で証明する。
使われ方：一般の安定 ∞ 圏の Verdier 商の実構成の最初の段階。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

variable (X : SSet.{u}) (W : Set (X _⦋1⦌))

def markedEdgeFamily : SSet.{u} := ∐ (fun _ : W => (Δ[1] : SSet.{u}))

def inverseIntervalFamily : SSet.{u} := ∐ (fun _ : W => walkingEquivalence.{u})

def markedEdgeEvaluation : markedEdgeFamily X W ⟶ X :=
  Sigma.desc (fun w => SSet.yonedaEquiv.symm w.val)

def inverseIntervalAttachment : markedEdgeFamily X W ⟶ inverseIntervalFamily X W :=
  Sigma.desc (fun w => walkingEquivalenceEdge ≫ Sigma.ι (fun _ : W => walkingEquivalence) w)

lemma markedEdgeEvaluation_ι (w : W) :
    Sigma.ι (fun _ : W => (Δ[1] : SSet.{u})) w ≫ markedEdgeEvaluation X W =
      SSet.yonedaEquiv.symm w.val := Sigma.ι_comp_desc _ _

lemma inverseIntervalAttachment_ι (w : W) :
    Sigma.ι (fun _ : W => (Δ[1] : SSet.{u})) w ≫ inverseIntervalAttachment X W =
      walkingEquivalenceEdge ≫ Sigma.ι (fun _ : W => walkingEquivalence) w :=
  Sigma.ι_comp_desc _ _

def inverseAttachment : SSet.{u} :=
  pushout (markedEdgeEvaluation X W) (inverseIntervalAttachment X W)

def inverseAttachmentInclusion : X ⟶ inverseAttachment X W :=
  pushout.inl _ _

def inverseAttachmentInterval (w : W) : walkingEquivalence.{u} ⟶ inverseAttachment X W :=
  Sigma.ι (fun _ : W => walkingEquivalence) w ≫ pushout.inr _ _

lemma inverseAttachment_edge (w : W) :
    SSet.yonedaEquiv.symm w.val ≫ inverseAttachmentInclusion X W =
      walkingEquivalenceEdge ≫ inverseAttachmentInterval X W w := by
  have h := congrArg (fun f => Sigma.ι (fun _ : W => (Δ[1] : SSet.{u})) w ≫ f)
    (pushout.condition (f := markedEdgeEvaluation X W) (g := inverseIntervalAttachment X W))
  rw [← Category.assoc, ← Category.assoc, markedEdgeEvaluation_ι,
    inverseIntervalAttachment_ι] at h
  simpa only [inverseAttachmentInclusion, inverseAttachmentInterval, Category.assoc] using h

lemma inverseAttachment_inverts : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (inverseAttachmentInclusion X W) W := by
  intro s hs
  let w : W := ⟨s, hs⟩
  have h := congrArg SSet.yonedaEquiv (inverseAttachment_edge X W w)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_comp] at h
  change (inverseAttachmentInclusion X W).app (Opposite.op ⦋1⦌) s = _ at h
  have he := kanSource_map_invertible (inverseAttachmentInterval X W w)
    (SSet.yonedaEquiv walkingEquivalenceEdge)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map
    ((truncation 2).map (inverseAttachmentInclusion X W)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr h).mpr he

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
