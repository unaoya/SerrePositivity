module
public import SerrePositivity.KST.Fibration.Relative.ClosedFlagFactor
public import SerrePositivity.KST.Fibration.Relative.ClosedCofiberProjection
public import SerrePositivity.KST.Fibration.TailWeakJointReflection

/-!
概要：P 相対旗の先行旗と最後の W 辺を共有端点で貼る。
方針：元の標準 tail 押し出しを全部分図式圏へ制限し、wide の持ち上げで反映する。
規約：商関手の核へ P を置換しない。使われ方：相対加法性の有限旗帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：最後の W 辺で伸ばした旗の閉じた条件。
方針：完全な先行制限と辺制限の逆像の交差。規約：全自然変換。
使われ方：相対 cofiber の基底変換の底。 -/
def closedTailPredicate {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    ClosedStablePredicate (ambientDiagramModel
      (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u}) (flagAmbient B)) :=
  ((closedFlagStablePredicate P ⦋n + 1⦌).comap
    (ambientDiagramRestriction (flagAmbient B) (standardTailPrefix n))).inter
      ((closedArrowPredicate P).comap
        (ambientDiagramRestriction (flagAmbient B) (tailAttachmentEdge (Δ[n] : SSet.{u}))))

/-- 概要：貼り合わせの安定模型。方針：閉じた全部分圏。
規約：P と元の辺を保持。使われ方：有限旗の加法性。 -/
def closedTailModel {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    StableModel.{u} := closedStableModel (closedTailPredicate P n)

/-- 概要：同じ貼り合わせの先行旗への完全射。
方針：元の周囲制限を全部分圏へ持ち上げる。
規約：指定先行旗を保持。使われ方：帰納の第一成分。 -/
def closedTailPrefix {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    closedTailModel P n ⟶ closedFlagModel P ⦋n + 1⦌ :=
  closedStableMap _ _ (ambientDiagramRestriction (flagAmbient B) (standardTailPrefix n))
    (fun _ hv => hv.1)

/-- 概要：同じ貼り合わせの最後の W 辺への完全射。
方針：元の辺制限を全部分圏へ持ち上げる。
規約：指定辺を保持。使われ方：全 cofiber 補完の基底変換。 -/
def closedTailEdge {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    closedTailModel P n ⟶ closedArrowModel P :=
  closedStableMap _ _
    (ambientDiagramRestriction (flagAmbient B) (tailAttachmentEdge (Δ[n] : SSet.{u})))
    (fun _ hv => hv.2)

/-- 概要：一辺の P 条件と wide への全体持ち上げの一致。
方針：一単体の正確な辺条件と標準単体の像を使う。
規約：全退化も保持。使われ方：貼り合わせ上の所属判定。 -/
lemma closedArrow_factor_iff {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (f : (Δ[1] : SSet.{u}) ⟶ B.carrier) :
    (closedArrowPredicate P).predicate (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ↔
      ∃ g : (Δ[1] : SSet.{u}) ⟶ (closedStableWide P : SSet.{u}),
        g ≫ (closedStableWide P).ι = f := by
  have h := closedFlag_factor_iff P 1 f
  change SSet.yonedaEquiv f ∈ (closedStableWide P).obj _ ↔ _ at h
  have ha := closedArrowPredicate_iff P (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  change _ ↔ SSet.yonedaEquiv f ∈ closedStableEdges P at ha
  exact ha.trans ((closedStableWide_edge_iff P _).symm.trans h)

/-- 概要：貼り合わせの二条件は同じ全図式の wide 持ち上げを与える。
方針：指定標準押し出しの普遍性と wide 包含の単射性。
規約：元の関手を厳密に回収。使われ方：元の全旗条件の反映。 -/
lemma closedTail_factor_iff {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ)
    (f : (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u}) ⟶ B.carrier) :
    (closedTailPredicate P n).predicate (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ↔
      ∃ g : (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u}) ⟶
        (closedStableWide P : SSet.{u}), g ≫ (closedStableWide P).ι = f := by
  change (closedFlagStablePredicate P ⦋n + 1⦌).predicate
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (standardTailPrefix n ≫ f)) ∧
      (closedArrowPredicate P).predicate
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (tailAttachmentEdge (Δ[n] : SSet.{u}) ≫ f)) ↔ _
  rw [closedFlagStablePredicate_iff, closedFlag_factor_iff, closedArrow_factor_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    let h := standardTail_isPushout.{u} n
    have hw : stdSimplex.δ (1 : Fin 2) ≫ b = standardTailEndpoint n ≫ a := by
      apply (cancel_mono (closedStableWide P).ι).1
      rw [Category.assoc, hb, ← Category.assoc, h.w, Category.assoc, ← ha, ← Category.assoc]
    refine ⟨h.desc b a hw, ?_⟩
    apply h.hom_ext
    · rw [← Category.assoc, h.inl_desc, hb]
    · rw [← Category.assoc, h.inr_desc, ha]
  · rintro ⟨g, hg⟩
    exact ⟨⟨standardTailPrefix n ≫ g, (Category.assoc _ _ _).trans (congrArg _ hg)⟩,
      ⟨tailAttachmentEdge (Δ[n] : SSet.{u}) ≫ g,
        (Category.assoc _ _ _).trans (congrArg _ hg)⟩⟩

/-- 概要：最後の辺を貼った条件は元の長い旗の全 W 条件を反映する。
方針：同じ wide の inner fibration に沿う strict 持ち上げ。
規約：元の全単体を保持。使われ方：相対旗への制限の trivial Kan 性。 -/
lemma closedFlag_tail_iff {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ)
    (v : ((ihom (Δ[n + 2] : SSet.{u})).obj B.carrier) _⦋0⦌) :
    (closedFlagStablePredicate P ⦋n + 2⦌).predicate v ↔
      (closedTailPredicate P n).predicate
        (((pre (standardTailInclusion n)).app B.carrier).app _ v) := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[n + 2] : SSet.{u}) B.carrier).surjective v
  change (closedFlagStablePredicate P ⦋n + 2⦌).predicate (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ↔
    (closedTailPredicate P n).predicate (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (standardTailInclusion n ≫ f))
  rw [closedFlagStablePredicate_iff, closedFlag_factor_iff, closedTail_factor_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨standardTailInclusion n ≫ g, by rw [Category.assoc, hg]⟩
  · rintro ⟨g, hg⟩
    exact closedWideFactor_of_innerAnodyne P _ (standardTailInclusion_innerAnodyne n) f g hg

end SerrePositivity.KST.Fibration.Relative
