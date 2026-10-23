module

public import SerrePositivity.InfinityCategories.F1.Limits.InverseSequenceComparison
public import SerrePositivity.InfinityCategories.F1.Transport.LocalizationCoproduct

/-!
概要：初頂点写像の局所化普遍性を、単射の可算余極限へ貼り合わせる。
方針：全関手と反転関手の極限表示を、相対持ち上げを持つ塔の比較で結ぶ。
規約：可算列の各遷移に単射性を要求し、底の充填性は要求しない。
使われ方：骨格のセル帰納による一般の底の局所化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet Opposite
namespace SerrePositivity.InfinityCategories

/-- 初頂点写像の局所化普遍性は、底の同型に沿って不変。 -/
lemma transportSimplexFirstVertexMap_isLocalization_of_iso {A B : SSet.{u}} (e : A ≅ B)
    (hB : IsLocalization (transportSimplexFirstVertexMap B) (transportSimplexInitialEdges B)) :
    IsLocalization (transportSimplexFirstVertexMap A) (transportSimplexInitialEdges A) := by
  refine ⟨transportSimplexFirstVertexMap_inverts A, fun E _ ↦ ?_⟩
  have : IsIso ((pre e.hom).app E) := by
    change IsIso ((internalHom.flip.obj E).map e.hom.op)
    infer_instance
  have : IsIso (transportSimplexInvertingRestriction e.hom E) := by
    change IsIso ((transportSimplexInvertingDiagram E).map e.hom.op)
    infer_instance
  obtain ⟨_, hB⟩ := hB
  have hb : IsQCatEquivalence (localizationPrecomposition (transportSimplexFirstVertexMap B)
      (transportSimplexInitialEdges B) (transportSimplexFirstVertexMap_inverts B) E ≫
        transportSimplexInvertingRestriction e.hom E) :=
    (hB E).comp (qCatEquivalenceOfIso
      (asIso (transportSimplexInvertingRestriction e.hom E))).isQCatEquivalence
  rw [← transportSimplexLocalizationPrecomposition_naturality e.hom E] at hb
  exact (qCatEquivalenceOfIso (asIso ((pre e.hom).app E))).isQCatEquivalence.cancel_left hb

/-- 単射の可算列の各頂点で初頂点写像が局所化なら、余極限でも局所化。 -/
lemma transportSimplexFirstVertexMap_isLocalization_of_sequential_colimit
    {F : ℕ ⥤ SSet.{u}} [∀ n, Mono (F.map (homOfLE (Nat.le_succ n)))]
    {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ n, IsLocalization (transportSimplexFirstVertexMap (F.obj n))
      (transportSimplexInitialEdges (F.obj n))) :
    IsLocalization (transportSimplexFirstVertexMap c.pt) (transportSimplexInitialEdges c.pt) := by
  refine ⟨transportSimplexFirstVertexMap_inverts c.pt, fun E _ ↦ ?_⟩
  let S := F.op ⋙ transportBaseRestrictionDiagram E
  let T := F.op ⋙ transportSimplexInvertingDiagram E
  let η : S ⟶ T := Functor.whiskerLeft F.op (transportSimplexLocalizationComparison E)
  let s := (transportBaseRestrictionDiagram E).mapCone c.op
  let t := (transportSimplexInvertingDiagram E).mapCone c.op
  have hs : IsLimit s := isLimitOfPreserves (internalHom.flip.obj E) hc.op
  have ht : IsLimit t := transportSimplexInvertingConeIsLimit hc E
  let L := localizationPrecomposition (transportSimplexFirstVertexMap c.pt)
    (transportSimplexInitialEdges c.pt) (transportSimplexFirstVertexMap_inverts c.pt) E
  have hL (j : ℕᵒᵖ) : L ≫ t.π.app j = s.π.app j ≫ η.app j :=
    (transportSimplexLocalizationPrecomposition_naturality (c.ι.app j.unop) E).symm
  have : ∀ j, Quasicategory (S.obj j) := by
    intro j
    change Quasicategory ((ihom (F.obj j.unop)).obj E)
    infer_instance
  have : ∀ j, Quasicategory (T.obj j) := by
    intro j
    change Quasicategory (fullSubcomplexOnVertices
      ((ihom (nerve (TransportSimplexCategory (F.obj j.unop)))).obj E)
      (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges (F.obj j.unop))) : SSet.{u})
    infer_instance
  have hη : ∀ j, IsQCatEquivalence (η.app j) := by
    intro j
    obtain ⟨_, hj⟩ := hF j.unop
    exact hj E
  have hS (n : ℕ) : F1B.KanEquivalenceLifting (S.map (homOfLE (Nat.le_succ n)).op) := by
    change F1B.KanEquivalenceLifting ((pre (F.map (homOfLE (Nat.le_succ n)))).app E)
    exact F1B.kanEquivalenceLifting_pre _
  have hT (n : ℕ) : F1B.KanEquivalenceLifting (T.map (homOfLE (Nat.le_succ n)).op) := by
    change F1B.KanEquivalenceLifting
      (transportSimplexInvertingRestriction (F.map (homOfLE (Nat.le_succ n))) E)
    exact kanEquivalenceLifting_transportSimplexInvertingRestriction _ E
  have : ∀ n, TrivialKanFibration
      (relativeEquivalencePathMapAt (T.map (homOfLE (Nat.le_succ n)).op) 0) := by
    intro n
    change TrivialKanFibration (relativeEquivalencePathMapAt
      (transportSimplexInvertingRestriction (F.map (homOfLE (Nat.le_succ n))) E) 0)
    infer_instance
  have he : IsPrecompositionEquivalence L :=
    isPrecompositionEquivalence_inverseSequenceConeMap η hη hS hT s t hs ht L hL
  exact he.isQCatEquivalence

end SerrePositivity.InfinityCategories
