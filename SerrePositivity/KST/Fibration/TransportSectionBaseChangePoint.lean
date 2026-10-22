module
public import SerrePositivity.KST.Fibration.RelativeSectionBaseChangeJointPoint

/-! # 全単体の切断の指定底変換同型は、元の pullback 係数成分を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 全単体上の底変換同型は、元の相対切断の共同同型の端点だけを表示変更する。 -/
theorem transportSimplexSectionInfinity_baseChangeIso_heq :
    HEq (transportSimplexSectionInfinity_baseChangeIso k)
      (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D)) := by
  unfold transportSimplexSectionInfinity_baseChangeIso
  dsimp only [transportSimplexSectionInfinity]
  have hcast {α β : Sort (u + 2)} (h : β = α) (x : α) : HEq (Eq.mpr h x) x := by
    cases h
    rfl
  let A := transportSimplexDomainFunctor D
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  have hm := hcast (congrArg
    (fun M => FunctorIso (relativeSectionDiagramInfinity A ≫ P)
      (relativeSectionDiagramInfinity M)) (transportSimplexDomainFunctor_baseChange k))
    (relativeSectionDiagramInfinityBaseChangeIso k A)
  exact (hcast _ _).trans hm

/-- 全単体上の元の指定同型の二重評価は、元の pullback 切断の同じ係数成分。 -/
theorem relativeSectionBaseChangeComponentIso_heq_transportMap
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    HEq (relativeSectionBaseChangeComponentIso k (transportSimplexDomainFunctor D) X c)
      (VertexIso.map (transportSimplexSectionInfinity_baseChangeIso k)
        (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
          (ULift.up (nerveVertex c)) (coherentNerveVertex X))) := by
  let A := transportSimplexDomainFunctor D
  have ht : (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (transportSimplexFunctor k)) ≫ transportSimplexSectionInfinity B =
        relativeSectionDiagramInfinity (A ⋙ Over.map k) :=
    (transportSimplexSectionInfinity_reindex (transportSimplexFunctor k)).trans
      (congrArg relativeSectionDiagramInfinity (transportSimplexDomainFunctor_baseChange k))
  have hm := F2.vertexIso_map_heq_of_heq (transportSimplexSectionInfinity_baseChangeIso k)
    (relativeSectionDiagramInfinityBaseChangeIso k A) rfl (congrArg functorVertex ht)
    (transportSimplexSectionInfinity_baseChangeIso_heq k)
    (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
      (ULift.up (nerveVertex c)) (coherentNerveVertex X))
  exact (relativeSectionBaseChangeComponentIso_heq_jointMap k A X c).trans hm.symm

/-- 同じ係数成分は、元の全単体の共同同型を実際の二段階評価で読んだ値。 -/
theorem relativeSectionBaseChangeComponentIso_heq_transportValueMap
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    HEq (relativeSectionBaseChangeComponentIso k (transportSimplexDomainFunctor D) X c)
      (VertexIso.map (functorIsoValue (transportSimplexSectionInfinity_baseChangeIso k)
        (ULift.up (nerveVertex c))) (evaluateFunctorAt (coherentNerveVertex X))) := by
  have h := functorIsoDoubleValue_heq_map (transportSimplexSectionInfinity_baseChangeIso k)
    (ULift.up (nerveVertex c)) (coherentNerveVertex X)
  exact (relativeSectionBaseChangeComponentIso_heq_transportMap k X c).trans h.symm

end SerrePositivity.KST.Fibration
