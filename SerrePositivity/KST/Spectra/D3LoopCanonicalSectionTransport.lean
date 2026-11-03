module

public import SerrePositivity.KST.Spectra.D3ProjectionStructureIso
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerUnit
public import SerrePositivity.InfinityCategories.Core.CatInfinity.FunctorIsoWhiskerExchange

/-!
概要：標準 loop 図式間の指定 transport を、同じ終点同型の切断への後合成として回収する。
方針：終点射影の充満忠実性と厳密切断条件で指定値を反映し、始点表示同型と交換する。
規約：標準模型間の比較因子を恒等とは扱わない。指定された同型の全図式を保持する。
使われ方：実 loop 段比較と元の右射影の構造正方形の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 厳密切断への後合成を元の射影へ戻すと、同じ指定同型を回収する。 -/
lemma d3FunctorIso_postcomp_retraction_heq {A E B : SSet.{u}}
    {f g : A ⟶ B} (e : FunctorIso f g) (s : B ⟶ E) (p : E ⟶ B)
    (hs : s ≫ p = 𝟙 B) : HEq ((e.postcomp s).postcomp p) e := by
  rw [F2.functorIso_postcomp_postcomp]
  exact (F2.functorIso_postcomp_heq_of_map_eq e hs).symm.trans
    (heq_of_eq (F2.functorIso_postcomp_id e))

/-- 指定同型の正方形は、四頂点の端点表示だけを正規化しても同じ値で可換。 -/
lemma d3FunctorIso_square_transport {A X : SSet.{u}}
    {a b c d a' b' c' d' : A ⟶ X}
    (ab : FunctorIso a b) (bd : FunctorIso b d)
    (ac : FunctorIso a c) (cd : FunctorIso c d)
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (h : ab ≪≫ bd = ac ≪≫ cd) :
    F2.functorIsoOfEq ab ha hb ≪≫ F2.functorIsoOfEq bd hb hd =
      F2.functorIsoOfEq ac ha hc ≪≫ F2.functorIsoOfEq cd hc hd := by
  subst a' b' c' d'
  exact h

variable {A X : SSet.{u}} [Quasicategory X] [HasZeroVertex X]
  (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)

/-- 指定終点同型の標準全図式間 transport は、同じ同型の厳密切断への後合成そのもの。 -/
lemma d3LoopCanonicalTransport_section {F G : A ⟶ loopDiagrams X} (e : FunctorIso F G) :
    d3LoopCanonicalTransport s hs e = (e.postcomp (loopDiagramEvaluation X 1 1)).postcomp s := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  let hf := isFullyFaithful_of_trivialKanFibration (loopDiagramEvaluation X 1 1)
  apply hf.postcomp_functorIso_injective
  rw [d3LoopCanonicalTransport_target]
  exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
    (d3FunctorIso_postcomp_retraction_heq (e.postcomp (loopDiagramEvaluation X 1 1))
      s (loopDiagramEvaluation X 1 1) hs).symm)

/-- 同じ標準 transport の始点作用は、元の終点同型の同じ切断始点作用への後合成。 -/
lemma d3LoopCanonicalTransport_source {F G : A ⟶ loopDiagrams X} (e : FunctorIso F G) :
    (d3LoopCanonicalTransport s hs e).postcomp (loopDiagramEvaluation X 0 0) =
      (e.postcomp (loopDiagramEvaluation X 1 1)).postcomp
        (s ≫ loopDiagramEvaluation X 0 0) := by
  rw [d3LoopCanonicalTransport_section, F2.functorIso_postcomp_postcomp]

/-- 標準始点表示の同型を保ち、同じ指定終点 transport と通常 loop の作用を交換する。 -/
lemma d3LoopCanonicalTransport_source_naturality {Ω : X ⟶ X}
    (uΩ : FunctorIso Ω (s ≫ loopDiagramEvaluation X 0 0))
    {F G : A ⟶ loopDiagrams X} (e : FunctorIso F G) :
    (e.postcomp (loopDiagramEvaluation X 1 1)).postcomp Ω ≪≫
        uΩ.precomp (G ≫ loopDiagramEvaluation X 1 1) =
      uΩ.precomp (F ≫ loopDiagramEvaluation X 1 1) ≪≫
        (d3LoopCanonicalTransport s hs e).postcomp (loopDiagramEvaluation X 0 0) := by
  rw [d3LoopCanonicalTransport_source]
  exact F2.functorIso_whisker_exchange (e.postcomp (loopDiagramEvaluation X 1 1)) uΩ

end SerrePositivity.KST.Spectra
