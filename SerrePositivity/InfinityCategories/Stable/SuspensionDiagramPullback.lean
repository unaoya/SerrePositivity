module
public import SerrePositivity.InfinityCategories.Stable.LoopToSuspensionEquivalence
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-!
概要：元の loop 四角形の押し出し性と、全 suspension/loop 図式の比較。
方針：同じ指定点の始対象性を実固定 span へ戻し、全図式の評価を比較する。
規約：安定性は仮定しない。使われ方：HA 1.4.2.27 の一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma isLoopDiagramVertex_of_isSuspension_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (v : (suspensionDiagrams X) _⦋0⦌) : IsLoopDiagramVertex v.val := by
  let e := (loopToSuspensionDiagramsOfLoopEquivalence_isQCatEquivalence s hs hΩ).choose
  obtain ⟨w, ⟨hw⟩⟩ := e.isEssentiallySurjective v
  let i := (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    IsSuspensionDiagramVertex).ι
  have h : VertexIso w.val v.val := by
    have hraw := hw.map i
    have he := ConcreteCategory.congr_hom
      (NatTrans.congr_app (loopToSuspensionDiagramsOfLoopEquivalence_ι s hs hΩ)
        (Opposite.op ⦋0⦌)) w
    change VertexIso (i.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) w)) v.val
      at hraw
    change i.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) w) = w.val at he
    rw [he] at hraw
    exact hraw
  have hF : FunctorIso (squareDiagram w.val) (squareDiagram v.val) := by
    change VertexIso (functorVertex (squareDiagram w.val))
      (functorVertex (squareDiagram v.val))
    have hwF : functorVertex (squareDiagram w.val) = w.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    have hvF : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    rw [hwF, hvF]
    exact h
  have hv := fullSubcomplexOnVertices_vertex v
  exact ⟨hv.1, hv.2.1,
    (fullSubcomplexOnVertices_vertex w).2.2.of_functorIso hF⟩

end SerrePositivity.InfinityCategories
