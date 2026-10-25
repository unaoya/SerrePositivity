module
public import SerrePositivity.KST.Fibration.WeakSpanKanQuotientTotalOverMap
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionFirstVertexLocalization

/-!
概要：元の marked span 全族の商比較を、同じ底を保つ相対関手空間内で降下する。
方針：相対初頂点前合成の本質的全射性から実射と相対比較を回収する。
規約：供給された単体圏単位と底条件に条件付き。相対前合成同値性は F1 正本から供給する。
使われ方：K-B-S の同じ fiber 内での単位回収。既存の絶対降下と底厳密化も保持する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)
  (f : CategoryTheory.Limits.pullback (markedSpanFamilyProjection B.obj (weakEquivalences i) x)
    (transportSimplexFirstVertexMap B.obj) ⟶
      smallLeftUnstraightening (weakSpanKanCoherentDiagram i x))
  (hf : f ≫ smallLeftUnstraighteningProjection (weakSpanKanCoherentDiagram i x) =
    weakSpanSimplexProjection i x)

/-- 概要：指定単体圏比較を相対関手空間内で回収する厳密な底上の実射がある。
方針：相対前合成の本質的全射性を使い、同じ相対頂点の実射表示へ戻す。
規約：単体圏単位と底条件に条件付き。相対初頂点同値性は F1 の公開補題を使う。
使われ方：同じ q を保つ K-B-S 全族比較と、その fiber 内の回収同型を構成する。 -/
theorem exists_weakSpanKanQuotientRelativeTotalMap :
    ∃ (g : markedSpanFamily B.obj (weakEquivalences i) x ⟶
        smallLeftUnstraightening (weakSpanKanQuotientDiagram h x))
      (hg : g ≫ smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
        markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom),
      Nonempty (VertexIso
        (relativeFunctorVertex
          (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
          (transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x) ≫
            markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
          (transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x) ≫ g)
          (by rw [Category.assoc, hg]))
        (relativeFunctorVertex
          (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
          (transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x) ≫
            markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
          (weakSpanKanQuotientTotalSimplexMap h x f)
          (weakSpanKanQuotientTotalSimplexMap_projection h x f hf))) := by
  let p := smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)
  let b := markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom
  let r := transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x)
  let v := relativeFunctorVertex p (r ≫ b) (weakSpanKanQuotientTotalSimplexMap h x f)
    (weakSpanKanQuotientTotalSimplexMap_projection h x f hf)
  have hrel := relativeFunctorPre_isQCatEquivalence_of_firstVertexLocalization p b
  obtain ⟨z, ⟨e⟩⟩ := hrel.choose.isEssentiallySurjective v
  obtain ⟨g, hg, hz⟩ := exists_relativeFunctorVertex p b z
  refine ⟨g, hg, ⟨?_⟩⟩
  rw [← hz] at e
  change VertexIso ((relativeFunctorPre p b r).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex p b g hg)) v at e
  rw [relativeFunctorPre_vertex] at e
  exact e

/-- 概要：指定単体圏単位から、元の全族を商へ送る厳密な底上の実射。
方針：同じ相対降下定理から一つの射を選ぶ。
規約：元の単体圏単位と底条件だけを明示入力とし、単位の存在は主張しない。
使われ方：同じ fiber 内の回収同型を持つ K-B-S 全族比較の利用側。 -/
def weakSpanKanQuotientRelativeTotalMap :
    markedSpanFamily B.obj (weakEquivalences i) x ⟶
      smallLeftUnstraightening (weakSpanKanQuotientDiagram h x) :=
  (exists_weakSpanKanQuotientRelativeTotalMap h x f hf).choose

/-- 概要：相対降下で選んだ同じ実射は元の q を厳密に保持する。
方針：同じ存在証拠から底条件を取り出す。
規約：比較射を別に選び直さない。
使われ方：K-B-S の元の全族の fiber への制限。 -/
theorem weakSpanKanQuotientRelativeTotalMap_projection :
    weakSpanKanQuotientRelativeTotalMap h x f hf ≫
      smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
        markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom :=
  (exists_weakSpanKanQuotientRelativeTotalMap h x f hf).choose_spec.choose

/-- 概要：同じ実射の初頂点制限は指定単体圏比較を相対関手空間内で回収する。
方針：射と底条件を選んだ同じ存在証拠から比較同型を取り出す。
規約：同型は元の固定底上の fiber 内にあり、絶対関手同型に弱めない。
使われ方：同じ単位と指定恒等点の fiber 内比較への入力。 -/
def weakSpanKanQuotientRelativeTotalMapRestrictionIso :
    VertexIso
      (relativeFunctorVertex
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x) ≫
          markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
        (transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x) ≫
          weakSpanKanQuotientRelativeTotalMap h x f hf)
        (by rw [Category.assoc, weakSpanKanQuotientRelativeTotalMap_projection]))
      (relativeFunctorVertex
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x) ≫
          markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
        (weakSpanKanQuotientTotalSimplexMap h x f)
        (weakSpanKanQuotientTotalSimplexMap_projection h x f hf)) :=
  Classical.choice
    (exists_weakSpanKanQuotientRelativeTotalMap h x f hf).choose_spec.choose_spec

end SerrePositivity.KST.Fibration
