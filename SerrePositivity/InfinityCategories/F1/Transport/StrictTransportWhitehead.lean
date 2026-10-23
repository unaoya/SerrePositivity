module

public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramPostcomposition
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportDiagramInfinity

/-!
概要：strict transport 間の対象ごとの同値に対する strict な逆変換。
方針：全ての strict transport を標的とする前合成の同値から逆変換と二つの比較を得る。
規約：比較同型は strict な変換空間の内部に保持する。
使われ方：Kerodon Corollary 5.6.0.6、図式の点ごとの同値を coherent な同値へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：strict transport 間の対象ごとの同値は strict な逆変換と両側の比較同型を持つ。
方針：前合成の本質的全射性で片側の逆を取り、充満忠実性で他方の逆条件を戻す。
規約：底 C は任意の通常の圏。逆変換の自然性は厳密、逆条件は変換空間内の同型。
使われ方：Kerodon Corollary 5.6.0.6、strict transport の像における同値判定。 -/
lemma exists_strictTransportInverse {C : Type u} [Category.{u} C]
    {E E' : SSet.{u}} (p : E ⟶ nerve C) (q : E' ⟶ nerve C)
    [LeftFibration p] [LeftFibration q]
    (η : leftStrictTransportDiagram p ⟶ leftStrictTransportDiagram q)
    (hη : ∀ c, IsQCatEquivalence (η.app c)) :
    ∃ θ : leftStrictTransportDiagram q ⟶ leftStrictTransportDiagram p,
      Nonempty (VertexIso (strictDiagramMappingVertex (η ≫ θ))
        (strictDiagramMappingVertex (𝟙 (leftStrictTransportDiagram p)))) ∧
      Nonempty (VertexIso (strictDiagramMappingVertex (θ ≫ η))
        (strictDiagramMappingVertex (𝟙 (leftStrictTransportDiagram q)))) := by
  have : ∀ c, KanComplex ((leftStrictTransportDiagram p).obj c) := fun c ↦
    inferInstanceAs (KanComplex (leftStrictTransport p c))
  have : ∀ c, KanComplex ((leftStrictTransportDiagram q).obj c) := fun c ↦
    inferInstanceAs (KanComplex (leftStrictTransport q c))
  have hp := strictDiagramMappingPre_isQCatEquivalence η hη p
  have hq := strictDiagramMappingPre_isQCatEquivalence η hη q
  obtain ⟨v, ⟨hv⟩⟩ := hp.choose.isEssentiallySurjective
    (strictDiagramMappingVertex (𝟙 (leftStrictTransportDiagram p)))
  obtain ⟨θ, hθ⟩ := exists_strictDiagramMappingVertex _ _ v
  have hu : VertexIso (strictDiagramMappingVertex (η ≫ θ))
      (strictDiagramMappingVertex (𝟙 (leftStrictTransportDiagram p))) := by
    change VertexIso ((strictDiagramMappingPre η (leftStrictTransportDiagram p)).app _ v)
      (strictDiagramMappingVertex (𝟙 (leftStrictTransportDiagram p))) at hv
    rw [← hθ, strictDiagramMappingPre_vertex] at hv
    exact hv
  have hc := VertexIso.map hu (strictDiagramMappingPost η (leftStrictTransportDiagram p))
  simp only [strictDiagramMappingPost_vertex, Category.assoc, Category.id_comp] at hc
  have hc' : VertexIso
      ((strictDiagramMappingPre η (leftStrictTransportDiagram q)).app _
        (strictDiagramMappingVertex (θ ≫ η)))
      ((strictDiagramMappingPre η (leftStrictTransportDiagram q)).app _
        (strictDiagramMappingVertex (𝟙 (leftStrictTransportDiagram q)))) := by
    simpa only [strictDiagramMappingPre_vertex, Category.comp_id] using hc
  exact ⟨θ, ⟨hu⟩, ⟨hq.isFullyFaithful.preimageVertexIso hc'⟩⟩

/-- 概要：strict transport の像に属する図式の対象ごとの同値は strict な逆を持つ。
方針：二つの図式を strict transport で表し、その逆変換の構成を適用する。
規約：代表の存在は命題の証明にだけ使用する。
使われ方：Kerodon Corollary 5.6.0.6、像の coherent nerve で同値を検出するための逆データ。 -/
lemma exists_strictTransportImageInverse {C : Type u} [Category.{u} C]
    (F G : StrictTransportDiagramObject C)
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (hη : ∀ c, IsQCatEquivalence (X := (F.val.obj c).obj)
      (Y := (G.val.obj c).obj) (η.app c)) :
    ∃ θ : G.val ⋙ kanObjectForget ⟶ F.val ⋙ kanObjectForget,
      Nonempty (VertexIso (strictDiagramMappingVertex (η ≫ θ))
        (strictDiagramMappingVertex (𝟙 (F.val ⋙ kanObjectForget)))) ∧
      Nonempty (VertexIso (strictDiagramMappingVertex (θ ≫ η))
        (strictDiagramMappingVertex (𝟙 (G.val ⋙ kanObjectForget)))) := by
  rcases F with ⟨F, ⟨p, rfl⟩⟩
  rcases G with ⟨G, ⟨q, rfl⟩⟩
  exact exists_strictTransportInverse p.val.hom q.val.hom η hη

end SerrePositivity.InfinityCategories
