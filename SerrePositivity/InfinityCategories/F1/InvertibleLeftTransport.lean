module

public import SerrePositivity.InfinityCategories.F1.TransportComposition
public import SerrePositivity.InfinityCategories.F1.TransportIdentity
public import SerrePositivity.InfinityCategories.F1.LeftFiberKan

/-!
概要：可逆な底の辺に沿う left fibration の transport は同値。
方針：逆辺の二つの合成三角形と transport の単位・合成同型を使う。
規約：選択済みの実際の標準 transport の同値性。
使われ方：Kerodon §5.2.5、表現の条件の可逆な辺に沿う不変性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：可逆な辺に沿う left fibration の標準 transport は同値。
方針：逆辺の transport を逆射とし、単位と合成の比較を使う。
規約：底 B の quasicategory 性だけを追加する。
使われ方：Kerodon §5.6.8、可逆な分類図式の辺に沿う表現条件の移送。 -/
lemma edgeTransport_isQCatEquivalence_of_isInvertibleEdge {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] {a b : B.obj (Opposite.op ⦋0⦌)}
    (e : SSet.Edge a b) (he : IsInvertibleEdge e) : IsQCatEquivalence (edgeTransport p e) := by
  obtain ⟨⟨i, σ, τ⟩⟩ := he.nonempty_inverse
  obtain ⟨hσ⟩ := edgeTransport_composition_iso p σ
  obtain ⟨hτ⟩ := edgeTransport_composition_iso p τ
  obtain ⟨ha⟩ := edgeTransport_identity_iso p a
  obtain ⟨hb⟩ := edgeTransport_identity_iso p b
  exact ⟨edgeTransport p i, ⟨hσ.symm ≪≫ ha⟩, ⟨hτ.symm ≪≫ hb⟩⟩

end SerrePositivity.InfinityCategories
