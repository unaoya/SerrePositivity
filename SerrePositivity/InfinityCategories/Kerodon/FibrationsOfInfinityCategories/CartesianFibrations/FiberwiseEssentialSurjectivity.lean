module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Edges

/-!
概要：fiber ごとの本質的全射性から全空間の本質的全射性を得る。
方針：標的の頂点をその像の fiber に含め、fiber 内の同型を全空間へ写す。
規約：共通基底を厳密に保つ射を扱う。fibration 性は不要。
使われ方：Kerodon Theorem 5.1.6.1（Tag 023M）、区間上の写像円柱比較の本質的全射性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- 概要：同じ基底上の射は全ての fiber で本質的全射なら全空間でも本質的全射。
方針：標的の各頂点の属する fiber で原像と同型を選び、包含で同型を写す。
規約：全空間と基底の quasicategory 性を要求しない。
使われ方：Kerodon Theorem 5.1.6.1（Tag 023M）、fiber ごとの同値判定の全射性の部分。 -/
lemma isEssentiallySurjective_of_vertexFiberMap {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective f := by
  intro y
  let b := q.app (Opposite.op ⦋0⦌) y
  let z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) _⦋0⦌ := ⟨y, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]⟩
  obtain ⟨x, ⟨hi⟩⟩ := h b z
  refine ⟨x.val, ⟨?_⟩⟩
  exact hi.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b)

/-- 概要：全ての fiber で同値な基底上の射は全空間で本質的全射。
方針：各 fiber の同値から本質的全射性を取り出し、全空間へ戻す。
規約：fiber の同値は IsQCatEquivalence により指定する。
使われ方：Kerodon Theorem 5.1.6.1（Tag 023M）、充満忠実性との組み合わせ。 -/
lemma isEssentiallySurjective_of_vertexFiberMap_equivalence {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [InnerFibration p] [InnerFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective f := by
  exact isEssentiallySurjective_of_vertexFiberMap p q f hf
    (fun b ↦ (h b).choose.isEssentiallySurjective)

/-- 概要：区間上の射は両端の fiber で本質的全射なら全空間でも本質的全射。
方針：区間の頂点を零・一の二つに分ける。
規約：両端以外の fiber の条件は不要。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、写像円柱の両端の比較。 -/
lemma isEssentiallySurjective_over_interval_of_endpoint_fibers {E F : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective f := by
  apply isEssentiallySurjective_of_vertexFiberMap p q f hf
  intro b
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
  fin_cases i
  · exact h0
  · exact h1

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
