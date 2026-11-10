module
public import SerrePositivity.InfinityCategories.Core.Idempotent.WalkingClassification

public import SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.RetractClosure
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Core.Idempotent.Coherent
public import SerrePositivity.InfinityCategories.Core.Idempotent.Walking

/-!
概要：retract に閉じた全部分圏へ、元の coherent 図式の厳密な強い分裂を反映する。
方針：分裂添字の二頂点を分類し、分裂頂点の元の retract から全単体を持ち上げる。
規約：同じ全 Idem 図式を包含への制限で厳密に回収する。
使われ方：HTT 5.1.4 の retract 閉包の冪等完備性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の分裂頂点と非分裂頂点が条件を満たせば、元の全分裂図式の全頂点が満たす。 -/
lemma StrongSplitting.vertices_mem {X : SSet.{u}} {d : CoherentIdempotent X}
    (s : StrongSplitting d) (P : X _⦋0⦌ → Prop) (hd : P d.vertex) (hs : P s.vertex)
    (v : SplitShape.{u} _⦋0⦌) : P (s.val.app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨x, rfl⟩ := (nerveEquiv (C := WalkingSplit.{u})).symm.surjective v
  rcases walkingSplit_object_cases x with rfl | rfl
  · rw [s.source_eq]
    exact hd
  · exact hs

/-- 元の全部分圏の図式の周囲での分裂は、retract 閉性により同じ全部分圏へ戻る。 -/
def StrongSplitting.liftFullSubcomplex {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (hP : ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y → P y → P x)
    {d : CoherentIdempotent (fullSubcomplexOnVertices X P)}
    (s : StrongSplitting (d ≫ (fullSubcomplexOnVertices X P).ι)) : StrongSplitting d := by
  have hd : P (CoherentIdempotent.vertex (d ≫ (fullSubcomplexOnVertices X P).ι)) :=
    fullSubcomplexOnVertices_vertex d.vertex
  have hs : P s.vertex := hP ⟨s.vertexRetraction⟩ hd
  let F := fullSubcomplexLift P s.val (s.vertices_mem P hd hs)
  refine ⟨F, ?_⟩
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (idemInclusion ≫ ·) (fullSubcomplexLift_ι P s.val _)).trans s.property)

/-- 全部分圏へ戻した元の全分裂は、元の包含後に同じ周囲の全分裂を厳密に回収する。 -/
lemma StrongSplitting.liftFullSubcomplex_inclusion {X : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (hP : ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y → P y → P x)
    {d : CoherentIdempotent (fullSubcomplexOnVertices X P)}
    (s : StrongSplitting (d ≫ (fullSubcomplexOnVertices X P).ι)) :
    (s.liftFullSubcomplex P hP).val ≫ (fullSubcomplexOnVertices X P).ι = s.val := rfl

/-- 冪等完備な周囲の ∞ 圏の retract に閉じた全部分圏も冪等完備。 -/
lemma fullSubcomplex_isIdempotentComplete {X : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (hP : ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y → P y → P x)
    (hX : IsIdempotentComplete X) :
    IsIdempotentComplete (fullSubcomplexOnVertices X P) := by
  intro d
  obtain ⟨s⟩ := hX (d ≫ (fullSubcomplexOnVertices X P).ι)
  exact ⟨s.liftFullSubcomplex P hP⟩

/-- 冪等完備な周囲の ∞ 圏内の任意の頂点条件の retract 閉包は冪等完備。 -/
lemma retractClosure_isIdempotentComplete {X : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (hX : IsIdempotentComplete X) :
    IsIdempotentComplete (fullSubcomplexOnVertices X (_root_.SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.retractClosure P)) :=
  fullSubcomplex_isIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.retractClosure P)
    (fun h hy ↦ _root_.SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.retractClosure_of_retract h hy) hX

end SerrePositivity.InfinityCategories.F2.Idempotent
