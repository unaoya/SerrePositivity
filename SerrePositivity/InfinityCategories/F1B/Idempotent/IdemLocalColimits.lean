module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftKanIdentityVertex
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes
public import SerrePositivity.InfinityCategories.Core.Idempotent.Coherent
public import SerrePositivity.InfinityCategories.F1B.Idempotent.IdemImageKanShape
public import SerrePositivity.InfinityCategories.F1B.Idempotent.IdemInclusionFull
public import SerrePositivity.InfinityCategories.F1B.Idempotent.PointColimitExistence
public import SerrePositivity.InfinityCategories.Core.Idempotent.Walking
public import SerrePositivity.InfinityCategories.Core.Idempotent.WalkingClassification

/-!
概要：元の冪等図式が余極限を持てば、元の包含に沿う全ての左局所図式が余極限を持つ。
方針：非分裂対象では元の恒等頂点の終対象性、分裂対象では元の射影同型を使う。
規約：同じ元の冪等図式を全局所図式へ移し、存在を追加の入力にしない。
使われ方：元の全 Idem 図式の余極限から強い分裂を厳密に構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の非分裂対象での左局所図式は、元の恒等頂点を終対象として余極限を持つ。 -/
lemma idemSourceKanDiagram_hasColimit {X : SSet.{u}} [Quasicategory X]
    (d : CoherentIdempotent X) :
    HasColimit (leftKanDiagram idemInclusion d (nerveVertex walkingSource)) := by
  have ht := F1B.kanLeftKanIdentityVertex_isTerminal idemInclusion
    idemInclusion_isFullyFaithful (nerveVertex walkingObject.{u})
  exact hasColimit_of_terminal_vertex _ _ ht

/-- 元の Idem 図式の余極限から、元の包含に沿う全左局所余極限の存在を得る。 -/
lemma idemLocalDiagrams_hasColimit {X : SSet.{u}} [Quasicategory X]
    (d : CoherentIdempotent X) (hd : HasColimit d) (b : SplitShape _⦋0⦌) :
    HasColimit (leftKanDiagram idemInclusion d b) := by
  obtain ⟨P, rfl⟩ := (nerveEquiv (C := WalkingSplit.{u})).symm.surjective b
  rcases walkingSplit_object_cases P with h | h
  · subst P
    exact idemSourceKanDiagram_hasColimit d
  · subst P
    exact idemImageKanDiagram_hasColimit d hd

end SerrePositivity.InfinityCategories.F2.Idempotent
