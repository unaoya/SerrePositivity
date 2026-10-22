module

public import SerrePositivity.InfinityCategories.F2.Idempotent.SplittingRestriction
public import SerrePositivity.InfinityCategories.F1B.FullSubcomplexMapping

/-!
概要：元の関手圏内の有効な coherent 冪等図式の全部分圏を構成する。
方針：元の全図式の厳密な強い分裂の存在を頂点条件とし、元の制限を因子化する。
規約：同じ元の全 Idem 図式と元の前合成を保持する。
使われ方：HTT 4.4.5.16 の有効図式への制限そのものの自明 Kan 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の関手圏の頂点が表す全 Idem 図式が、元の厳密な強い分裂を持つという条件。 -/
def IsEffectiveIdempotentVertex {X : SSet.{u}} (v : ((ihom IdemShape).obj X) _⦋0⦌) : Prop :=
  Nonempty (StrongSplitting ((functorVertexEquiv IdemShape X).symm v))

/-- 元の関手圏内の、有効な元の全 Idem 図式の全部分複体。 -/
def effectiveIdempotents (X : SSet.{u}) : ((ihom IdemShape).obj X).Subcomplex :=
  fullSubcomplexOnVertices _ IsEffectiveIdempotentVertex

/-- 有効な元の全図式の全部分複体は、元の全部分 quasicategory。 -/
instance effectiveIdempotents_quasicategory (X : SSet.{u}) [Quasicategory X] :
    Quasicategory (effectiveIdempotents X).toSSet :=
  inferInstanceAs (Quasicategory (fullSubcomplexOnVertices _
    (IsEffectiveIdempotentVertex (X := X)) : SSet.{u}))

/-- 元の全強分裂図式を制限した元の図式は、同じ元の図式として有効。 -/
lemma strongSplittingRestriction_effective_vertex (X : SSet.{u})
    (v : ((ihom SplitShape).obj X) _⦋0⦌) :
    IsEffectiveIdempotentVertex ((strongSplittingRestriction X).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨F, rfl⟩ := (functorVertexEquiv SplitShape X).surjective v
  change Nonempty (StrongSplitting
    ((functorVertexEquiv IdemShape X).symm (functorVertex (idemInclusion ≫ F))))
  have h : (functorVertexEquiv IdemShape X).symm
      (functorVertex (idemInclusion ≫ F)) = idemInclusion ≫ F :=
    (functorVertexEquiv IdemShape X).symm_apply_apply _
  rw [h]
  exact ⟨⟨F, rfl⟩⟩

/-- 元の前合成による制限を、有効な元の全図式の全部分圏へ因子化する。 -/
def effectiveSplittingRestriction (X : SSet.{u}) :
    (ihom SplitShape).obj X ⟶ effectiveIdempotents X :=
  fullSubcomplexLift IsEffectiveIdempotentVertex (strongSplittingRestriction X)
    (strongSplittingRestriction_effective_vertex X)

/-- 全部分圏の元の包含の後で、元の全図式の前合成そのものを厳密に回収する。 -/
lemma effectiveSplittingRestriction_inclusion (X : SSet.{u}) :
    effectiveSplittingRestriction X ≫ (effectiveIdempotents X).ι = strongSplittingRestriction X :=
  fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories.F2.Idempotent
