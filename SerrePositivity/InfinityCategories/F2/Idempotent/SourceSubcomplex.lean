module

public import SerrePositivity.InfinityCategories.F2.Idempotent.SourceChains
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping

/-!
概要：元の非分裂対象だけを頂点とする全部分複体を構成する。
方針：元の Idem 包含を全頂点条件で因子化し、全単体の各対象の条件を回収する。
規約：元の全包含を、元の全部分複体の包含後に厳密に回収する。
使われ方：元の Idem 包含の inner fibration 性と写像空間の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の分裂添字の頂点が、元の非分裂対象であるという条件。 -/
def IsSourceVertex (v : SplitShape.{u} _⦋0⦌) : Prop := v.obj 0 = walkingSource

/-- 元の非分裂対象を頂点とする元の全部分複体。 -/
def sourceSubcomplex : SplitShape.{u}.Subcomplex :=
  fullSubcomplexOnVertices SplitShape IsSourceVertex

/-- 元の Idem 包含の各頂点は、元の非分裂対象そのもの。 -/
lemma idemInclusion_source_vertex (a : IdemShape.{u} _⦋0⦌) :
    IsSourceVertex (idemInclusion.app (Opposite.op ⦋0⦌) a) := by
  change walkingInclusion.obj (a.obj 0) = walkingSource
  exact congrArg walkingInclusion.obj (walkingObject_eq (a.obj 0))

/-- 元の Idem 包含を、元の非分裂対象の全部分複体へ全単体ごと持ち上げる。 -/
def idemSourceLift : IdemShape.{u} ⟶ sourceSubcomplex :=
  fullSubcomplexLift IsSourceVertex idemInclusion idemInclusion_source_vertex

/-- 元の全部分複体の包含の後で、元の全 Idem 包含を厳密に回収する。 -/
lemma idemSourceLift_inclusion : idemSourceLift.{u} ≫ sourceSubcomplex.ι = idemInclusion :=
  fullSubcomplexLift_ι _ _ _

/-- 元の全部分複体の全単体の全対象は、元の非分裂対象そのもの。 -/
lemma sourceSubcomplex_chain_vertex {n : ℕ} (F : sourceSubcomplex.{u}.toSSet _⦋n⦌)
    (i : Fin (n + 1)) : F.val.obj i = walkingSource :=
  F.property (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)

end SerrePositivity.InfinityCategories.F2.Idempotent
