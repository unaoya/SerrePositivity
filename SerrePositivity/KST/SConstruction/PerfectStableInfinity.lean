module
public import SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.F2.Idempotent.Coherent
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeUnitHom
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping

/-! # 小さい冪等完備安定 ∞ 圏の Cat^perf
概要：元の安定 ∞ 圏の圏から、coherent な冪等図式が全て分裂する対象を取る。
方針：StableInfinity の全部分複体として全高次単体と完全関手の写像空間を保持する。
規約：冪等完備化や Ind の存在は仮定しない。使われ方：BGT (a) の定義域。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open F2.Idempotent
open scoped Simplicial

/-- 元の安定 ∞ 圏の頂点が、全 coherent 冪等図式の分裂を持つという条件。 -/
def perfectStableVertexPredicate (a : StableInfinity.{u} _⦋0⦌) : Prop :=
  IsIdempotentComplete (stableObject a).obj

/-- Cat^perf は、完全関手を持つ安定 ∞ 圏の圏の冪等完備対象による全部分圏。 -/
def perfectStableInfinity : SSet.{u + 1} :=
  fullSubcomplexOnVertices StableInfinity perfectStableVertexPredicate

/-- 同じ全高次単体を保持する Cat^perf は quasicategory。 -/
instance perfectStableInfinity_quasicategory : Quasicategory perfectStableInfinity.{u} :=
  fullSubcomplexOnVertices_quasicategory _ _

/-- Cat^perf から元の安定 ∞ 圏の圏への実際の包含。 -/
def perfectStableInfinityInclusion : perfectStableInfinity.{u} ⟶ StableInfinity.{u} :=
  (fullSubcomplexOnVertices StableInfinity perfectStableVertexPredicate).ι

/-- Cat^perf の包含は、元の完全関手の写像空間を充満忠実に保持する。 -/
lemma perfectStableInfinityInclusion_isFullyFaithful :
    IsFullyFaithful perfectStableInfinityInclusion.{u} :=
  isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- 同じ小さい冪等完備安定 ∞ 圏を Cat^perf の実頂点へ束ねる。 -/
def perfectStableVertex (C : StableCategory.{u}) (hC : IsIdempotentComplete C.obj) :
    perfectStableInfinity.{u} _⦋0⦌ :=
  fullSubcomplexVertexEquiv perfectStableVertexPredicate ⟨stableVertex C, hC⟩

/-- Cat^perf の頂点から元の同じ安定 ∞ 圏を取り出す。 -/
def perfectStableObject (a : perfectStableInfinity.{u} _⦋0⦌) : StableCategory.{u} :=
  stableObject a.val

/-- 取り出した対象は、N レーンの全 coherent 冪等図式について冪等完備。 -/
lemma perfectStableObject_isIdempotentComplete (a : perfectStableInfinity.{u} _⦋0⦌) :
    IsIdempotentComplete (perfectStableObject a).obj := fullSubcomplexOnVertices_vertex a

/-- 元の対象から束ねた頂点は、同じ安定 ∞ 圏を回収する。 -/
lemma perfectStableObject_vertex (C : StableCategory.{u}) (hC : IsIdempotentComplete C.obj) :
    perfectStableObject (perfectStableVertex C hC) = C := rfl

/-- 包含は、元の対象の StableInfinity における同じ頂点を回収する。 -/
lemma perfectStableInfinityInclusion_vertex
    (C : StableCategory.{u}) (hC : IsIdempotentComplete C.obj) :
    perfectStableInfinityInclusion.app (Opposite.op ⦋0⦌) (perfectStableVertex C hC) =
      stableVertex C := rfl

end SerrePositivity.KST.SConstruction
