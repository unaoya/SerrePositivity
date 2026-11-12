module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Coherent
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeUnitHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping

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

open scoped Simplicial

/-- 元の安定 ∞ 圏の頂点が、全 coherent 冪等図式の分裂を持つという条件。 -/
def perfectStableVertexPredicate (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject a).obj

/-- Cat^perf は、完全関手を持つ安定 ∞ 圏の圏の冪等完備対象による全部分圏。 -/
def perfectStableInfinity : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity perfectStableVertexPredicate

/-- 同じ全高次単体を保持する Cat^perf は quasicategory。 -/
instance perfectStableInfinity_quasicategory : Quasicategory perfectStableInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- Cat^perf から元の安定 ∞ 圏の圏への実際の包含。 -/
def perfectStableInfinityInclusion : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity perfectStableVertexPredicate).ι

/-- Cat^perf の包含は、元の完全関手の写像空間を充満忠実に保持する。 -/
lemma perfectStableInfinityInclusion_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful perfectStableInfinityInclusion.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- 同じ小さい冪等完備安定 ∞ 圏を Cat^perf の実頂点へ束ねる。 -/
def perfectStableVertex (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) :
    perfectStableInfinity.{u} _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.fullSubcomplexVertexEquiv perfectStableVertexPredicate ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex C, hC⟩

/-- Cat^perf の頂点から元の同じ安定 ∞ 圏を取り出す。 -/
def perfectStableObject (a : perfectStableInfinity.{u} _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject a.val

/-- 取り出した対象は、N レーンの全 coherent 冪等図式について冪等完備。 -/
lemma perfectStableObject_isIdempotentComplete (a : perfectStableInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (perfectStableObject a).obj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex a

/-- 元の対象から束ねた頂点は、同じ安定 ∞ 圏を回収する。 -/
lemma perfectStableObject_vertex (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) :
    perfectStableObject (perfectStableVertex C hC) = C := rfl

/-- 包含は、元の対象の StableInfinity における同じ頂点を回収する。 -/
lemma perfectStableInfinityInclusion_vertex
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) :
    perfectStableInfinityInclusion.app (Opposite.op ⦋0⦌) (perfectStableVertex C hC) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex C := rfl

end SerrePositivity.KST.SConstruction
