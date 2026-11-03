module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.JoinCells
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Core.KanFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.LeftFiberKan
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.CoconeMappingRestriction
public import SerrePositivity.InfinityCategories.F1.Fibrations.RightFibrationYoneda
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTriangleFiber
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderOverMono
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalEdgeFamilyLifting
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalObjects
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeSectionRestrictionComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeCosliceIntervalMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismVertexEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeTensorSectionLifting

/-!
概要：点ごとの局所辺を持つ任意の coherent な prism の始点余錐制限は自明 Kan 射となる。
方針：全パラメータの指数則と相対持ち上げを、元の図式の全境界へ移す。
規約：底 K は任意の単体集合。使われ方：HTT 5.5.4.5(2) の余極限比較辺の局所性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- curry した族の係数頂点は、元の prism の同じ頂点評価を表す。 -/
lemma curry_vertex_prismEvaluation {A K X : SSet.{u}} (g : A ⊗ K ⟶ X)
    (k : K _⦋0⦌) : (curry g).app (Opposite.op ⦋0⦌) k =
      functorVertex (prismVertexEvaluation g k) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  have hα : α = (SimplexCategory.const n.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 点ごとの辺が局所なら、標準点との積を残した始点切断制限は自明 Kan。 -/
lemma localPrism_tensorSource_sections_trivial {K X : SSet.{u}} [Quasicategory X]
    (g : (Δ[1] : SSet.{u}) ⊗ K ⟶ X) (z : X _⦋0⦌)
    (h : ∀ k : K _⦋0⦌, IsLocalForHom
      (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge (prismVertexEvaluation g k))) z) :
    TrivialKanFibration (relativeFunctorPre (sliceOverProjection (SSet.yonedaEquiv.symm z)) g
      (stdSimplex.δ (1 : Fin 2) ▷ K)) := by
  let p := sliceOverProjection (SSet.yonedaEquiv.symm z)
  let sq := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom
    (stdSimplex.δ (1 : Fin 2)) p
  apply relativeFunctorPre_tensor_trivial_of_vertexFibers
    (stdSimplex.δ (1 : Fin 2)) p sq g
  apply localEdgeFamily_vertexFiber_isContractibleKan (curry g) z _ sq
  intro k
  have he : (functorVertexEquiv Δ[1] X).symm ((curry g).app (Opposite.op ⦋0⦌) k) =
      prismVertexEvaluation g k := by
    rw [curry_vertex_prismEvaluation]
    exact (functorVertexEquiv Δ[1] X).symm_apply_apply _
  exact he.symm ▸ h k

/-- 標準点との積の同型を除くと、元の prism の始点面への包含となる。 -/
lemma prismSource_tensor_shape (K : SSet.{u}) :
    inv (snd (Δ[0] : SSet.{u}) K) ≫ (stdSimplex.δ (1 : Fin 2) ▷ K) =
      prismEndpoint 0 K := by
  apply (cancel_epi (snd (Δ[0] : SSet.{u}) K)).mp
  rw [IsIso.hom_inv_id_assoc, prismEndpoint, comp_lift, SSet.comp_const, Category.comp_id,
    stdSimplex.δ_one_eq_const]
  rfl

/-- 点ごとの辺が局所なら、元の prism の始点面への切断制限は自明 Kan。 -/
lemma localPrism_source_sections_trivial {K X : SSet.{u}} [Quasicategory X]
    (g : (Δ[1] : SSet.{u}) ⊗ K ⟶ X) (z : X _⦋0⦌)
    (h : ∀ k : K _⦋0⦌, IsLocalForHom
      (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge (prismVertexEvaluation g k))) z) :
    TrivialKanFibration (relativeFunctorPre (sliceOverProjection (SSet.yonedaEquiv.symm z)) g
      (prismEndpoint 0 K)) := by
  let p := sliceOverProjection (SSet.yonedaEquiv.symm z)
  let i := stdSimplex.δ (1 : Fin 2) ▷ K
  let j := inv (snd (Δ[0] : SSet.{u}) K)
  have ht := localPrism_tensorSource_sections_trivial g z h
  have hj := relativeFunctorPre_trivialKanFibration_of_rightAnodyne p (i ≫ g) j
    (rightAnodyneExtensions.of_isIso j)
  have hc : TrivialKanFibration
      (relativeFunctorPre p g i ≫ relativeFunctorPre p (i ≫ g) j) :=
    ⟨trivialKanFibrations.comp_mem _ _ ht.mem hj.mem⟩
  have hh : j ≫ i = prismEndpoint 0 K := prismSource_tensor_shape K
  rw [relativeFunctorPre_comp] at hc
  let P : (K ⟶ (Δ[1] : SSet.{u}) ⊗ K) → Prop :=
    fun a ↦ TrivialKanFibration (relativeFunctorPre p g a)
  exact (congrArg P hh).mp hc

/-- 点ごとの辺が局所なら、元の prism の始点面への終点固定余錐制限は自明 Kan。 -/
lemma localPrism_source_cocones_trivial {K X : SSet.{u}} [Quasicategory X]
    (g : (Δ[1] : SSet.{u}) ⊗ K ⟶ X) (z : X _⦋0⦌)
    (h : ∀ k : K _⦋0⦌, IsLocalForHom
      (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge (prismVertexEvaluation g k))) z) :
    TrivialKanFibration (cosliceRestrictionFiberMap g (prismEndpoint 0 K) z) := by
  have := localPrism_source_sections_trivial g z h
  have := vertexFiber_kanComplex_of_leftFibration (sliceUnderProjection g) z
  have := vertexFiber_kanComplex_of_leftFibration
    (sliceUnderProjection (prismEndpoint 0 K ≫ g)) z
  have he := (cosliceRestriction_homotopyEquivalence_iff_sections g (prismEndpoint 0 K) z).mpr
    (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  have := coconeMappingSpace_restrict_fibration g (prismEndpoint 0 K) z
  exact trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _ he

end SerrePositivity.InfinityCategories.HomotopyLimits
