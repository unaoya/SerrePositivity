module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.Localization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SupportOperations
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom

/-! # 主イデアル上の台の任意直和閉性

概要：一般の D_{V(a)} の semifree モデルは小さい任意直和で閉じる。
方針：局所化後の非輪状 semifree 複体は可縮であり、可縮複体の直和も可縮となる。
規約：一様な冪消去を使わない。使われ方：非有界の台つき部分圏の直和閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S]

/-- 概要：可縮複体の任意の小さい直和の全ホモロジーは零である。
方針：dg 加群のホモトピー圏の余積の射の一意性を使う。
規約：任意の添字、小ささのみ。使われ方：局所化後の直和の非輪状性。 -/
lemma contractibleCoproduct_homology_zero {I : Type v} [Small.{u} I]
    (P : I → Complex S) (hP : ∀ i, Nonempty (Homotopy (𝟙 (P i)) 0)) :
    ∀ n : ℤ, IsZero ((∐ P).homology n) := by
  let M := fun i => ForgetEnrichment.of (Complex S) (ringModule S (P i))
  let F := (ringEvaluationHomotopyEquivalence S).functor ⋙ complexHomotopyComparison S
  have hz (i : I) : IsZero ((moduleToHomotopy S PUnit.{1}).obj (M i)) := by
    apply IsZero.of_full_of_faithful_of_isZero F
    apply (IsZero.iff_id_eq_zero _).2
    exact ((HomotopyCategory.quotient _ _).map_id (P i)).symm.trans
      ((HomotopyCategory.eq_of_homotopy _ _ (hP i).some).trans
        ((HomotopyCategory.quotient _ _).map_zero _ _))
  have hsum : IsZero ((moduleToHomotopy S PUnit.{1}).obj (∐ M)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply moduleHomotopyCoproduct_hom_ext S PUnit.{1} M
    intro i
    simp only [Category.comp_id, comp_zero]
    exact (hz i).eq_of_src _ _
  have heval := F.map_isZero hsum
  have hq : IsZero ((HomotopyCategory.quotient _ _).obj (∐ P)) :=
    heval.of_iso ((HomotopyCategory.quotient _ _).mapIso
      (PreservesCoproduct.iso (ringModuleEquivalence S).functor M)).symm
  intro n
  exact ((HomotopyCategory.homologyFunctor (ModuleCat S) (.up ℤ) n).map_isZero hq).of_iso
    ((HomotopyCategory.homologyFunctorFactors _ _ n).app (∐ P)).symm

/-- 概要：主イデアルの台を持つ semifree 複体の任意直和も同じ台を持つ。
方針：局所化と直和を交換し、K 射影非輪状複体の可縮性を使う。
規約：有界性・有限生成性は不要。使われ方：一般の D_Z の直和閉性。 -/
lemma supportedSemifree_coproduct_support (a : S) {I : Type v} [Small.{u} I]
    (P : I → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)
    (hP : ∀ i, HasHomologySupportOn (supportZeroLocus (Ideal.span ({a} : Set S))) (P i).val) :
    HasHomologySupportOn (supportZeroLocus (Ideal.span ({a} : Set S))) (∐ fun i => (P i).val) := by
  let T := Localization.Away a
  let f := algebraMap S T
  let Q := fun i => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).obj (P i).val
  have hQ (i : I) : (Q i).IsKProjective :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective T (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_baseChange f (P i).property)
  have hacy (i : I) : (Q i).Acyclic := by
    intro n
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ n).2
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homologySupport_iff_localization_acyclic (T := T) a _).1 (hP i) n)
  have hh := contractibleCoproduct_homology_zero T Q (fun i => by
    have := hQ i
    exact ⟨CochainComplex.IsKProjective.homotopyZero (𝟙 (Q i)) (hacy i)⟩)
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homologySupport_iff_localization_acyclic (T := T) a _).2
  intro n
  exact (hh n).of_iso ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (PreservesCoproduct.iso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f) (fun i => (P i).val)))

/-- 概要：D_{V(a)} のモデルの任意の小さい直和。
方針：semifree 性と主イデアルの台の直和閉性を組み合わせる。
規約：完全性は課さない。使われ方：一般の台つき導来部分圏の直和。 -/
def supportedSemifreeCoproduct (a : S) {I : Type v} [Small.{u} I]
    (P : I → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportedSemifree S (supportZeroLocus (Ideal.span ({a} : Set S)))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportedSemifree S (supportZeroLocus (Ideal.span ({a} : Set S))) :=
  ⟨⟨∐ (fun i => (P i).val.val),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_coproduct S _ (fun i => (P i).val.property)⟩,
    supportedSemifree_coproduct_support S a (fun i => (P i).val) (fun i => (P i).property)⟩

/-- 概要：D_{V(a)} の正本の任意の小さい頂点族の直和。
方針：各頂点から台つきモデルを取り出し直和を正本へ戻す。
規約：有界性・完全性は不要。使われ方：一般の台つき導来部分圏の直和閉性。 -/
def supportedInfinityCoproduct (a : S) {I : Type v} [Small.{u} I]
    (x : I → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S
      (supportZeroLocus (Ideal.span ({a} : Set S)))) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S (supportZeroLocus (Ideal.span ({a} : Set S)))) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportedInfinityVertex S _ (supportedSemifreeCoproduct S a
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportedInfinityRepresentative S _ (x i)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
