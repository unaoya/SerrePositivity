module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedKernelYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGThickKernelNativeRetract
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientThickKernel

/-!
概要：同じ実平坦商の零化対象は、D-9 の同じ実小核の本質像そのものである。
方針：D 正本の thick 核の retract 表示を、同じ実核の native 冪等完備性で戻す。
規約：同じ I と実供給 P に依存する実模型への特殊化。一般商の核 API は新設しない。
使われ方：K-6 c5 の完備化前の実 Verdier 列を Sp の認証へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
local notation "B" => DGCategoryCellResolution.Source R (DGKappaCone R D I)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)
local notation "C" => dgKappaResolvedKernelKInput R D I
local notation "i" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (ULift.down (dgKappaResolvedKernelInputMap R D I))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (ULift.down (dgKappaResolvedSuspensionInputMap R D I))

/-- 概要：同じ実核の本質像は、元の指定零化対象の native 安定閉包そのもの。
方針：元の dg 包含の頂点回収と安定閉包の同型閉性を使う。
規約：同じ平坦源・同じ元の対象集合を保持する。
使われ方：D 正本の元の Verdier 辺と Sp の本質像 cofiber 辺の照合。 -/
theorem dgKappaNativeKernel_image_iff (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (B)) _⦋0⦌) :
    (∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((i).app (Opposite.op ⦋0⦌) a) b)) ↔
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' (P)) b := by
  constructor
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective a
    have hix : (i).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm x) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x.val :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (ULift.down (dgKappaResolvedKernelInputMap R D I)) x
    rw [hix] at e
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_iso e x.property
  · intro hb
    obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective b
    let a : C := ⟨x, hb⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex a, ⟨?_⟩⟩
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
    exact Iso.refl _

/-- 概要：同じ実商の零化対象は、完備化前の同じ実核の本質像に厳密に一致する。
方針：D の thick 核判定と retract 表示を、同じ実核の冪等完備な充満忠実像へ戻す。
規約：固定 ν の完備化後の認証は主張しない。I の実例の存在も主張しない。
使われ方：K-6 c5 の完備化前の連結 fibration の kernel 認証。 -/
theorem dgKappaNativeProjection_zero_iff_kernelImage (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (B)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((q).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((i).app (Opposite.op ⦋0⦌) a) b) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D I)
  constructor
  · intro hb
    obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective b
    have hx := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_vertex_isZero_iff_thick R
      (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) x).mp hb
    obtain ⟨y, hy, ⟨r⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty_iff_nativeStableRetract R (B) (P) x).mp hx
    let a : C := ⟨y, hy⟩
    have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
        ((i).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex a)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
      exact r
    have hC := dgKappaResolvedKernelNerve_isIdempotentComplete R D I
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)
    have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (B)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (B) (P))
    obtain ⟨a', ⟨e⟩⟩ := hC.retract_iso_in_image i hi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) hr
    exact ⟨a', ⟨e.symm⟩⟩
  · rintro ⟨a, ⟨e⟩⟩
    have hz := dgKappaResolvedKernel_quotient_kills R D I a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at hz
    exact hz.of_vertexIso (e.map q)

end SerrePositivity.KST.NonConnective
