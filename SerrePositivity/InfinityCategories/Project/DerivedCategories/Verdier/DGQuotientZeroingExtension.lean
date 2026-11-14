module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientZeroObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorZeroObjects

/-! # 指定対象を零化する dg 関手の商への延長

概要：dg nerve で指定対象を零化する dg 関手を、明示的 dg 商からの関手へ延長する。
方針：実零対象性から収縮元を選び、既存の指定収縮付き延長を適用する。
規約：dg 関手から来る写像に関する主張。全 ∞ 関手圏の局所化普遍性は別途必要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable {P : Set D}

/-- 対象像が実零頂点なら、その dg 関手に指定収縮データを付けられる。 -/
lemma dgFunctor_exists_contracted_of_zeroing (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hF : ∀ b : P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj b.val))) :
    ∃ C : _root_.SerrePositivity.DifferentialGraded.DGQuotient.ContractedFunctor A D P E, C.toDGFunctor = F := by
  have hc (b : P) := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_iff_contractingElement (F.obj b.val)).1 (hF b)
  exact ⟨⟨F, fun b => (hc b).choose, fun b => (hc b).choose_spec⟩, rfl⟩

/-- 指定収縮データが存在することと、対象像が実零頂点となることは同値。 -/
lemma dgFunctor_zeroing_iff_exists_contracted (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) :
    (∀ b : P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj b.val))) ↔
      ∃ C : _root_.SerrePositivity.DifferentialGraded.DGQuotient.ContractedFunctor A D P E, C.toDGFunctor = F := by
  constructor
  · exact dgFunctor_exists_contracted_of_zeroing F
  · rintro ⟨C, rfl⟩ b
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isZeroVertex _ (C.homotopy b) (C.d_homotopy b)

variable [Small.{u} D]

/-- 指定対象を実零頂点へ送る dg 関手は、商の nerve を経由する dg 関手の像に延長する。 -/
lemma dgQuotient_exists_nerve_extension_of_zeroing (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hF : ∀ b : P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex b.val))) :
    ∃ G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) E,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  have hz (b : P) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj b.val)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] using hF b
  obtain ⟨C, hC⟩ := dgFunctor_exists_contracted_of_zeroing F hz
  refine ⟨_root_.SerrePositivity.DifferentialGraded.DGQuotient.extension A C, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveExtension A C = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveExtension_projection, hC]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
