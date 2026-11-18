module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeOverJoin
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeJoin

/-!
概要：slice 内の元の大域二重 cone の射影は、元の大域 cone 自身と厳密に一致する。
方針：恒等錐の同じ先端への射影を保持し、全 coslice 単体の射影を uncurry する。
規約：HA Construction 1.3.1.6・1.3.1.13、点ごとの射の類ではなく大域写像の等式。使われ方：二重 join の元の前面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeOverJoin_projection :
    strictRawModuleTensorDoubleConeOverJoin A X P Q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (strictRawModuleTensorConePoint A X P) = strictRawModuleTensorConeJoin A X P Q := by
  let K := nerve (strictRawModuleTensorElementIndex A X P Q)
  let C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P)
  let q : S ⟶ C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (strictRawModuleTensorConePoint A X P)
  have ht : ∀ (p : (Δ[0] : SSet.{u + 1}) ⟶ S) (r : (Δ[0] : SSet.{u + 1}) ⟶ C),
      p ≫ q = r → ∀ (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r),
      (∀ (n : SimplexCategoryᵒᵖ) (c : K.obj n), (f.app n c).val ≫ q = (g.app n c).val) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry g := by
    intro p r hp f g hf
    subst r
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp]
    congr 1
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    exact hf n c
  apply ht (strictRawModuleTensorIdentityOverPoint A X P) (strictRawModuleTensorConePoint A X P)
    (strictRawModuleTensorIdentityOverPoint_projection A X P)
    (strictRawModuleTensorDoubleConeUnderOverMap A X P Q) (strictRawModuleTensorConeUnderMap A X P Q)
  rintro ⟨⟨n⟩⟩ c
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P))).symm
        (strictRawModuleTensorDoubleConeOverSimplex A X P Q c)) ≫ q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm (strictRawModuleTensorConeSimplex A X P Q c)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp,
    strictRawModuleTensorDoubleConeOverSimplex_projection]

end SerrePositivity.EInfinity.BarrattEccles
