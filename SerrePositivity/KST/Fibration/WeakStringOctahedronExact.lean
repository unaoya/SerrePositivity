module
public import SerrePositivity.KST.Fibration.FamilyExactness
public import SerrePositivity.KST.Fibration.WeakStringOctahedronKernel

/-! # 八面体の比較列の完全な関手化

共通 cofiber 完全関手との自然同型で両端の完全性を示し、
元の cofiber 射影の反映性で全四角形の族の完全性を導く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 八面体の最後の列の始点が表す関手は完全である。 -/
lemma weakStringOctahedron_source_preservesCofiberData {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    PreservesCofiberData ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 0 0)) := by
  apply preservesCofiberData_of_familyVertexIso _
    ((weakStringKernelCofiber q (SimplexCategory.δ (2 : Fin 3) ≫ β)).val ≫
      (closedStableInclusion (kernelClosedPredicate q)).val)
  · rw [(weakStringOctahedronFamily q β).last_source, weakStringCofiberFamily_quotient]
  · exact (weakStringKernelCofiber q _).property.comp
      (closedStableInclusion (kernelClosedPredicate q)).property

/-- 中間頂点の族も、長辺の共通 cofiber 完全関手との自然同型で完全である。 -/
lemma weakStringOctahedron_middle_preservesCofiberData {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    PreservesCofiberData ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (weakStringCategory q n) B.obj).symm
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 1 0)) := by
  apply preservesCofiberData_of_familyVertexIso _
    ((weakStringKernelCofiber q (SimplexCategory.δ (1 : Fin 3) ≫ β)).val ≫
      (closedStableInclusion (kernelClosedPredicate q)).val)
  · rw [(weakStringOctahedronFamily q β).last_middle]
    have he := cofiberFamilyCornerIso (weakStringOctahedronFamily_compositeComparison q β)
    rw [weakStringCofiberFamily_quotient] at he
    exact he
  · exact (weakStringKernelCofiber q _).property.comp
      (closedStableInclusion (kernelClosedPredicate q)).property

/-- 八面体の最後の実 cofiber 列の全四角形を、元の列図式圏上の族へ戻す。 -/
def weakStringOctahedronCofiberFamily {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) : weakStringCategory q n ⟶ cofiberDiagrams B.obj :=
  cofiberFamilyUntranspose (weakStringOctahedronFamily q β).second.rightZeroTriangle
    (weakStringOctahedronFamily q β).second.right_isCofiber

/-- 比較列の全四角形の族は完全関手である。 -/
lemma weakStringOctahedronCofiberFamily_preservesCofiberData {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    PreservesCofiberData (weakStringOctahedronCofiberFamily q β) := by
  apply cofiberFamily_preservesCofiberData_of_endpoints
  · change PreservesCofiberData (cofiberFamilyUntranspose _ _ ≫
      (cofiberStableEvaluation (sInputModel B)
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)).val)
    rw [cofiberFamilyUntranspose_corner]
    exact weakStringOctahedron_source_preservesCofiberData q β
  · change PreservesCofiberData (cofiberFamilyUntranspose _ _ ≫
      (cofiberStableEvaluation (sInputModel B)
        (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0)).val)
    rw [cofiberFamilyUntranspose_corner]
    exact weakStringOctahedron_middle_preservesCofiberData q β

/-- 全パラメーターを保った八面体の比較列を、K-1 の完全関手として保持する。 -/
def weakStringOctahedronCofiberExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    weakStringModel q n ⟶ cofiberStableModel (sInputModel B) :=
  ⟨weakStringOctahedronCofiberFamily q β,
    weakStringOctahedronCofiberFamily_preservesCofiberData q β⟩

end SerrePositivity.KST.Fibration
