module
public import SerrePositivity.KST.Fibration.WeakStringCofiberFamilies

/-! # 退化辺の共通 cofiber 族の零性

元の退化辺の任意の選択した cofiber は零である。
これを核値完全関手全体の零性へ移し、全高次入力を持つ退化の正規化を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 核値完全関手の各値は、元の同じ実四角形の cofiber 頂点である。 -/
lemma weakStringKernelCofiber_vertex_val {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) (v : (weakStringCategory q n) _⦋0⦌) :
    ((weakStringKernelCofiber q α).val.app (Opposite.op ⦋0⦌) v).val =
      (vertexCofiberSquare (B := B) (weakStringCofiberVertex q α v)).cofiber :=
  cofiberVertex_corner B (weakStringCofiberVertex q α v)
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)

/-- 元の退化辺に対する共通の実 cofiber 頂点は零である。 -/
lemma weakStringCofiberVertex_degenerate_zero {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (γ : ⦋0⦌ ⟶ n) (v : (weakStringCategory q n) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (vertexCofiberSquare (B := B)
      (weakStringCofiberVertex q (SimplexCategory.σ (0 : Fin 1) ≫ γ) v)).cofiber := by
  apply (weakStringCofiberVertex_zero_iff q _ v).2
  rw [op_comp, B.obj.map_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_degenerate (X := B.obj)
    (B.obj.map γ.op (simplexVertexValue n v.val))

/-- 退化辺の共通 cofiber 完全関手は、核の全関手圏で実際に零対象である。 -/
lemma weakStringKernelCofiber_degenerate_isZeroVertex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (γ : ⦋0⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (weakStringKernelCofiber q
      (SimplexCategory.σ (0 : Fin 1) ≫ γ)).val) := by
  apply isZeroVertex_functorVertex_of_pointwise
  intro v
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex
      (((weakStringKernelCofiber q (SimplexCategory.σ (0 : Fin 1) ≫ γ)).val.app
        (Opposite.op ⦋0⦌) v).val) := by
    rw [weakStringKernelCofiber_vertex_val]
    exact weakStringCofiberVertex_degenerate_zero q γ v
  exact ⟨isInitialVertex_fullSubcomplex_of_ambient (kernelClosedPredicate q).predicate _ hz.1,
    isTerminalVertex_fullSubcomplex_of_ambient (kernelClosedPredicate q).predicate _ hz.2⟩

end SerrePositivity.KST.Fibration
