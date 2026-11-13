module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedComposition

/-!
概要：可逆なホモトピー圏の射による pinched 写像空間の後合成は同値。
方針：同じ射の逆による後合成を逆射とし、既存の合成・単位の全族比較を使う。
規約：指定した後合成射を保つ。
使われ方：G14 の検出族の順方向。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 可逆な射の元の pinched 後合成は、元の逆射の後合成を逆とする同値。 -/
lemma postcompose_isQCatEquivalence_of_isIso {E : SSet.{u}} [Quasicategory E]
    (M : E _⦋0⦌) {x y : E _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj E) ⟶ HomotopyCategory.mk y) [IsIso f] :
    IsQCatEquivalence (postcompose M f) := by
  refine ⟨postcompose M (inv f), ⟨?_⟩, ⟨?_⟩⟩
  · have h := postcomposeCompIso M f (inv f)
    rw [IsIso.hom_inv_id] at h
    exact h ≪≫ postcomposeIdIso M x
  · have h := postcomposeCompIso M (inv f) f
    rw [IsIso.inv_hom_id] at h
    exact h ≪≫ postcomposeIdIso M y

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
