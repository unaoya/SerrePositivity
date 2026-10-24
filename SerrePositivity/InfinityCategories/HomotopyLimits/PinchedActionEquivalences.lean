module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.PinchedComposition
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-!
概要：写像空間の前後合成は hX の同型を写像空間の同値に送る。
方針：同じ逆射で前後合成し、既存の合成則・恒等則の可逆二胞体を使う。
規約：局所化・反射の存在を仮定しない。使われ方：HTT 5.5.4 の局所対象。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 同型による写像空間の前合成は、元の合成・恒等同型を保つ同値。 -/
lemma pinchedPrecompose_isQCatEquivalence_of_isIso {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    [IsIso f] (z : X _⦋0⦌) : IsQCatEquivalence (PinchedInterval.precompose z f) := by
  exact (show QCatEquivalence (pinchedHom y z) (pinchedHom x z) from
    { hom := PinchedInterval.precompose z f
      inv := PinchedInterval.precompose z (inv f)
      homInvIso := by
        have h := PinchedInterval.precomposeCompIso z (inv f) f
        simp only [IsIso.inv_hom_id] at h
        exact h ≪≫ PinchedInterval.precomposeIdIso y z
      invHomIso := by
        have h := PinchedInterval.precomposeCompIso z f (inv f)
        simp only [IsIso.hom_inv_id] at h
        exact h ≪≫ PinchedInterval.precomposeIdIso x z
    }).isQCatEquivalence

/-- 同型による写像空間の後合成は同値。 -/
lemma pinchedPostcompose_isQCatEquivalence_of_isIso {y z : X _⦋0⦌}
    (f : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk z)
    [IsIso f] (x : X _⦋0⦌) : IsQCatEquivalence (PinchedInterval.postcompose x f) := by
  exact (show QCatEquivalence (pinchedHom x y) (pinchedHom x z) from
    { hom := PinchedInterval.postcompose x f
      inv := PinchedInterval.postcompose x (inv f)
      homInvIso := by
        have h := PinchedInterval.postcomposeCompIso x f (inv f)
        simp only [IsIso.hom_inv_id] at h
        exact h ≪≫ PinchedInterval.postcomposeIdIso x y
      invHomIso := by
        have h := PinchedInterval.postcomposeCompIso x (inv f) f
        simp only [IsIso.inv_hom_id] at h
        exact h ≪≫ PinchedInterval.postcomposeIdIso x z
    }).isQCatEquivalence

end
end SerrePositivity.InfinityCategories.HomotopyLimits
