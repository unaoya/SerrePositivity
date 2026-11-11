module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StandardCofiberSquare
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberSquare
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # 標準 cofiber の fiber の回転比較

概要：cofiber の二包含の差の fiber は、元の始域とホモトピー同値になる。
方針：第二直和成分の符号を反転し、包含の cone の回転ホモトピー同値をシフトする。
規約：具体的な四角形の比較射との照合は別途必要。使われ方：D7 の fiber/cofiber の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomologicalComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 二項直和の第二成分だけの符号を反転する自己同型。 -/
def cofiberBiproductSignIso (B C : _root_.SerrePositivity.DifferentialGraded.Complex S) : B ⊞ C ≅ B ⊞ C where
  hom := biprod.map (𝟙 B) (-𝟙 C)
  inv := biprod.map (𝟙 B) (-𝟙 C)
  hom_inv_id := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply biprod.hom_ext <;> simp [Category.assoc]

/-- 二包含の差は直和の符号反転の後の標準 cone 包含に等しい。 -/
lemma cofiberOutputDifference_eq (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g) =
      (cofiberBiproductSignIso B C).hom ≫ mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g) := by
  apply biprod.hom_ext'
  · simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB, cofiberBiproductSignIso, ← Category.assoc]
  · simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC, cofiberBiproductSignIso, ← Category.assoc]

/-- 符号反転は二包含の差と標準包含の間の可換四角形を作る。 -/
lemma cofiberOutputDifference_comm (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g) ≫ 𝟙 _ =
      (cofiberBiproductSignIso B C).hom ≫ mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g) := by
  rw [Category.comp_id, cofiberOutputDifference_eq]

/-- 二包含の差の cone と標準包含の cone の同型。 -/
def cofiberOutputConeIso (f : A ⟶ B) (g : A ⟶ C) :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)) ≅
      mappingCone (mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g)) where
  hom := mappingCone.map _ _ (cofiberBiproductSignIso B C).hom (𝟙 _)
    (cofiberOutputDifference_comm f g)
  inv := mappingCone.map _ _ (cofiberBiproductSignIso B C).inv (𝟙 _) (by
    rw [Category.comp_id, cofiberOutputDifference_eq, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.hom_inv_id, Category.id_comp, mappingCone.map_id]
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.inv_hom_id, Category.id_comp, mappingCone.map_id]

/-- 複体のホモトピー同値は全整数シフトで保たれる。 -/
def cochainHomotopyEquivShift {K L : _root_.SerrePositivity.DifferentialGraded.Complex S} (e : HomotopyEquiv K L) (n : ℤ) :
    HomotopyEquiv (K⟦n⟧) (L⟦n⟧) where
  hom := e.hom⟦n⟧'
  inv := e.inv⟦n⟧'
  homotopyHomInvId := by simpa using e.homotopyHomInvId.shift n
  homotopyInvHomId := by simpa using e.homotopyInvHomId.shift n

/-- 標準 cofiber の二包含の差の fiber は元の始域とホモトピー同値。 -/
def cofiberFiberRotationEquiv (f : A ⟶ B) (g : A ⟶ C) :
    HomotopyEquiv A (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)) :=
  ((HomotopyEquiv.ofIso
    ((shiftFunctorCompIsoId (_root_.SerrePositivity.DifferentialGraded.Complex S) (1 : ℤ) (-1) (by omega)).app A).symm).trans
      (cochainHomotopyEquivShift
        (mappingCone.rotateHomotopyEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g)) (-1))).trans
    (HomotopyEquiv.ofIso ((CategoryTheory.shiftFunctor (_root_.SerrePositivity.DifferentialGraded.Complex S) (-1 : ℤ)).mapIso
      (cofiberOutputConeIso f g).symm))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
