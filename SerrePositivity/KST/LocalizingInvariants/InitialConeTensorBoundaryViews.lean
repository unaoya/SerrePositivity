module

public import SerrePositivity.KST.LocalizingInvariants.InitialConeTensorCornerGluing

/-!
概要：反転で構成した全境界の二部分を、元の図式と回収済み尾部の積に戻す。
方針：積と反転の同型、左錐の反転同型を使い、共有部分と全包含を計算する。
規約：両部分と共有部分の全射を厳密に保持する。
使われ方：c5 の次元帰納から、元の実図式と尾部を相対貼合せへ代入する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

private lemma opTensorBoundary_natural {A B A' B' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') :
    SSet.opFunctor.map (f ⊗ₘ g) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso A' B').inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso A B).inv ≫ (SSet.opFunctor.map f ⊗ₘ SSet.opFunctor.map g) := rfl

def initialConeTensorOldIso (A L : SSet.{u}) :
    (A.op ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L.op (Δ[0] : SSet.{u})).op ≅ A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso A.op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L.op (Δ[0] : SSet.{u}))).symm ≪≫
    tensorIso (SSet.opFunctorCompOpFunctorIso.app A) (initialConeOppositeIso L)

def initialConeTensorTailIso (A L : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A.op (Δ[0] : SSet.{u}) ⊗ L.op).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ L :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A.op (Δ[0] : SSet.{u})) L.op).symm ≪≫
    tensorIso (initialConeOppositeIso A) (SSet.opFunctorCompOpFunctorIso.app L)

def initialConeTensorOverlapIso (A L : SSet.{u}) : (A.op ⊗ L.op).op ≅ A ⊗ L :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso A.op L.op).symm ≪≫
    tensorIso (SSet.opFunctorCompOpFunctorIso.app A) (SSet.opFunctorCompOpFunctorIso.app L)

lemma initialConeTensorOldIso_overlap (A L : SSet.{u}) :
    SSet.opFunctor.map (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) ≫
      (initialConeTensorOldIso A L).hom =
      (initialConeTensorOverlapIso A L).hom ≫ (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) L) := by
  simp only [initialConeTensorOldIso, initialConeTensorOverlapIso,
    Iso.trans_hom, Iso.symm_hom, tensorIso_hom, ← id_tensorHom]
  rw [← Category.assoc, opTensorBoundary_natural]
  simp only [Category.assoc, tensorHom_comp_tensorHom, SSet.opFunctor.map_id,
    Category.id_comp, Category.comp_id, initialConeOppositeIso_old]

lemma initialConeTensorTailIso_overlap (A L : SSet.{u}) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op (Δ[0] : SSet.{u}) ▷ L.op) ≫
      (initialConeTensorTailIso A L).hom =
      (initialConeTensorOverlapIso A L).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) A ▷ L) := by
  simp only [initialConeTensorTailIso, initialConeTensorOverlapIso,
    Iso.trans_hom, Iso.symm_hom, tensorIso_hom, ← tensorHom_id]
  rw [← Category.assoc, opTensorBoundary_natural]
  simp only [Category.assoc, tensorHom_comp_tensorHom, SSet.opFunctor.map_id,
    Category.id_comp, Category.comp_id, initialConeOppositeIso_old]

lemma initialConeTensorOldInclusion_view (A L : SSet.{u}) :
    initialConeTensorOldInclusion A L ≫ initialConeTensorCornerInclusion A L =
      (initialConeTensorOldIso A L).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) A ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L) := by
  rw [initialConeTensorOldInclusion, initialConeTensorCornerInclusion,
    ← Category.assoc, ← SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_old]
  simp only [initialConeTensorOldIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    ← tensorHom_id]
  rw [← Category.assoc, opTensorBoundary_natural]
  simp only [Category.assoc, tensorHom_comp_tensorHom, SSet.opFunctor.map_id,
    Category.id_comp, Category.comp_id, initialConeOppositeIso_old]

lemma initialConeTensorTailInclusion_view (A L : SSet.{u}) :
    initialConeTensorTailInclusion A L ≫ initialConeTensorCornerInclusion A L =
      (initialConeTensorTailIso A L).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) L) := by
  rw [initialConeTensorTailInclusion, initialConeTensorCornerInclusion,
    ← Category.assoc, ← SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_lower]
  simp only [initialConeTensorTailIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    ← id_tensorHom]
  rw [← Category.assoc, opTensorBoundary_natural]
  simp only [Category.assoc, tensorHom_comp_tensorHom, SSet.opFunctor.map_id,
    Category.id_comp, Category.comp_id, initialConeOppositeIso_old]

end SerrePositivity.KST.LocalizingInvariants
