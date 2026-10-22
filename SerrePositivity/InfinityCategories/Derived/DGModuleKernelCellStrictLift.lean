module
public import SerrePositivity.InfinityCategories.Derived.DGFreeSphereHomSurjective
public import SerrePositivity.InfinityCategories.Derived.DGModuleCoproductHomSurjective
public import SerrePositivity.InfinityCategories.Derived.DGModulePrimitiveOverZero
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeStrictPostcomposition
public import SerrePositivity.DifferentialGraded.Module.KernelCells
public import SerrePositivity.DifferentialGraded.Derived.CoproductProjective
/-!
概要：実 kernel cell 付加の一段を、次数別全射準同型に沿って厳密に持ち上げる。
方針：自由 sphere の余積の Hom を使い、零像の原始元から cone を延長する。
規約：前段への制限と augmentation 正方形は厳密。使われ方：canonical strict lift。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgModuleKernelCellHom_postcompose_surjective
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    {M N T U : ModuleCategory R D} (f : M ⟶ N) (q : T ⟶ U)
    (hq : moduleDegreewiseSurjective R D q) (p : ℤ) :
    Function.Surjective
      ((eHomWhiskerLeft (Complex R) (moduleKernelCellSource R D f) q).f p) := by
  exact dgModuleCoproductHom_postcompose_surjective R D (moduleKernelCellFamily R D f) q
    (fun j p => dgModuleFreeSphereHom_postcompose_surjective R D
      j.1 (j.2.1 + 1) q hq p) p
lemma dgModuleKernelCellStep_strict_lift
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    {M N T U : ModuleCategory R D} (f : M ⟶ N) (g : N ⟶ U) (q : T ⟶ U)
    (hqs : moduleDegreewiseSurjective R D q) (hqq : moduleQuasiIso R D q)
    (b : M ⟶ T) (hb : b ≫ q = f ≫ g) :
    ∃ c : moduleKernelCellStep R D f ⟶ T,
      moduleKernelCellStepι R D f ≫ c = b ∧
        c ≫ q = moduleKernelCellStepπ R D f ≫ g := by
  have hp : moduleHomotopicallyProjective R D (moduleKernelCellSource R D f) :=
    moduleCoproduct_homotopicallyProjective R D (moduleKernelCellFamily R D f)
      (fun j => freeSphere_homotopicallyProjective R D j.1 (j.2.1 + 1))
  have hz : moduleKernelCellMap R D f ≫ b ≫ q = 0 := by
    rw [hb, ← Category.assoc, moduleKernelCellMap_comp, zero_comp]
  obtain ⟨h, hh, hhq⟩ := dgModuleBoundary_primitive_over_zero R D
    (moduleKernelCellMap R D f) b q hp hqq
    (dgModuleKernelCellHom_postcompose_surjective R D f q hqs) hz
  let c := moduleConeDescOfBoundary R D (moduleKernelCellMap R D f) h b hh
  refine ⟨c, moduleConeDescOfBoundary_inr R D _ h b hh, ?_⟩
  have hzero : moduleKernelCellMap R D f ≫ (f ≫ g) = 0 := by
    rw [← Category.assoc, moduleKernelCellMap_comp, zero_comp]
  have hc := dgModuleConeBoundaryDesc_postcompose_zero R D
    (moduleKernelCellMap R D f) h b hh q hhq (f ≫ g) hb hzero
  exact hc.trans (dgModuleConeDesc_postcompose R D
    (moduleKernelCellMap R D f) f (moduleKernelCellMap_comp R D f) g).symm
end
end SerrePositivity.InfinityCategories
