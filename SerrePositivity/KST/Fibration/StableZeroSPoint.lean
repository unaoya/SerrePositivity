module
public import SerrePositivity.KST.Fibration.StableZeroSContraction
public import SerrePositivity.KST.Fibration.RelativeSQuotient
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-! # 同じ零自己関手の S• 像の、全単体で自然な零図式の一点への因子化 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ元の零自己完全関手による、全単体的 S• の元の後合成射。 -/
def stableZeroSMap (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    simplicialSConstruction A.obj ⟶ simplicialSConstruction A.obj :=
  simplicialSPostcomp (stableZeroEndMap A).hom (exactMap_preservesSData _)

/-- 同じ零対象から作った元の各 S_n 零図式の頂点を、全単体で自然に保持する。 -/
def stableZeroSPoint (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj (𝟙_ SSet.{u}) ⟶ simplicialSConstruction A.obj where
  app n := (SSet.unitHomEquiv _).symm
    (sConstructionZeroVertex n.unop.len (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex A.obj).vertex
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex A.obj).isZero)
  naturality {n m} θ := by
    apply (SSet.unitHomEquiv _).injective
    simp only [Functor.const_obj_map]
    change SSet.unitHomEquiv _ ((SSet.unitHomEquiv _).symm _) =
      ((simplicialSConstruction A.obj).map θ).app (Opposite.op ⦋0⦌)
        (SSet.unitHomEquiv _ ((SSet.unitHomEquiv _).symm _))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (sMap_zeroVertex θ.unop.toOrderHom _ _).symm

/-- 元の各 S_n の零自己関手は、同じ零図式への定値射そのもの。 -/
theorem stableZeroSMap_app_constant (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    (stableZeroSMap A).app n = SSet.const
      (sConstructionZeroVertex n.unop.len (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex A.obj).vertex
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex A.obj).isZero) := by
  apply (cancel_mono (gappedSubcomplex n.unop.len A.obj).ι).1
  change sPostcomp n.unop.len (stableZeroEndMap A).hom
    (exactMap_preservesSData (stableZeroEndMap A)) ≫ _ = _
  rw [sPostcomp_ι, stableZeroEndMap_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.ihom_map_const, SSet.comp_const, SSet.const_comp]
  rfl

/-- 全 S• 図式から同じ一点図式への元の一意な実射。 -/
def stableZeroSToPoint (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    simplicialSConstruction A.obj ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (𝟙_ SSet.{u}) where
  app _ := toUnit _
  naturality {_ _} _ := isTerminalTensorUnit.hom_ext _ _

/-- 元の零自己関手の全 S• 像は、同じ一点射と同じ零図式点を厳密に通る。 -/
theorem stableZeroSMap_factor (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    stableZeroSMap A = stableZeroSToPoint A ≫ stableZeroSPoint A := by
  apply NatTrans.ext
  funext n
  rw [stableZeroSMap_app_constant]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.KST.Fibration
