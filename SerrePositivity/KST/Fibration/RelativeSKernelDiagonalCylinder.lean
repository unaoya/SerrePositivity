module
public import SerrePositivity.KST.Fibration.RelativeSKernelContractionCylinder
public import SerrePositivity.KST.Fibration.StableZeroSDiagonalCylinder

/-! # 相対 S• 核の元の対角を、全単体に共通の零図式へ収縮する実円柱 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 元の全単体的包含同型の、同じ元の対角上の同型。 -/
def relativeSKernelDiagonalIso (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction (i.hom ≫ q.hom)) ≅
      simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj) :=
  simplicialDiagonalFunctor.mapIso (relativeSKernelSimplicialIso h)

/-- 全時刻で面・退化と整合する相対核円柱の、同じ対角上の実評価。 -/
def relativeSKernelDiagonalCylinder (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction (i.hom ≫ q.hom)) ⊗
      (Δ[1] : SSet.{u}) ⟶
        simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction (i.hom ≫ q.hom)) :=
  simplicialCylinderDiagonal _ _ _ (relativeSKernelContractionCylinder h)

/-- 元の相対核円柱は、同じ包含同型を通る元の S• 円柱を厳密に回収する。 -/
theorem relativeSKernelDiagonalCylinder_eq (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    relativeSKernelDiagonalCylinder h =
      ((relativeSKernelDiagonalIso h).hom ▷ (Δ[1] : SSet.{u})) ≫
        stableZeroSDiagonalCylinder A ≫ (relativeSKernelDiagonalIso h).inv := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 全相対核の零図式点を、元の同じ対角の点として保持する。 -/
def relativeSKernelDiagonalPoint (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    𝟙_ SSet.{u} ⟶
      simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction (i.hom ≫ q.hom)) :=
  stableZeroSDiagonalPoint A ≫ (relativeSKernelDiagonalIso h).inv

/-- 元の相対核円柱の始点は、同じ一点を通る同じ零図式射。 -/
theorem relativeSKernelDiagonalCylinder_zero (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    SSet.ι₀ ≫ relativeSKernelDiagonalCylinder h =
      toUnit _ ≫ relativeSKernelDiagonalPoint h := by
  rw [relativeSKernelDiagonalCylinder_eq, ← Category.assoc, SSet.ι₀_comp,
    Category.assoc, ← Category.assoc SSet.ι₀, stableZeroSDiagonalCylinder_zero,
    stableZeroSDiagonalMap_factor, ← Category.assoc]
  have ht : (relativeSKernelDiagonalIso h).hom ≫ toUnit _ = toUnit _ :=
    isTerminalTensorUnit.hom_ext _ _
  rw [← Category.assoc, ht, Category.assoc]
  rfl

/-- 元の相対核円柱の終点は、同じ元の核対角の恒等射。 -/
theorem relativeSKernelDiagonalCylinder_one (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    SSet.ι₁ ≫ relativeSKernelDiagonalCylinder h =
      𝟙 (simplicialDiagonalFunctor.obj
        (relativeSimplicialSConstruction (i.hom ≫ q.hom))) := by
  rw [relativeSKernelDiagonalCylinder_eq, ← Category.assoc, SSet.ι₁_comp,
    Category.assoc, ← Category.assoc SSet.ι₁, stableZeroSDiagonalCylinder_one,
    Category.id_comp, Iso.hom_inv_id]

/-- 同じ全単体的実円柱から得た、元の相対核対角の具体的収縮ホモトピー。 -/
def relativeSKernelDiagonalContraction (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    SSet.Homotopy (toUnit _ ≫ relativeSKernelDiagonalPoint h)
      (𝟙 (simplicialDiagonalFunctor.obj
        (relativeSimplicialSConstruction (i.hom ≫ q.hom)))) where
  h := relativeSKernelDiagonalCylinder h
  h₀ := relativeSKernelDiagonalCylinder_zero h
  h₁ := relativeSKernelDiagonalCylinder_one h
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.KST.Fibration
