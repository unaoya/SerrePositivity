module
public import SerrePositivity.KST.SConstruction.CubicalDayTensor

/-! # 元の零次元立方体と cubical Day 単位の比較
概要：全 cubical sets の Day 単位を、元の零次元の表現可能立方体と比較する。
方針：Day 単位の普遍性と、同じ零次元恒等 cell の Yoneda 射を使う。
規約：元の Kan 延長の単位を固定する。使われ方：cubical rigidification の単位。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite

/-- 元の cubical sets の Day 単位の underlying 前層。 -/
def cubicalDayUnit : CubicalSet.{u} := (𝟙_ CubicalDaySet.{u}).functor

/-- 元の Day 単位を生成する零次元 cell。 -/
def cubicalDayUnitCell : cubicalDayUnit.{u}.obj (op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) :=
  DayFunctor.ν _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u) PUnit.unit

/-- 元の Day 単位から零次元の表現可能立方体への比較。 -/
def cubicalDayUnitProjection : cubicalDayUnit.{u} ⟶ cubicalYoneda.{u}.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) :=
  (DayFunctor.unitDesc (F := DayFunctor.mk (cubicalYoneda.{u}.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)))
    (TypeCat.ofHom fun _ => ULift.up (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)))).natTrans

/-- 元の Day 単位比較は、同じ零次元の恒等 cell を回収する。 -/
lemma cubicalDayUnitProjection_cell :
    cubicalDayUnitProjection.{u}.app (op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) cubicalDayUnitCell =
      ULift.up (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) :=
  congrArg (fun t => t PUnit.unit)
    (DayFunctor.ν_comp_unitDesc
      (F := DayFunctor.mk (cubicalYoneda.{u}.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)))
      (TypeCat.ofHom fun _ => ULift.up (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0))))

/-- 元の Day 単位への零次元 cell の Yoneda 射。 -/
def cubicalDayUnitInclusion : cubicalYoneda.{u}.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) ⟶ cubicalDayUnit.{u} :=
  cubicalCell (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell

/-- 元の零次元生成 cell の像は Day 単位からの射を決定する。 -/
lemma cubicalDayUnit_hom_ext {M : CubicalSet.{u}} {f g : cubicalDayUnit ⟶ M}
    (h : f.app (op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) cubicalDayUnitCell =
      g.app (op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) cubicalDayUnitCell) : f = g := by
  have hh : (show 𝟙_ CubicalDaySet.{u} ⟶ DayFunctor.mk M from .mk f) =
      (show 𝟙_ CubicalDaySet.{u} ⟶ DayFunctor.mk M from .mk g) := by
    apply DayFunctor.unit_hom_ext
    apply ConcreteCategory.hom_ext
    intro t
    cases t
    exact h
  exact congrArg DayFunctor.Hom.natTrans hh

/-- 零次元立方体側の単位比較の逆律。 -/
lemma cubicalDayUnitInclusion_projection :
    cubicalDayUnitInclusion.{u} ≫ cubicalDayUnitProjection =
      𝟙 (cubicalYoneda.{u}.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) := by
  apply uliftYonedaEquiv.injective
  erw [uliftYonedaEquiv_comp]
  change cubicalDayUnitProjection.app (op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0))
    (uliftYonedaEquiv (uliftYonedaEquiv.symm cubicalDayUnitCell)) = _
  rw [Equiv.apply_symm_apply, cubicalDayUnitProjection_cell]
  rfl

/-- 元の Day 単位側でも零次元比較の逆律が成り立つ。 -/
lemma cubicalDayUnitProjection_inclusion :
    cubicalDayUnitProjection.{u} ≫ cubicalDayUnitInclusion = 𝟙 cubicalDayUnit := by
  apply cubicalDayUnit_hom_ext
  change cubicalDayUnitInclusion.app (op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0))
    (cubicalDayUnitProjection.app (op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) cubicalDayUnitCell) = _
  rw [cubicalDayUnitProjection_cell]
  change cubicalDayUnit.map (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)).op cubicalDayUnitCell = cubicalDayUnitCell
  simp

/-- 元の cubical Day 単位は零次元の表現可能立方体と同型。 -/
def cubicalDayUnitIso : cubicalDayUnit.{u} ≅ cubicalYoneda.{u}.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) where
  hom := cubicalDayUnitProjection
  inv := cubicalDayUnitInclusion
  hom_inv_id := cubicalDayUnitProjection_inclusion
  inv_hom_id := cubicalDayUnitInclusion_projection

end SerrePositivity.KST.SConstruction
