module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGHomotopyFiniteCellGeneration

/-! # 有限 cell 条件の主導来局所化による反映

概要：全有限 cell の K(D) 内の像では、指定有限 cell 条件を主導来局所化から反映できる。
方針：指定有限 cell 表示との導来同型を、全有限 cell 上の完全忠実性で K(D) へ戻す。
規約：任意の加群での反映は主張しない。使われ方：有限 cell roof の分母条件の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定有限 cell の K(D) 内の像は、全有限 cell の像に含まれる。 -/
lemma dgHomotopyFiniteCell_subset_univ (S : Set D) :
    homotopyFiniteCellOver A D S ≤ homotopyFiniteCellOver A D Set.univ := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyFiniteCellOver_le_iff_generators A D
    (homotopyFiniteCellOver A D Set.univ) S).mpr
  intro x _
  exact (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToHomotopy A D)
    (moduleFiniteCell_representable A D x)

/-- 全有限 cell の範囲では、指定有限 cell 条件を導来圏で判定できる。 -/
theorem dgHomotopyFiniteCell_iff_derivedFiniteCell (S : Set D)
    (X : ModuleHomotopyCategory A D) (hX : homotopyFiniteCellOver A D Set.univ X) :
    homotopyFiniteCellOver A D S X ↔ derivedFiniteCellOver A D S
      ((moduleHomotopyToDerivedClosed A D).obj X) := by
  constructor
  · intro h
    exact homotopyFiniteCellToDerived_mem A D S ⟨X, h⟩
  · rintro ⟨M, hM, ⟨e⟩⟩
    have hMS := (moduleFiniteCellOver A D S).prop_map_obj (moduleToHomotopy A D) hM
    let a : HomotopyFiniteCellCategoryOver A D Set.univ := ⟨X, hX⟩
    let b : HomotopyFiniteCellCategoryOver A D Set.univ :=
      ⟨(moduleToHomotopy A D).obj M, dgHomotopyFiniteCell_subset_univ A D S _ hMS⟩
    let i := (homotopyFiniteCellToDerived A D Set.univ).preimageIso
      (X := b) (Y := a) ((moduleToHomotopyDerivedIso A D).app M ≪≫ e)
    exact (homotopyFiniteCellOver A D S).prop_of_iso
      ((homotopyFiniteCellOver A D Set.univ).ι.mapIso i) hMS

end SerrePositivity.InfinityCategories.Project.DerivedCategories
