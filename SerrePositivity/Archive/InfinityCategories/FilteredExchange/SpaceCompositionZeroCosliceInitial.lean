module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionTetrahedronZeroCylinder
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionPrefixInitial
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceSourceIdentity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex

/-!
概要：零面の元の実 coslice 円柱は同じ始点の恒等 coslice 点を固定する。
方針：prefix 円柱の初点の定値 cone の座標を元の恒等 coslice 点に同定する。
規約：全時刻で同じ実始点を保持する。
使われ方：全 pointed 族の始点固定延長空間への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の零面の coslice 円柱は同じ恒等始点に全時刻で固定される。 -/
lemma spaceCompositionZeroCosliceHomotopy_initial (s : SpaceInfinity.{u} _⦋2⦌) :
    (scaffoldFirstVertex 2 ▷ Δ[1]) ≫ (spaceCompositionTetrahedronZeroCosliceHomotopy s).h =
      fst Δ[0] Δ[1] ≫ cosliceIdentityPoint (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  apply spaceCosliceSourceSimplex_injective (s.obj ⟨ULift.up 0⟩) d.unop.len
  have hi := congrArg Subtype.val (cosliceInitialCoordinates_identity
    (s.obj ⟨ULift.up 0⟩) a)
  exact (spacePrefixConeCosliceSimplex_coordinates (coherentCompositionTetrahedron s)
    (OrderHom.const _ 0) t.down.toOrderHom).trans
      ((coherentCompositionPrefix_initial s t.down.toOrderHom).trans hi.symm)

end SerrePositivity.InfinityCategories.F2
