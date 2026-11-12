module

public import SerrePositivity.KST.Spectra.CoherentTrianglePathMaximum

/-!
概要：二単体の長い Hom の path の nerve と標準区間は厳密に同型である。
方針：最大内点で元の path を復元し、既存の区間への逆の式と合わせる。
規約：元の path の包含方向を保持。使われ方：錐の二つの三角形の Hom 経路による照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 二単体の長い path は、その最大内点の二値フラグから厳密に復元できる。 -/
lemma trianglePath_maximum_recover
    (P : Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) :
    flaggedPath (fun _ : Fin 1 ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (i := (0 : Fin 2)) P) = P := by
  apply SimplicialThickening.Path.ext
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk | ⟨r, hr, ha⟩
    · have he : k = ULift.up (0 : Fin 3) := ULift.ext hk
      rw [he]
      exact P.left
    · have he : k = ULift.up (2 : Fin 3) := ULift.ext hk
      rw [he]
      exact P.right
    · fin_cases r
      have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mem (i := (0 : Fin 2)) P
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (i := (0 : Fin 2)) P = 1 at ha
      rw [ha] at hm
      have he : k = ULift.up (1 : Fin 3) := ULift.ext hr
      rw [he]
      exact hm
  · intro hk
    rcases k with ⟨k⟩
    fin_cases k
    · exact Or.inl rfl
    · refine Or.inr (Or.inr ⟨0, rfl, ?_⟩)
      apply le_antisymm (Fin.le_last _) ?_
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum (i := (0 : Fin 2)) P 1 hk
    · exact Or.inr (Or.inl rfl)

/-- 最大内点を取り元の区間の path を続けると、元の path の nerve の恒等射。 -/
lemma trianglePathInterval_maximum_reverse :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 2) ≫ trianglePathInterval.{u} =
      𝟙 (nerve (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2))) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · exact trianglePath_maximum_recover (P.obj i)
  · intro _ _ _
    exact Subsingleton.elim _ _

/-- 元の二値 path の区間と、元の長い Hom の nerve の厳密な同型。 -/
def trianglePathIntervalIso : (Δ[1] : SSet.{u}) ≅
    nerve (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) where
  hom := trianglePathInterval
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 2)
  hom_inv_id := trianglePathInterval_maximum
  inv_hom_id := trianglePathInterval_maximum_reverse

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
