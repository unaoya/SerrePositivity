module

public import SerrePositivity.InfinityCategories.F2.SpaceSimplexSourceCone
public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedLiftFaces

/-!
概要：元の初点からの coslice 単体の面を、元の全 Space 単体の面へ同定する。
方針：join 座標で全ての面を計算し、初点を残す面では退化の恒等式を使う。
規約：同じ初点と元の全 Hom を保持。使われ方：全 Hom 族の厳密な面制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の初点からの coslice の全ての面は、元の退化全単体の対応する面。 -/
lemma spaceSimplexSourceCone_face_coordinates {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌) (i : Fin (n + 2)) :
    coherentCosliceSourceSimplex (s.obj ⟨ULift.up 0⟩)
      ((sliceUnder (SSet.yonedaEquiv.symm
        (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))).δ i (spaceSimplexSourceCone s)) =
      SpaceInfinity.δ i.succ (coherentConeTailExtension s) := by
  exact (pointedSimplexCoordinates_face (spaceSimplexSourceCone s).val i).trans
    (congrArg (fun t => SpaceInfinity.δ i.succ t)
      (spaceSimplexSourceCone_coordinates s))

/-- 初点を残す面では、元の面の同じ初点 coslice を全単体として回収する。 -/
lemma spaceSimplexSourceCone_positive_face {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌) (i : Fin (n + 1)) :
    (sliceUnder (SSet.yonedaEquiv.symm
      (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))).δ i.succ (spaceSimplexSourceCone s) =
      spaceSimplexSourceCone (SpaceInfinity.δ i.succ s) := by
  apply Subtype.ext
  apply (cancel_epi (leftPointStdSimplexIso n).inv).mp
  apply SSet.yonedaEquiv.injective
  exact (spaceSimplexSourceCone_face_coordinates s i.succ).trans
    ((coherentConeTailExtension_positive_face s i).trans
      (spaceSimplexSourceCone_coordinates (SpaceInfinity.δ i.succ s)).symm)

/-- 同じ面の制限は、coslice に値を持つ実際の Yoneda 射でも厳密に可換。 -/
lemma spaceSimplexSourceCone_map_positive_face {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌) (i : Fin (n + 1)) :
    stdSimplex.δ i.succ ≫ SSet.yonedaEquiv.symm (spaceSimplexSourceCone s) =
      SSet.yonedaEquiv.symm (spaceSimplexSourceCone (SpaceInfinity.δ i.succ s)) :=
  (SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ i.succ)
    (spaceSimplexSourceCone s)).trans
      (congrArg SSet.yonedaEquiv.symm (spaceSimplexSourceCone_positive_face s i))

end SerrePositivity.InfinityCategories.F2
