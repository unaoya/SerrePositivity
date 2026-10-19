module

public import SerrePositivity.KST.Spectra.CoherentPathParameters

/-!
概要：三単体の path 正方形の二つの零座標の辺を、元の二単体の path 区間へ同定する。
方針：内点一または二を欠く path は、その面の path の添字写像による像である。
規約：元の内点と面の番号を保持。使われ方：円評価の三単体の二つの面の Hom 内の式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 内点一を欠く path は、一番目の面の元の path を写したもの。 -/
lemma flaggedPath_skipFirst (b : Fin 2) :
    (SimplicialThickening.functorMap
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap
        ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩).obj
          (flaggedPath.{u} (fun _ : Fin 1 ↦ b)) = flaggedPath (twoFlags 0 b) := by
  fin_cases b <;> apply SimplicialThickening.Path.ext <;> ext k
  all_goals
    rcases k with ⟨k⟩
    fin_cases k <;> simp only [flaggedPath, twoFlags, Set.mem_ofPred_eq, Set.mem_image,
      ULift.exists, Fin.exists_fin_succ, Fin.exists_fin_zero] <;> decide

/-- 内点二を欠く path は、二番目の面の元の path を写したもの。 -/
lemma flaggedPath_skipSecond (a : Fin 2) :
    (SimplicialThickening.functorMap
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap
        ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩).obj
          (flaggedPath.{u} (fun _ : Fin 1 ↦ a)) = flaggedPath (twoFlags a 0) := by
  fin_cases a <;> apply SimplicialThickening.Path.ext <;> ext k
  all_goals
    rcases k with ⟨k⟩
    fin_cases k <;> simp only [flaggedPath, twoFlags, Set.mem_ofPred_eq, Set.mem_image,
      ULift.exists, Fin.exists_fin_succ, Fin.exists_fin_zero] <;> decide

/-- 正方形の第一座標零の辺は、一番目の面の元の path 区間を写した射。 -/
lemma tetrahedronPathSquare_skipFirst :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        tetrahedronPathSquare =
      trianglePathInterval ≫ nerveMap (SimplicialThickening.functorMap
        (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap
          ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · exact (flaggedPath_skipFirst (a i)).symm
  · intro i j f
    exact Subsingleton.elim _ _

/-- 正方形の第二座標零の辺は、二番目の面の元の path 区間を写した射。 -/
lemma tetrahedronPathSquare_skipSecond :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        tetrahedronPathSquare =
      trianglePathInterval ≫ nerveMap (SimplicialThickening.functorMap
        (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap
          ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · exact (flaggedPath_skipSecond (a i)).symm
  · intro i j f
    exact Subsingleton.elim _ _

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
