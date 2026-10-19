module

public import SerrePositivity.KST.Spectra.CoherentPathParameters

/-!
概要：三単体の path 正方形の一座標の辺を、二つの部分 path の合成へ同定する。
方針：内点一または二を含む path は、その点で切った二つの path の和である。
規約：Mathlib の合成の向き。使われ方：元の三単体の Hom 正方形の残る二辺の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 指定した path の定値な包含列を持つ区間パラメーター。 -/
def constantPathParameter {n : ℕ} {i j : Fin n}
    (P : Path (ULift.up i : ULift.{u} (Fin n)) (ULift.up j)) :
    (Δ[1] : SSet.{u}) ⟶ nerve (Path (ULift.up i : ULift.{u} (Fin n)) (ULift.up j)) where
  app _ := ↾fun _ ↦ (CategoryTheory.Functor.const _).obj P
  naturality := by intros; rfl

/-- 三単体の最初の辺を表す、二端点だけの path。 -/
def tetrahedronInitialPath :
    Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 1) where
  I := {k | k.down = 0 ∨ k.down = 1}
  left := Or.inl rfl
  right := Or.inr rfl
  left_le k _ := Fin.zero_le k.down
  le_right k hk := by
    change k.down ≤ 1
    rcases hk with h | h
    · simpa only [h] using (by decide : (0 : Fin 4) ≤ 1)
    · exact le_of_eq h

/-- 三単体の最後の辺を表す、二端点だけの path。 -/
def tetrahedronFinalPath :
    Path (ULift.up (2 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) where
  I := {k | k.down = 2 ∨ k.down = 3}
  left := Or.inl rfl
  right := Or.inr rfl
  left_le k hk := by
    change 2 ≤ k.down
    rcases hk with h | h
    · exact le_of_eq h.symm
    · simpa only [h] using (by decide : (2 : Fin 4) ≤ 3)
  le_right k _ := Fin.le_last k.down

/-- 内点一を含む path は、最初の辺と零番目の面の path の合成。 -/
lemma flaggedPath_includeFirst (b : Fin 2) :
    (tetrahedronInitialPath.{u} :
      (⟨ULift.up (0 : Fin 4)⟩ : SimplicialThickening (ULift.{u} (Fin 4))) ⟶
        ⟨ULift.up 1⟩) ≫
      (SimplicialThickening.functorMap
        (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap
          ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩).obj
            (flaggedPath (fun _ : Fin 1 ↦ b)) = flaggedPath (twoFlags 1 b) := by
  fin_cases b <;> apply SimplicialThickening.Path.ext <;> ext k
  all_goals
    rcases k with ⟨k⟩
    fin_cases k <;> simp only [SimplicialThickening.comp_I, tetrahedronInitialPath,
      flaggedPath, twoFlags, Set.mem_union, Set.mem_ofPred_eq, Set.mem_image,
      ULift.exists, Fin.exists_fin_succ, Fin.exists_fin_zero] <;> decide

/-- 内点二を含む path は、三番目の面の path と最後の辺の合成。 -/
lemma flaggedPath_includeSecond (a : Fin 2) :
    (SimplicialThickening.functorMap
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap
        ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩).obj
          (flaggedPath.{u} (fun _ : Fin 1 ↦ a)) ≫
      (tetrahedronFinalPath :
        (⟨ULift.up (2 : Fin 4)⟩ : SimplicialThickening (ULift.{u} (Fin 4))) ⟶
          ⟨ULift.up 3⟩) = flaggedPath (twoFlags a 1) := by
  fin_cases a <;> apply SimplicialThickening.Path.ext <;> ext k
  all_goals
    rcases k with ⟨k⟩
    fin_cases k <;> simp only [SimplicialThickening.comp_I, tetrahedronFinalPath,
      flaggedPath, twoFlags, Set.mem_union, Set.mem_ofPred_eq, Set.mem_image,
      ULift.exists, Fin.exists_fin_succ, Fin.exists_fin_zero] <;> decide

/-- 第一座標一の辺は、最初の辺と零番目の面の path 区間の豊穣合成。 -/
lemma tetrahedronPathSquare_includeFirst :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        tetrahedronPathSquare =
      lift (constantPathParameter tetrahedronInitialPath)
        (trianglePathInterval ≫ nerveMap (SimplicialThickening.functorMap
          (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap
            ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩)) ≫
        eComp SSet (⟨ULift.up (0 : Fin 4)⟩ : SimplicialThickening (ULift.{u} (Fin 4)))
          ⟨ULift.up 1⟩ ⟨ULift.up 3⟩ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · exact (flaggedPath_includeFirst (a i)).symm
  · intro i j f
    exact Subsingleton.elim _ _

/-- 第二座標一の辺は、三番目の面の path 区間と最後の辺の豊穣合成。 -/
lemma tetrahedronPathSquare_includeSecond :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        tetrahedronPathSquare =
      lift (trianglePathInterval ≫ nerveMap (SimplicialThickening.functorMap
          (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap
            ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩))
        (constantPathParameter tetrahedronFinalPath) ≫
        eComp SSet (⟨ULift.up (0 : Fin 4)⟩ : SimplicialThickening (ULift.{u} (Fin 4)))
          ⟨ULift.up 2⟩ ⟨ULift.up 3⟩ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · exact (flaggedPath_includeSecond (a i)).symm
  · intro i j f
    exact Subsingleton.elim _ _

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
