module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyInitial
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex

/-!
概要：全 pointed 族の同じ始点を、相対延長空間の境界の形に正規化する。
方針：最初の頂点との積を、同じ初点の lift の前合成で表示する。
規約：全係数と始点写像を保持。使われ方：全三角形の始点固定の比較空間。
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

/-- 初点包含との積は、同じ始点への lift を係数射影で前合成した射。 -/
lemma scaffoldFirstVertex_tensor_lift (n : ℕ) (A : SSet.{u}) :
    scaffoldFirstVertex n ▷ A = snd Δ[0] A ≫
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))) (𝟙 A) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [whiskerRight_fst, Category.assoc, lift_fst, scaffoldFirstVertex,
      SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]
  · rw [whiskerRight_snd, Category.assoc, lift_snd, Category.comp_id]

/-- 同じ初点包含で制限しても、全係数に対する元の標準 fiber 比較を保持する。 -/
lemma spaceSimplexPointedFamily_firstVertex {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌) :
    (scaffoldFirstVertex n ▷ _) ≫ spaceSimplexPointedFamily s =
      snd Δ[0] _ ≫ pointedCoherentFiberComparison (s.obj ⟨ULift.up 0⟩) ≫
        vertexFiberι pointedSpaceProjection (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) := by
  rw [scaffoldFirstVertex_tensor_lift, Category.assoc, spaceSimplexPointedFamily_initial]

/-- 指定した全初点族は、同じ元の全 Space 図式の初点制限を被覆する。 -/
lemma spaceSimplexPointedFamily_boundary {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌) :
    (snd Δ[0] _ ≫ pointedCoherentFiberComparison (s.obj ⟨ULift.up 0⟩) ≫
      vertexFiberι pointedSpaceProjection (coherentNerveVertex (s.obj ⟨ULift.up 0⟩))) ≫
        pointedSpaceProjection =
      (scaffoldFirstVertex n ▷ _) ≫
        (fst Δ[n] ((SSet.uliftFunctor.{u + 1, u}).obj
          (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op) ≫
            SSet.yonedaEquiv.symm s) := by
  rw [← spaceSimplexPointedFamily_firstVertex, Category.assoc,
    spaceSimplexPointedFamily_projection]

end SerrePositivity.InfinityCategories.F2
