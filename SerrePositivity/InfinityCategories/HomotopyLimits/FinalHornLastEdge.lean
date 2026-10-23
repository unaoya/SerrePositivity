module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornUnknownHom
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv
public import SerrePositivity.InfinityCategories.Coherent.FaceCellCompatibility

/-!
# 最終区間の回収射と元の固定最終辺

概要：実際の固定最終辺と回収射を照合し、元の相対ホーンへ Hom 持ち上げを適用する。
方針：既知面の自然性・通常の射の抽出・区間の単調性を使う。
規約：ambient の全対象に Hom 条件を仮定せず、元の下段始域について証明する。
使われ方：HTT 5.2.4.6 の Cartesian な持ち上げの構成。豊穣単体の復元は別途必要。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open CategoryTheory.SimplicialThickening
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (τ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 元の最終外側ホーンの固定最終辺が表す単調写像。 -/
def finalHornLastSimplex (n : ℕ) : ⦋1⦌ ⟶ ⦋n + 2⦌ :=
  (finalHornEdge.{0} n).1.down

/-- 固定最終辺の始点は元の penultimate 頂点である。 -/
lemma finalHornLastSimplex_zero (n : ℕ) :
    (finalHornLastSimplex n).toOrderHom 0 = finalHornPenultimate n := rfl

/-- 固定最終辺の終点は元の最終頂点である。 -/
lemma finalHornLastSimplex_one (n : ℕ) :
    (finalHornLastSimplex n).toOrderHom 1 = Fin.last (n + 2) := rfl

/-- 固定最終辺は、既知の零面の中に含まれる。 -/
lemma finalHornLastSimplex_avoids_zero (n : ℕ) (a : Fin 2) :
    (finalHornLastSimplex n).toOrderHom a ≠ 0 := by
  fin_cases a
  · exact ne_of_gt (finalHornPenultimate_pos n)
  · exact ne_of_gt ((finalHornPenultimate_pos n).trans (finalHornPenultimate_lt_last n))

/-- 零面内で回収した最終一単体は元の固定最終辺に一致する。 -/
lemma finalHornLastCell_eq (n : ℕ) :
    hornCell.{u} (Fin.last (n + 2)) (finalHornLastSimplex n) 0
      (ne_of_lt ((finalHornPenultimate_pos n).trans (finalHornPenultimate_lt_last n)))
      (finalHornLastSimplex_avoids_zero n) = finalHornEdge n := Subtype.ext rfl

/-- 最終既知区間 Hom を固定最終辺へ制限すると、元の同じ辺の Hom に一致する。 -/
lemma finalHornLastHom_on_edge :
    (SimplicialThickening.functor (finalHornLastSimplex n).toOrderHom.uliftMap).map
      ⟨ULift.up.{u} (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩ ≫
      finalHornKnownIntervalHom τ (finalHornPenultimate n) (Fin.last (n + 2))
        (le_of_lt (finalHornPenultimate_lt_last n))
        (Or.inl (ne_of_gt (finalHornPenultimate_pos n))) =
      hornHomOnCell τ (finalHornEdge n) 0 1 := by
  rw [finalHornKnownIntervalHom_eq_viaFace τ (finalHornPenultimate n)
    (Fin.last (n + 2)) (le_of_lt (finalHornPenultimate_lt_last n))
    (Or.inl (ne_of_gt (finalHornPenultimate_pos n))) 0
    (ne_of_lt ((finalHornPenultimate_pos n).trans (finalHornPenultimate_lt_last n)))
    (Or.inl (finalHornPenultimate_pos n))]
  have h := hornHomViaFace_on_cell τ (finalHornLastSimplex n) 0
    (ne_of_lt ((finalHornPenultimate_pos n).trans (finalHornPenultimate_lt_last n)))
    (finalHornLastSimplex_avoids_zero n) 0 1
  exact h

/-- 最終区間から回収した通常の射は、元の固定最終辺の同じ Hom 零単体を持つ。 -/
lemma finalHornLastArrow_homEquiv :
    SimplicialCategory.homEquiv' (hornObj τ (finalHornPenultimate n))
      (hornObj τ (Fin.last (n + 2))) (finalHornLastArrow τ) =
    (hornHomOnCell τ (finalHornEdge n) 0 1).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentOnePath) := by
  change (SSet.unitHomEquiv _) (eHomEquiv SSet (finalHornLastArrow τ)) = _
  rw [finalHornLastArrow_eHom]
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ coherentOnePath)) (finalHornLastHom_on_edge τ)
  have hp : (finalHornLastPathIso.{u} n).hom.app (Opposite.op ⦋0⦌) PUnit.unit =
      ((SimplicialThickening.functor (finalHornLastSimplex n).toOrderHom.uliftMap).map
        ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ coherentOnePath) := by
    exact CategoryTheory.Functor.ext (fun _ ↦ finalHornLastPath_eq n _ _)
  exact (congrArg (fun F ↦ (finalHornKnownIntervalHom τ (finalHornPenultimate n)
    (Fin.last (n + 2)) (le_of_lt (finalHornPenultimate_lt_last n))
    (Or.inl (ne_of_gt (finalHornPenultimate_pos n)))).app (Opposite.op ⦋0⦌) F) hp).trans h

/-- 最終区間の回収射は、共通対象上の固定最終辺から抽出した通常の射に一致する。 -/
lemma finalHornLastArrow_eq_extraction :
    finalHornLastArrow τ =
      (coherentNerveArrowData (hornFunctorOnCell τ (finalHornEdge n))).2.2 := by
  apply (SimplicialCategory.homEquiv' (hornObj τ (finalHornPenultimate n))
    (hornObj τ (Fin.last (n + 2)))).injective
  rw [finalHornLastArrow_homEquiv]
  exact ((SimplicialCategory.homEquiv' _ _).apply_symm_apply _).symm

/-- 対象を点ごとの等しい対象へ移した豊穣関手は、元の関手に等しい。 -/
lemma reobjectFunctor_eq_original {D : Type w} [EnrichedCategory SSet.{u} D]
    (F : EnrichedFunctor SSet D C) (g : D → C) (h : ∀ x, F.obj x = g x) :
    reobjectFunctor F g h = F := by
  have hg : g = F.obj := (funext h).symm
  subst g
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro x y
  simp only [reobjectFunctor, eqToHom_refl, Category.comp_id]

/-- 回収した最終区間の射が定める coherent な辺は、元のホーンの固定最終辺の像である。 -/
lemma finalHornLastArrow_edge :
    (coherentNerveEdge (finalHornLastArrow τ)).edge =
      τ.app (Opposite.op ⦋1⦌) (finalHornEdge n) := by
  rw [coherentNerveEdge_edge]
  have hrec := coherentNerveArrowData_reconstruct (hornFunctorOnCell τ (finalHornEdge n))
  rw [← finalHornLastArrow_eq_extraction τ] at hrec
  exact hrec.trans (reobjectFunctor_eq_original _ _ _)

/-- 固定最終辺の指定は、回収射の両端点と通常の射を含むデータの等式を与える。 -/
lemma finalHornLastArrow_data_of_fixedEdge {X Y : C} (f : X ⟶ Y)
    (h : τ.app (Opposite.op ⦋1⦌) (finalHornEdge n) = (coherentNerveEdge f).edge) :
    (⟨hornObj τ (finalHornPenultimate n), hornObj τ (Fin.last (n + 2)),
      finalHornLastArrow τ⟩ : Σ A B : C, A ⟶ B) = ⟨X, Y, f⟩ := by
  have hd := congrArg coherentNerveArrowData ((finalHornLastArrow_edge τ).trans h)
  simpa only [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow] using hd

/-- 指定した元の辺の後合成の trivial Kan 性を、同じ回収射へ移す。 -/
lemma finalHornLastArrow_postcomposition_trivialKanFibration_of_fixedEdge
    {X Y : C} (f : X ⟶ Y)
    (h : τ.app (Opposite.op ⦋1⦌) (finalHornEdge n) = (coherentNerveEdge f).edge)
    (A : C) [TrivialKanFibration (eHomWhiskerLeft SSet A f)] :
    TrivialKanFibration (eHomWhiskerLeft SSet A (finalHornLastArrow τ)) := by
  let P (d : Σ U V : C, U ⟶ V) : Prop :=
    TrivialKanFibration (eHomWhiskerLeft SSet A d.2.2)
  change P ⟨_, _, finalHornLastArrow τ⟩
  rw [finalHornLastArrow_data_of_fixedEdge τ f h]
  exact inferInstanceAs (TrivialKanFibration (eHomWhiskerLeft SSet A f))

/-- 元の指定最終辺の後合成の trivial Kan 性から、二つの未知 Hom を構成する。 -/
lemma finalHornUnknownHom_extension_of_fixedEdge {X Y : C} (f : X ⟶ Y)
    (h : τ.app (Opposite.op ⦋1⦌) (finalHornEdge n) = (coherentNerveEdge f).edge)
    [KanComplex (SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (Fin.last (n + 2))))]
    [TrivialKanFibration (eHomWhiskerLeft SSet (hornObj τ 0) f)] :
    ∃ g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (Fin.last (n + 2))),
      (∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
        (pathAvoids (ULift.up j)).ι ≫ g = hornInnerZeroHom τ j (ne_of_lt hjn) hj0 hjn) ∧
      (∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n),
        (pathThrough (ULift.up b)).ι ≫ g = finalHornUpperCompositionHom τ b hb0 hbp) ∧
      ∃ f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
        (ULift.up (finalHornPenultimate n))) ⟶
          SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (finalHornPenultimate n)),
        (∀ j, (pathCubeBoundaryFace j).ι ≫ f = finalHornFrontBoundaryFaceHom τ j) ∧
        f ≫ eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ) =
          finalHornAppend n ≫ g := by
  have := finalHornLastArrow_postcomposition_trivialKanFibration_of_fixedEdge
    τ f h (hornObj τ 0)
  exact finalHornUnknownHom_extension τ

end
end SerrePositivity.InfinityCategories.HomotopyLimits
