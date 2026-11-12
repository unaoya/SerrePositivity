module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.InitialReverseThickeningCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionReindex

/-!
概要：実反転合成単体の初点 Hom を、同じ反転 path 上の元の Hom に揃える。
方針：元の端点移送式と実 thickening の反転座標の一致を合成する。
規約：二係数・全 path を保持。使われ方：固定射 prism の初点 Hom の直接比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable {X Y Z A B : C} {n : ℕ}

/-- 元の反転合成単体の初点 Hom の表示変更は、同じ全反転 path による前合成。 -/
lemma coherentReverseComposition_initial_transport
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (j : Fin (n + 1))
    (hA : coherentCompositionObj X Y Z t j.rev.castSucc = A)
    (hB : coherentCompositionObj X Y Z t (Fin.last (n + 1)) = B) :
    ((coherentReverseThickening (n + 1)).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
      coherentCompositionHom σ τ t j.succ.rev (Fin.rev 0)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          ((congrArg (coherentCompositionObj X Y Z t) (Fin.rev_succ j)).trans hA)
          ((congrArg (coherentCompositionObj X Y Z t) (Fin.rev_zero (n + 1))).trans hB)) =
    nerveMap (reflectedFirstPathFunctor j) ≫
      coherentCompositionHom σ τ t j.rev.castSucc (Fin.last (n + 1)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) := by
  rw [Category.assoc, coherentCompositionHom_transport σ τ t
    (Fin.rev_succ j) (Fin.rev_zero (n + 1)) hA hB]
  rw [← Category.assoc, ← Category.assoc, coherentReverseThickening_initial_map]
  exact Category.assoc _ _ _

/-- 一ラベルの初点 Hom は、元の第二係数の同じ最大座標による評価。 -/
lemma coherentReverseComposition_initial_one
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (j : Fin (n + 1)) (hj : t j.rev ≠ 0) :
    nerveMap (reflectedFirstPathFunctor j) ≫
      (coherentCompositionHom σ τ t j.rev.castSucc (Fin.last (n + 1)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentCompositionObj_one X Y Z t j.rev hj)
          (coherentCompositionObj_last X Y Z n t))) =
    nerveMap (reflectedFirstPathFunctor j) ≫ pathLastMaximumMap j.rev ≫
      SSet.yonedaEquiv.symm τ := by
  rw [coherentCompositionHom_one_last σ τ t j.rev hj]

/-- 零ラベルの初点 Hom では、固定した第一係数と元の第二係数をそのまま合成する。 -/
lemma coherentReverseComposition_initial_zero_constant
    (σ : (SimplicialCategory.sHom X Y) _⦋0⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (j : Fin (n + 1)) (hj : t j.rev = 0) :
    nerveMap (reflectedFirstPathFunctor j) ≫
      (coherentCompositionHom (PinchedHom.constant σ n) τ t j.rev.castSucc
        (Fin.last (n + 1)) ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentCompositionObj_zero X Y Z t j.rev hj)
          (coherentCompositionObj_last X Y Z n t))) =
    lift (SSet.const σ)
      (nerveMap (reflectedFirstPathFunctor j) ≫ pathLastMaximumMap j.rev ≫
        SSet.yonedaEquiv.symm τ) ≫ eComp SSet X Y Z := by
  have hc : SSet.yonedaEquiv.symm (PinchedHom.constant σ n) =
      (SSet.const σ : (Δ[n] : SSet.{u}) ⟶ _) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [coherentCompositionHom_zero_last (PinchedHom.constant σ n) τ t j.rev hj, hc]
  simp only [← Category.assoc, comp_lift, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2
