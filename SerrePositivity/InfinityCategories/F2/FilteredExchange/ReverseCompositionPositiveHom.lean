module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ReverseCompositionInitialHom

/-!
概要：実反転合成単体の正頂点間の Hom を、同じ二係数の標準表示へ移す。
方針：実際の反転射を保持したまま、二端点の添字移送を適用する。
規約：元の全 path を保持。使われ方：固定射の二つの実 prism の tail の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 同じ実反転単体の tail Hom は、二端点を揃えた元の合成 Hom に一致する。 -/
lemma coherentReverseComposition_positive_transport {X Y Z A B : Cᵒᵖ} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hA : coherentCompositionObj X Y Z t j.rev.castSucc = A)
    (hB : coherentCompositionObj X Y Z t i.rev.castSucc = B) :
    (coherentOppositeInverseSimplex (coherentCompositionSimplex σ τ t)).map
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg Opposite.unop
          ((congrArg (coherentCompositionObj X Y Z t) (Fin.rev_succ i)).trans hB))
        (congrArg Opposite.unop
          ((congrArg (coherentCompositionObj X Y Z t) (Fin.rev_succ j)).trans hA))) =
    (coherentReverseThickening (n + 1)).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
        (Fin.rev_succ j) (Fin.rev_succ i)) ≫
      coherentCompositionHom σ τ t j.rev.castSucc i.rev.castSucc ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) := by
  change (((coherentReverseThickening (n + 1)).map
    ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      coherentCompositionHom σ τ t j.succ.rev i.succ.rev) ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]
  change ((coherentReverseThickening (n + 1)).map
    ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      coherentCompositionHom σ τ t j.succ.rev i.succ.rev) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        ((congrArg (coherentCompositionObj X Y Z t) (Fin.rev_succ j)).trans hA)
        ((congrArg (coherentCompositionObj X Y Z t) (Fin.rev_succ i)).trans hB)) = _
  rw [Category.assoc, coherentCompositionHom_transport σ τ t
    (Fin.rev_succ j) (Fin.rev_succ i) hA hB]

/-- 元の正規化した Hom が定値なら、同じ実反転射での前合成は定値を保つ。 -/
lemma coherentReverseComposition_positive_const {X Y Z A B : Cᵒᵖ} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hA : coherentCompositionObj X Y Z t j.rev.castSucc = A)
    (hB : coherentCompositionObj X Y Z t i.rev.castSucc = B)
    (v : (SimplicialCategory.sHom A B) _⦋0⦌)
    (hv : coherentCompositionHom σ τ t j.rev.castSucc i.rev.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) = SSet.const v) :
    (coherentOppositeInverseSimplex (coherentCompositionSimplex σ τ t)).map
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg Opposite.unop
          ((congrArg (coherentCompositionObj X Y Z t) (Fin.rev_succ i)).trans hB))
        (congrArg Opposite.unop
          ((congrArg (coherentCompositionObj X Y Z t) (Fin.rev_succ j)).trans hA))) =
      SSet.const v := by
  refine (coherentReverseComposition_positive_transport σ τ t i j hA hB).trans ?_
  rw [hv, SSet.comp_const, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2
