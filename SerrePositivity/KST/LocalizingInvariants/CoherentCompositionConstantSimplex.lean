module

public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionSimplex
public import SerrePositivity.InfinityCategories.F1.Coherent.Edges

/-!
概要：二つの定値豊穣射の合成二単体を、元の通常の合成三角形と同定する。
方針：三頂点と九つの豊穣 Hom の作用を比較し、定値な合成の式を使う。
規約：単体的圏の Kan 性は不要。使われ方：後合成 prism の端点三角形の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma coherentComposition_constant_simplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    coherentCompositionSimplex (PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 1)
      (PinchedHom.constant (SimplicialCategory.homEquiv' Y Z g) 1)
      (OrderHom.id : Fin 2 →o Fin 2) = (coherentNerveCompStruct f g).simplex := by
  change _ = enrichedFunctorOfOrderDiagram
    ((⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 3) →o Fin 3).toFunctor ⋙
      ComposableArrows.mk₂ f g)
  apply EnrichedFunctor.ext SSet
    (fun i ↦ by rcases i with ⟨⟨i⟩⟩; fin_cases i <;> rfl)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  fin_cases i <;> fin_cases j
  all_goals
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro P
  all_goals
    simp -implicitDefEqProofs +instances [coherentCompositionSimplex, coherentCompositionHom,
      coherentCompositionObj, enrichedFunctorOfOrderDiagram, PinchedHom.constant]
  all_goals
    dsimp [Fin.lastCases] at *
  all_goals
    dsimp [Fin.reverseInduction, Fin.reverseInduction.go, orderDiagramEnrichedHom] at *
  case «0».«0» =>
    change (eId SSet X).app (Opposite.op ⦋n⦌) PUnit.unit = _
    simpa only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
      using unitHom_app_constant (eId SSet X) n
  case «0».«1» =>
    exact PinchedHom.constant_pullback (SimplicialCategory.homEquiv' X Y f) _
  case «0».«2» =>
    change (eComp SSet X Y Z).app (Opposite.op ⦋n⦌)
      (((SimplicialCategory.sHom X Y).map _)
        (PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 1),
       ((SimplicialCategory.sHom Y Z).map _)
        (PinchedHom.constant (SimplicialCategory.homEquiv' Y Z g) 1)) = _
    rw [PinchedHom.constant_pullback, PinchedHom.constant_pullback]
    exact simplicialHom_constant_comp f g n
  case «1».«0» =>
    have h := SimplicialThickening.Path.le (P.obj 0)
    change (1 : Fin 3) ≤ 0 at h
    omega
  case «1».«1» =>
    change (eId SSet Y).app (Opposite.op ⦋n⦌) PUnit.unit = _
    simpa only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
      using unitHom_app_constant (eId SSet Y) n
  case «1».«2» =>
    exact PinchedHom.constant_pullback (SimplicialCategory.homEquiv' Y Z g) _
  case «2».«0» =>
    have h := SimplicialThickening.Path.le (P.obj 0)
    change (2 : Fin 3) ≤ 0 at h
    omega
  case «2».«1» =>
    have h := SimplicialThickening.Path.le (P.obj 0)
    change (2 : Fin 3) ≤ 1 at h
    omega
  case «2».«2» =>
    change (eId SSet Z).app (Opposite.op ⦋n⦌) PUnit.unit =
      PinchedHom.constant (SimplicialCategory.homEquiv' Z Z
        ((ComposableArrows.mk₂ f g).map (𝟙 (2 : Fin 3)))) n
    rw [CategoryTheory.Functor.map_id]
    change (eId SSet Z).app (Opposite.op ⦋n⦌) PUnit.unit =
      PinchedHom.constant (SimplicialCategory.homEquiv' Z Z (𝟙 Z)) n
    simpa only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
      using unitHom_app_constant (eId SSet Z) n

end SerrePositivity.KST.LocalizingInvariants
