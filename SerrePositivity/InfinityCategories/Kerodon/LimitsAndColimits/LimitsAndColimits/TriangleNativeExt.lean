module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.StrictFaceHomConstancy
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathDegeneracy

/-!
概要：二短辺と全 native 長 Hom で二単体を厳密に同定する。
方針：区間外の面の Hom 全射性で真部分区間を回収し、逆向きは空性を使う。
規約：quasicategory 性を仮定しない。使われ方：K-B の元の二単体の回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


private lemma triangleFaceHom_eq
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F G : (SimplicialNerve C) _⦋2⦌)
    (ho : ∀ x, F.obj x = G.obj x) (j : Fin 3)
    (h : (SimplicialNerve C).δ j F = (SimplicialNerve C).δ j G)
    (a b : Fin 2) (hout : j < j.succAbove a ∨ j.succAbove b < j) :
    F.map ⟨ULift.up (j.succAbove a)⟩ ⟨ULift.up (j.succAbove b)⟩ ≫
      eqToHom (by rw [ho, ho]) =
        G.map ⟨ULift.up (j.succAbove a)⟩ ⟨ULift.up (j.succAbove b)⟩ := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pathFaceMap_epi_of_outside.{u} j a b hout
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} j a b)).1
  rw [← Category.assoc]
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans ?_
  change HEq (((SimplicialNerve C).δ j F).map ⟨ULift.up a⟩ ⟨ULift.up b⟩)
    (((SimplicialNerve C).δ j G).map ⟨ULift.up a⟩ ⟨ULift.up b⟩)
  rw [h]

/-- 二短辺の厳密一致と全 native 長 Hom の異種等号は二単体そのものを同定する。 -/
theorem nativeTriangle_ext
    (C : Type v) [Category.{u} C] [SimplicialCategory C]
    (F G : (SimplicialNerve C) _⦋2⦌)
    (h₀ : (SimplicialNerve C).δ (0 : Fin 3) F = (SimplicialNerve C).δ (0 : Fin 3) G)
    (h₂ : (SimplicialNerve C).δ (2 : Fin 3) F = (SimplicialNerve C).δ (2 : Fin 3) G)
    (h₀₂ : HEq (F.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      (G.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)) : F = G := by
  have ho : ∀ x, F.obj x = G.obj x := by
    rintro ⟨⟨i⟩⟩
    fin_cases i
    · exact congrArg (fun T => T.obj ⟨ULift.up 0⟩) h₂
    · exact congrArg (fun T => T.obj ⟨ULift.up 0⟩) h₀
    · exact congrArg (fun T => T.obj ⟨ULift.up 1⟩) h₀
  refine EnrichedFunctor.ext SSet ho ?_
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change Fin 3 at i j
  by_cases hij : i ≤ j
  swap
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathEmpty_hom_ext (ULift.up i) (ULift.up j) hij _ _
  fin_cases i <;> fin_cases j
  all_goals first
    | exact triangleFaceHom_eq F G ho 2 h₂ 0 0 (by decide)
    | exact triangleFaceHom_eq F G ho 2 h₂ 0 1 (by decide)
    | exact triangleFaceHom_eq F G ho 0 h₀ 0 0 (by decide)
    | exact triangleFaceHom_eq F G ho 0 h₀ 0 1 (by decide)
    | exact triangleFaceHom_eq F G ho 0 h₀ 1 1 (by decide)
    | exact eq_of_heq ((comp_eqToHom_heq _ _).trans h₀₂)
    | norm_num at hij

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
