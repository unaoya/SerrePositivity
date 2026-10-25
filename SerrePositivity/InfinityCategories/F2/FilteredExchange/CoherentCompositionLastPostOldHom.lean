module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPost
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPostNormalized
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionPostCoordinates

/-!
概要：元の合成単体の終域後合成で、旧対象と最後を含まない全 Hom を照合する。
方針：元の切替ラベルの標準座標で、同じ三つの非空分岐を比較する。
規約：全 Hom 単体と同じラベルを保持。使われ方：元の合成 prism の終域自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {X Y Z W : C} {n : ℕ}
  (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
  (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (g : Z ⟶ W)
  (t : Fin (n + 1) →o Fin 2)
local notation "τg" => NatTrans.app (eHomWhiskerLeft SSet Y g) (Opposite.op ⦋n⦌) τ
local notation "s" => coherentCompositionSimplex σ τ t
local notation "g'" => eqToHom (coherentCompositionObj_last X Y Z n t) ≫ g
local notation "s'" => coherentSimplexLastPost s g'
local notation "r" => coherentCompositionSimplex σ τg t

/-- 元の合成単体の終域後合成は、最後の対象を除き同じ全対象を持つ。 -/
lemma coherentCompositionLastPost_obj (i : Fin (n + 2)) :
    (s').obj ⟨ULift.up i⟩ = (r).obj ⟨ULift.up i⟩ := by
  induction i using Fin.lastCases <;>
    simp only [coherentSimplexLastPost, coherentSimplexLastPostObj,
      coherentCompositionSimplex, coherentCompositionObj, Fin.lastCases_last,
      Fin.lastCases_castSucc]

/-- 最後を含まない元の全 Hom も、同じ第二射の後合成で値まで一致する。 -/
lemma coherentCompositionLastPost_old_hom (i j : Fin (n + 1)) :
    (s').map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionLastPost_obj σ τ g t i.castSucc)
        (coherentCompositionLastPost_obj σ τ g t j.castSucc)) =
      (r).map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ := by
  by_cases hi : t i = 0 <;> by_cases hj : t j = 0
  · apply simplicialHom_eq_of_normalized
      (coherentCompositionLastPost_obj σ τ g t i.castSucc)
      (coherentCompositionLastPost_obj σ τ g t j.castSucc)
      (coherentCompositionObj_zero X Y W t i hi)
      (coherentCompositionObj_zero X Y W t j hj) _ _
    have e := coherentSimplexLastPostHom_cast_cast_normalized s g' i j
      (coherentCompositionObj_zero X Y Z t i hi) (coherentCompositionObj_zero X Y Z t j hj)
    erw [coherentCompositionHom_zero_zero σ τ t i j hi hj] at e
    exact e.trans (coherentCompositionHom_zero_zero σ τg t i j hi hj).symm
  · apply simplicialHom_eq_of_normalized
      (coherentCompositionLastPost_obj σ τ g t i.castSucc)
      (coherentCompositionLastPost_obj σ τ g t j.castSucc)
      (coherentCompositionObj_zero X Y W t i hi)
      (coherentCompositionObj_one X Y W t j hj) _ _
    have e := coherentSimplexLastPostHom_cast_cast_normalized s g' i j
      (coherentCompositionObj_zero X Y Z t i hi) (coherentCompositionObj_one X Y Z t j hj)
    erw [coherentCompositionHom_zero_one σ τ t i j hi hj] at e
    exact e.trans (coherentCompositionHom_zero_one σ τg t i j hi hj).symm
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    exact False.elim (pathCut_backward_false t hi hj (P.obj 0))
  · apply simplicialHom_eq_of_normalized
      (coherentCompositionLastPost_obj σ τ g t i.castSucc)
      (coherentCompositionLastPost_obj σ τ g t j.castSucc)
      (coherentCompositionObj_one X Y W t i hi)
      (coherentCompositionObj_one X Y W t j hj) _ _
    have e := coherentSimplexLastPostHom_cast_cast_normalized s g' i j
      (coherentCompositionObj_one X Y Z t i hi) (coherentCompositionObj_one X Y Z t j hj)
    erw [coherentCompositionHom_one_one σ τ t i j hi hj] at e
    exact e.trans (coherentCompositionHom_one_one σ τg t i j hi hj).symm

end SerrePositivity.InfinityCategories.F2
