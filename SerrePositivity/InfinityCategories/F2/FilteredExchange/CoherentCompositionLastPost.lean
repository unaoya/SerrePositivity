module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionLastPostOldHom
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ThickeningSelfHomComparison

/-!
概要：元の合成単体の第二 Hom の後合成は、同じ単体の最後の対象の指定後合成と一致する。
方針：全対象・旧 Hom・最後への二座標を照合し、豊穣関手の外延性を使う。
規約：元の二つの全 Hom と切替ラベルを保持。使われ方：元の合成 prism の終域自然性。
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

/-- 元の合成単体は、第二 Hom の後合成と最後の対象の後合成で全 Hom ごと厳密に一致する。 -/
lemma coherentCompositionSimplex_last_post : s' = r := by
  apply EnrichedFunctor.ext SSet (fun i => coherentCompositionLastPost_obj σ τ g t i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change coherentSimplexLastPostHom s g' i j ≫ eqToHom _ = coherentCompositionHom σ τg t i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    exact thickeningSelfHom_comparison s' r ⟨ULift.up (Fin.last (n + 1))⟩
      (coherentCompositionLastPost_obj σ τ g t (Fin.last (n + 1)))
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hp := Path.le (P.obj 0)
    change n + 1 ≤ j.val at hp
    have hj : j.val < n + 1 := j.isLt
    omega
  case cast.cast i j => exact coherentCompositionLastPost_old_hom σ τ g t i j
  case cast.last i =>
    by_cases hi : t i = 0
    · apply simplicialHom_eq_of_normalized
        (coherentCompositionLastPost_obj σ τ g t i.castSucc)
        (coherentCompositionLastPost_obj σ τ g t (Fin.last (n + 1)))
        (coherentCompositionObj_zero X Y W t i hi) (coherentCompositionObj_last X Y W n t) _ _
      exact (coherentSimplexLastPostHom_cast_last_normalized s i
        (coherentCompositionObj_zero X Y Z t i hi) (coherentCompositionObj_last X Y Z n t) g).trans
          (coherentCompositionHom_zero_last_post σ τ g t i hi)
    · apply simplicialHom_eq_of_normalized
        (coherentCompositionLastPost_obj σ τ g t i.castSucc)
        (coherentCompositionLastPost_obj σ τ g t (Fin.last (n + 1)))
        (coherentCompositionObj_one X Y W t i hi) (coherentCompositionObj_last X Y W n t) _ _
      exact (coherentSimplexLastPostHom_cast_last_normalized s i
        (coherentCompositionObj_one X Y Z t i hi) (coherentCompositionObj_last X Y Z n t) g).trans
          (coherentCompositionHom_one_last_post σ τ g t i hi)

end SerrePositivity.InfinityCategories.F2
