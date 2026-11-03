module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPostReindexLastHom
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ThickeningSelfHomComparison

/-!
概要：coherent 単体の最後の指定後合成は、最後を固定する全添字制限に厳密に自然。
方針：旧 Hom・最後への Hom・自己 Hom を同じ対象表示で比較する。
規約：面・退化を同じ式で扱い、同型へ弱めない。使われ方：slice の終域後合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {m n : ℕ}
  (α : ⦋m⦌ ⟶ ⦋n⦌) (s : (SimplicialNerve C) _⦋n + 1⦌) {Y : C}
  (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y)
local notation "F" => SimplicialThickening.functor
  (OrderHom.uliftMap (SimplexCategory.Hom.toOrderHom (PinchedHom.extend α)))
local notation "p" => EnrichedFunctor.comp SSet F s
local notation "gp" => eqToHom (coherentSimplexLastReindex_last α s) ≫ g
local notation "L" => EnrichedFunctor.comp SSet F (coherentSimplexLastPost s g)
local notation "R" => coherentSimplexLastPost p gp

/-- 最後の指定後合成は、元の全添字写像への制限で全 Hom ごと値を保つ。 -/
lemma coherentSimplexLastPost_reindex :
    (SimplicialNerve C).map (PinchedHom.extend α).op (coherentSimplexLastPost s g) = R := by
  apply EnrichedFunctor.ext SSet (fun i => coherentSimplexLastPost_reindex_obj α s g i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    exact thickeningSelfHom_comparison L R ⟨ULift.up (Fin.last (m + 1))⟩
      (coherentSimplexLastPost_reindex_obj α s g (Fin.last (m + 1)))
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hp := Path.le (P.obj 0)
    change m + 1 ≤ j.val at hp
    have hj : j.val < m + 1 := j.isLt
    omega
  case cast.cast i j => exact coherentSimplexLastPost_reindex_old_hom α s g i j
  case cast.last i => exact coherentSimplexLastPost_reindex_last_hom α s g i

end SerrePositivity.InfinityCategories.F2
