module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomReindex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPost
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPostNormalized
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionPostCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ThickeningSelfHomComparison

/-!
概要：元の全 Hom の右比較単体は、同じ固定射の後合成と全 Hom ごと整合する。
方針：旧 Hom の恒等性と最後への元の最大座標を照合する。
規約：元の全 Hom 単体を保持。使われ方：元の右 Hom fiber 比較の終域自然性。
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
  {X Y Z : C} {n : ℕ} (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (g : Y ⟶ Z)
local notation "σg" => NatTrans.app (eHomWhiskerLeft SSet X g) (Opposite.op ⦋n⦌) σ
local notation "s" => coherentHomComparisonSimplex σ
local notation "g'" => eqToHom (coherentHomComparisonObj_last X Y n) ≫ g
local notation "L" => coherentSimplexLastPost s g'
local notation "R" => coherentHomComparisonSimplex σg

/-- 元の右 Hom 比較単体の指定後合成は、同じ標準全対象を持つ。 -/
lemma coherentHomLastPost_obj (i : Fin (n + 2)) :
    (L).obj ⟨ULift.up i⟩ = (R).obj ⟨ULift.up i⟩ := by
  induction i using Fin.lastCases <;>
    simp only [coherentSimplexLastPost, coherentSimplexLastPostObj,
      coherentHomComparisonSimplex, coherentHomComparisonObj,
      Fin.lastCases_last, Fin.lastCases_castSucc]

/-- 元の右 Hom 比較単体の後合成は、元の Hom の後合成を全 Hom ごと厳密に保持する。 -/
lemma coherentHomComparisonSimplex_last_post : L = R := by
  apply EnrichedFunctor.ext SSet (fun i => coherentHomLastPost_obj σ g i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change coherentSimplexLastPostHom s g' i j ≫ eqToHom _ = coherentHomComparisonHom σg i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    exact thickeningSelfHom_comparison L R ⟨ULift.up (Fin.last (n + 1))⟩
      (coherentHomLastPost_obj σ g (Fin.last (n + 1)))
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hp := Path.le (P.obj 0)
    change n + 1 ≤ j.val at hp
    have hj : j.val < n + 1 := j.isLt
    omega
  case cast.cast i j =>
    apply simplicialHom_eq_of_normalized
      (coherentHomLastPost_obj σ g i.castSucc) (coherentHomLastPost_obj σ g j.castSucc)
      (coherentHomComparisonObj_cast X Z i) (coherentHomComparisonObj_cast X Z j) _ _
    have e := coherentSimplexLastPostHom_cast_cast_normalized s g' i j
      (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_cast X Y j)
    erw [coherentHomComparisonHom_cast_cast σ i j] at e
    exact e.trans (coherentHomComparisonHom_cast_cast σg i j).symm
  case cast.last i =>
    apply simplicialHom_eq_of_normalized
      (coherentHomLastPost_obj σ g i.castSucc) (coherentHomLastPost_obj σ g (Fin.last (n + 1)))
      (coherentHomComparisonObj_cast X Z i) (coherentHomComparisonObj_last X Z n) _ _
    have e := coherentSimplexLastPostHom_cast_last_normalized s i
      (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_last X Y n) g
    erw [coherentHomComparisonHom_cast_last σ i] at e
    have r := coherentHomComparisonHom_cast_last σg i
    rw [simplicialHom_yoneda_post σ g, ← Category.assoc] at r
    exact e.trans r.symm

end SerrePositivity.InfinityCategories.F2
