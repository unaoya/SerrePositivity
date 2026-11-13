module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentDiagramVertices

/-!
概要：元の HA 単体の間の閉零成分が、全ての高次成分と厳密に可換する型を与える。
方針：成分の閉零合成と Leibniz 則で恒等・合成を構成する。
規約：高次成分の自然性を通常の辺の自然性に置き換えない。
使われ方：3b-3 R6、元の指定余錐の全パラメーター族を組み立てる局所データ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (E : Type v) [DGCategory A E]

/-- 同じ次元の元の HA データの間で、閉零成分と全高次成分が可換する写像。 -/
structure StrictSimplexMap {n : ℕ} (s t : SimplexData A E n) where
  /-- 各頂点での同じ閉零成分。 -/
  app : ∀ i, zeroCycles (homObject A E (s.obj i) (t.obj i))
  /-- 全ての有限部分集合の HA 成分に対する厳密自然性。 -/
  naturality : ∀ I a b k hI ha hb hk,
    compose A (app b).val (s.hom I a b k hI ha hb hk) (add_zero k) =
      compose A (t.hom I a b k hI ha hb hk) (app a).val (zero_add k)

namespace StrictSimplexMap
variable {A E} {n : ℕ} {s t r w : SimplexData A E n}

/-- 全成分が一致する厳密 HA 写像は同じ。 -/
@[ext] lemma ext {η θ : StrictSimplexMap A E s t} (h : ∀ i, η.app i = θ.app i) : η = θ := by
  cases η with
  | mk f hf =>
    cases θ with
    | mk g hg =>
      have hfg : f = g := funext h
      cases hfg
      rfl

/-- 同じ HA 単体上の厳密な恒等写像。 -/
def id (s : SimplexData A E n) : StrictSimplexMap A E s s where
  app i := unitElement A (s.obj i)
  naturality I a b k hI ha hb hk :=
    (unit_compose A _).trans (compose_unit A _).symm

/-- 全高次成分と可換する二つの写像の、同じ閉零成分による合成。 -/
def comp (η : StrictSimplexMap A E s t) (θ : StrictSimplexMap A E t r) :
    StrictSimplexMap A E s r where
  app i := ⟨compose A (θ.app i).val (η.app i).val (zero_add 0), by
    change differential A (compose A (θ.app i).val (η.app i).val (zero_add 0)) = 0
    have hθ : differential A (θ.app i).val = 0 := (θ.app i).property
    have hη : differential A (η.app i).val = 0 := (η.app i).property
    rw [differential_compose]
    simp only [hθ, hη, zero_compose, compose_zero, smul_zero, zero_add]⟩
  naturality I a b k hI ha hb hk := by
    change compose A (compose A (θ.app b).val (η.app b).val (zero_add 0))
        (s.hom I a b k hI ha hb hk) (add_zero k) =
      compose A (r.hom I a b k hI ha hb hk)
        (compose A (θ.app a).val (η.app a).val (zero_add 0)) (zero_add k)
    calc
      _ = compose A (θ.app b).val
          (compose A (η.app b).val (s.hom I a b k hI ha hb hk) (add_zero k))
          (add_zero k) :=
        (NestedCut.compose_assoc_of_sum _ _ _ (add_zero k) (zero_add 0) (add_zero k)).symm
      _ = compose A (θ.app b).val
          (compose A (t.hom I a b k hI ha hb hk) (η.app a).val (zero_add k))
          (add_zero k) := by rw [η.naturality]
      _ = compose A (compose A (θ.app b).val (t.hom I a b k hI ha hb hk) (add_zero k))
          (η.app a).val (zero_add k) :=
        NestedCut.compose_assoc_of_sum _ _ _ (zero_add k) (add_zero k) (add_zero k)
      _ = compose A (compose A (r.hom I a b k hI ha hb hk) (θ.app a).val (zero_add k))
          (η.app a).val (zero_add k) := by rw [θ.naturality]
      _ = _ :=
        (NestedCut.compose_assoc_of_sum _ _ _ (zero_add 0) (zero_add k) (zero_add k)).symm

/-- 元の閉零成分の合成の左単位律。 -/
lemma id_comp (η : StrictSimplexMap A E s t) : (id s).comp η = η := by
  apply ext
  intro i
  apply Subtype.ext
  exact compose_unit A (η.app i).val

/-- 元の閉零成分の合成の右単位律。 -/
lemma comp_id (η : StrictSimplexMap A E s t) : η.comp (id t) = η := by
  apply ext
  intro i
  apply Subtype.ext
  exact unit_compose A (η.app i).val

/-- 元の閉零成分による合成の結合律。 -/
lemma comp_assoc (η : StrictSimplexMap A E s t) (θ : StrictSimplexMap A E t r)
    (κ : StrictSimplexMap A E r w) : (η.comp θ).comp κ = η.comp (θ.comp κ) := by
  apply ext
  intro i
  apply Subtype.ext
  exact NestedCut.compose_assoc_of_sum (η.app i).val (θ.app i).val (κ.app i).val
    (zero_add 0) (zero_add 0) (zero_add 0)

end StrictSimplexMap
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
