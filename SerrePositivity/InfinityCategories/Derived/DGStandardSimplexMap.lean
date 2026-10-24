module
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearChainMap
public import SerrePositivity.InfinityCategories.DoldKanComparison.StandardComposition
public import SerrePositivity.InfinityCategories.DGNerve.FunctorMapping
/-!
概要：dg 関手と Hom 鎖写像の標準 DK 単体への作用を構成する。
方針：線形単体との符号同値を共役し、全成分で係数写像を計算する。
規約：対象の Small 性を仮定せず、元の全次数と二入力を保持する。
使われ方：coherent 合成 prism の dg 関手自然性の係数計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom DoldKanComparison
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

def dgStandardSimplexMap {x y : D} {x' y' : E}
    (φ : homObject A D x y ⟶ homObject A E x' y') {n : ℕ}
    (s : StandardSimplex A x y n) : StandardSimplex A x' y' n :=
  standardSimplexEquiv x' y' n
    (pinchedLinearSimplexMap φ ((standardSimplexEquiv x y n).symm s))

lemma dgStandardSimplexMap_component {x y : D} {x' y' : E}
    (φ : homObject A D x y ⟶ homObject A E x' y') {n : ℕ}
    (s : StandardSimplex A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (dgStandardSimplexMap φ s).val.component J k hJ hk =
      φ.f k (s.val.component J k hJ hk) := by
  change degreeSign (J.card - 1) •
    (φ.f k (degreeSign (J.card - 1) • s.val.component J k hJ hk)) = _
  rw [map_zsmul, degreeSign_smul_involutive]

lemma dgStandardSimplexMap_aw (Q : DGFunctor A D E) {x y z : D} {n : ℕ}
    (g : StandardSimplex A y z n) (f : StandardSimplex A x y n) :
    dgStandardSimplexMap (Q.map x z) (standardAW g f) =
      standardAW (dgStandardSimplexMap (Q.map y z) g)
        (dgStandardSimplexMap (Q.map x y) f) := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (dgStandardSimplexMap (Q.map x z) (standardAW g f)).val.component J k hJ hk = _
  rw [dgStandardSimplexMap_component]
  change (Q.map x z).f k ((awData g.val f.val).component J k hJ hk) =
    (awData (dgStandardSimplexMap (Q.map y z) g).val
      (dgStandardSimplexMap (Q.map x y) f).val).component J k hJ hk
  rw [awData_component, awData_component, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold awTerm
  rw [dgStandardSimplexMap_component, dgStandardSimplexMap_component]
  exact map_compose Q _ _ _
end SerrePositivity.InfinityCategories
