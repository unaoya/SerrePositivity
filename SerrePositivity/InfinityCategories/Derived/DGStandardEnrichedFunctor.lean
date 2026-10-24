module
public import SerrePositivity.InfinityCategories.Derived.DGStandardSimplexMap
public import SerrePositivity.InfinityCategories.DoldKanComparison.SimplicialCategory
/-!
概要：dg 関手の標準 DK Hom への作用を単体的豊穣関手へ束ねる。
方針：係数写像の面・退化、単位、AW 合成の保存を使う。
規約：Small 仮定なしで対象と全係数をそのまま写す。
使われ方：coherent 合成 prism の二入力自然性の上流入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve DGNerve.PinchedHom DoldKanComparison
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

lemma dgStandardSimplexMap_val {x y : D} {x' y' : E}
    (φ : homObject A D x y ⟶ homObject A E x' y') {n : ℕ}
    (s : StandardSimplex A x y n) :
    (dgStandardSimplexMap φ s).val = pinchedLinearDataMap φ s.val := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  exact dgStandardSimplexMap_component φ s J k hJ hk

lemma dgStandardSimplexMap_pullback {x y : D} {x' y' : E}
    (φ : homObject A D x y ⟶ homObject A E x' y') {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : StandardSimplex A x y n) :
    dgStandardSimplexMap φ (standardPullback α s) =
      standardPullback α (dgStandardSimplexMap φ s) := by
  apply Subtype.ext
  rw [dgStandardSimplexMap_val, standardPullback_val, standardPullback_val,
    dgStandardSimplexMap_val, pinchedLinearDataMap_pullback]

def dgStandardHomMap {x y : D} {x' y' : E}
    (φ : homObject A D x y ⟶ homObject A E x' y') :
    standardHomSpace (R := A) x y ⟶ standardHomSpace (R := A) x' y' where
  app _ := ↾fun s => dgStandardSimplexMap φ s
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact dgStandardSimplexMap_pullback φ α.unop.toOrderHom s

lemma dgStandardSimplexMap_unit (Q : DGFunctor A D E) (x : D) (n : ℕ) :
    dgStandardSimplexMap (Q.map x x) (standardUnit (R := A) x n) =
      standardUnit (R := A) (Q.obj x) n := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (dgStandardSimplexMap (Q.map x x) (standardUnit x n)).val.component J k hJ hk = _
  rw [dgStandardSimplexMap_component]
  change (Q.map x x).f k ((standardConstant (unitElement A x) n).val.component J k hJ hk) =
    (standardConstant (unitElement A (Q.obj x)) n).val.component J k hJ hk
  by_cases hc : J.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hc
    have hk0 : k = 0 := by simpa using hk
    subst k
    rw [standardConstant_singleton, standardConstant_singleton]
    exact DGFunctor.map_unitElement A Q x
  · have hc2 : 2 ≤ J.card := by
      change J.card ≠ 1 at hc
      have hp : 0 < J.card := Finset.card_pos.mpr hJ
      omega
    rw [standardConstant_component_zero _ J k hJ hk hc2,
      standardConstant_component_zero _ J k hJ hk hc2, map_zero]

def dgStandardEnrichedFunctor (Q : DGFunctor A D E) :
    EnrichedFunctor SSet (ClosedCategory A D) (ClosedCategory A E) where
  obj x := ForgetEnrichment.of (Complex A) (Q.obj x)
  map x y := dgStandardHomMap (Q.map x y)
  map_id x := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    exact dgStandardSimplexMap_unit Q x d.unop.len
  map_comp x y z := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    exact dgStandardSimplexMap_aw Q g f
end SerrePositivity.InfinityCategories
