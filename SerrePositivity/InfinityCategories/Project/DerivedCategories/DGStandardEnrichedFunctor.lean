module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardSimplexMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplicialCategory
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardEnrichedFunctor
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

lemma dgStandardSimplexMap_val {x y : D} {x' y' : E}
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y') {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap φ s).val = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap φ s.val := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap_component φ s J k hJ hk

lemma dgStandardSimplexMap_pullback {x y : D} {x' y' : E}
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y') {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap φ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap φ s) := by
  apply Subtype.ext
  rw [dgStandardSimplexMap_val, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val,
    dgStandardSimplexMap_val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_pullback]

def dgStandardHomMap {x y : D} {x' y' : E}
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) x' y' where
  app _ := ↾fun s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap φ s
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact dgStandardSimplexMap_pullback φ α.unop.toOrderHom s

lemma dgStandardSimplexMap_unit (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (x : D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap (Q.map x x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) x n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (Q.obj x) n := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap (Q.map x x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit x n)).val.component J k hJ hk = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap_component]
  change (Q.map x x).f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (_root_.SerrePositivity.DifferentialGraded.unitElement A x) n).val.component J k hJ hk) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (_root_.SerrePositivity.DifferentialGraded.unitElement A (Q.obj x)) n).val.component J k hJ hk
  by_cases hc : J.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hc
    have hk0 : k = 0 := by simpa using hk
    subst k
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_singleton, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_singleton]
    exact _root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement A Q x
  · have hc2 : 2 ≤ J.card := by
      change J.card ≠ 1 at hc
      have hp : 0 < J.card := Finset.card_pos.mpr hJ
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_component_zero _ J k hJ hk hc2,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_component_zero _ J k hJ hk hc2, map_zero]

def dgStandardEnrichedFunctor (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) :
    EnrichedFunctor SSet (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D) (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A E) where
  obj x := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (Q.obj x)
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
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap_aw Q g f
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardEnrichedFunctor
