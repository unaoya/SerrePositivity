module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NestedCutMaximum
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionNaturality

/-!
概要：二つの時刻切断を持つ coherent 合成図式の対象と第一の混合 Hom。
方針：内側零頂点を保つ外側切断で制限し、元の最大座標の式を使う。
規約：第一射の全単体と元の path の旗を保持する。
使われ方：第二三角形の始域から中間対象へ向かう Hom の比較。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
variable (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
variable (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌)
variable (s t : Fin (n + 1) →o Fin 2)

/-- 元の合成単体を、独立の外側時刻で切断した実際の図式。 -/
def coherentCompositionNestedCutSimplex : (SimplicialNerve C) _⦋n⦌ :=
  (SimplicialNerve C).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s)).op
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex σ τ t)

/-- 内側零頂点を保つ外側切断で、零時刻の対象は元の始域。 -/
lemma coherentCompositionNestedCutSimplex_obj_zero
    (hst : ∀ k, t k = 0 → s k = 0) (i : Fin (n + 1)) (hi : t i = 0) :
    (coherentCompositionNestedCutSimplex σ τ s t).obj ⟨ULift.up i⟩ = X := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s i) = X
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s i (hst i hi), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Z t i hi]

/-- 外側零・内側一時刻の対象は、元の中間対象。 -/
lemma coherentCompositionNestedCutSimplex_obj_middle
    (i : Fin (n + 1)) (hs : s i = 0) (hi : t i = 1) :
    (coherentCompositionNestedCutSimplex σ τ s t).obj ⟨ULift.up i⟩ = Y := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s i) = Y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s i hs,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one X Y Z t i (by rw [hi]; decide)]

/-- 外側一時刻の対象は、元の最終対象。 -/
lemma coherentCompositionNestedCutSimplex_obj_last
    (i : Fin (n + 1)) (hi : s i = 1) :
    (coherentCompositionNestedCutSimplex σ τ s t).obj ⟨ULift.up i⟩ = Z := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s i) = Z
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one s i (by rw [hi]; decide), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last]

/-- 始域から中間対象へ向かう Hom は、第一射を元の最後の零頂点で評価した族。 -/
lemma coherentCompositionNestedCutSimplex_zero_middle
    (hst : ∀ k, t k = 0 → s k = 0)
    (i j : Fin (n + 1)) (hi : t i = 0) (hsj : s j = 0) (hj : t j = 1) :
    (coherentCompositionNestedCutSimplex σ τ s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionNestedCutSimplex_obj_zero σ τ s t hst i hi)
        (coherentCompositionNestedCutSimplex_obj_middle σ τ s t j hsj hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap t hi j ≫ SSet.yonedaEquiv.symm σ := by
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s j)) ≫ eqToHom _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_transport σ τ t
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s i (hst i hi)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s j hsj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Z t i hi)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one X Y Z t j (by rw [hj]; decide)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_one σ τ t i j hi (by rw [hj]; decide)]
  simp only [← Category.assoc]
  exact congrArg (fun f ↦ f ≫ SSet.yonedaEquiv.symm σ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNestedCut_maximumMap s t hst i j hi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s j hsj))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
