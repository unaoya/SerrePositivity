module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGOverInitialRefinementDegeneracies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInitialRefinementPositiveFaces

/-! # 同じ実分母部分圏内の細分と一般順序写像・正番号退化

概要：零固定・正番号非零の順序写像との厳密可換性を、同じ実分母部分圏へ上げる。
方針：元の over の可換性を、同じ全部分型の外延性で使う。
規約：追加実辺の等式輸送を明示。使われ方：有限錐の全正番号退化の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x : D)

/-- 同じ実分母部分圏内の細分は、一般の零固定・正番号非零の制限と厳密に可換。 -/
lemma dgVerdierSimplexInitialRefinement_pullback_initial {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋n⦌)
    (h₀ : α.toOrderHom 0 = 0) (hz : ∀ i, i ≠ 0 → α.toOrderHom i ≠ 0)
    (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ σ.val)).obj 0))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).map α.op
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement A D P x σ q s hs) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement A D P x ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).map α.op σ) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexReindex_source _ α σ.val h₀))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P s _ hs) :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_pullback_initial _ α σ.val h₀ hz q s)

/-- 全次元の同じ実分母部分圏内の細分は、全正番号基本退化を厳密に保つ。 -/
lemma dgVerdierSimplexInitialRefinement_degeneracy_positive {n : ℕ}
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋n⦌) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ σ.val)).obj 0))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ j
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement A D P x σ q s hs) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement A D P x ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ j σ) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexReindex_source _ (SimplexCategory.σ j) σ.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDegeneracy_zero j)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P s _ hs) :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_degeneracy_positive _ σ.val q s j hj)

/-- 同じ実分母部分圏内の零面は、全次元で元のまま保たれる。 -/
lemma dgVerdierSimplexInitialRefinement_face_zero {n : ℕ}
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋n + 1⦌) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ σ.val)).obj 0))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement A D P x σ q s hs) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 σ :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_pullback_avoids_zero _
    (SimplexCategory.δ (0 : Fin (n + 2))) σ.val
    (0 : Fin (n + 2)).succAboveOrderEmb.injective
    (fun i => by change i.succ ≠ 0; exact Fin.succ_ne_zero i) q s)

/-- 同じ実分母部分圏内の全正番号面は、元の同じ面の同じ閉細分。 -/
lemma dgVerdierSimplexInitialRefinement_face_positive {n : ℕ}
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋n + 1⦌) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ σ.val)).obj 0))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (j : Fin (n + 2)) (hj : j ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ j
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement A D P x σ q s hs) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement A D P x ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ j σ) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexReindex_source _ (SimplexCategory.δ j) σ.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPositiveCoface_zero j hj)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P s _ hs) :=
  dgVerdierSimplexInitialRefinement_pullback_initial A D P x (SimplexCategory.δ j) σ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPositiveCoface_zero j hj)
    (fun _i hi he => hi (j.succAboveOrderEmb.injective
      (he.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPositiveCoface_zero j hj).symm))) q s hs

end SerrePositivity.InfinityCategories.Project.DerivedCategories
