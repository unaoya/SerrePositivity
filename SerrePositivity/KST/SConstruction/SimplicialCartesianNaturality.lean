module
public import SerrePositivity.KST.Comparison.HomotopyPullbackGeneralPasting
public import SerrePositivity.KST.Comparison.SequenceHomotopyPullbacks
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

/-! # 面と退化から全単体作用素への homotopy-cartesian 性
概要：自然性四角形の homotopy pullback 性は恒等と合成で閉じ、面・退化での判定で十分。
方針：関手的な Kan 分解と横の貼り合わせを使い、単体圏の生成定理を適用する。
規約：行の Kan 性は不要。使われ方：経路境界の全ての面条件を既存の実現定理へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 自然変換の恒等添字射の四角形は行の Kan 性なしに homotopy pullback。 -/
lemma naturality_homotopyPullback_id {D : Type v} [Category.{w} D]
    {F G : D ⥤ SSet.{u}} (α : F ⟶ G) (d : D) :
    IsHomotopyPullback (CommSq.mk (α.naturality (𝟙 d))) := by
  apply (diagramKan_arrowSquare_iff α (𝟙 d)).mpr
  exact diagramArrow_id_homotopyPullback (diagramKanProjection α) d (diagramKanProjection_rlp α d)

/-- 二つの添字射で homotopy pullback となる自然性四角形は合成でもそうなる。 -/
lemma naturality_homotopyPullback_comp {D : Type v} [Category.{w} D]
    {F G : D ⥤ SSet.{u}} (α : F ⟶ G) {d e k : D} (f : d ⟶ e) (g : e ⟶ k)
    (hf : IsHomotopyPullback (CommSq.mk (α.naturality f)))
    (hg : IsHomotopyPullback (CommSq.mk (α.naturality g))) :
    IsHomotopyPullback (CommSq.mk (α.naturality (f ≫ g))) := by
  simpa only [CategoryTheory.Functor.map_comp] using isHomotopyPullback_paste_horiz
    (CommSq.mk (α.naturality f)) (CommSq.mk (α.naturality g)) hf hg

/-- 面と退化の元の自然性四角形が homotopy pullback なら全単体作用素もそうなる。 -/
lemma simplicial_naturality_homotopyPullback_of_generators
    {F G : SimplicialObject SSet.{u}} (α : F ⟶ G)
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)), IsHomotopyPullback
      (CommSq.mk (α.naturality (SimplexCategory.δ i).op)))
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsHomotopyPullback
      (CommSq.mk (α.naturality (SimplexCategory.σ i).op)))
    {d e : SimplexCategory} (θ : d ⟶ e) :
    IsHomotopyPullback (CommSq.mk (α.naturality θ.op)) := by
  let W : MorphismProperty SimplexCategory := fun _ _ θ =>
    IsHomotopyPullback (CommSq.mk (α.naturality θ.op))
  let : W.IsMultiplicative := {
    id_mem := fun d => naturality_homotopyPullback_id α (Opposite.op d)
    comp_mem := fun f g hf hg => by
      change IsHomotopyPullback (CommSq.mk (α.naturality ((f ≫ g).op)))
      rw [op_comp]
      exact naturality_homotopyPullback_comp α g.op f.op hg hf }
  have hW : W = ⊤ :=
    SimplexCategory.morphismProperty_eq_top W (fun i => hδ _ i) (fun i => hσ _ i)
  change W θ
  rw [hW]
  trivial

end SerrePositivity.KST.SConstruction
