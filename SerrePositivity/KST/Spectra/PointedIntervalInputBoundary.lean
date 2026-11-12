module

public import SerrePositivity.KST.Spectra.PointedIntervalInputSquare
public import SerrePositivity.KST.Spectra.PointedPrecompositionConstants
public import SerrePositivity.KST.Spectra.PointedRelativeCofiberHomotopy

/-!
概要：射影を固定する入力比較を、射影を経由する二端点の間の区間へ作用させる。
方針：同じ前合成ホモトピーの制限を一定と計算し、正方形の両端へ移す。
規約：全区間の一定性を証明する。使われ方：交換の自然性正方形の指定境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

/-- 二度の入力制限も、同じ合成入力への制限と実辺全体で一致する。 -/
lemma pre_pre_path {A B C E D : PointedSimplicialSet.{u}} {p : E ⟶ D}
    {f g : A ⟶ E} (P : VerticalPath p f g) (i : B ⟶ A) (j : C ⟶ B) :
    ((P.pre i).pre j).path = (P.pre (j ≫ i)).path := by
  change (P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E).right) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right =
    P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (j ≫ i) E).right
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun q => P.path ≫ q.right) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp j i E)

/-- 射影を経由する一つの固定族では、同じ入力比較の前合成作用は全区間で一定。 -/
lemma basedPre_at_factored_family {A B C : PointedSimplicialSet.{u}}
    {p : B ⟶ C} {a b : A ⟶ B} (H : VerticalPath p a b)
    {E : PointedSimplicialSet.{u}} (u : C ⟶ E) :
    pointFamily (p ≫ u) ▷ (Δ[1] : SSet.{u}) ≫
        (H.forgetProjection.basedPre E).homotopy.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ pointFamily ((a ≫ p) ≫ u) := by
  have hp := pre_homotopy_h (H.forgetProjection.basedPre E) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed p E)
  have hk := hp.symm.trans (H.basedPre_projection_constant E)
  rw [← pointFamily_pre p u, comp_whiskerRight_assoc]
  change (pointFamily u ▷ (Δ[1] : SSet.{u})) ≫
    ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed p E).right ▷ (Δ[1] : SSet.{u}) ≫
      (H.forgetProjection.basedPre E).homotopy.h) = _
  rw [hk]
  have hpf : pointFamily u ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (a ≫ p) E).right =
      pointFamily ((a ≫ p) ≫ u) := pointFamily_pre (a ≫ p) u
  rw [← Category.assoc, whiskerRight_fst, Category.assoc, hpf]

/-- 同じ入力正方形の始辺は、元の区間の始点の固定族への同じ入力比較。 -/
lemma inputSquare_left {A B E C : PointedSimplicialSet.{u}} {p : B ⟶ C}
    {a b : A ⟶ B} (H : VerticalPath p a b) {f g : B ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g) :
    SquareAdjustment.leftSide ≫ (inputSquare H P).h =
      CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫
        (pointFamily f ▷ (Δ[1] : SSet.{u})) ≫
          (H.forgetProjection.basedPre E).homotopy.h := by
  have hl : SquareAdjustment.leftSide.{u} =
      CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫
        (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  change SquareAdjustment.leftSide ≫ (P.path ▷ (Δ[1] : SSet.{u}) ≫ _) = _
  rw [hl, Category.assoc, ← Category.assoc (stdSimplex.δ (1 : Fin 2) ▷ _),
    ← comp_whiskerRight, P.zero]

/-- 同じ入力正方形の終辺も、元の区間の終点の固定族への同じ入力比較。 -/
lemma inputSquare_right {A B E C : PointedSimplicialSet.{u}} {p : B ⟶ C}
    {a b : A ⟶ B} (H : VerticalPath p a b) {f g : B ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g) :
    SquareAdjustment.rightSide ≫ (inputSquare H P).h =
      CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫
        (pointFamily g ▷ (Δ[1] : SSet.{u})) ≫
          (H.forgetProjection.basedPre E).homotopy.h := by
  have hr : SquareAdjustment.rightSide.{u} =
      CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫
        (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  change SquareAdjustment.rightSide ≫ (P.path ▷ (Δ[1] : SSet.{u}) ≫ _) = _
  rw [hr, Category.assoc, ← Category.assoc (stdSimplex.δ (0 : Fin 2) ▷ _),
    ← comp_whiskerRight, P.one]

/-- 始点が同じ射影を経由するなら、入力正方形の左辺全体は同じ頂点で一定。 -/
lemma inputSquare_start_factored {A B C E : PointedSimplicialSet.{u}} {p : B ⟶ C}
    {a b : A ⟶ B} (H : VerticalPath p a b) (u v : C ⟶ E)
    (P : VerticalPath (PointedObject.toPoint E) (p ≫ u) (p ≫ v)) :
    SquareAdjustment.leftSide ≫ (inputSquare H P).h =
      SSet.const (familyVertex ((a ≫ p) ≫ u)) := by
  rw [inputSquare_left, basedPre_at_factored_family, pointFamily_eq_const,
    SSet.comp_const, SSet.comp_const]

/-- 終点も同じ射影を経由するなら、右辺全体も同じ終頂点で一定。 -/
lemma inputSquare_finish_factored {A B C E : PointedSimplicialSet.{u}} {p : B ⟶ C}
    {a b : A ⟶ B} (H : VerticalPath p a b) (u v : C ⟶ E)
    (P : VerticalPath (PointedObject.toPoint E) (p ≫ u) (p ≫ v)) :
    SquareAdjustment.rightSide ≫ (inputSquare H P).h =
      SSet.const (familyVertex ((a ≫ p) ≫ v)) := by
  rw [inputSquare_right, basedPre_at_factored_family, pointFamily_eq_const,
    SSet.comp_const, SSet.comp_const]

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
