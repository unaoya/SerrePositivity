module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.TransposeFunctorIsoComposition

/-!
概要：転置後の指定相対切断底変換同型と添字制限の全自然な両立。
方針：既存定義の転置を正規化し、元の実現同型の添字制限を移す。
規約：指定された底変換同型そのものを比較する。
使われ方：P-12 の単体切断底変換の合成への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の転置後の切断底変換同型を端点正規化した転置として回収する。
方針：既存定義の端点書き換えを異種等式で除く。
規約：元の実現同型を使う。使われ方：添字制限と合成の転置の正規化。 -/
lemma relativeSectionDiagramInfinityBaseChangeIso_normalized {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) :
    relativeSectionDiagramInfinityBaseChangeIso k A =
      diagramIsoCongr
        (transposeFunctorFamily_comp (leftFibrationInfinityBaseChange k)
          (relativeSectionEnrichedDiagram A).realization) rfl
        (relativeSectionBaseChangeRealizationIso k A).transpose := by
  have he : HEq (relativeSectionDiagramInfinityBaseChangeIso k A)
      (relativeSectionBaseChangeRealizationIso k A).transpose := by
    unfold relativeSectionDiagramInfinityBaseChangeIso
    dsimp only [_root_.id]
    have hcast {T U : Sort (u + 2)} (h : T = U) (z : T) : HEq (Eq.mp h z) z := by
      cases h
      rfl
    exact hcast _ _
  exact eq_of_heq (he.trans (diagramIsoCongr_heq _ _ _).symm)

/-- 概要：元の相対切断底変換同型は添字関手の制限と全自然に両立する。
方針：元の実現同型の制限の式を転置し端点を同じ切断図式に揃える。
規約：対象ごとの比較ではなく図式全体の指定同型の等式。
使われ方：全単体の添字制限を使った指定 straightening 合成の降下。 -/
lemma relativeSectionDiagramInfinityBaseChangeIso_reindex {B D : SSet.{u}}
    {J L : Type u} [Category.{u} J] [Category.{u} L]
    (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) (H : L ⥤ J) :
    relativeSectionDiagramInfinityBaseChangeIso k (H.op ⋙ A) =
      diagramIsoCongr
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f ↦ f ≫ (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})
            (relativeSectionDiagramInfinity_reindex A H)))
        (relativeSectionDiagramInfinity_reindex (A ⋙ Over.map k) H)
        ((relativeSectionDiagramInfinityBaseChangeIso k A).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H))) := by
  rw [relativeSectionDiagramInfinityBaseChangeIso_normalized,
    relativeSectionBaseChangeRealizationIso_reindex,
    diagramIsoCongr_transpose, diagramIsoCongr_comp]
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap H)
  let e := relativeSectionBaseChangeRealizationIso k A
  let hf := transposeFunctorFamily_pre
    (leftFibrationInfinityBaseChange k ≫ (relativeSectionEnrichedDiagram A).realization) q
  let hg := transposeFunctorFamily_pre
    (relativeSectionEnrichedDiagram (A ⋙ Over.map k)).realization q
  have hr := functorIsoTranspose_postcomp_pre q e
  rw [relativeSectionDiagramInfinityBaseChangeIso_normalized k A,
    diagramIsoCongr_precomp, diagramIsoCongr_comp]
  rw [← hr, diagramIsoCongr_comp]

end SerrePositivity.InfinityCategories.F2.Presentable
