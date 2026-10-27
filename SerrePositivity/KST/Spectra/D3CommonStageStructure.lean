module

public import SerrePositivity.KST.Spectra.D3StageStructure

/-!
概要：同じ共通 BF 比較の段間構造条件を、元の構造随伴射の厳密正方形として公開する。
方針：元の列射の構造条件を随伴表示へ移し、補助列の指定構造をそのまま展開する。
規約：新しい比較射や円交換因子を選ばない。各成分は元の共通包含・比較・右射影。
使われ方：実 loop 全図式の段比較と元の BF 構造との整合性認証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 元の共通左包含は、同じ BF 構造随伴射を各段で厳密に保つ。 -/
lemma commonInclusion_structure (X : OmegaSpectrum.{u}) (n : ℕ) :
    (commonInclusion X).app n ≫
      KanSequence.ordinaryStructureAdjoint (commonRefinement X).toKanSequence n =
    KanSequence.ordinaryStructureAdjoint X.toKanSequence n ≫
      (ihom PointedSimplicialSet.circle.{u}).map ((commonInclusion X).app (n + 1)) :=
  KanSequence.ordinaryStructureAdjoint_natural
    (⟨(commonInclusion X).app, (commonInclusion X).comm⟩ :
      KanSequence.Hom X.toKanSequence (commonRefinement X).toKanSequence) n

/-- 元の比較右脚も、同じ BF 構造随伴射を各段で厳密に保つ。 -/
lemma commonComparison_structure (X : OmegaSpectrum.{u}) (n : ℕ) :
    (commonComparison X).app n ≫
      KanSequence.ordinaryStructureAdjoint (middle X).toKanSequence n =
    KanSequence.ordinaryStructureAdjoint (commonRefinement X).toKanSequence n ≫
      (ihom PointedSimplicialSet.circle.{u}).map ((commonComparison X).app (n + 1)) :=
  KanSequence.ordinaryStructureAdjoint_natural
    (⟨(commonComparison X).app, (commonComparison X).comm⟩ :
      KanSequence.Hom (commonRefinement X).toKanSequence (middle X).toKanSequence) n

/-- 同じ共通右射影は、元の次段構造の通常 loop と厳密に可換。
補助列の構造を元の定義で展開しており、円交換因子を比較していない。 -/
lemma commonProjection_structure (X : OmegaSpectrum.{u}) (n : ℕ) :
    (commonProjection X).app n ≫
      (ihom PointedSimplicialSet.circle.{u}).map
        (KanSequence.ordinaryStructureAdjoint X.toKanSequence (n + 1)) =
    KanSequence.ordinaryStructureAdjoint (commonRefinement X).toKanSequence n ≫
      (ihom PointedSimplicialSet.circle.{u}).map ((commonProjection X).app (n + 1)) := by
  have h := KanSequence.ordinaryStructureAdjoint_natural (commonProjection X) n
  change (commonProjection X).app n ≫
      KanSequence.ordinaryStructureAdjoint (KanSequence.adjointLoop
        (KanSequence.tail X.toKanSequence)) n = _ at h
  rw [KanSequence.adjointLoop_ordinaryStructureAdjoint] at h
  exact h

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
