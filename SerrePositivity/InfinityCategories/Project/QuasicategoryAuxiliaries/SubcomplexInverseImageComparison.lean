module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：部分複体の逆像と標準 pullback の比較。
方針：充填性を仮定しない pullback の表示と前合成同値の移送を共用する。
規約：元の宣言名・型・証明本文を保持する。
使われ方：F1 と F1B の共通の幾何的な計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：部分複体の逆像の通常の四角形は pullback。
方針：各次数で元と所属証明の組を一意に回収する。
規約：射の充填性は不要。
使われ方：部分複体による逆像の表示と標準 pullback の同定。 -/
lemma subcomplexInverseImage_isPullback {E B : SSet.{u}} (p : E ⟶ B) (A : B.Subcomplex) :
    IsPullback (A.fromPreimage p) (A.preimage p).ι A.ι p := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    exact Subtype.ext h.2
  · intro a e h
    have he : p.app d e ∈ A.obj d := by rw [← h]; exact a.property
    exact ⟨⟨e, he⟩, Subtype.ext h.symm, rfl⟩

/-- 概要：逆像部分複体の包含の前合成同値性を標準 pullback の射影へ移す。
方針：pullback の標準同型を消去する。
規約：射影は全空間 E への第二射影。
使われ方：replacement の内ホーンのセル分解を pullback の比較に渡す。 -/
lemma isPrecompositionEquivalence_pullback_snd_of_subcomplexInverseImage
    {E B : SSet.{u}} (p : E ⟶ B) (A : B.Subcomplex)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (A.preimage p).ι) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pullback.snd A.ι p) := by
  let hp := subcomplexInverseImage_isPullback p A
  have hh : hp.isoPullback.hom ≫ pullback.snd A.ι p = (A.preimage p).ι :=
    hp.isoPullback_hom_snd
  rw [← hh] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso hp.isoPullback).cancel_left h

/-- 概要：部分複体による逆像と標準 pullback の包含は同じ前合成同値条件を持つ。
方針：標準 pullback 同型を合成または消去する。
規約：射 p の充填性は不要。
使われ方：標準単体と nerve の表示の変更に対応する。 -/
lemma isPrecompositionEquivalence_subcomplexInverseImage_iff
    {E B : SSet.{u}} (p : E ⟶ B) (A : B.Subcomplex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (A.preimage p).ι ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pullback.snd A.ι p) := by
  refine ⟨isPrecompositionEquivalence_pullback_snd_of_subcomplexInverseImage p A, ?_⟩
  intro h
  let hp := subcomplexInverseImage_isPullback p A
  have hh : hp.isoPullback.hom ≫ pullback.snd A.ι p = (A.preimage p).ι :=
    hp.isoPullback_hom_snd
  rw [← hh]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso hp.isoPullback).comp h

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
