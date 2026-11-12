module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.KanMonoArrowFactorization
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：任意の Kan 複体列を、全隣接遷移が単射な Kan 複体列に置換する。
方針：置換済みの段から元の次段への射を単射と trivial Kan fibration に帰納的に分解する。
規約：元の列への比較は厳密自然変換で、全成分が同値。
使われ方：HTT 4.2.4.1、一般の遷移を持つ列の実際の homotopy 逐次余極限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：元の列の各段への比較を伴う単射な置換の段。
方針：零段を保持し、比較と元の遷移の合成を次の段で境界分解する。
規約：比較の始域も Kan 対象として保持する。
使われ方：HTT 4.2.4.1、一般の列の cofibrant な置換の帰納的な構成。 -/
def kanSequenceMonoStage (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (n : ℕ) → Σ X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}, X ⟶ F.obj (AsSmall.up.obj n)
  | 0 => ⟨F.obj (AsSmall.up.obj 0), 𝟙 _⟩
  | n + 1 =>
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowObject ((kanSequenceMonoStage F n).2 ≫
      F.map (AsSmall.up.map (homOfLE (Nat.le_succ n)))),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowRight ((kanSequenceMonoStage F n).2 ≫
        F.map (AsSmall.up.map (homOfLE (Nat.le_succ n))))⟩

/-- 概要：単射な置換の隣接する段の間の実際の遷移。
方針：次の段を定義した境界分解の左因子を取る。
規約：元の隣接射の単射性は不要。
使われ方：全ての自然数の間の射を合成で延長する列の構成。 -/
def kanSequenceMonoStep (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (n : ℕ) :
    (kanSequenceMonoStage F n).1 ⟶ (kanSequenceMonoStage F (n + 1)).1 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowLeft ((kanSequenceMonoStage F n).2 ≫
    F.map (AsSmall.up.map (homOfLE (Nat.le_succ n))))

/-- 概要：置換の段の比較は隣接遷移と厳密に可換。
方針：境界分解の左右の因子の合成の式を使う。
規約：通常の Kan 複体の圏における等号。
使われ方：元の列への比較の全ての射に対する自然性。 -/
lemma kanSequenceMonoStep_comparison (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (n : ℕ) :
    kanSequenceMonoStep F n ≫ (kanSequenceMonoStage F (n + 1)).2 =
      (kanSequenceMonoStage F n).2 ≫ F.map (AsSmall.up.map (homOfLE (Nat.le_succ n))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrow_fac _

/-- 概要：任意の Kan 複体列から構成した単射な遷移を持つ Kan 複体列。
方針：隣接射の列を自然数圏上の関手へ延長し、添字を AsSmall へ戻す。
規約：元の列と同じ添字の宇宙。
使われ方：HTT 4.2.4.1、単射な列の逐次余極限定理への入力。 -/
def kanSequenceMonoReplacement (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  AsSmall.down ⋙ Functor.ofSequence (kanSequenceMonoStep F)

/-- 概要：単射な置換した列から元の列への厳密自然変換。
方針：隣接射での可換性を全ての自然数の間の射へ延長する。
規約：台の単体集合の図式の間の実際の射。
使われ方：成分ごとの同値を使った元の図式への余極限の輸送。 -/
def kanSequenceMonoComparison (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    kanSequenceMonoReplacement F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (kanSequenceMonoStage F (AsSmall.down.obj i)).2
  naturality i j f := by
    let η : Functor.ofSequence (kanSequenceMonoStep F) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
        AsSmall.up ⋙ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget := NatTrans.ofSequence
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (kanSequenceMonoStage F n).2) (by
        intro n
        change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map
          ((Functor.ofSequence (kanSequenceMonoStep F)).map (homOfLE (Nat.le_succ n))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (kanSequenceMonoStage F (n + 1)).2 = _
        rw [Functor.ofSequence_map_homOfLE_succ, ← Functor.map_comp,
          kanSequenceMonoStep_comparison, Functor.map_comp]
        rfl)
    exact η.naturality (AsSmall.down.map f)

/-- 概要：置換した Kan 複体列の全隣接遷移は台で単射。
方針：隣接遷移を境界分解の左因子へ戻す。
規約：通常の Kan 複体の圏での Mono ではなく台の単体集合の Mono。
使われ方：反変 Hom の塔の fibration 条件の検証。 -/
instance kanSequenceMonoReplacement_step_mono (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (n : ℕ) :
    Mono ((kanSequenceMonoReplacement F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)))) := by
  change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map
    ((Functor.ofSequence (kanSequenceMonoStep F)).map (homOfLE (Nat.le_succ n))))
  rw [Functor.ofSequence_map_homOfLE_succ]
  change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowLeft _))
  infer_instance

/-- 概要：単射な列から元の列への比較は全成分で同値。
方針：零段では恒等、それ以降では境界分解の右因子のホモトピー同値性を使う。
規約：元の全隣接遷移に条件を付けない。
使われ方：HTT 4.2.4.1、元の列の coherent 表示への関手同型。 -/
lemma kanSequenceMonoComparison_isQCatEquivalence
    (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (i : AsSmall.{u} ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := ((kanSequenceMonoReplacement F).obj i).obj) (Y := (F.obj i).obj)
      ((kanSequenceMonoComparison F).app i) := by
  rcases i with ⟨n⟩
  cases n with
  | zero => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  | succ n =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (X := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowObject ((kanSequenceMonoStage F n).2 ≫
        F.map (AsSmall.up.map (homOfLE (Nat.le_succ n))))).obj)
      (Y := (F.obj (AsSmall.up.obj (n + 1))).obj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowRight_homotopyEquivalence _)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
