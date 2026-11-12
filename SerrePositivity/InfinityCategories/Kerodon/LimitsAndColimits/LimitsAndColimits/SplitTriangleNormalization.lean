module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FixedInnerHornFamily

/-!
概要：厳密な全族切断から、読出しを保つ正規化と同じ固定ホーン内の可逆比較を得る。
方針：read ≫ encode の合成式と、固定ホーン充填空間の可縮 Kan 性を使う。
規約：encode・read 自体の存在はこの葉では主張しない。
使われ方：Ind-S (9) の採用済み正規化後の全対角回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 読み出した同じ全族を再構成する正規化。 -/
def splitTriangleNormalization {L T : SSet.{u}} (encode : L ⟶ T) (read : T ⟶ L) : T ⟶ T :=
  read ≫ encode

/-- 厳密切断による正規化は冪等。 -/
lemma splitTriangleNormalization_idempotent {L T : SSet.{u}}
    (encode : L ⟶ T) (read : T ⟶ L) (h : encode ≫ read = 𝟙 L) :
    splitTriangleNormalization encode read ≫ splitTriangleNormalization encode read =
      splitTriangleNormalization encode read := by
  simp only [splitTriangleNormalization, Category.assoc]
  rw [← Category.assoc encode read encode, h, Category.id_comp]

/-- 正規化は同じ全族の読出しを厳密に保つ。 -/
lemma splitTriangleNormalization_read {L T : SSet.{u}}
    (encode : L ⟶ T) (read : T ⟶ L) (h : encode ≫ read = 𝟙 L) :
    splitTriangleNormalization encode read ≫ read = read := by
  rw [splitTriangleNormalization, Category.assoc, h, Category.comp_id]

/-- 再構成済みの全族は正規化で厳密に不変。 -/
lemma splitTriangleNormalization_encode {L T : SSet.{u}}
    (encode : L ⟶ T) (read : T ⟶ L) (h : encode ≫ read = 𝟙 L) :
    encode ≫ splitTriangleNormalization encode read = encode := by
  rw [splitTriangleNormalization, ← Category.assoc, h, Category.id_comp]

/-- 再構成が持つ全対角の厳密式は、正規化した任意の入力全族へ移る。 -/
lemma splitTriangleNormalization_diagonal {L T D : SSet.{u}}
    (encode : L ⟶ T) (read : T ⟶ L) (diagonal : T ⟶ D) (direct : L ⟶ D)
    (h : encode ≫ diagonal = direct) :
    splitTriangleNormalization encode read ≫ diagonal = read ≫ direct := by
  rw [splitTriangleNormalization, Category.assoc, h]

/-- 元の入力とその正規化を、同じ固定ホーン充填空間の中で可逆比較する。 -/
lemma splitTriangleNormalization_vertexIso {L T : SSet.{u}}
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan T) (encode : L ⟶ T) (read : T ⟶ L) (t : T _⦋0⦌) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t ((splitTriangleNormalization encode read).app (Opposite.op ⦋0⦌) t)) := by
  have := hc.kanComplex
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex t) (hc.isTerminalVertex _)⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
