module

public import SerrePositivity.KST.Spectra.CosimplicialHornFactorization
public import SerrePositivity.KST.Spectra.AnodyneHomotopyEquivalence

/-!
概要：余単体単体集合の関手的 Reedy fibrant 置換と各段の Kan 性。
方針：終対象への射を相対 latching anodyne と相対 matching horn RLP に因子分解する。
規約：全基点 π_* 同型は元の各段が Kan の場合に主張する。
使われ方：Goerss–Jardine VII §4、HTT A.3.3。Tot の段ごとの具体的な置換。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SSet
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.CosimplicialKanReplacement

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：余単体図式から終図式への実際の射。
方針：各成分を終対象への一意な射にする。
規約：終図式の値は単体集合の終対象。
使われ方：HTT A.3.3。Reedy 置換の因子分解の入力。 -/
abbrev terminalArrows : CosimplicialObject SSet.{u} ⥤ Arrow (CosimplicialObject SSet.{u}) where
  obj X := Arrow.mk (show X ⟶
      (Functor.const SimplexCategory).obj (⊤_ SSet.{u}) from
    { app := fun j ↦ terminal.from (X.obj j)
      naturality := fun _ _ _ ↦ by simp })
  map f := Arrow.homMk f (𝟙 _) (by ext j; simp)

/-- 概要：余単体単体集合の実際の関手的 Reedy 置換。
方針：終図式への射の horn 因子分解の中間図式を取る。
規約：対象も射も通常の余単体図式。
使われ方：Goerss–Jardine VII §4。Tot の Reedy fibrant な係数。 -/
abbrev functor : CosimplicialObject SSet.{u} ⥤ CosimplicialObject SSet.{u} :=
  terminalArrows.{u} ⋙ CosimplicialHornFactorization.factorization.{u}.Z

/-- 概要：元の余単体図式から Reedy 置換への自然な比較。
方針：horn 因子分解の左射を使う。
規約：自然性は全ての余単体射に対する厳密な等式。
使われ方：HTT A.3.3。置換前後の Tot の比較。 -/
def unit : 𝟭 (CosimplicialObject SSet.{u}) ⟶ functor where
  app X := CosimplicialHornFactorization.factorization.{u}.i.app (terminalArrows.{u}.obj X)
  naturality _ _ f := CosimplicialHornFactorization.factorization.{u}.i.naturality
    (terminalArrows.{u}.map f)

/-- 概要：Reedy 置換の単位は相対 latching anodyne。
方針：実際の因子分解の左類の証明を取り出す。
規約：通常の対象ごとの anodyne より強い相対条件。
使われ方：Goerss–Jardine VII §4。Reedy 置換の左類。 -/
lemma unit_reedy_anodyne (X : CosimplicialObject SSet.{u}) :
    reedyLeft simplex anodyneExtensions (unit.app X) := by
  change reedyLeft simplex anodyneExtensions
    (CosimplicialHornFactorization.factorization.{u}.i.app (terminalArrows.{u}.obj X))
  exact CosimplicialHornFactorization.factorization.{u}.hi (terminalArrows.{u}.obj X)

/-- 概要：Reedy 置換の単位は各段でも anodyne。
方針：相対 latching 条件を各成分へ移す。
規約：元の図式の Kan 性は不要。
使われ方：Goerss–Jardine VII §4。各段のホモトピー群の比較。 -/
lemma unit_anodyne (X : CosimplicialObject SSet.{u}) (j : SimplexCategory) :
    anodyneExtensions ((unit.app X).app j) :=
  CosimplicialHornFactorization.left_app _ (unit_reedy_anodyne X) j

/-- 概要：Reedy 置換の終図式への射は相対 matching horn RLP。
方針：実際の因子分解の右類の証明を取り出す。
規約：Kan–Quillen モデル構造を仮定しない。
使われ方：HTT A.3.3。Tot の Reedy 充填の入力。 -/
lemma reedy_terminal_rlp (X : CosimplicialObject SSet.{u}) :
    reedyRight simplex modelCategoryQuillen.J.rlp
      (CosimplicialHornFactorization.factorization.{u}.p.app (terminalArrows.{u}.obj X)) :=
  CosimplicialHornFactorization.factorization.{u}.hp (terminalArrows.{u}.obj X)

/-- 概要：Reedy 置換の各値は Kan 複体。
方針：相対 matching の右類を各段へ移し、終対象への fibration を得る。
規約：元の図式の Kan 性は不要。
使われ方：Goerss–Jardine VII §4。Tot の Kan な係数列。 -/
instance kanComplex (X : CosimplicialObject SSet.{u}) (j : SimplexCategory) :
    KanComplex (functor.obj X |>.obj j) := by
  let p := (CosimplicialHornFactorization.factorization.{u}.p.app (terminalArrows.{u}.obj X)).app j
  have hp := CosimplicialHornFactorization.right_app _ (reedy_terminal_rlp X) j
  have he : p = terminal.from ((functor.obj X).obj j) := terminal.hom_ext _ _
  change modelCategoryQuillen.J.rlp p at hp
  rw [he] at hp
  exact (isFibrant_iff _).mpr ((modelCategoryQuillen.fibration_iff _).mpr hp)

/-- 概要：Kan な余単体図式の単位は各段の全基点 π_* 同型。
方針：両側が Kan な anodyne のホモトピー不変性を適用する。
規約：零次数の成分集合も含む。
使われ方：Goerss–Jardine VII §4。Tot の置換不変性の係数比較。 -/
lemma unit_piIsomorphism (X : CosimplicialObject SSet.{u})
    [∀ j, KanComplex (X.obj j)] (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := X.obj j) (Y := (functor.obj X).obj j)
      ((unit.app X).app j) := by
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (show X.obj j ⟶ (functor.obj X).obj j from (unit.app X).app j)
  exact kanPiIsomorphism_of_anodyne (A := X.obj j) (B := (functor.obj X).obj j)
    ((unit.app X).app j) (unit_anodyne X j)

end

end SerrePositivity.KST.Spectra.CosimplicialKanReplacement
