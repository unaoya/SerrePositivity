module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalMapping
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftKanRestrictionComparison

/-!
概要：終対象上の元の左 Kan 関手の全部分圏の制限は充満忠実。
方針：標準相対余極限を通常の余極限へ移し、元の関手圏の指定 pinched 比較を使う。
規約：既存の相対左 Kan 関手の全部分圏をそのまま用いる。
使われ方：原典の元の関手全体からの制限定理の絶対的な場合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：終対象上の標準相対余極限条件は通常の余極限条件と同値。
方針：標準条件を全余錐の相対境界充填へ移し、終対象上の絶対判定を使う。
規約：標的の終対象性を明示し、U の inner 性は自動的に得る。
使われ方：相対 Kan 関手の全部分圏の絶対的な場合の同定。 -/
lemma kanIsRelativeColimitCone_iff_isColimit_of_terminal {J D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (hE : IsTerminal E)
    {p : J ⟶ D} (c : JoinCocone p) : IsRelativeColimitCone U c ↔ IsColimitCone c := by
  have : InnerFibration U := (quasicategory_iff_of_isTerminal U hE).1 inferInstance
  exact (kanRelativeCoconeLifting_iff_isRelativeColimitCone U c).symm.trans
    (kanRelativeCoconeLifting_iff_isColimit_of_terminal U hE c)

/-- 概要：終対象上の元の相対左 Kan 関手の全部分圏からの制限は充満忠実。
方針：始点の標準局所余錐を絶対的な余極限と読み、全部分圏の写像空間と制限を合成する。
規約：δ の単射性・充満忠実性と局所余極限の存在は不要。
使われ方：元の左 Kan 関手全体からの制限の絶対的な写像空間の普遍性。 -/
lemma kanRelativeLeftKanRestriction_terminal_isFullyFaithful {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hE : IsTerminal E) (δ : K ⟶ C) :
    IsFullyFaithful (kanRelativeLeftKanRestriction U δ
      (Functor.PullbackObjObj.ofIsTerminal internalHom δ U hE)) := by
  intro x y
  let F := (functorVertexEquiv C D).symm x.val
  let G := (functorVertexEquiv C D).symm y.val
  have hx := fullSubcomplexOnVertices_vertex x
  change IsRelativeLeftKanExtendedFrom U δ F at hx
  have hF : ∀ c : C _⦋0⦌, IsColimitCone (leftKanCanonicalCocone δ F c) := fun c ↦
    (kanIsRelativeColimitCone_iff_isColimit_of_terminal U hE _).1 (hx c)
  have hf : functorVertex F = x.val := (functorVertexEquiv C D).apply_symm_apply _
  have hg : functorVertex G = y.val := (functorVertexEquiv C D).apply_symm_apply _
  change IsSimplicialHomotopyEquivalence (pinchedHomMap
    ((kanRelativeLeftKanDiagrams U δ).ι ≫ (pre δ).app D) x y)
  rw [pinchedHomMap_comp]
  have hi := kanLeftCanonical_pinchedHomMap_equivalence δ F hF G
  rw [hf, hg] at hi
  exact (isFullyFaithful_fullSubcomplexOnVertices_ι _ _ x y).comp hi

end SerrePositivity.InfinityCategories.F1B
