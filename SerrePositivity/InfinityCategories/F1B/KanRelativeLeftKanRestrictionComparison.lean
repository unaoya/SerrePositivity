module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeLeftKanCommaFamily
public import SerrePositivity.InfinityCategories.F1B.KanLeftCommaRelativeTargetComparison

/-!
概要：元の相対左 Kan 関手の全部分圏からの制限と comma 側の制限の比較。
方針：元の関手圏の相対制限を全部分複体へ制限し、普遍前合成の可換性を合成する。
規約：始域は C 上の関手そのものの全部分圏。
使われ方：相対 join の制限定理を元の包含による制限へ移す主経路の可換正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元の相対左 Kan 関手を元の制限図式と U による像の組へ写す。
方針：通常の相対内部 Hom の比較に全部分複体の包含を前合成する。
規約：局所条件を持つ元の C 上の関手を始域とする。
使われ方：原典の相対 Kan 関手全体からの制限射。 -/
def kanRelativeLeftKanRestriction {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U) : (kanRelativeLeftKanDiagrams U δ : SSet.{u}) ⟶ s.pt :=
  (kanRelativeLeftKanDiagrams U δ).ι ≫ s.π

/-- 概要：単射による相対左 Kan 関手の制限は右持ち上げ条件の下で inner fibration。
方針：相対内部 Hom の inner 性と全部分複体の包含の inner 性を合成する。
規約：元の U の右持ち上げ条件は明示する。
使われ方：元の制限射の写像空間の同値と存在から自明 Kan 性へ進む。 -/
lemma kanRelativeLeftKanRestriction_innerFibration {K C D E : SSet.{u}}
    (U : D ⟶ E) (hU : KanEquivalenceLifting U) (δ : K ⟶ C) [Mono δ]
    (s : internalHom.PullbackObjObj δ U) :
    InnerFibration (kanRelativeLeftKanRestriction U δ s) := by
  have hs : KanEquivalenceLifting s.π := by
    intro A B i hm hi
    exact KanEquivalenceLifting.relativeInternalHom hU δ s i hm hi
  have : InnerFibration s.π := hs.innerFibration
  have : InnerFibration (kanRelativeLeftKanDiagrams U δ).ι :=
    inferInstanceAs (InnerFibration (fullSubcomplexOnVertices _ (KanRelativeLeftKanVertex U δ)).ι)
  exact ⟨innerFibrations.comp_mem _ _
    (InnerFibration.mem (q := (kanRelativeLeftKanDiagrams U δ).ι))
    (InnerFibration.mem (q := s.π))⟩

/-- 概要：元の相対左 Kan 関手の制限は comma 側の相対普遍図式の制限と可換。
方針：全部分圏の包含の後で普遍前合成の相対制限の可換性を使う。
規約：元と標的の図式をともに保つ単体写像の正方形。
使われ方：元の制限射の写像空間と相対 join の制限定理を比較する。 -/
lemma kanRelativeLeftKanRestriction_comma_square {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C)) U) :
    kanRelativeLeftKanToCommaDiagrams U δ ≫
      kanRelativeJoinRelativeColimitRestriction (kanLeftCommaProjection δ) U t =
        kanRelativeLeftKanRestriction U δ s ≫ kanLeftCommaRelativeTargetMap δ U s t := by
  rw [kanRelativeJoinRelativeColimitRestriction, ← Category.assoc,
    kanRelativeLeftKanToCommaDiagrams_ι, Category.assoc,
    kanLeftCommaUniversalFamily_relativeRestriction, ← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.F1B
