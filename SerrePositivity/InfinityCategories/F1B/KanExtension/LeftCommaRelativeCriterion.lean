module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftExtension
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeColimitReindex
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit

/-!
概要：comma fiber の相対普遍余錐と元の指定変換の相対左 Kan 条件の同定。
方針：標準局所添字への制限と余錐全体の比較同型で標準 U 余極限性を移す。
規約：指定変換は元の添字に制限して得られる既存の変換を保つ。
使われ方：相対 join 表示の制限定理を元の Kan 図式へ戻すための局所判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：comma 上の候補の比較余錐は fiber の余錐と同じ相対余極限性を持つ。
方針：単射な前合成同値への制限と、図式全体の関手同型の二つの同値判定を合成する。
規約：U は inner fibration、K・C・D・E は quasicategory。
使われ方：元の指定変換の局所相対 Kan 条件の判定。 -/
lemma kanLeftCommaCoconeTransport_isRelativeColimit_iff {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀)
    (c : C _⦋0⦌) :
    IsRelativeColimitCone U (kanLeftCommaCoconeTransport δ F₀ H hH c).cocone ↔
      IsRelativeColimitCone U (kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H) := by
  let z := kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H
  let i := kanLeftKanShapeToCommaFiber δ c
  have he := kanIsRelativeColimitCone_iff_of_functorIso U
    (kanLeftCommaCoconeTransport δ F₀ H hH c).cocone (z.restrict i)
    (kanLeftCommaCoconeTransport_functorIso δ F₀ H hH c)
  exact he.trans (kanIsRelativeColimitCone_iff_restrict_of_precompositionEquivalence U z i
    (kanLeftKanShapeToCommaFiber_isPrecompositionEquivalence δ c)).symm

/-- 概要：全 comma fiber で相対普遍な図式の候補は元の関手に沿う相対左 Kan 拡張。
方針：既存の指定変換と局所輸送を選び、fiber の相対余極限を標準局所余錐へ戻す。
規約：元の関手 δ に単射性や fibration 性を要求しない。
使われ方：相対 Kan 図式の大域的な組み立てから元の関手の相対 Kan 条件へ進む。 -/
lemma kanLeftCommaCandidate_isRelativeLeftKanExtension {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀)
    (hc : ∀ c : C _⦋0⦌,
      IsRelativeColimitCone U (kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H)) :
    IsRelativeLeftKanExtension U δ F₀ (kanLeftCommaCandidate δ H)
      (kanLeftCommaCandidateTransformation δ F₀ H hH) := by
  intro c
  exact ⟨kanLeftCommaCoconeTransport δ F₀ H hH c,
    (kanLeftCommaCoconeTransport_isRelativeColimit_iff U δ F₀ H hH c).2 (hc c)⟩

/-- 概要：comma 上の候補の相対左 Kan 条件は全 fiber の標準 U 余極限性と同値。
方針：同じ指定変換の輸送の選択不変性で標準局所輸送へ戻し、fiber の判定を使う。
規約：候補に付随する指定変換そのものを保つ。
使われ方：元の Kan 条件と相対 join の局所条件を双方向に比較する。 -/
lemma kanLeftCommaCandidate_isRelativeLeftKanExtension_iff {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀) :
    IsRelativeLeftKanExtension U δ F₀ (kanLeftCommaCandidate δ H)
        (kanLeftCommaCandidateTransformation δ F₀ H hH) ↔
      ∀ c : C _⦋0⦌,
        IsRelativeColimitCone U (kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H) := by
  constructor
  · intro h c
    obtain ⟨t, ht⟩ := h c
    have hs := (kanLeftTransport_isRelativeColimit_iff U t
      (kanLeftCommaCoconeTransport δ F₀ H hH c)).1 ht
    exact (kanLeftCommaCoconeTransport_isRelativeColimit_iff U δ F₀ H hH c).1 hs
  · exact kanLeftCommaCandidate_isRelativeLeftKanExtension U δ F₀ H hH

end SerrePositivity.InfinityCategories.F1B
