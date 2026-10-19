module

public import SerrePositivity.InfinityCategories.F1B.KanLocalRelativeJoinConeEndpoint
public import SerrePositivity.InfinityCategories.F1B.KanJoinPrismFixed
public import SerrePositivity.InfinityCategories.Stable.InitialBoundaryTransport
public import SerrePositivity.InfinityCategories.Stable.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Stable.ColimitDiagramIso

/-!
概要：comma fiber の普遍余錐から候補の局所余錐の余極限性を導く。
方針：標準局所比較への制限と、図式・頂点を固定した関手同型で普遍性を移す。
規約：元の関手に fibration 性は要求しない。
使われ方：点ごとの余極限から左 Kan 拡張を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：余錐全体の関手同型は余極限性を保つ。
方針：余錐制限の相対始点境界充填を関手同型で移送する。
規約：直線化に依存する余錐の評価のモジュールを import しない。
使われ方：固定図式上の局所比較から余極限性を移す。 -/
lemma kanIsColimitCone_of_functorIso {A D : SSet.{u}} [Quasicategory D]
    {p q : A ⟶ D} {c : JoinCocone p} {d : JoinCocone q}
    (hc : IsColimitCone c) (e : FunctorIso c.val d.val) : IsColimitCone d := by
  apply isColimitCone_of_initialBoundaryLifting_coconeRestriction d
  exact InitialBoundaryLifting.of_vertexIso (coconeRestriction A D) hc.initialBoundaryLifting e

/-- 概要：標準局所輸送の余錐と fiber の余錐の制限は全余錐の関手圏で同型。
方針：局所比較の始端と終端を計算し、両因子を固定する円柱の同型判定を使う。
規約：同型は頂点だけでなく余錐全体を比較する。
使われ方：余極限性の移送。 -/
def kanLeftCommaCoconeTransport_functorIso {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀)
    (c : C _⦋0⦌) :
    FunctorIso (kanLeftCommaCoconeTransport δ F₀ H hH c).cocone.val
      ((kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H).restrict
        (kanLeftKanShapeToCommaFiber δ c)).val := by
  let P := kanLocalRelativeJoinConeComparison δ c ≫ H
  let e := kanJoinPrism_fixed_functorIso P (leftKanDiagram δ F₀ c)
    (SSet.yonedaEquiv.symm c ≫ kanLeftCommaCandidate δ H)
    (by
      rw [← Category.assoc]
      exact kanLocalRelativeJoinConeComparison_diagram δ F₀ H hH c)
    (by
      rw [← Category.assoc]
      exact kanLocalRelativeJoinConeComparison_vertex δ H c)
  exact kanFunctorIsoTransport e (kanLocalRelativeJoinConeComparison_zero δ F₀ H hH c)
    (kanLocalRelativeJoinConeComparison_one δ H c)

/-- 概要：各点の fiber の余錐が普遍なら候補の標準局所輸送の余錐も普遍。
方針：標準局所比較に沿う制限は前合成同値で、比較円柱は全余錐の関手同型となる。
規約：標準局所比較の同値性に K と C の quasicategory 性を使う。
使われ方：候補が点ごとの左 Kan 条件を満たすことの証明。 -/
lemma kanLeftCommaCoconeTransport_isColimit {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀)
    (c : C _⦋0⦌) (hc : IsColimitCone (kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H)) :
    IsColimitCone (kanLeftCommaCoconeTransport δ F₀ H hH c).cocone := by
  let d := vertexFiberι (kanLeftCommaProjection δ) c ≫
    relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H
  let a := kanLeftKanShapeToCommaFiber δ c
  have : TrivialKanFibration (sliceUnderRestrict d a) :=
    sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence d a
      (kanLeftKanShapeToCommaFiber_isPrecompositionEquivalence δ c)
  have hcr : IsColimitCone
      ((kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H).restrict a) :=
    ((qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict d a)).isInitialVertex_iff
      (kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H)).1 hc
  exact kanIsColimitCone_of_functorIso hcr (kanLeftCommaCoconeTransport_functorIso δ F₀ H hH c).symm

/-- 概要：各 fiber で普遍な相対 join の図式の候補は元の関手に沿う左 Kan 拡張。
方針：構成した標準局所輸送の余錐の余極限性を全頂点で使う。
規約：指定変換は元の K への制限から抽出したもの。
使われ方：点ごとの余極限の存在からの左 Kan 拡張の組み立て。 -/
lemma kanLeftCommaCandidate_isLeftKanExtension {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀)
    (hc : ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H)) :
    IsLeftKanExtension δ F₀ (kanLeftCommaCandidate δ H)
      (kanLeftCommaCandidateTransformation δ F₀ H hH) := by
  intro c
  exact ⟨kanLeftCommaCoconeTransport δ F₀ H hH c,
    kanLeftCommaCoconeTransport_isColimit δ F₀ H hH c (hc c)⟩

/-- 概要：局所添字の図式の余極限が各点で存在すれば左 Kan 拡張が存在する。
方針：coherent な fiber の普遍余錐の図式を構成し候補の左 Kan 条件を証明する。
規約：K・C・D は同じ宇宙の quasicategory、δ は任意。
使われ方：Kerodon §7.3.5 の点ごとの存在からの組み立て。 -/
lemma exists_kanLeftExtension_of_local_colimits {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, HasColimit (leftKanDiagram δ F₀ c)) :
    ∃ (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)), IsLeftKanExtension δ F₀ F β := by
  obtain ⟨H, hH, hc⟩ := exists_kanLeftComma_diagram_with_colimit_fibers δ F₀ hcol
  exact ⟨kanLeftCommaCandidate δ H, kanLeftCommaCandidateTransformation δ F₀ H hH,
    kanLeftCommaCandidate_isLeftKanExtension δ F₀ H hH hc⟩

/-- 概要：左 Kan 拡張の存在は各点の標準局所図式の余極限の存在と同値。
方針：必要性は点ごとの値、十分性は coherent な普遍余錐の組み立てを使う。
規約：K・C・D は同じ宇宙の quasicategory。
使われ方：左 Kan 拡張の存在の点ごとの判定。 -/
lemma exists_kanLeftExtension_iff_local_colimits {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C) (F₀ : K ⟶ D) :
    (∃ (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)), IsLeftKanExtension δ F₀ F β) ↔
      ∀ c : C _⦋0⦌, HasColimit (leftKanDiagram δ F₀ c) := by
  constructor
  · rintro ⟨F, β, h⟩ c
    obtain ⟨t, ht, _⟩ := h.colimitValue c
    exact ⟨t, ht⟩
  · exact exists_kanLeftExtension_of_local_colimits δ F₀

end SerrePositivity.InfinityCategories.F1B
