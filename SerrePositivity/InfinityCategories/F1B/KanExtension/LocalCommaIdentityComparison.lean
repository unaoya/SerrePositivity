module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaIdentityComparison
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftKanShapeCommaIdentification

/-!
概要：局所 Kan 添字上で元の添字の恒等矢印から標準の comma の矢印への比較を構成する。
方針：oriented comma 内の比較を標準局所比較に沿って制限する。
規約：元の添字を固定し、底への射影は slice の標準変換を保つ。
使われ方：局所余錐の輸送の中間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：局所添字の恒等矢印の族から標準の comma の族への比較。
方針：標準局所比較に沿って comma 内の比較を制限する。
規約：終点は fiber の包含後の標準局所比較。
使われ方：元の図式と fiber の余錐の比較の入力。 -/
def kanLocalCommaIdentityComparison {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    SSet.Homotopy (leftKanProjection δ c ≫ kanLeftCommaInclusion δ)
      (kanLeftKanShapeToCommaFiber δ c ≫ vertexFiberι (kanLeftCommaProjection δ) c) := by
  let a := kanLeftKanShapeToCommaFiber δ c ≫ vertexFiberι (kanLeftCommaProjection δ) c
  let T := functorHomotopyPrecomp (kanLeftCommaIdentityComparison δ) a
  refine { h := T.h, h₀ := ?_, h₁ := T.h₁, rel := T.rel }
  rw [T.h₀, ← Category.assoc]
  change (kanLeftKanShapeToCommaFiber δ c ≫ vertexFiberι (kanLeftCommaProjection δ) c ≫
    kanLeftCommaSource δ) ≫ kanLeftCommaInclusion δ = _
  rw [kanLeftKanShapeToCommaFiber_source]
  rfl

/-- 概要：局所比較中も元の添字は固定される。
方針：大域的な比較の固定条件を前合成し、標準局所比較の射影を使う。
規約：元の添字 K 上の射の等式。
使われ方：局所余錐の図式部分を F₀ に固定する。 -/
lemma kanLocalCommaIdentityComparison_source {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (kanLocalCommaIdentityComparison δ c).h ≫ kanLeftCommaSource δ =
      fst (leftKanShape δ c) Δ[1] ≫ leftKanProjection δ c := by
  change ((kanLeftKanShapeToCommaFiber δ c ≫ vertexFiberι (kanLeftCommaProjection δ) c) ▷
    (Δ[1] : SSet.{u})) ≫ (kanLeftCommaIdentityComparison δ).h ≫ kanLeftCommaSource δ = _
  rw [kanLeftCommaIdentityComparison_source, ← Category.assoc, whiskerRight_fst,
    Category.assoc, Category.assoc, kanLeftKanShapeToCommaFiber_source]

/-- 概要：局所比較の底への射影は slice の標準指定変換。
方針：大域的な比較の射影と comma の持ち上げの変換の回収を使う。
規約：変換の raw な円柱の射が一致する。
使われ方：局所余錐の輸送に使う底の正方形。 -/
lemma kanLocalCommaIdentityComparison_projection {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (kanLocalCommaIdentityComparison δ c).h ≫ kanLeftCommaProjection δ =
      (kanLeftKanShapeHomotopy δ c).h := by
  change ((kanLeftKanShapeToCommaFiber δ c ≫ vertexFiberι (kanLeftCommaProjection δ) c) ▷
    (Δ[1] : SSet.{u})) ≫ (kanLeftCommaIdentityComparison δ).h ≫ kanLeftCommaProjection δ = _
  rw [kanLeftCommaIdentityComparison_projection]
  change (kanLeftCommaLift δ (leftKanProjection δ c) (SSet.const c)
    (kanLeftKanShapeHomotopy δ c) ▷ (Δ[1] : SSet.{u})) ≫ (kanLeftCommaHomotopy δ).h = _
  exact kanLeftCommaLift_homotopy_h δ _ _ _

end SerrePositivity.InfinityCategories.F1B
