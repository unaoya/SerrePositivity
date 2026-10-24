module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianSectionFamilies
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialSectionTransport

/-!
概要：始対象での cocartesian section の fiber 評価に切断を構成する。
方針：fiber 全体をパラメータとする図式を始対象から延長して curry する。
規約：切断は単体集合の射。境界を固定する持ち上げ性は別の課題。
使われ方：一般の strict transport の fiber 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始対象での評価は単体集合の射として切断を持つ。
方針：始対象の fiber の包含を、全 fiber をパラメータとして cocartesian に延長する。
規約：底は quasicategory、射影は cocartesian fibration。
使われ方：評価の任意のパラメータの族に対する全射性。 -/
lemma exists_kanCocartesianSectionsEvaluate_section {A E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hv : IsInitialVertex v) :
    ∃ s : vertexFiber p (a.app (Opposite.op ⦋0⦌) v) ⟶ SerrePositivity.InfinityCategories.cocartesianSections p a,
      s ≫ SerrePositivity.InfinityCategories.cocartesianSectionsEvaluate p a v = 𝟙 _ := by
  obtain ⟨F, hFp, hFi, hFc⟩ := exists_kanInitialSectionTransport p a v hv
    (vertexFiberι p (a.app (Opposite.op ⦋0⦌) v)) (vertexFiberι_comp _ _)
  let s := SerrePositivity.InfinityCategories.cocartesianSectionsCurry F hFp hFc
  refine ⟨s, ?_⟩
  apply (cancel_mono (vertexFiberι p (a.app (Opposite.op ⦋0⦌) v))).1
  rw [Category.assoc, ← SerrePositivity.InfinityCategories.cocartesianSectionsUncurry_evaluate,
    show SerrePositivity.InfinityCategories.cocartesianSectionsUncurry s = F from SerrePositivity.InfinityCategories.cocartesianSectionsUncurry_curry F hFp hFc,
    hFi, Category.id_comp]

end SerrePositivity.InfinityCategories
