module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionStrictDiagram
public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionInitialBase
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：strict な under 切断図式を、元の積上の fibration の同じ添字での値へ評価する。
方針：恒等射への left anodyne な制限と、元の頂点のグラフへの同型を合成する。
規約：元の底と指定した添字を保ち、追加の同値性仮定を置かない。
使われ方：coherent 図式と strict 図式の大域比較の各値での照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 同じ恒等射での評価を、元の添字での同じ引き戻しへ正規化する。 -/
def underSectionEvaluate (i : I) :
    underSectionFamily p i ⟶ pullback p (underSectionFiberBase B i) :=
  parametrizedSectionsPointRestriction p
    (sectionFamilyProductBase B (nerveMap (Under.forget i))) (nervePoint (Under.mk (𝟙 i))) ≫
      (pullback.congrHom rfl (underSectionInitialBase B i)).hom

/-- 同じ評価は元の底への射影を厳密に保つ。 -/
lemma underSectionEvaluate_projection (i : I) :
    underSectionEvaluate p i ≫ pullback.snd p (underSectionFiberBase B i) =
      underSectionFamilyProjection p i := by
  simp only [underSectionEvaluate, Category.assoc, pullback.congrHom,
    asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id,
    parametrizedSectionsPointRestriction_projection]
  rfl

/-- 元の値写像は、同じ初頂点への制限と元の関手評価の合成。 -/
lemma underSectionEvaluate_map (i : I) :
    underSectionEvaluate p i ≫ pullback.fst p (underSectionFiberBase B i) =
      parametrizedSectionsMap p (sectionFamilyProductBase B (nerveMap (Under.forget i))) ≫
        (pre (nervePoint (Under.mk (𝟙 i)))).app E ≫ (pointFunctorEvaluationIso E).hom := by
  simp only [underSectionEvaluate, Category.assoc, pullback.congrHom,
    asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  exact parametrizedSectionsPointRestriction_map _ _ _

/-- 同じ恒等射での評価は全境界を持ち上げる。 -/
lemma underSectionEvaluate_trivialKanFibration [LeftFibration p] (i : I) :
    TrivialKanFibration (underSectionEvaluate p i) := by
  have h := parametrizedSectionsPointRestriction_trivialKanFibration p
    (sectionFamilyProductBase B (nerveMap (Under.forget i))) (nervePoint (Under.mk (𝟙 i)))
    (nervePoint_leftAnodyne (Under.mkIdInitial (X := i)))
  exact ⟨trivialKanFibrations.comp_mem _ _ h.mem (MorphismProperty.rlp_of_isIso _ _)⟩

instance underSectionFiberProjection_leftFibration [LeftFibration p] (i : I) :
    LeftFibration (pullback.snd p (underSectionFiberBase B i)) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := p))⟩

instance underSectionFiber_quasicategory [Quasicategory B] [LeftFibration p] (i : I) :
    Quasicategory (pullback p (underSectionFiberBase B i)) :=
  quasicategory_of_innerFibration (pullback.snd p (underSectionFiberBase B i))

/-- 元の底が ∞ 圏なら、元の同じ評価射そのものが同値。 -/
lemma underSectionEvaluate_isQCatEquivalence [Quasicategory B] [LeftFibration p] (i : I) :
    IsQCatEquivalence (underSectionEvaluate p i) := by
  have := underSectionEvaluate_trivialKanFibration p i
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.F2.Ind
