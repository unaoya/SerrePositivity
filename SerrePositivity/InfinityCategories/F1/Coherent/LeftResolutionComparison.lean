module

public import SerrePositivity.InfinityCategories.F1.Coherent.LeftResolutionEnriched
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedComparisonIso

/-!
概要：左 Hom の具体的な解像と恒等の空間値関手の大域的な比較。
方針：標準比較のパラメーター付き自然性を二点図式で実現し、各成分の同値性を使う。
規約：任意の coherent な空間値図式に引き戻せる関手空間内の同型を構成する。
使われ方：Kerodon Corollary 5.6.0.6、左 fiber の具体的な模型の高次の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：左解像への標準比較は恒等豊穣関手から左解像への豊穣な比較。
方針：内部 Hom の評価に対するパラメーター付きの可換式を使う。
規約：各成分は構成済みの coherentLeftResolutionComparison。
使われ方：Kerodon Corollary 5.6.0.6、coherent な大域的な比較の入力。 -/
noncomputable def coherentLeftResolutionKanComparison :
    KanEnrichedComparison (EnrichedFunctor.id SSet.{u} KanObject.{u})
      coherentLeftResolutionKanEnriched := by
  refine ⟨(fun X ↦ show X ⟶ coherentLeftResolutionKanEnriched.obj X from
    coherentLeftResolutionComparison X.obj), ?_⟩
  intro X Y
  change (coherentLeftResolutionComparison X.obj ▷ (ihom X.obj).obj Y.obj) ≫
      uncurry (coherentLeftResolutionEnrichedMap X.obj Y.obj) =
    uncurry (𝟙 ((ihom X.obj).obj Y.obj)) ≫ coherentLeftResolutionComparison Y.obj
  rw [coherentLeftResolutionEnrichedMap, uncurry_curry]
  exact coherentLeftResolutionParameterizedMap_comparison _

/-- 概要：左解像の豊穣自己関手が空間の coherent nerve に誘導する自己写像。
方針：構成した高次の Hom の作用に coherent nerve を適用する。
規約：対象では左 fiber の具体的な旗の模型を使う。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式の左解像への置き換え。 -/
noncomputable def coherentLeftResolutionInfinityMap : SpaceInfinity.{u} ⟶ SpaceInfinity.{u} :=
  coherentNerveMap coherentLeftResolutionKanEnriched

/-- 概要：空間の恒等写像と左解像の自己写像は大域的に関手同型。
方針：標準比較の豊穣な実現と各 Kan 複体での比較の同値性を使う。
規約：対象ごとの同値の族でなく関手空間内の同型。
使われ方：Kerodon Corollary 5.6.0.6、左 fiber の比較の証明を一般の図式へ移す。 -/
noncomputable def coherentLeftResolutionInfinityComparisonIso :
    FunctorIso (𝟙 SpaceInfinity.{u}) coherentLeftResolutionInfinityMap.{u} := by
  have h := kanEnrichedComparisonIso coherentLeftResolutionKanComparison
    (fun X ↦ coherentLeftResolutionComparison_isQCatEquivalence X.obj)
  rw [coherentNerveMap_id] at h
  exact h

/-- 概要：左解像の自己写像は空間の coherent nerve の同値。
方針：恒等写像を逆とし、大域的な標準比較の関手同型を両合成の条件に使う。
規約：順方向は構成した左解像の豊穣作用の coherent nerve。
使われ方：Kerodon Corollary 5.6.0.6、左解像の模型への自然な移送の同値データ。 -/
noncomputable def coherentLeftResolutionInfinityEquivalence :
    QCatEquivalence SpaceInfinity.{u} SpaceInfinity.{u} where
  hom := coherentLeftResolutionInfinityMap
  inv := 𝟙 _
  homInvIso := by
    rw [Category.comp_id]
    exact coherentLeftResolutionInfinityComparisonIso.symm
  invHomIso := by
    rw [Category.id_comp]
    exact coherentLeftResolutionInfinityComparisonIso.symm

/-- 概要：任意の coherent な空間値図式は、その値を左解像に置き換えた図式と関手同型。
方針：大域的な比較を元の図式で引き戻す。
規約：底の quasicategory 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6、左 fiber の具体的な模型を用いる復元比較の高次の整合性。 -/
noncomputable def coherentLeftResolutionDiagramComparisonIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) : FunctorIso F (F ≫ coherentLeftResolutionInfinityMap) := by
  have h := coherentLeftResolutionInfinityComparisonIso.precomp F
  rw [Category.comp_id] at h
  exact h

end SerrePositivity.InfinityCategories
