module
public import SerrePositivity.KST.SConstruction.SpectrumFixedFactorEvaluation

/-! # 元の全 BF 辺の各段定数性を両 whisker へ移す
概要：元の BF 辺の段評価が定数なら、固定因子との両実合成辺の同じ段評価も定数。
方針：元の全辺の合成式と固定因子の評価式を、同じ全実射の等号として合成する。
規約：全一単体の像を保持し、段の頂点だけの比較にはしない。
使われ方：三入力 BF 比較の元の三辺を零段で定数として回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance whiskerEvaluationPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance whiskerEvaluationSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の全比較辺の定数な段評価を、固定第一因子との同じ実合成へ移す。 -/
lemma spectrumComparisonLeftWhisker_constant {W X Y Z : OmegaSpectrum.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (gh : X ⟶ Z)
    (e : (SimplicialCategory.sHom X Z).Edge (SimplicialCategory.homEquiv' _ _ gh)
      (SimplicialCategory.homEquiv' _ _ (g ≫ h))) (n : ℕ)
    (he : ∃ v, SSet.yonedaEquiv.symm e.edge ≫ OmegaSpectrum.evaluation X Z n = SSet.const v) :
    ∃ v, SSet.yonedaEquiv.symm (enrichedComparisonLeftWhisker f g h gh e).edge ≫
      OmegaSpectrum.evaluation W Z n = SSet.const v := by
  obtain ⟨v, hv⟩ := he
  let P := lift (SSet.const ((OmegaSpectrum.evaluation W X n).app (Opposite.op ⦋0⦌)
    (SimplicialCategory.homEquiv' _ _ f))) (𝟙 _) ≫
      eComp SSet (W.level n).space (X.level n).space (Z.level n).space
  refine ⟨P.app (Opposite.op ⦋0⦌) v, ?_⟩
  calc
    _ = (SSet.yonedaEquiv.symm e.edge ≫ enrichedFixedLeftComposition f) ≫
        OmegaSpectrum.evaluation W Z n :=
      congrArg (· ≫ OmegaSpectrum.evaluation W Z n)
        (enrichedComparisonLeftWhisker_map f g h gh e)
    _ = (SSet.yonedaEquiv.symm e.edge ≫ OmegaSpectrum.evaluation X Z n) ≫ P :=
      (Category.assoc _ _ _).trans
        ((congrArg (SSet.yonedaEquiv.symm e.edge ≫ ·)
          (spectrumFixedLeftComposition_evaluation f n)).trans (Category.assoc _ _ _).symm)
    _ = SSet.const v ≫ P := congrArg (· ≫ P) hv
    _ = _ := SSet.const_comp v P

/-- 元の全比較辺の定数な段評価を、固定最終因子との同じ実合成へ移す。 -/
lemma spectrumComparisonRightWhisker_constant {W X Y Z : OmegaSpectrum.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y)
    (e : (SimplicialCategory.sHom W Y).Edge (SimplicialCategory.homEquiv' _ _ fg)
      (SimplicialCategory.homEquiv' _ _ (f ≫ g))) (n : ℕ)
    (he : ∃ v, SSet.yonedaEquiv.symm e.edge ≫ OmegaSpectrum.evaluation W Y n = SSet.const v) :
    ∃ v, SSet.yonedaEquiv.symm (enrichedComparisonRightWhisker f g h fg e).edge ≫
      OmegaSpectrum.evaluation W Z n = SSet.const v := by
  obtain ⟨v, hv⟩ := he
  let P := lift (𝟙 _) (SSet.const ((OmegaSpectrum.evaluation Y Z n).app (Opposite.op ⦋0⦌)
    (SimplicialCategory.homEquiv' _ _ h))) ≫
      eComp SSet (W.level n).space (Y.level n).space (Z.level n).space
  refine ⟨P.app (Opposite.op ⦋0⦌) v, ?_⟩
  calc
    _ = (SSet.yonedaEquiv.symm e.edge ≫ enrichedFixedRightComposition h) ≫
        OmegaSpectrum.evaluation W Z n :=
      congrArg (· ≫ OmegaSpectrum.evaluation W Z n)
        (enrichedComparisonRightWhisker_map f g h fg e)
    _ = (SSet.yonedaEquiv.symm e.edge ≫ OmegaSpectrum.evaluation W Y n) ≫ P :=
      (Category.assoc _ _ _).trans
        ((congrArg (SSet.yonedaEquiv.symm e.edge ≫ ·)
          (spectrumFixedRightComposition_evaluation h n)).trans (Category.assoc _ _ _).symm)
    _ = SSet.const v ≫ P := congrArg (· ≫ P) hv
    _ = _ := SSet.const_comp v P

end SerrePositivity.KST.SConstruction
