module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.UnderSourceVertex
public import SerrePositivity.HomologicalAlgebra.StandardSimplexWeight
public import SerrePositivity.HomologicalAlgebra.BarWeightProjective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.UnderSourceVertex
import all SerrePositivity.HomologicalAlgebra.UnderNerveWeight
import all SerrePositivity.HomologicalAlgebra.StandardSimplexWeight

/-!
# 指定された bar／標準単体の線形重みの比較

## 概要
元の先頭頂点作用素で、bar 重みから標準単体の重みへの全自然比較を構成する。

## 方針
同じ増大を保つことを照合し、射影分解の比較の一意性から同じ射の鎖ホモトピー同値を得る。

## 規約
任意に選んだ比較射を前向きの射には使わない。選択は後向きの持ち上げとホモトピーのみ。

## 使われ方
HTT 4.2.4.1、HA 1.2.4、Weibel §2.2。実現複体と native bar の計算比較の線形入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]

/-- 元の先頭頂点作用素から得る、全対象・全単体に自然な線形重みの比較。 -/
def barStandardWeightComparison (P : C) :
    coefficientBarWeight SimplexCategoryᵒᵖ P ⟶ standardSimplexWeight P where
  app n :=
    { app x := (copowerFunctor P).map (↾fun τ => underSourceVertex τ)
      naturality {x y} f := by
        change (copowerFunctor P).map _ ≫ (copowerFunctor P).map _ =
          (copowerFunctor P).map _ ≫ (copowerFunctor P).map _
        rw [← (copowerFunctor P).map_comp, ← (copowerFunctor P).map_comp]
        congr 1 }
  naturality {n m} r := by
    apply NatTrans.ext
    funext x
    change (copowerFunctor P).map _ ≫ (copowerFunctor P).map _ =
      (copowerFunctor P).map _ ≫ (copowerFunctor P).map _
    rw [← (copowerFunctor P).map_comp, ← (copowerFunctor P).map_comp]
    congr 1
    apply ConcreteCategory.hom_ext
    intro τ
    exact underSourceVertex_whisker τ r.unop

/-- 比較は同じ係数の増大を全単体で厳密に保つ。 -/
theorem barStandardWeightComparison_augmentation (P : C) :
    barStandardWeightComparison P ≫ standardSimplexWeightAugmentation P =
      coefficientBarWeightAugmentation SimplexCategoryᵒᵖ P := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext x
  change (copowerFunctor P).map _ ≫ (copowerFunctor P).map _ = (copowerFunctor P).map _
  rw [← (copowerFunctor P).map_comp]
  congr 1
  exact terminal.hom_ext _ _

/-- 同じ増大頂点を恒等射で保つ、増大線形重みの比較。 -/
def barStandardWeightAugmentedMap (P : C) :
    coefficientBarWeightAugmented SimplexCategoryᵒᵖ P ⟶ standardSimplexWeightAugmented P where
  left := barStandardWeightComparison P
  right := 𝟙 _
  w := by
    dsimp only [coefficientBarWeightAugmented, standardSimplexWeightAugmented]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact barStandardWeightComparison_augmentation P

/-- 交代面複体の実際の比較射も同じ鎖増大を保つ。 -/
theorem barStandardWeightComparison_chain_π [Preadditive C] [HasZeroObject C] (P : C) :
    (alternatingFaceMapComplex _).map (barStandardWeightComparison P) ≫
        AlternatingFaceMapComplex.ε.app (standardSimplexWeightAugmented P) =
      AlternatingFaceMapComplex.ε.app (coefficientBarWeightAugmented SimplexCategoryᵒᵖ P) := by
  have h := AlternatingFaceMapComplex.ε.naturality (barStandardWeightAugmentedMap P)
  change (alternatingFaceMapComplex _).map (barStandardWeightComparison P) ≫
    AlternatingFaceMapComplex.ε.app (standardSimplexWeightAugmented P) =
    AlternatingFaceMapComplex.ε.app (coefficientBarWeightAugmented SimplexCategoryᵒᵖ P) ≫
      (ChainComplex.single₀ _).map (𝟙 _) at h
  rw [CategoryTheory.Functor.map_id] at h
  exact h.trans (Category.comp_id _)

/-- 元の先頭頂点比較を前向きの射とする、線形重みの同じ鎖ホモトピー同値。 -/
def barStandardWeightHomotopyEquiv [Abelian C] (P : C) [Projective P] :
    HomotopyEquiv (coefficientBarWeightResolution SimplexCategoryᵒᵖ P).complex
      (standardSimplexWeightResolution P).complex where
  hom := (alternatingFaceMapComplex _).map (barStandardWeightComparison P)
  inv := ProjectiveResolution.lift (𝟙 _) (standardSimplexWeightResolution P)
    (coefficientBarWeightResolution SimplexCategoryᵒᵖ P)
  homotopyHomInvId := by
    apply ProjectiveResolution.liftHomotopy (𝟙 _)
      (P := coefficientBarWeightResolution SimplexCategoryᵒᵖ P)
      (Q := coefficientBarWeightResolution SimplexCategoryᵒᵖ P)
    · simp only [Category.assoc, ProjectiveResolution.lift_commutes,
        CategoryTheory.Functor.map_id, Category.comp_id]
      exact barStandardWeightComparison_chain_π P
    · simp
  homotopyInvHomId := by
    apply ProjectiveResolution.liftHomotopy (𝟙 _)
      (P := standardSimplexWeightResolution P) (Q := standardSimplexWeightResolution P)
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => ProjectiveResolution.lift (𝟙 _)
          (standardSimplexWeightResolution P)
          (coefficientBarWeightResolution SimplexCategoryᵒᵖ P) ≫ f)
          (barStandardWeightComparison_chain_π P)).trans
            (ProjectiveResolution.lift_commutes _ _ _))
    · simp

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
