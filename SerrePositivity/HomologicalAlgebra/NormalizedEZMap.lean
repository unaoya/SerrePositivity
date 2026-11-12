module
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedEZHomotopy

/-!
概要：整数係数の指定 EZ ホモトピーを加法関手で運び、元の Moore 正規化へ戻す。
方針：Functor.mapHomotopy と指定 Moore 比較同型による前後合成を使う。
規約：平坦性を仮定しない。テンソル側は移した元のテンソルを保持する。
使われ方：HA 1.2.4、G10 の係数拡大後の正規化テンソル／積重み比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory AlgebraicTopology HomologicalComplex
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.HomologicalAlgebra
variable {B : Type v} [Category.{w} B] [Abelian B]
variable (F : ModuleCat.{u} ℤ ⥤ B) [F.Additive]
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 元の Moore 正規化から移したテンソルへの指定 AW 射。 -/
def mappedNormalizedAlexanderWhitney :
    (normalizedMooreComplex B).obj (simplicialIntegerTensor C D ⋙ F) ⟶
      (F.mapHomologicalComplex (.down ℕ)).obj
        (chainIntegerTensor ((normalizedMooreComplex _).obj C)
          ((normalizedMooreComplex _).obj D)) :=
  (normalizedMooreMapIso F (simplicialIntegerTensor C D)).inv ≫
    (F.mapHomologicalComplex (.down ℕ)).map (normalizedAlexanderWhitney C D)

/-- 移したテンソルから元の Moore 正規化への指定 shuffle 射。 -/
def mappedNormalizedShuffle :
    (F.mapHomologicalComplex (.down ℕ)).obj
        (chainIntegerTensor ((normalizedMooreComplex _).obj C)
          ((normalizedMooreComplex _).obj D)) ⟶
      (normalizedMooreComplex B).obj (simplicialIntegerTensor C D ⋙ F) :=
  (F.mapHomologicalComplex (.down ℕ)).map (normalizedShuffle C D) ≫
    (normalizedMooreMapIso F (simplicialIntegerTensor C D)).hom

/-- 指定 AW と shuffle の合成は同じ正規化複体の恒等と鎖ホモトピック。 -/
def mappedNormalizedEZHomotopy :
    Homotopy (𝟙 _) (mappedNormalizedAlexanderWhitney F C D ≫
      mappedNormalizedShuffle F C D) := by
  let e := normalizedMooreMapIso F (simplicialIntegerTensor C D)
  let h := ((F.mapHomotopy (normalizedEZHomotopy C D)).compLeft e.inv).compRight e.hom
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · change 𝟙 _ = (e.inv ≫ (F.mapHomologicalComplex (.down ℕ)).map (𝟙 _)) ≫ e.hom
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id]
  · dsimp only [mappedNormalizedAlexanderWhitney, mappedNormalizedShuffle, e]
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]

/-- 移した shuffle は両入力の全単体的射について自然。 -/
theorem mappedNormalizedShuffle_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') :
    (F.mapHomologicalComplex (.down ℕ)).map
        (chainIntegerTensorMap ((normalizedMooreComplex _).map f)
          ((normalizedMooreComplex _).map g)) ≫ mappedNormalizedShuffle F C' D' =
      mappedNormalizedShuffle F C D ≫
        (normalizedMooreComplex B).map
          (CategoryTheory.Functor.whiskerRight (simplicialIntegerTensorMap f g) F) := by
  dsimp only [mappedNormalizedShuffle]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, normalizedShuffle_naturality,
    CategoryTheory.Functor.map_comp, Category.assoc]
  change _ ≫ (F.mapHomologicalComplex (.down ℕ)).map
      ((normalizedMooreComplex _).map (simplicialIntegerTensorMap f g)) ≫
      normalizedMooreMapHom F _ = (_ ≫ normalizedMooreMapHom F _) ≫ _
  rw [normalizedMooreMapHom_naturality, Category.assoc]

/-- 移した AW は両入力の全単体的射について自然。 -/
theorem mappedNormalizedAlexanderWhitney_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') :
    (normalizedMooreComplex B).map
        (CategoryTheory.Functor.whiskerRight (simplicialIntegerTensorMap f g) F) ≫
        mappedNormalizedAlexanderWhitney F C' D' =
      mappedNormalizedAlexanderWhitney F C D ≫
        (F.mapHomologicalComplex (.down ℕ)).map
          (chainIntegerTensorMap ((normalizedMooreComplex _).map f)
            ((normalizedMooreComplex _).map g)) := by
  dsimp only [mappedNormalizedAlexanderWhitney]
  have h := (normalizedMooreMapNatIso F).inv.naturality (simplicialIntegerTensorMap f g)
  change (normalizedMooreComplex B).map
      (CategoryTheory.Functor.whiskerRight (simplicialIntegerTensorMap f g) F) ≫
      (normalizedMooreMapIso F _).inv =
    (normalizedMooreMapIso F _).inv ≫
      (F.mapHomologicalComplex (.down ℕ)).map
        ((normalizedMooreComplex _).map (simplicialIntegerTensorMap f g)) at h
  rw [← Category.assoc, h, Category.assoc, ← CategoryTheory.Functor.map_comp,
    normalizedAlexanderWhitney_naturality, CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.HomologicalAlgebra
