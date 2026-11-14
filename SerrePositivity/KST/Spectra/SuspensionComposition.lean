module

public import SerrePositivity.KST.Spectra.PointedEnrichment
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TensorMapping

/-!
概要：suspension の写像空間への作用の単位と合成。
方針：閉構造の評価へ戻して smash の結合子の自然性を使う。
規約：点つき閉構造の豊穣合成に関する等式。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの写像空間の厳密合成。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：suspension は内部 Hom の豊穣単位を保つ。
方針：通常の恒等射への作用と curry' の単位の式を使う。
規約：点つき内部 Hom の射の等式。
使われ方：BF 1978 §2。写像空間の単位律。 -/
theorem suspensionHom_id (X : PointedSimplicialSet.{u}) :
    MonoidalClosed.id X ≫ suspensionHom X X = MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) := by
  simpa only [MonoidalClosed.curry'_id, MonoidalCategory.whiskerLeft_id] using
    suspensionHom_curry' (𝟙 X)

/-- 概要：suspension は内部 Hom の豊穣合成を保つ。
方針：両辺を評価へ戻し、結合子の自然性と評価の式を使う。
規約：全単体次数の合成に関する等式。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの合成の境界整合性。 -/
theorem suspensionHom_comp (X Y Z : PointedSimplicialSet.{u}) :
    MonoidalClosed.comp X Y Z ≫ suspensionHom X Z =
      (suspensionHom X Y ⊗ₘ suspensionHom Y Z) ≫
        MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Z) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.comp PointedSimplicialSet.circle.{u} X Y Z

local instance : SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 概要：suspension の単体的写像空間への作用は単体的合成を保つ。
方針：点つき豊穣合成の保存を、忘却の lax monoidal 比較で移す。
規約：合成の定義域は通常の単体集合の直積。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの合成の境界条件。 -/
theorem suspensionHom_simplicial_comp (X Y Z : PointedSimplicialSet.{u}) :
    eComp SSet X Y Z ≫ (suspensionHom X Z).right =
      ((suspensionHom X Y).right ⊗ₘ (suspensionHom Y Z).right) ≫
        eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Z) := by
  change PointedSimplicialSet.productToSmash _ _ ≫
      (MonoidalClosed.comp X Y Z).right ≫ (suspensionHom X Z).right =
    ((suspensionHom X Y).right ⊗ₘ (suspensionHom Y Z).right) ≫
      PointedSimplicialSet.productToSmash _ _ ≫
        (MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Z)).right
  rw [← Under.comp_right, suspensionHom_comp, Under.comp_right, ← Category.assoc,
    ← PointedSimplicialSet.productToSmash_naturality, Category.assoc]

/-- 概要：suspension の単体的写像空間への作用は単体的単位を保つ。
方針：点つき豊穣単位の保存を忘却の単位比較で移す。
規約：単位は終対象パラメータの射。
使われ方：HTT A.3.3、BF 1978 §2。スペクトルの写像空間の単位。 -/
theorem suspensionHom_simplicial_id (X : PointedSimplicialSet.{u}) :
    eId SSet X ≫ (suspensionHom X X).right = eId SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) := by
  change (PointedSimplicialSet.forgetUnit ≫ (MonoidalClosed.id X).right) ≫
      (suspensionHom X X).right =
    PointedSimplicialSet.forgetUnit ≫ (MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).right
  rw [Category.assoc, ← Under.comp_right, suspensionHom_id]

/-- 概要：suspension は点つき単体集合の単体的豊穣関手。
方針：写像空間への作用と証明済みの単位・合成の保存を束ねる。
規約：通常の suspension の全単体次数での延長。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの Hom の単体的合成。 -/
def suspensionEnrichedFunctor :
    EnrichedFunctor SSet.{u} PointedSimplicialSet.{u} PointedSimplicialSet.{u} where
  obj := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension
  map X Y := (suspensionHom X Y).right
  map_id := suspensionHom_simplicial_id
  map_comp := suspensionHom_simplicial_comp

end

end SerrePositivity.KST.Spectra
