module

public import SerrePositivity.InfinityCategories.F1.Coherent.StraighteningFamilyCounit
public import SerrePositivity.InfinityCategories.F1.Coherent.StraighteningFamilyBaseChange

/-!
概要：族の選択分類と、普遍図式の再構成の実際の制限を接続する。
方針：積の底上の cartesian な表現の比較を curry する。
規約：任意のパラメーター単体集合に一つの関手同型を与える。
使われ方：全図式の普遍族の比較を指定した族の分類へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：制限した族の選択分類と元の族の分類の制限は関手同型。
方針：積の底上の比較と内部 currying の自然性を使う。
規約：パラメーターも制限射も任意。
使われ方：分類の高次パラメーターの制限に対する比較。 -/
def coherentStraighteningFamilyRestrictionIso {B K L : SSet.{u + 1}}
    (t : K ⟶ (ihom B).obj SpaceInfinity.{u}) (i : L ⟶ K) :
    FunctorIso
      (curry (smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection (uncurry (i ≫ t)))
        (leftUnstraighteningProjection_hasSmallSimplexFibers _)))
      (i ≫ curry (smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection (uncurry t))
        (leftUnstraighteningProjection_hasSmallSimplexFibers _))) :=
  coherentStraighteningFamilyBaseChangeIso (uncurry (i ≫ t)) (uncurry t) i
    (uncurry_natural_left i t).symm

/-- 概要：指定した族の分類は普遍再構成の実際の制限と関手同型。
方針：恒等関手が表す普遍図式にパラメーター制限の比較を適用する。
規約：選択した全空間の表現を経由する比較であり点ごとの同型の族ではない。
使われ方：普遍余単位を指定した族の分類に接続する。 -/
def coherentStraighteningFamilyUniversalIso {B K : SSet.{u + 1}}
    (t : K ⟶ (ihom B).obj SpaceInfinity.{u}) :
    FunctorIso
      (curry (smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection (uncurry t))
        (leftUnstraighteningProjection_hasSmallSimplexFibers _)))
      (t ≫ universalCoherentReconstructionMap B) := by
  let U := uncurry (𝟙 ((ihom B).obj SpaceInfinity.{u}))
  have h : (B ◁ t) ≫ U = uncurry t := by
    rw [← uncurry_natural_left, Category.comp_id]
  exact coherentStraighteningFamilyBaseChangeIso (uncurry t) U t h

end SerrePositivity.InfinityCategories
