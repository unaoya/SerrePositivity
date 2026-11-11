module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantHammockValue
public import SerrePositivity.EInfinity.BarrattEccles.DKMappingComponentsValue
public import SerrePositivity.EInfinity.BarrattEccles.DKHammockComparisonFactorization
public import SerrePositivity.EInfinity.SimplicialLocalization.DKHammockComponentsValue

/-!
# 元の実 DK/Map^h 高次比較と保存済み π₀ 同値の一致

概要：同じ高次比較から誘導した全連結成分の同値を以前の同値へ同定する。
方針：元の両評価・同じ cofibrant 包含と HomLift・全因子化を使う。
規約：比較・局所化同値・Map^h を選び直さない。
使われ方：E2b γ2 d の全次数の比較と元の射の零次の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite SimplicialLocalization Hammock
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

def cofibrantAlgebraDKHigherPiZeroEquiv :
    SSet.π₀ (localizationHom (cofibrantAlgebraRelativeCategory A)
      (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)) ≃
        SSet.π₀ (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y) :=
  (cofibrantAlgebraDKMappingSpaceComponentsIso A
    (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)).toEquiv.trans
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.equiv (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y))

lemma cofibrantAlgebraDKHigherPiZeroEquiv_eq :
    cofibrantAlgebraDKHigherPiZeroEquiv A X Y = cofibrantAlgebraDKPiZeroEquiv A X Y := by
  let := modelCategory A
  let x := cofibrantAlgebraDKObject A X
  let y := cofibrantAlgebraDKObject A Y
  let B := (cofibrantAlgebraInclusion A).obj X
  let D := (cofibrantAlgebraInclusion A).obj Y
  let raw := cofibrantAlgebraDKMappingSpaceComponentsIso A x y
  let mh := mappingSpaceReducedHammockComponentsIso A B D
  let native := AnodyneComponents.iso
    (dkHammockComparisonIso (cofibrantAlgebraRelativeCategory A) x y)
  let alg := AnodyneComponents.iso (cofibrantAlgebraDKHammockComparisonIso A x y)
  let v := algebraReducedHammockPiZeroValue A B D
  apply Equiv.ext
  intro z
  apply (mappingSpacePiZeroEquiv A (weakEquivalences (operad A).Algebra).Q (op B) D).injective
  have hm := mappingSpaceReducedHammockComponentsIso_value A B D (raw.hom z)
  have hh := ConcreteCategory.congr_hom
    (cofibrantAlgebraDKMappingSpaceComponentsIso_hammock A x y) z
  change mh.hom (raw.hom z) = alg.hom z at hh
  have hf := congrArg AnodyneComponents.map
    (cofibrantAlgebraDKHammockComparisonIso_factorization A x y)
  simp only [AnodyneComponents.map_comp, AnodyneComponents.map_actual,
    ← AnodyneComponents.iso_hom] at hf
  have hfp := ConcreteCategory.congr_hom hf z
  change alg.hom z = SSet.mapπ₀ (cofibrantAlgebraHammockInclusionMap A x y)
    (native.hom z) at hfp
  exact hm.symm.trans ((congrArg v hh).trans ((congrArg v hfp).trans
    ((cofibrantAlgebraHammockInclusionMap_components_value A X Y (native.hom z)).trans
      ((congrArg (cofibrantAlgebraDKHoHomMap A X Y)
        (dkHammockComparisonIso_components_value (cofibrantAlgebraRelativeCategory A) x y z)).trans
          (cofibrantAlgebraDKPiZeroEquiv_value A X Y z).symm))))

end SerrePositivity.EInfinity.BarrattEccles
