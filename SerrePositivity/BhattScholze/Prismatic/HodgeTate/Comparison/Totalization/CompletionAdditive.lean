module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletionBounds
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import Mathlib.CategoryTheory.Preadditive.Comma

/-!
# 指定された複体の完備化関手の加法性

## 概要
既存の主元完備化関手を余鎖図式へ施すため、その加法性を明示する。

## 方針
各 Koszul 段、可算直積、差分の Arrow 関手、写像錐の射の加法性を順に使う。

## 規約
完備化の模型・単位・遷移を置き換えない。全て既存の関手の法則である。

## 使われ方
BS 著者版 Lemma 4.22 の行ごとの完備化と積全複体の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.homotopyCofiber
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

/-- 既存の全 Koszul 段の直積関手は加法的である。 -/
instance powerKoszulProduct_additive (a : R) :
    (complexPowerKoszulProductFunctor R a).Additive where
  map_add {K M} f g := by
    dsimp only [complexPowerKoszulProductFunctor]
    apply Pi.hom_ext
    intro n
    simp only [Preadditive.add_comp, complexTowerProductMap_projection,
      Functor.map_add, Preadditive.comp_add]

/-- 既存の直積の差分を取る Arrow 関手は加法的である。 -/
instance powerKoszulDifference_additive (a : R) :
    (complexPowerKoszulDifferenceFunctor R a).Additive where
  map_add {K M} f g := by
    apply Arrow.hom_ext
    · exact (complexPowerKoszulProductFunctor R a).map_add (f := f) (g := g)
    · exact (complexPowerKoszulProductFunctor R a).map_add (f := f) (g := g)

/-- 既存の写像錐関手の射は、左成分では一つ上の次数の射となる。 -/
@[reassoc] theorem completionCone_inl_map {X Y : Arrow (CochainComplex (ModuleCat.{u} R) ℤ)} (f : X ⟶ Y) (i : ℤ) :
    inlX X.hom (i + 1) i rfl ≫ ((cochainMappingConeFunctor R).map f).f i =
      f.left.f (i + 1) ≫ inlX Y.hom (i + 1) i rfl := by
  dsimp only [cochainMappingConeFunctor]
  rw [mapArrowHom, inlX_desc_f _ _ _ _ _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
  simp [Homotopy.trans, Homotopy.ofEq, Homotopy.compLeft,
    inrCompHomotopy_hom _ _ _ _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]

/-- 既存の写像錐関手の射は、右成分では同じ次数の射となる。 -/
@[reassoc] theorem completionCone_inr_map {X Y : Arrow (CochainComplex (ModuleCat.{u} R) ℤ)} (f : X ⟶ Y) (i : ℤ) :
    inrX X.hom i ≫ ((cochainMappingConeFunctor R).map f).f i =
      f.right.f i ≫ inrX Y.hom i := by
  dsimp only [cochainMappingConeFunctor]
  rw [mapArrowHom, inrX_desc_f]
  rfl

/-- 既存の Arrow 圏上の写像錐関手は加法的である。 -/
instance completionCone_additive : (cochainMappingConeFunctor R).Additive where
  map_add {X Y} f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ext_from_X X.hom (i + 1) i (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)
    · simp [HomologicalComplex.add_f_apply, Preadditive.comp_add,
        completionCone_inl_map, Preadditive.add_comp]
    · simp [HomologicalComplex.add_f_apply, Preadditive.comp_add,
        completionCone_inr_map, Preadditive.add_comp]

/-- 同じ主元完備化関手は加法的であり、余鎖図式へ施せる。 -/
instance complexCompletion_additive (a : R) : (complexCompletionFunctor R a).Additive := by
  dsimp only [complexCompletionFunctor]
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
