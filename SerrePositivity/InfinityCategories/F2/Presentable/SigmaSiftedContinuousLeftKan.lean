module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaKanCoconeComparison
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalRestrictionHom

/-!
概要：元の sifted 保存関手自身が、P_Σ Yoneda に沿う恒等単位付き全左 Kan 延長。
方針：同じ小さい元の圏に制限した標準 Kan 余錐を、元の密度全余錐の像へ同定する。
規約：元の全余錐を使い、左 Kan 条件を未証明の入力には置かない。
使われ方：保存関手の全部分 ∞ 圏からの、元の Yoneda 制限の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}}
  (G : SigmaPresheafInfinity C ⟶ D) (v : (SigmaPresheafInfinity C) _⦋0⦌)

/-- 標準 Kan 余錐を小さい元の圏へ制限した全写像は、元の密度余錐の同じ像。 -/
lemma sigmaLeftKanCanonicalCocone_restrict_val :
    ((leftKanCanonicalCocone (sigmaYonedaInfinityMap C) G v).restrict
      (sigmaElementsLeftKanComparison v)).val =
        (mapJoinCocone G (sigmaVertexDensityCocone v)).val := by
  change joinMap (sigmaElementsLeftKanComparison v) (𝟙 Δ[0]) ≫
    (slicePullbackCoconeMap (sigmaYonedaInfinityMap C) (SSet.yonedaEquiv.symm v) ≫ G) = _
  rw [← Category.assoc, sigmaElementsLeftKanComparison_coconeMap]
  rfl

/-- 元の sifted 保存関手の、同じ標準局所 Kan 余錐は余極限。 -/
lemma sigmaSiftedContinuous_canonicalColimits [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (hG : PreservesSmallSiftedColimits G) :
    IsColimitCone (leftKanCanonicalCocone (sigmaYonedaInfinityMap C) G v) := by
  apply (isColimitCone_iff_restrict_equivalentShape (sigmaElementsLeftKanComparison v)
    (sigmaElementsLeftKanComparison_isQCatEquivalence v) _).mpr
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _
    (sigmaLeftKanCanonicalCocone_restrict_val G v)).mpr
      (sigmaVertexDensity_image_isColimit v hC G hG)

/-- 元の sifted 保存関手自身は、元の Yoneda による同じ制限の恒等単位付き左 Kan 延長。 -/
lemma sigmaSiftedContinuous_isLeftKanExtension [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (hG : PreservesSmallSiftedColimits G) :
    IsLeftKanExtension (sigmaYonedaInfinityMap C) (sigmaYonedaInfinityMap C ≫ G) G
      (functorHomotopyRefl (sigmaYonedaInfinityMap C ≫ G)) :=
  F1B.kanLeftKanExtension_refl_of_canonicalColimits (sigmaYonedaInfinityMap C) G
    (sigmaSiftedContinuous_canonicalColimits G · hC hG)

end SerrePositivity.InfinityCategories.HomotopyLimits
