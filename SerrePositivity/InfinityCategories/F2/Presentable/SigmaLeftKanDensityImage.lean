module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaLeftKanExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaSiftedContinuousLeftKan
public import SerrePositivity.InfinityCategories.F1B.KanLeftUnitCanonical

/-!
概要：元の左 Kan 延長は、元の指定頂点への全密度余錐を余極限へ送る。
方針：同じ指定単位の可逆性から標準 Kan 余錐を読み、元の比較同値と全写像の一致で戻す。
規約：任意の sifted 余錐の保存性は仮定しない。全密度余錐の像を元のまま保持する。
使われ方：延長の sifted 保存性に必要な、元の Hom 表示の構成。
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
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の左 Kan 延長の同じ標準局所 Kan 余錐自身が余極限。 -/
lemma sigmaLeftKanExtension_canonicalColimits
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
    (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β) :
    ∀ v : (SigmaPresheafInfinity C) _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone (sigmaYonedaInfinityMap C) G v) :=
  F1B.kanLeftKanExtension_canonicalColimits_of_unit_isIso (sigmaYonedaInfinityMap C) β hβ
    (sigmaLeftKanExtension_unit_isIso β hβ)

/-- 元の標準 Kan 全余錐の普遍性は、元の全密度余錐の同じ像の普遍性と同値。 -/
lemma sigmaCanonicalColimits_iff_densityImages (G : SigmaPresheafInfinity C ⟶ D) :
    (∀ v : (SigmaPresheafInfinity C) _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone (sigmaYonedaInfinityMap C) G v)) ↔
    ∀ v : (SigmaPresheafInfinity C) _⦋0⦌,
      IsColimitCone (mapJoinCocone G (sigmaVertexDensityCocone v)) := by
  have h (v : (SigmaPresheafInfinity C) _⦋0⦌) :
      IsColimitCone (leftKanCanonicalCocone (sigmaYonedaInfinityMap C) G v) ↔
        IsColimitCone (mapJoinCocone G (sigmaVertexDensityCocone v)) :=
    (isColimitCone_iff_restrict_equivalentShape (sigmaElementsLeftKanComparison v)
      (sigmaElementsLeftKanComparison_isQCatEquivalence v) _).trans
      (F2.isColimitCone_iff_of_cocone_val_eq _ _
        (sigmaLeftKanCanonicalCocone_restrict_val G v))
  exact ⟨fun hc v => (h v).mp (hc v), fun hc v => (h v).mpr (hc v)⟩

/-- 元の左 Kan 延長は、元の指定頂点への全密度余錐を同じ指定値の余極限へ送る。 -/
lemma sigmaLeftKanExtension_density_image_isColimit
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
    (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β)
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsColimitCone (mapJoinCocone G (sigmaVertexDensityCocone v)) :=
  (sigmaCanonicalColimits_iff_densityImages G).mp
    (sigmaLeftKanExtension_canonicalColimits β hβ) v

/-- 元の関手自身の恒等単位付き左 Kan 条件は、元の全密度余錐の像の普遍性と同値。 -/
lemma sigma_isLeftKanExtension_refl_iff_densityImages (G : SigmaPresheafInfinity C ⟶ D) :
    IsLeftKanExtension (sigmaYonedaInfinityMap C) (sigmaYonedaInfinityMap C ≫ G) G
      (functorHomotopyRefl (sigmaYonedaInfinityMap C ≫ G)) ↔
    ∀ v : (SigmaPresheafInfinity C) _⦋0⦌,
      IsColimitCone (mapJoinCocone G (sigmaVertexDensityCocone v)) := by
  constructor
  · intro h
    exact sigmaLeftKanExtension_density_image_isColimit _ h
  · intro h
    exact F1B.kanLeftKanExtension_refl_of_canonicalColimits (sigmaYonedaInfinityMap C) G
      ((sigmaCanonicalColimits_iff_densityImages G).mpr h)

/-- 元の延長を、同じ全密度余錐の像の普遍性と元の図式の回収比較とともに得る。 -/
lemma sigma_exists_densityLeftKanExtension_with_recovery
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (hD : HasSmallSiftedColimits D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    ∃ G : SigmaPresheafInfinity C ⟶ D,
      (∀ v : (SigmaPresheafInfinity C) _⦋0⦌,
        IsColimitCone (mapJoinCocone G (sigmaVertexDensityCocone v))) ∧
          Nonempty (FunctorIso (sigmaYonedaInfinityMap C ≫ G) F₀) := by
  obtain ⟨G, β, hβ⟩ := sigma_exists_leftKanExtension hC hD F₀
  exact ⟨G, sigmaLeftKanExtension_density_image_isColimit β hβ,
    ⟨sigmaLeftKanExtensionRecoveryIso β hβ⟩⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
