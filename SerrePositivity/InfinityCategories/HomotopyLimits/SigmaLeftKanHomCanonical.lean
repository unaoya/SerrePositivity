module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaConeLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaLeftKanDensityImage
public import SerrePositivity.InfinityCategories.F1B.KanCosliceOpposite

/-!
概要：P_Σ の元の左 Kan 標準余錐は、元の共同 Hom の全反変族で極限錐となる。
方針：同じ指定単位から標準余錐の余極限性を回収し、元の全余錐を反転して写す。
規約：全係数を持つ一つの Hom 関手圏の錐を使い、値ごとの極限だけに縮約しない。
使われ方：延長の全 Hom 表示を、元の局所右 Kan 比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の延長の標準 Kan 全余錐は、元の共同 Hom 全族による同じ極限錐を与える。 -/
lemma sigmaLeftKanHomCanonicalCone_isLimit {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D}
    {G : SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
    (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β)
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsLimitCone (mapJoinCone (coyonedaInfinityMap D) (JoinCone.ulift.{u + 1, u + 2}
      (F1B.kanCoconeReverseCone (leftKanCanonicalCocone (sigmaYonedaInfinityMap C) G v)))) :=
  coyonedaInfinityMap_map_isLimit _
    ((F1B.kanIsColimitCone_iff_reverseCone _).mp (sigmaLeftKanExtension_canonicalColimits β hβ v))

end SerrePositivity.InfinityCategories.HomotopyLimits
