module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RightAnodyneTensor
public import SerrePositivity.InfinityCategories.F1B.CofinalAnodyneRecognition
public import SerrePositivity.InfinityCategories.F1B.CofinalComposition
public import SerrePositivity.InfinityCategories.F1B.CofinalOpposite

/-!
概要：right cofinal な元の射と任意の単体集合の直積。
方針：元の anodyne・trivial Kan 因子分解を直積し、元の合成を回収する。
規約：両底と相手因子の quasicategory 性は不要。
使われ方：元の sifted 二項対角から全有限反復対角への入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- trivial Kan fibration と任意の右因子の直積は、元の積射のまま trivial Kan。 -/
lemma trivialKanFibration_whiskerRight {E B : SSet.{u}} (p : E ⟶ B)
    [TrivialKanFibration p] (K : SSet.{u}) : TrivialKanFibration (p ▷ K) where
  mem := by
    intro A D i hi
    have : Mono i := hi
    have := TrivialKanFibration.mem (p := p) i hi
    constructor
    intro a b sq
    have hs : CommSq (a ≫ fst E K) i p (b ≫ fst B K) := by
      constructor
      rw [Category.assoc, ← whiskerRight_fst, ← Category.assoc, sq.w, Category.assoc]
    refine CommSq.HasLift.mk' { l := lift hs.lift (b ≫ snd B K), fac_left := ?_, fac_right := ?_ }
    · apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, hs.fac_left]
      · rw [Category.assoc, lift_snd, ← Category.assoc, ← sq.w, Category.assoc,
          whiskerRight_snd]
    · apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst, hs.fac_right]
      · rw [Category.assoc, whiskerRight_snd, lift_snd]

/-- right cofinal な元の射は、任意の右因子との直積でも right cofinal。 -/
lemma isRightCofinal_whiskerRight {A B : SSet.{u}} {i : A ⟶ B}
    (hi : IsRightCofinal i) (K : SSet.{u}) : IsRightCofinal (i ▷ K) := by
  obtain ⟨Z, j, p, _, hj, hp, he⟩ := hi.exists_anodyne_trivialKan_factorization
  have : TrivialKanFibration p := hp
  have : TrivialKanFibration (p ▷ K) := trivialKanFibration_whiskerRight p K
  have h := (isRightCofinal_of_rightAnodyne (j ▷ K)
    (rightAnodyneExtensions_whiskerRight j hj K)).comp
      (isRightCofinal_of_trivialKanFibration (p ▷ K))
  rwa [← MonoidalCategory.comp_whiskerRight, he] at h

/-- right cofinal な元の射は、任意の左因子との直積でも right cofinal。 -/
lemma isRightCofinal_whiskerLeft {A B : SSet.{u}} {i : A ⟶ B}
    (hi : IsRightCofinal i) (K : SSet.{u}) : IsRightCofinal (K ◁ i) := by
  have h := (isRightCofinal_of_isIso (β_ K A).hom).comp
    ((isRightCofinal_whiskerRight hi K).comp (isRightCofinal_of_isIso (β_ B K).hom))
  have he : (β_ K A).hom ≫ (i ▷ K) ≫ (β_ B K).hom = K ◁ i := rfl
  rwa [he] at h

end SerrePositivity.InfinityCategories.HomotopyLimits
