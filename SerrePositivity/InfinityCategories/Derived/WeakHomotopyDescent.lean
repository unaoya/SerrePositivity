module
public import SerrePositivity.InfinityCategories.F1B.KanHomotopyClasses
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-! # 弱同値に沿う Kan 標的への写像の降下

概要：弱同値に沿って Kan 標的への写像をホモトピーまで延長し、一意性を反映する。
方針：全 Kan 標的の内部 Hom の π₀ の全単射を使う。
規約：始域・終域に Kan 性や有限性は不要。使われ方：実屋根の写像空間上の降下。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet

/-- 弱同値に沿う任意の Kan 標的への写像は、ホモトピーまで延長できる。 -/
lemma IsWeakHomotopyEquivalence.homotopyExtension {A B Z : SSet.{u}}
    {w : A ⟶ B} (hw : IsWeakHomotopyEquivalence w) [KanComplex Z] (f : A ⟶ Z) :
    ∃ g : B ⟶ Z, Nonempty (SSet.Homotopy (w ≫ g) f) := by
  obtain ⟨c, hc⟩ := (hw Z).surjective (SSet.π₀.mk (functorVertex f))
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective c
  obtain ⟨g, rfl⟩ := (functorVertexEquiv B Z).surjective v
  exact ⟨g, (functorVertex_piZero_eq_iff_homotopy _ _).mp hc⟩

/-- Kan 標的への写像のホモトピーは、弱同値による前合成で反映される。 -/
lemma IsWeakHomotopyEquivalence.reflects_homotopy {A B Z : SSet.{u}}
    {w : A ⟶ B} (hw : IsWeakHomotopyEquivalence w) [KanComplex Z]
    {f g : B ⟶ Z} (H : SSet.Homotopy (w ≫ f) (w ≫ g)) :
    Nonempty (SSet.Homotopy f g) := by
  apply (functorVertex_piZero_eq_iff_homotopy f g).mp
  apply (hw Z).injective
  exact (functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨H⟩

/-- 同じ図式を降下する二組の写像は、全空間上でもホモトピック。
    中間の Kan への戻し方の選択にも依存しない。 -/
lemma weakRoofDescent_unique {R Q E Z : SSet.{u}} [KanComplex Z]
    {w : R ⟶ Q} {i : Z ⟶ E} (hw : IsWeakHomotopyEquivalence w)
    (hi : IsWeakHomotopyEquivalence i) (t : R ⟶ E)
    (r₁ r₂ : E ⟶ Z) (q₁ q₂ : Q ⟶ Z)
    (H₁ : SSet.Homotopy (i ≫ r₁) (𝟙 Z)) (H₂ : SSet.Homotopy (i ≫ r₂) (𝟙 Z))
    (K₁ : SSet.Homotopy (w ≫ q₁) (t ≫ r₁))
    (K₂ : SSet.Homotopy (w ≫ q₂) (t ≫ r₂)) : Nonempty (SSet.Homotopy q₁ q₂) := by
  have hr : Nonempty (SSet.Homotopy r₁ r₂) := by
    apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
    apply (hi Z).injective
    exact ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨H₁⟩).trans
      ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨H₂⟩).symm
  obtain ⟨Hr⟩ := hr
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  apply (hw Z).injective
  exact ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨K₁⟩).trans
    (((functorVertex_piZero_eq_iff_homotopy _ _).mpr
      ⟨functorHomotopyPrecomp Hr t⟩).trans
        ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨K₂⟩).symm)

end SerrePositivity.InfinityCategories
