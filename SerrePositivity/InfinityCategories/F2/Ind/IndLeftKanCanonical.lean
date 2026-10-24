module

public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanUnitRecovery
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftUnitCanonical

/-!
概要：元の Yoneda に沿う左 Kan 延長の局所普遍性を、元の標準 Kan 余錐で読む。
方針：指定単位の可逆性を既存の全余錐輸送へ渡す。
規約：元の延長と指定単位を保持し、余錐を点ごとに選び直さない。
使われ方：κ-filtered 保存性の証明に用いる元の標準局所公式。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の Yoneda に沿う左 Kan 延長では、同じ標準局所 Kan 余錐自身が余極限。 -/
lemma indLeftKanExtension_canonicalColimits
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    ∀ v : (IndInfinity κ C) _⦋0⦌, IsColimitCone (leftKanCanonicalCocone (indYoneda κ C) G v) :=
  F1B.kanLeftKanExtension_canonicalColimits_of_unit_isIso (indYoneda κ C) β hβ
    (indLeftKanExtension_unit_isIso κ β hβ)

/-- 構成済み延長を、元の全標準局所余極限条件と元の図式の回収比較とともに得る。 -/
lemma ind_exists_canonicalLeftKanExtension_with_recovery [Fact κ.IsRegular]
    (hD : HasSmallKappaFilteredColimits κ D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    ∃ G : IndInfinity κ C ⟶ D,
      (∀ v : (IndInfinity κ C) _⦋0⦌, IsColimitCone (leftKanCanonicalCocone (indYoneda κ C) G v)) ∧
        Nonempty (FunctorIso (indYoneda κ C ≫ G) F₀) := by
  obtain ⟨G, β, hβ⟩ := ind_exists_leftKanExtension κ hD F₀
  exact ⟨G, indLeftKanExtension_canonicalColimits κ β hβ,
    ⟨indLeftKanExtensionRecoveryIso κ β hβ⟩⟩

end SerrePositivity.InfinityCategories.F2.Ind
