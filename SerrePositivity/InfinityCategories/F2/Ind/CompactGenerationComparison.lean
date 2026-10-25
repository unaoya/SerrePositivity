module

public import SerrePositivity.InfinityCategories.F2.Ind.CompactGeneration

/-!
概要：compact 生成同値の順射・逆射を元の Yoneda と包含へ照合する。
方針：順射の厳密な一致と同値の全関手二胞体を、同じ包含へ後合成する。
規約：逆同値の選択を固定せず、対象別の同型に弱めない。
使われ方：I-2 e と K-B の K-7 d4 における選択比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]

/-- 選んだ生成同値の順射と compact 包含の合成は、元の全 Yoneda。 -/
lemma compactGenerationEquivalence_inclusion (hC : Idempotent.IsIdempotentComplete C) :
    (compactGenerationEquivalence κ hC).hom ≫
      Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C) = indYoneda κ C :=
  Compact.compactIndYoneda_inclusion κ

/-- 同じ順射を持つ任意の逆同値は、元の Yoneda の後合成で compact 包含へ戻る。 -/
def compactGenerationChoice_inclusion
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj C)
      (Compact.kappaCompactObjects.{u, u + 1} κ (IndInfinity κ C)))
    (he : e.hom = Compact.compactIndYoneda κ C) :
    FunctorIso (e.inv ≫ indYoneda κ C)
      (Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C)) := by
  have h := e.invHomIso.postcomp
    (Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C))
  simpa only [he, Category.assoc, Compact.compactIndYoneda_inclusion, Category.id_comp]
    using h

/-- 公開生成同値の逆射と元の Yoneda は、同じ全 compact 包含と同型。 -/
def compactGenerationInverse_inclusion (hC : Idempotent.IsIdempotentComplete C) :
    FunctorIso ((compactGenerationEquivalence κ hC).inv ≫ indYoneda κ C)
      (Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C)) :=
  compactGenerationChoice_inclusion κ _ (compactGenerationEquivalence_hom κ hC)

/-- 同じ順射の任意の逆同値と公開逆同値の、全関手としての選択比較。 -/
def compactGenerationInverse_choiceIso (hC : Idempotent.IsIdempotentComplete C)
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj C)
      (Compact.kappaCompactObjects.{u, u + 1} κ (IndInfinity κ C)))
    (he : e.hom = Compact.compactIndYoneda κ C) :
    FunctorIso e.inv (compactGenerationEquivalence κ hC).inv := by
  let q := compactGenerationEquivalence κ hC
  have hq : e.hom = q.hom := he.trans (compactGenerationEquivalence_hom κ hC).symm
  have h₁ : FunctorIso e.inv (e.inv ≫ q.hom ≫ q.inv) := by
    simpa only [Category.comp_id] using (q.homInvIso.precomp e.inv).symm
  have h₂ : FunctorIso (e.inv ≫ q.hom ≫ q.inv) q.inv := by
    simpa only [Category.id_comp, Category.assoc, hq] using e.invHomIso.postcomp q.inv
  exact h₁ ≪≫ h₂

/-- 任意の入力族にも、同じ全包含との比較を前合成できる。 -/
def compactGenerationInverse_familyIso (hC : Idempotent.IsIdempotentComplete C)
    {T : SSet.{u + 1}}
    (a : T ⟶ Compact.kappaCompactObjects.{u, u + 1} κ (IndInfinity κ C)) :
    FunctorIso (a ≫ (compactGenerationEquivalence κ hC).inv ≫ indYoneda κ C)
      (a ≫ Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C)) := by
  simpa only [Category.assoc] using (compactGenerationInverse_inclusion κ hC).precomp a

end SerrePositivity.InfinityCategories.F2.Ind
