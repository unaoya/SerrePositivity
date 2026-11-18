module

public import SerrePositivity.InfinityCategories.Sheaves.RightKanCosliceCounit
public import SerrePositivity.InfinityCategories.Sheaves.MovingConePrismCounit
public import SerrePositivity.InfinityCategories.Sheaves.MovingIndexPointClass

/-!
概要：元の区間に沿う頂点射は、共通の添字に制限した二つの標準錐の余単位を可換にする。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma coneCounitAtApex_morphism
    {J D : SSet.{u}} {p : J ⟶ D} (c d : JoinCone p) {x y : D _⦋0⦌}
    (hc : c.vertex = x) (hd : d.vertex = y)
    (a : (HomotopyCategory.mk c.vertex : hoFunctor.obj D) ⟶ HomotopyCategory.mk d.vertex)
    (b : (HomotopyCategory.mk x : hoFunctor.obj D) ⟶ HomotopyCategory.mk y)
    (hb : Arrow.mk a = Arrow.mk b)
    (ha : constantFunctorHomMap J a ≫ coneCounitHom d = coneCounitHom c) :
    constantFunctorHomMap J b ≫ coneCounitAtApex d hd = coneCounitAtApex c hc := by
  subst x y
  have h : a = b := Arrow.mk_injective _ _ hb
  simpa only [coneCounitAtApex, eqToHom_refl, constantFunctorHomMap_id, Category.id_comp, ← h] using ha

private lemma sliceEndpoint_uncurry {J X B : SSet.{u}} {η : B ⟶ X}
    (w : J ⟶ sliceUnder η) (r : (Δ[0] : SSet.{u}) ⟶ B)
    {z : (Δ[0] : SSet.{u}) ⟶ X} (hz : r ≫ η = z) :
    joinMap r (𝟙 J) ≫ sliceUnderUncurry w =
      sliceUnderUncurry (w ≫ sliceUnderRestrict η r ≫ eqToHom (congrArg sliceUnder hz)) := by
  subst z
  rw [eqToHom_refl, Category.comp_id, sliceUnderUncurry_restrict]

/-- 元の区間に沿う頂点射は、共通の添字に制限した二つの標準錐の余単位を可換にする。
Kerodon Definition 7.3.1.2（Tag 02Y9）。HTT 5.1.5.6 に使う動く添字の照合。 -/
lemma rightKanMovingIndex_cosliceCounit
    {J K X D : SSet.{u}} [Quasicategory X] [Quasicategory D]
    (δ : K ⟶ X) (G : X ⟶ D) {v₀ v₁ : X _⦋0⦌} (e : X.Edge v₀ v₁)
    (j₀ : J ⟶ rightKanShape δ v₀) (j₁ : J ⟶ rightKanShape δ v₁)
    (hface : rightKanMovingIndexFace δ (SSet.yonedaEquiv.symm e.edge)
      e.δ_one_yonedaEquiv_symm e.δ_zero_yonedaEquiv_symm j₀ j₁) :
    let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
    let q₁ := sliceUnderProjection (SSet.yonedaEquiv.symm v₁)
    let a₀ := j₀ ≫ pullback.fst q₀ δ
    let a₁ := j₁ ≫ pullback.fst q₁ δ
    let p := (j₀ ≫ rightKanProjection δ v₀) ≫ δ
    ∀ (h₀ : a₀ ≫ q₀ ≫ G = p ≫ G) (h₁ : a₁ ≫ q₁ ≫ G = p ≫ G),
    constantFunctorHomMap J (Truncated.HomotopyCategory.homMk (e.map G).toTruncated) ≫
      coneCounitAtApex (coneOfCosliceMap a₁ G h₁) (coneOfCosliceMap_atApex a₁ G h₁) =
    coneCounitAtApex (coneOfCosliceMap a₀ G h₀) (coneOfCosliceMap_atApex a₀ G h₀) := by
  intro q₀ q₁ a₀ a₁ p h₀ h₁
  obtain ⟨w, hs, ht, hw₁, ⟨i⟩⟩ := hface
  let η := SSet.yonedaEquiv.symm e.edge
  let r₀ := sliceUnderRestrict η (stdSimplex.δ (1 : Fin 2)) ≫
    eqToHom (congrArg sliceUnder e.δ_one_yonedaEquiv_symm)
  let f := w ≫ r₀
  have hw : w ≫ sliceUnderProjection η = p := by
    have hr₀ : r₀ ≫ q₀ = sliceUnderProjection η := by
      dsimp only [r₀, q₀]
      rw [Category.assoc, sliceUnder_eqToHom_projection e.δ_one_yonedaEquiv_symm,
        sliceUnderRestrict_projection]
    rw [← hr₀, ← Category.assoc]
    exact hs
  let hF : f ≫ q₀ ≫ G = p ≫ G := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ G) hs)
  let F := coneOfCosliceMap f G hF
  let D₁ := coneOfCosliceMap a₁ G h₁
  let hvF := coneOfCosliceMap_atApex f G hF
  let hv₁ := coneOfCosliceMap_atApex a₁ G h₁
  have e₀ : joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w ≫ G = F.val := by
    exact congrArg (· ≫ G) (sliceEndpoint_uncurry w _ e.δ_one_yonedaEquiv_symm)
  have e₁ : joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w ≫ G = D₁.val := by
    change _ = sliceUnderUncurry a₁ ≫ G
    rw [← Category.assoc, sliceEndpoint_uncurry w _ e.δ_zero_yonedaEquiv_symm]
    exact congrArg (fun t => sliceUnderUncurry t ≫ G) hw₁
  obtain ⟨a, ha, hc⟩ := movingConePrism_counit_naturality e G w F D₁ e₀ e₁
    (congrArg (· ≫ G) hw)
  exact (coneCounitAtApex_morphism F D₁ hvF hv₁ a _ ha hc).trans
    (coneOfCosliceMap_counit_relativeIso v₀ G f a₀ hs ht i)

end SerrePositivity.InfinityCategories.Sheaves
