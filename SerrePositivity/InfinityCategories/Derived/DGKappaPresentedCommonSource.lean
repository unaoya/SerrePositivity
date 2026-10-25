module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSeedRefinement
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceModel
public import SerrePositivity.InfinityCategories.Derived.DGKappaSourceCodeCoproductComparison
/-!
概要：異なる出発提示を共通提示へまとめ、元の実評価をホモトピー同型まで回収する。
方針：全 Hom での厳密な成分因子分解と、seed の実延長の代表化を合成する。
規約：標的の任意閉射の持ち上げは含めず、対象の同時精密化だけを結論する。
使われ方：c′ の二項・可算直和を共通源の seed 演算へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D]
  (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
  {J : Type u} (X : J → DGKappaPresentedSourceObject R D κ)
  (s : DGKappaFreeSumShape (fun j => (X j).code.ordinal))

abbrev dgKappaPresentedCommonCode : DGCategoryPresentationCode R κ :=
  dgKappaSourceCodeCoproduct R κ (fun j => (X j).code) s

def dgKappaPresentedCommonArrow :
    DGFunctor R ((dgKappaPresentedCommonCode R D κ X s).Objects R κ) D :=
  dgKappaSourceCodeCoproductDesc R κ (fun j => (X j).code) s D (fun j => (X j).arrow)

include hκ hreg in
lemma dgKappaPresentedCommonSource_homotopyCovers (j : J) :
    ∃ M : ModuleCategory R ((dgKappaPresentedCommonCode R D κ X s).Objects R κ),
      dgKappaClosedProjectiveObjects R
        ((dgKappaPresentedCommonCode R D κ X s).Objects R κ) κ M ∧
      Nonempty ((moduleToHomotopy R D).obj ((dgModuleExtension R
        ((dgKappaPresentedCommonCode R D κ X s).Objects R κ) D
        (dgKappaPresentedCommonArrow R D κ X s)).onClosed.obj M) ≅
        (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
          (dgKappaPresentedSourceValue R D κ (X j)))) := by
  have h := dgKappaClosedProjectiveSeed_extension_composition_homotopyRange R
    ((X j).code.Objects R κ) ((dgKappaPresentedCommonCode R D κ X s).Objects R κ) D
    (dgKappaSourceCodeCoproductInclusion R κ (fun j => (X j).code) s j)
    (dgKappaSourceCodeCoproductDesc R κ (fun j => (X j).code) s D (fun j => (X j).arrow))
    κ hκ hreg (X j).seed
  rw [dgKappaSourceCodeCoproductInclusion_comp_desc] at h
  unfold dgKappaPresentedSourceValue dgKappaPresentedSourceSeed dgKappaPresentedSeedAt
  exact h

include hκ hreg in
lemma dgKappaPresentedCommonSource_seedCovers (j : J) :
    ∃ i : (dgKappaClosedProjectiveFamily R
      ((dgKappaPresentedCommonCode R D κ X s).Objects R κ) κ).1,
      Nonempty ((moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
        (dgKappaPresentedSourceValue R D κ
          ⟨dgKappaPresentedCommonCode R D κ X s, i,
            dgKappaPresentedCommonArrow R D κ X s⟩)) ≅
        (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
          (dgKappaPresentedSourceValue R D κ (X j)))) := by
  obtain ⟨M, ⟨i, hi⟩, ⟨e⟩⟩ :=
    dgKappaPresentedCommonSource_homotopyCovers R D κ hκ hreg X s j
  refine ⟨i, ⟨?_⟩⟩
  rw [← hi] at e
  unfold dgKappaPresentedSourceValue dgKappaPresentedSourceSeed
    dgKappaPresentedSeedAt at e ⊢
  exact e

end SerrePositivity.InfinityCategories
