module
public import SerrePositivity.KST.Fibration.ZeroFunctorPostcompFamilies
public import SerrePositivity.KST.Fibration.StableZeroEndContraction
public import SerrePositivity.KST.Fibration.StableHomCompositionVertices

/-! # 同じ零自己関手円柱の零値完全関手への像を、元の全 Kan Hom に保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の共通零自己関手円柱を、零値完全関手への後合成で元の Kan Hom に読む。 -/
def zeroEndPostcompFamily {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    (Δ[1] : SSet.{u}) ⟶ (A ⟶[SSet.{u}] C) :=
  stableZeroEndContractionFamily A ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A A).ι ≫
    zeroFunctorPostcompStableHom A A C F.hom hF

/-- 元の Kan Hom で読んだ円柱は、周囲で同じ零自己関手族の全後合成を回収する。 -/
theorem zeroEndPostcompFamily_ambient {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    zeroEndPostcompFamily F hF ≫ stableHomAmbient A C =
      stableZeroEndContractionFamily A ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A A).ι ≫ (ihom A.obj).map F.hom := by
  rw [zeroEndPostcompFamily, Category.assoc, Category.assoc,
    zeroFunctorPostcompStableHom_ambient]

/-- 同じ実円柱の元の全頂点は、零値完全関手である。 -/
theorem zeroEndPostcompFamily_zero_vertices {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (v : (Δ[1] : SSet.{u}) _⦋0⦌) :
    StableHomZeroVertex A C ((zeroEndPostcompFamily F hF).app (Opposite.op ⦋0⦌) v) :=
  zeroFunctorPostcompStableHom_zero A A C F.hom hF
    (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A A).ι).app (Opposite.op ⦋0⦌)
      ((stableZeroEndContractionFamily A).app (Opposite.op ⦋0⦌) v))

/-- 元の円柱の終点は、指定した同じ完全関手の元の Kan Hom 頂点そのもの。 -/
theorem zeroEndPostcompFamily_one {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    stdSimplex.δ (0 : Fin 2) ≫ zeroEndPostcompFamily F hF =
      SSet.yonedaEquiv.symm (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A C F) := by
  let : Mono (stableHomAmbient A C) := by
    dsimp [stableHomAmbient]
    infer_instance
  apply (cancel_mono (stableHomAmbient A C)).1
  rw [Category.assoc, zeroEndPostcompFamily_ambient, ← Category.assoc,
    ← Category.assoc, stableZeroEndContractionFamily_one,
    SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp,
    SSet.yonedaEquiv_symm_comp, stableHomAmbient_homEquiv']
  change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 A.obj ≫ F.hom)) =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)
  rw [Category.id_comp]

/-- 元の円柱の始点は、同じ零自己関手と指定完全関手の実合成の頂点。 -/
theorem zeroEndPostcompFamily_zero {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    stdSimplex.δ (1 : Fin 2) ≫ zeroEndPostcompFamily F hF = SSet.yonedaEquiv.symm
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A C
        (show A ⟶ C from (show A ⟶ A from stableZeroEndMap A) ≫
          (show A ⟶ C from F))) := by
  let : Mono (stableHomAmbient A C) := by
    dsimp [stableHomAmbient]
    infer_instance
  apply (cancel_mono (stableHomAmbient A C)).1
  rw [Category.assoc, zeroEndPostcompFamily_ambient, ← Category.assoc,
    ← Category.assoc, stableZeroEndContractionFamily_zero,
    SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp,
    SSet.yonedaEquiv_symm_comp, stableHomAmbient_homEquiv']
  rfl

end SerrePositivity.KST.Fibration
