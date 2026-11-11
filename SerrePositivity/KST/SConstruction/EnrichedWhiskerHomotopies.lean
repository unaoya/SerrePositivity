module
public import SerrePositivity.KST.SConstruction.EnrichedFixedCompositionMaps
public import SerrePositivity.KST.SConstruction.FixedBoundaryPostcomposition

/-! # 元の全比較円柱を固定因子の豊穣合成へ写す
概要：元の二比較辺を結ぶ全円柱を固定因子と合成し、同じ両端固定の比較を得る。
方針：Hom 全体への実合成写像で後合成し、元の辺の厳密な像の式で両端の表示を合わせる。
規約：円柱を選び直さず、全写像の像と全境界の固定を同時に保持する。
使われ方：三入力の二実三角形の上辺を元の BF 比較辺の合成へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の全比較円柱を固定第一射と合成した、同じ二辺の実比較円柱。 -/
def enrichedLeftWhiskerHomotopy {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (gh : X ⟶ Z)
    {e d : (SimplicialCategory.sHom X Z).Edge (SimplicialCategory.homEquiv' _ _ gh)
      (SimplicialCategory.homEquiv' _ _ (g ≫ h))}
    (H : SSet.Homotopy (SSet.yonedaEquiv.symm e.edge) (SSet.yonedaEquiv.symm d.edge)) :=
  familyHomotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (enrichedFixedLeftComposition f))
    (enrichedComparisonLeftWhisker_map f g h gh e)
    (enrichedComparisonLeftWhisker_map f g h gh d).symm

/-- 左合成後の円柱全体は、元の同じ全円柱の実合成写像での像そのもの。 -/
lemma enrichedLeftWhiskerHomotopy_h {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (gh : X ⟶ Z)
    {e d : (SimplicialCategory.sHom X Z).Edge (SimplicialCategory.homEquiv' _ _ gh)
      (SimplicialCategory.homEquiv' _ _ (g ≫ h))}
    (H : SSet.Homotopy (SSet.yonedaEquiv.symm e.edge) (SSet.yonedaEquiv.symm d.edge)) :
    (enrichedLeftWhiskerHomotopy f g h gh H).h = H.h ≫ enrichedFixedLeftComposition f :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 左合成は元の全区間境界の厳密な固定をそのまま保持する。 -/
lemma enrichedLeftWhiskerHomotopy_relative {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (gh : X ⟶ Z)
    {e d : (SimplicialCategory.sHom X Z).Edge (SimplicialCategory.homEquiv' _ _ gh)
      (SimplicialCategory.homEquiv' _ _ (g ≫ h))}
    (H : SSet.Homotopy (SSet.yonedaEquiv.symm e.edge) (SSet.yonedaEquiv.symm d.edge))
    (hr : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm e.edge) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (enrichedLeftWhiskerHomotopy f g h gh H).h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (enrichedComparisonLeftWhisker f g h gh e).edge := by
  rw [enrichedLeftWhiskerHomotopy_h]
  exact (fixedBoundaryFamily_postcomp _ _ H.h hr (enrichedFixedLeftComposition f)).trans
    (congrArg (fun q => fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫ q)
      (enrichedComparisonLeftWhisker_map f g h gh e).symm)

/-- 元の全比較円柱を固定最終射と合成した、同じ二辺の実比較円柱。 -/
def enrichedRightWhiskerHomotopy {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y)
    {e d : (SimplicialCategory.sHom W Y).Edge (SimplicialCategory.homEquiv' _ _ fg)
      (SimplicialCategory.homEquiv' _ _ (f ≫ g))}
    (H : SSet.Homotopy (SSet.yonedaEquiv.symm e.edge) (SSet.yonedaEquiv.symm d.edge)) :=
  familyHomotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (enrichedFixedRightComposition h))
    (enrichedComparisonRightWhisker_map f g h fg e)
    (enrichedComparisonRightWhisker_map f g h fg d).symm

/-- 右合成後の円柱全体も、元の同じ全円柱の実合成写像での像そのもの。 -/
lemma enrichedRightWhiskerHomotopy_h {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y)
    {e d : (SimplicialCategory.sHom W Y).Edge (SimplicialCategory.homEquiv' _ _ fg)
      (SimplicialCategory.homEquiv' _ _ (f ≫ g))}
    (H : SSet.Homotopy (SSet.yonedaEquiv.symm e.edge) (SSet.yonedaEquiv.symm d.edge)) :
    (enrichedRightWhiskerHomotopy f g h fg H).h = H.h ≫ enrichedFixedRightComposition h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 右合成も元の全区間境界の厳密な固定をそのまま保持する。 -/
lemma enrichedRightWhiskerHomotopy_relative {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y)
    {e d : (SimplicialCategory.sHom W Y).Edge (SimplicialCategory.homEquiv' _ _ fg)
      (SimplicialCategory.homEquiv' _ _ (f ≫ g))}
    (H : SSet.Homotopy (SSet.yonedaEquiv.symm e.edge) (SSet.yonedaEquiv.symm d.edge))
    (hr : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm e.edge) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (enrichedRightWhiskerHomotopy f g h fg H).h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (enrichedComparisonRightWhisker f g h fg e).edge := by
  rw [enrichedRightWhiskerHomotopy_h]
  exact (fixedBoundaryFamily_postcomp _ _ H.h hr (enrichedFixedRightComposition h)).trans
    (congrArg (fun q => fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫ q)
      (enrichedComparisonRightWhisker_map f g h fg e).symm)

end SerrePositivity.KST.SConstruction
