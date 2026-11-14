module
public import SerrePositivity.KST.Fibration.VerdierUpperCompositeMap
public import SerrePositivity.KST.Fibration.QuotientSKernelZeroFunctorMap

/-!
概要：指定 Verdier 零角比較の上辺を、元の上側合成の全 S• 作用に厳密照合する。
方針：元の指定左辺・上辺を合成し、零値作用の合成則で同じ全単体を回収する。
規約：元の零角比較と上側二胞体の指定合成を保持する。
使われ方：商核四角形と指定 Verdier 四角形の零角を通る上面の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 指定左辺の実完全関手は、同じ指定零角への零値関手。 -/
theorem verdierLeftExactMap_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (verdierLeftExactMap d).hom) :=
  isZeroVertex_functorVertex_of_pointwise _ (fun x => d.zero_corner _)

/-- 指定両端で読んだ元の上側合成は、同じ零値関手。 -/
theorem verdierUpperComposite_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (verdierNullCompositeOriginalMap d 0).hom) :=
  isZeroVertex_functorVertex_of_pointwise _ (verdierNullCompositeOriginalMap_zero d 0)

/-- 元の零角比較は、同じ核包含後の指定左辺の全 S• 作用である。 -/
theorem verdierRelativeSZeroCornerMap_fullS (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierRelativeSZeroCornerMap d =
      (relativeSKernelSimplicialIso d.isVerdier).hom ≫
        zeroFunctorFullSMap (verdierLeftExactMap d) (verdierLeftExactMap_zero d) := by
  have hi : (relativeSKernelSimplicialIso d.isVerdier).hom =
      relativeSimplicialSConstructionInclusion (d.inclusion.hom ≫ d.projection.hom) := by
    apply NatTrans.ext
    funext n
    exact relativeSKernelTopIso_hom_inclusion d.isVerdier n.unop.len
  rw [hi, zeroFunctorFullSMap_eq_zeroTarget _ _ d.zero_corner]
  rfl

/-- 指定左辺と指定上辺の全 S• 作用は、元の指定上側合成の同じ全作用。 -/
theorem verdierUpperFullSMap_comp (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    zeroFunctorFullSMap (verdierLeftExactMap d) (verdierLeftExactMap_zero d) ≫
        coreSExactMap (verdierTopExactMap d) =
      zeroFunctorFullSMap (verdierNullCompositeOriginalMap d 0) (verdierUpperComposite_zero d) := by
  have hFG : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((verdierLeftExactMap d).hom ≫ (verdierTopExactMap d).hom)) := by
    have hz := verdierUpperComposite_zero d
    rw [verdierNullCompositeOriginalMap_upper] at hz
    exact hz
  rw [zeroFunctorFullSMap_comp _ _ _ hFG]
  have hc : ∀ (F G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right) (h : F = G)
      (hf : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (hg : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G.hom)),
      zeroFunctorFullSMap F hf = zeroFunctorFullSMap G hg := by
    intro F G h hf hg
    subst G
    rfl
  exact hc _ _ (verdierNullCompositeOriginalMap_upper d).symm _ _

/-- 元の零角比較を指定上辺へ送ると、同じ核包含後の元の上側合成を厳密に回収する。 -/
theorem verdierRelativeSZeroCornerMap_top (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierRelativeSZeroCornerMap d ≫ coreSExactMap (verdierTopExactMap d) =
      (relativeSKernelSimplicialIso d.isVerdier).hom ≫
        zeroFunctorFullSMap (verdierNullCompositeOriginalMap d 0) (verdierUpperComposite_zero d) := by
  rw [verdierRelativeSZeroCornerMap_fullS, Category.assoc, verdierUpperFullSMap_comp]

end SerrePositivity.KST.Fibration
