module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators

/-! # 閉 dg 分母の実合成の閉性

概要：元の二閉 Verdier 分母の合成は、元の実辺として再び Verdier 分母となる。
方針：同じ閉射の導来像の trW 条件と、その合成閉性を使う。
規約：元の Hom の平坦性は不要。使われ方：相対原始元の持ち上げでの分母の細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 二つの元の閉実 Verdier 分母の合成は再び実 Verdier 分母。 -/
lemma dgClosedVerdierDenominator_comp (P : Set D) {x y z : ClosedCategory A D}
    (r : x ⟶ y) (s : y ⟶ z)
    (hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (r ≫ s)).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P (r ≫ s)).mpr
  have h := (derivedFiniteCellOver A D P).trW.comp_mem _ _
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P r).mp hr)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P s).mp hs)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap, Functor.map_comp] using h

/-- 元の恒等閉射の実辺は Verdier 分母である。 -/
lemma dgClosedVerdierDenominator_id (P : Set D) (x : D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (𝟙 (ForgetEnrichment.of (Complex A) x))).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P _).mpr
  have hi := congrArg (moduleToDerived A D).map
    ((dgYoneda A D).onClosed.map_id (ForgetEnrichment.of (Complex A) x))
  have he := hi.trans ((moduleToDerived A D).map_id _)
  change (derivedFiniteCellOver A D P).trW ((moduleToDerived A D).map
    ((dgYoneda A D).onClosed.map (𝟙 (ForgetEnrichment.of (Complex A) x))))
  rw [he]
  exact (derivedFiniteCellOver A D P).trW.id_mem _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
