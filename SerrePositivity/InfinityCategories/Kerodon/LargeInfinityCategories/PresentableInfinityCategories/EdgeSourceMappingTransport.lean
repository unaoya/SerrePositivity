module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EdgeCosliceMappingFiber

/-!
概要：元の辺・始点図式の表示を変更しても、同じ基点の始点制限 fiber の可縮性を保つ。
方針：図式の等号による厳密な fiber 同型を作り、基点を元の全余錐の射で比較する。
規約：写像空間全体を保持し、基点のホモトピー類だけでは同定しない。
使われ方：HTT 5.5.5.13–14 の pushout の基点を元の局所性判定へ戻す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 図式の等号による余錐空間の表示変更は、元の全余錐の射を変えない。 -/
lemma coconeMappingDiagramChange_val {K C : SSet.{u}} {p q : K ⟶ C}
    (h : p = q) (y : C _⦋0⦌) (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) _⦋0⦌) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberDiagramIso h y).hom.app _ d).val).val = d.val.val := by
  cases h
  rfl

/-- 正規化した制限の対応する基点上の fiber は、元の制限の同じ fiber と厳密に同型。 -/
def normalizedCoconeMappingFiberIso {K L C : SSet.{u}} (e : K ⟶ C) (i : L ⟶ K)
    {p : L ⟶ C} (ha : i ≫ e = p) (y : C _⦋0⦌)
    (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (i ≫ e) y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e i y) d ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber e i ha y)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberDiagramIso ha y).hom.app _ d) := by
  cases ha
  exact Iso.refl _

/-- 元の指定辺と元の基点を回収すれば、raw な始点制限の可縮 fiber をそのまま戻せる。 -/
lemma edgeCosliceSourceMapping_contractible_of_raw
    {C : SSet.{u}} [Quasicategory C] {a b : C _⦋0⦌} (f : C.Edge a b)
    (y : C _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ C)
    (he : e = SSet.yonedaEquiv.symm f.edge)
    (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (stdSimplex.δ (1 : Fin 2) ≫ e) y) _⦋0⦌)
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e
      (stdSimplex.δ (1 : Fin 2)) y) d))
    (g : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm a) y) _⦋0⦌)
    (hg : d.val.val = g.val.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.edgeCosliceSourceMapping f y) g) := by
  subst e
  have ha : stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge =
      SSet.yonedaEquiv.symm a := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact f.src_eq
  have hb : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberDiagramIso ha y).hom.app _ d = g := by
    apply Subtype.ext
    apply Subtype.ext
    rw [coconeMappingDiagramChange_val]
    exact hg
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso
    (normalizedCoconeMappingFiberIso (SSet.yonedaEquiv.symm f.edge)
      (stdSimplex.δ (1 : Fin 2)) ha y d) hd
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.edgeCosliceSourceMapping f y)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberDiagramIso ha y).hom.app _ d)) at h
  rwa [hb] at h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
