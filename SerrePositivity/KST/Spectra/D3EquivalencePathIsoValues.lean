module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointUnitDiagramComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.PathCorrectedSquareExactIso

/-!
概要：元の可逆 path の族が指定する同型の値を、全パラメータの制限に沿って追跡する。
方針：同じ一単体の Yoneda 表現と、同じ関手空間の前合成による作用を照合する。
規約：既存 componentIso を別の同型に置き換えず、指定値との照合の証拠を構成する。
使われ方：元の厳密 loop 切断補正の終点値を認証するための path 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 元の同じ全 path の辺は、添字の前合成で同じ関手空間の辺の像になる。 -/
lemma d3EquivalencePathFamilyEdge_precomp {A B Y : SSet.{u}}
    (L : A ⟶ equivalencePath Y) (r : B ⟶ A) :
    ((pre r).app Y).app (Opposite.op ⦋1⦌) (equivalencePathFamilyEdge L).edge =
      (equivalencePathFamilyEdge (r ≫ L)).edge := by
  rw [equivalencePathFamilyEdge_yoneda, equivalencePathFamilyEdge_yoneda,
    ← SSet.yonedaEquiv_comp]
  congr 1

/-- 元の path 同型の添字制限は、同じ制限 path からの同型そのもの。 -/
lemma d3EquivalencePathFamilyIso_precomp {A B Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ equivalencePath Y) (r : B ⟶ A) :
    F2.functorIsoOfEq ((equivalencePathFamilyIso L).precomp r)
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm =
    equivalencePathFamilyIso (r ≫ L) := by
  apply Iso.ext
  apply eq_of_heq
  refine (d3FunctorIsoOfEq_hom_heq _ _ _).trans ?_
  rw [F2.functorIso_precomp_hom, equivalencePathFamilyIso_hom,
    equivalencePathFamilyIso_hom]
  apply d3HomMk_heq
    ((equivalencePathFamilyEdge L).toTruncated.map ((truncation 2).map ((pre r).app Y)))
    (equivalencePathFamilyEdge (r ≫ L)).toTruncated
    (congrArg functorVertex (Category.assoc r L (equivalencePathEndpoint Y 0)).symm)
    (congrArg functorVertex (Category.assoc r L (equivalencePathEndpoint Y 1)).symm)
  exact d3EquivalencePathFamilyEdge_precomp L r

/-- 元の定値 path の族を表す辺は、同じ関手頂点の恒等辺そのもの。 -/
lemma d3EquivalencePathFamilyEdge_refl {A Y : SSet.{u}} [Quasicategory Y]
    (f : A ⟶ Y) :
    (equivalencePathFamilyEdge (f ≫ equivalencePathRefl Y)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj Y))
        (functorVertex f)).edge := by
  rw [equivalencePathFamilyEdge_yoneda, ← pinchedConstant_one, Category.assoc,
    equivalencePathRefl_ι]
  have ht : transposeFunctorFamily (f ≫ curry (snd (Δ[1] : SSet.{u}) Y)) =
      curry (fst A (Δ[1] : SSet.{u}) ≫ f) := by
    apply uncurry_injective
    rw [transposeFunctorFamily, uncurry_curry, uncurry_natural_left, uncurry_curry]
    rfl
  rw [ht]
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 定値 path からの同じ指定同型は、端点表示を揃えると恒等同型そのもの。 -/
lemma d3EquivalencePathFamilyIso_refl {A Y : SSet.{u}} [Quasicategory Y]
    (f : A ⟶ Y) :
    F2.functorIsoOfEq (equivalencePathFamilyIso (f ≫ equivalencePathRefl Y))
      (by rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id])
      (by rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]) = Iso.refl
        (SSet.HomotopyCategory.mk (functorVertex f)) := by
  apply Iso.ext
  apply eq_of_heq
  refine (d3FunctorIsoOfEq_hom_heq _ _ _).trans ?_
  have h := d3HomMk_heq (equivalencePathFamilyEdge (f ≫ equivalencePathRefl Y)).toTruncated
    (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj Y)) (functorVertex f))
    (congrArg functorVertex (show (f ≫ equivalencePathRefl Y) ≫ equivalencePathEndpoint Y 0 = f by
      rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]))
    (congrArg functorVertex (show (f ≫ equivalencePathRefl Y) ≫ equivalencePathEndpoint Y 1 = f by
      rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]))
    (d3EquivalencePathFamilyEdge_refl f)
  simpa only [SSet.HomotopyCategory.mk, equivalencePathFamilyIso_hom, Iso.refl_hom,
    SSet.Truncated.HomotopyCategory.homMk_id] using h

/-- 同じ path 族の等式は、その指定同型の同じ値を端点表示込みで保つ。 -/
lemma d3EquivalencePathFamilyIso_of_eq {A Y : SSet.{u}} [Quasicategory Y]
    {L L' : A ⟶ equivalencePath Y} (h : L = L') :
    HEq (equivalencePathFamilyIso L) (equivalencePathFamilyIso L') := by
  cases h
  rfl

/-- 元の可逆 path の普遍族が指定する、両端評価間の同じ関手同型。 -/
def d3UniversalEquivalencePathIso (Y : SSet.{u}) [Quasicategory Y] :
    FunctorIso (equivalencePathEndpoint Y 0) (equivalencePathEndpoint Y 1) :=
  F2.functorIsoOfEq (equivalencePathFamilyIso (𝟙 (equivalencePath Y)))
    (Category.id_comp _) (Category.id_comp _)

/-- 普遍 path 比較への同じ族の前合成は、その族の指定同型を厳密回収する。 -/
lemma d3UniversalEquivalencePathIso_precomp {A Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ equivalencePath Y) :
    (d3UniversalEquivalencePathIso Y).precomp L = equivalencePathFamilyIso L := by
  apply eq_of_heq
  unfold d3UniversalEquivalencePathIso
  refine (functorIsoOfEq_precomp_heq _ _ _ _).trans ?_
  have h := d3EquivalencePathFamilyIso_precomp (𝟙 (equivalencePath Y)) L
  have hh := (F2.functorIsoOfEq_heq _ _ _).symm.trans (heq_of_eq h)
  exact hh.trans (d3EquivalencePathFamilyIso_of_eq (Category.comp_id L))

/-- 普遍 path 比較を元の定値族へ制限した指定値は、等式由来の恒等比較。 -/
lemma d3UniversalEquivalencePathIso_refl {A Y : SSet.{u}} [Quasicategory Y]
    (f : A ⟶ Y) :
    F2.IsFunctorEqIso ((d3UniversalEquivalencePathIso Y).precomp
      (f ≫ equivalencePathRefl Y)) := by
  rw [d3UniversalEquivalencePathIso_precomp]
  have h0 : (f ≫ equivalencePathRefl Y) ≫ equivalencePathEndpoint Y 0 = f := by
    rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]
  have h1 : (f ≫ equivalencePathRefl Y) ≫ equivalencePathEndpoint Y 1 = f := by
    rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]
  have hh := (F2.functorIsoOfEq_heq (equivalencePathFamilyIso (f ≫ equivalencePathRefl Y))
    h0 h1).symm.trans (heq_of_eq (d3EquivalencePathFamilyIso_refl f))
  have hid : F2.IsFunctorEqIso (Iso.refl (SSet.HomotopyCategory.mk (functorVertex f)) :
      FunctorIso f f) := ⟨rfl, rfl⟩
  exact hid.of_heq h0.symm h1.symm hh

end SerrePositivity.KST.Spectra
