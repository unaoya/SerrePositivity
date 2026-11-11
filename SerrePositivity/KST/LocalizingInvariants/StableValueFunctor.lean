module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactMapHomotopy
public import SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi
public import SerrePositivity.KST.LocalizingInvariants.ValueHomotopy

/-!
概要：安定圏の完全関手の像を、元の BF 値の h Sp の射へ関手的に移す。
方針：coherent nerve の合成と、元の辺・端点の同定を用いる。
規約：BF 射の厳密な合成則へ強めない。使われ方：K-8 の切断の像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants

local instance stableValueSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 完全関手の通常の圏から、元の安定圏の ∞ 圏のホモトピー圏への関手。 -/
def stableHoFunctor : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} ⥤ hoFunctor.obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} where
  obj A := SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A)
  map F := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).toTruncated
  map_id A := by
    change SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (𝟙 A)).toTruncated = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, SSet.Edge.toTruncated_id]
    exact SSet.Truncated.HomotopyCategory.homMk_id _
  map_comp F G :=
    (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) F G).toTruncated).symm

variable (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u})

/-- 元の BF 値の頂点と、元の ∞ 関手の値の頂点との比較。 -/
def valueObjectIso (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : SpectrumHo.obj (value E A) ≅
    (hoFunctor.map E).toFunctor.obj (stableHoFunctor.obj A) :=
  eqToIso (congrArg SSet.HomotopyCategory.mk (value_vertex E A))

lemma valueMap_naturality {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    SpectrumHo.hom (valueMap E F) ≫ (valueObjectIso E B).hom =
      (valueObjectIso E A).hom ≫
        (hoFunctor.map E).toFunctor.map (stableHoFunctor.map F) :=
  FiberModel.homMk_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (valueMap E F)).toTruncated
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).map E).toTruncated (value_vertex E A) (value_vertex E B)
    (valueMap_edge E F)

lemma valueMap_hom {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    SpectrumHo.hom (valueMap E F) = (valueObjectIso E A).hom ≫
      (hoFunctor.map E).toFunctor.map (stableHoFunctor.map F) ≫ (valueObjectIso E B).inv := by
  have h := congrArg (fun m => m ≫ (valueObjectIso E B).inv) (valueMap_naturality E F)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- 元の BF 値と元の BF 射の類を使う実際の関手。 -/
def stableValueFunctor : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} ⥤ hoFunctor.obj Sp.{u} where
  obj A := SpectrumHo.obj (value E A)
  map F := SpectrumHo.hom (valueMap E F)
  map_id A := by
    rw [valueMap_hom, stableHoFunctor.map_id, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Iso.hom_inv_id]
  map_comp F G := by
    simp only [valueMap_hom, stableHoFunctor.map_comp,
      CategoryTheory.Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc]

/-- 完全関手の関手同型は、局所化不変量の元の値の射の等式へ移る。 -/
lemma valueMap_hom_eq_of_functorIso {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {F G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) :
    SpectrumHo.hom (valueMap E F) = SpectrumHo.hom (valueMap E G) := by
  rw [valueMap_hom, valueMap_hom]
  rw [show stableHoFunctor.map F = stableHoFunctor.map G from
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.stableArrow_homMk_eq_of_functorIso e]

end SerrePositivity.KST.LocalizingInvariants
