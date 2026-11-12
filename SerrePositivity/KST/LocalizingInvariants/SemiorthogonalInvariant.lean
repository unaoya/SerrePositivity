module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition
public import SerrePositivity.KST.LocalizingInvariants.StableValueFunctor
public import SerrePositivity.KST.LocalizingInvariants.InvariantProductDecomposition

/-!
概要：半直交分解の切断が元の Sp 値でも切断となり、K-5 の積同値を誘導する。
方針：随伴の余単位同型を値の関手で写し、元の包含・射影を持つ Verdier 列へ適用する。
規約：Sp の安定性は仮定しない。使われ方：K-8 の Tamme 分裂。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants

namespace SemiorthogonalDecomposition
variable {A B T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition A B T)

/-- 元の右因子の包含の値は、元の射影の値の h Sp での切断。 -/
lemma value_section (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}) :
    SpectrumHo.hom (valueMap E d.rightInclusion) ≫ SpectrumHo.hom (valueMap E d.projection) =
      𝟙 (SpectrumHo.obj (value E B)) := by
  let c : B ⟶ B := (d.rightInclusion : B ⟶ T) ≫ (d.projection : T ⟶ B)
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.hom (𝟙 B : B ⟶ B).hom := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.rightInclusion.hom ≫ d.projection.hom) (𝟙 B.obj)
    exact d.sectionIso
  have h := valueMap_hom_eq_of_functorIso E (F := c) (G := 𝟙 B) e
  change (stableValueFunctor E).map c =
    (stableValueFunctor E).map (𝟙 B) at h
  simpa only [c, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    stableValueFunctor] using h

end SemiorthogonalDecomposition

namespace IsLocalizingInvariant
variable {E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hE : IsLocalizingInvariant E)
  {A B T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition A B T)

/-- 半直交分解の元の値に適用する、実 Sp 積の頂点からの同値。 -/
def semiorthogonalSplitEquivalence : SpectrumHo.obj
    (NativeSplit.product (hE.abstractFiberTriangle d.verdierSequence)) ≅
      SpectrumHo.obj (value E T) :=
  hE.splitEquivalence d.verdierSequence (SpectrumHo.hom (valueMap E d.rightInclusion))
    ((_root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.value_section d) E)

lemma semiorthogonalSplitEquivalence_inclusion : SpectrumHo.hom (Binary.inl _ _) ≫
    (hE.semiorthogonalSplitEquivalence d).hom =
      (hE.splitLeftFactorIso d.verdierSequence).inv ≫
        SpectrumHo.hom (valueMap E d.inclusion) :=
  hE.splitEquivalence_inclusion _ _ _

lemma semiorthogonalSplitEquivalence_section : SpectrumHo.hom (Binary.inr _ _) ≫
    (hE.semiorthogonalSplitEquivalence d).hom =
      (hE.splitRightFactorIso d.verdierSequence).inv ≫
        SpectrumHo.hom (valueMap E d.rightInclusion) :=
  hE.splitEquivalence_section _ _ _

lemma semiorthogonalSplitEquivalence_projection : (hE.semiorthogonalSplitEquivalence d).hom ≫
    SpectrumHo.hom (valueMap E d.projection) = SpectrumHo.hom (Binary.snd _ _) ≫
      (hE.splitRightFactorIso d.verdierSequence).inv :=
  hE.splitEquivalence_projection _ _ _

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants
