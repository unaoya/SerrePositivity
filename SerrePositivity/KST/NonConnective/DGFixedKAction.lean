module

public import SerrePositivity.KST.NonConnective.FixedSpectrumAction
public import SerrePositivity.KST.Fibration.DGKPiComparison

/-!
概要：同じ厳密 dg 入力の h の等号と、固定 BF K の整数 π 作用の比較。
方針：入力を変数として端点輸送を一度証明し、具体的な cone に特殊化する。
規約：固定された dgKInputK と dgKInputSpectrumMap の実辺を使う。
使われ方：swindle と固定 K の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Fibration
open scoped Simplicial
namespace SerrePositivity.KST.NonConnective
local instance : SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 同じ通常 dg 射の豊穣頂点を、元の native 関手頂点で表示する。 -/
lemma dgFixedInputVertex (R : Type u) [CommRing R] {P Q : PerfDGInput.{u, v} R}
    (f : P ⟶ Q) :
    SimplicialCategory.homEquiv' P Q f =
      ULift.up (dgFunctorNativeMappingVertex R P Q f.down) := by
  change SSet.unitHomEquiv _ (perfDGInputUnitHomEquiv R P Q f) = _
  exact perfDGInputUnitHomEquiv_vertex R P Q f

/-- 同じ入力の h の等号を固定 BF K の同じ実自己射の整数 π 作用へ移す。 -/
lemma dgFixedKAction_eq (R : Type u) [CommRing R] (P : PerfDGInput.{u, v} R)
    (f g : P ⟶ P)
    (h : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated) (j : ℤ) :
    OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R f) j =
      OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R g) j := by
  have h := congrArg ((hoFunctor.map (dgKInputK R)).toFunctor.map) h
  change Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK R)).toTruncated =
    Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).map (dgKInputK R)).toTruncated at h
  have hf := dgKPiComparison_naturality R f j
  have hg := dgKPiComparison_naturality R g j
  have hh : CommGrpCat.ofHom (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R f) j) =
      CommGrpCat.ofHom (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R g) j) := by
    apply (cancel_epi (dgKPiComparison R P j).hom).mp
    exact hf.symm.trans ((congrArg (fun a ↦
      (SpectrumHo.piFunctor j).map a ≫ (dgKPiComparison R P j).hom) h).trans hg)
  exact congrArg (fun a ↦ a.hom) hh

end SerrePositivity.KST.NonConnective
