module

public import SerrePositivity.EInfinity.PowerOperation.OmegaSpectrumHoFunctor
public import SerrePositivity.EInfinity.PowerOperation.OrdinaryNerveHomotopyFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
# 元の Ω スペクトルの native nerve と同じホモトピー圏の通常関手

DAG XIII §2.2 の π/H 比較の補助。同じ coherent な辺とその実際の端点輸送を使う。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.KST.Spectra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open scoped Simplicial
local instance omegaSpectrumNativeComparisonSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

def omegaSpectrumNativeHoComparison :
    ordinaryNerveHomotopyFunctor OmegaSpectrum.{u} ⋙
      (hoFunctor.map (nerveToCoherent OmegaSpectrum.{u})).toFunctor ≅
      omegaSpectrumHoFunctor.{u} :=
  NatIso.ofComponents
    (fun X => eqToIso (congrArg HomotopyCategory.mk (nerveToCoherent_vertex X)))
    (fun {X Y} f => by
      let hx := congrArg HomotopyCategory.mk (nerveToCoherent_vertex X)
      let hy := congrArg HomotopyCategory.mk (nerveToCoherent_vertex Y)
      have h := MorphismSpaces.homMk_transport (nerveToCoherent_vertex X)
        (nerveToCoherent_vertex Y)
        (((nerve.edgeMk f).map (nerveToCoherent OmegaSpectrum.{u})).toTruncated)
        (coherentNerveEdge f).toTruncated rfl
      change SSet.HomotopyCategory.homMk
        ((nerve.edgeMk f).map (nerveToCoherent OmegaSpectrum.{u})) ≫ (eqToIso hy).hom =
        (eqToIso hx).hom ≫
          SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated
      apply (cancel_epi (eqToIso hx).inv).mp
      simpa only [hx, hy, SSet.HomotopyCategory.homMk, Category.assoc,
        Iso.inv_hom_id_assoc, eqToIso.hom, eqToIso.inv,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using h)

end SerrePositivity.EInfinity.PowerOperation
