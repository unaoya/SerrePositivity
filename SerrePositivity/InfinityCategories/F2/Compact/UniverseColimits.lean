module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeUniverseFiberComparison
public import SerrePositivity.InfinityCategories.F2.Compact.CanonicalCoconeWeakEquivalence
public import SerrePositivity.InfinityCategories.F2.Compact.Preservation
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalColimit

/-!
概要：指定した空間の宇宙変更は、小さい κ-filtered 図式の元の余極限余錐を保存する。
方針：元の fiber 写像の弱同値を同じ余錐像へ移し、標準全空間余錐で判定する。
規約：値ごとの同値で代用せず、指定された元の全余錐像の余極限性を証明する。
使われ方：元の Yoneda 像の κ-compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} [Quasicategory B] {F : B ⟶ SpaceInfinity.{u}}

/-- 元の fiber 写像が弱同値なら、宇宙変更後の同じ余錐の実 fiber 写像も弱同値。 -/
lemma coconeUniverseImage_fiber_weakEquivalence (c : JoinCocone F)
    (hc : IsWeakHomotopyEquivalence (coconeFiberMap c)) :
    IsWeakHomotopyEquivalence (coconeFiberMap (coconeUniverseImage c)) := by
  have h := (weakHomotopyEquivalence_ulift (coconeFiberMap c) hc).comp
    (coconeUniverseVertexMap_isQCatEquivalence c).isWeakHomotopyEquivalence
  have h' := (weakHomotopyEquivalence_iff_of_functorIso (coconeUniverseFiberIso c)).mpr h
  have hs := (coconeUniverseSourceComparison_isPrecompositionEquivalence c)
  exact hs.isWeakHomotopyEquivalence.cancel_left h'

/-- 同じ元の fiber 写像の弱同値性から、指定された元の余錐像の余極限性を得る。 -/
lemma coconeUniverseImage_isColimit_of_fiber_weakEquivalence (c : JoinCocone F)
    (hc : IsWeakHomotopyEquivalence (coconeFiberMap c)) :
    IsColimitCone (coconeUniverseImage c) :=
  isColimitCone_of_coconeFiberMap_weakEquivalence _
    (coconeUniverseImage_fiber_weakEquivalence c hc)

/-- 元の小さい任意の coherent 図式の指定余極限余錐を、同じ宇宙変更が保存する。 -/
lemma spaceUniverseDiagram_map_isColimit {I : SSet.{u}} [Quasicategory I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ SpaceInfinity.{u})
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (coconeUniverseImage c) := by
  let d := coherentDiagramTotalCocone D
  have hd : IsColimitCone d := coherentDiagramTotalCocone_isColimit D
  have hFd : IsColimitCone (coconeUniverseImage d) :=
    coconeUniverseImage_isColimit_of_fiber_weakEquivalence d
      (coherentTotalCoconeFiber_isWeakHomotopyEquivalence D)
  let c' := JoinCocone.ulift.{u + 1, u + 2} c
  let d' := JoinCocone.ulift.{u + 1, u + 2} d
  have hc' : IsColimitCone c' := (isColimitCone_iff_ulift c).mp hc
  have hd' : IsColimitCone d' := (isColimitCone_iff_ulift d).mp hd
  exact hFd.of_functorIso
    ((coconeFunctorIsoOfVertexIso d' c' (colimitConeIso d' c' hd' hc')).postcomp
      spaceUniverseDiagram)

/-- 指定した同じ宇宙変更は、小さい κ-filtered 図式の元の余極限余錐を保存する。 -/
lemma spaceUniverseDiagram_preservesKappaFilteredColimits (κ : Cardinal.{u}) :
    PreservesKappaFilteredColimits.{u, u + 1} κ spaceUniverseDiagram.{u} := by
  intro I hI hFiltered D c hc
  exact spaceUniverseDiagram_map_isColimit D c hc

end SerrePositivity.InfinityCategories.F2.Compact
