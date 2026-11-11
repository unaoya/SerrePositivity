module
public import SerrePositivity.KST.SConstruction.FamilyChainWitnessTransport

/-! # 元の全合成証人付き円柱の前合成と表示移送
概要：保存済みの全合成円柱と全木を、同じ前合成・端点表示移送へまとめる。
方針：元の全合成証人を写し、その全三角形の厳密な像を回収する。
規約：同じ入力列を合成し直さず、元の全木と全円柱を保持する。
使われ方：単一合成射の直接補正を二入力の共通パラメータへ写す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の円柱と全合成木を同じ前合成で写したデータ。 -/
def FamilyChainCompositeData.precomp {T U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} (D : FamilyChainCompositeData c) (j : T ⟶ U) :
    FamilyChainCompositeData (familyHomotopyChainPrecomp j c) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp D.homotopy j, familyChainWitnessPrecomp j D.witness⟩

/-- 前合成した実円柱は、元の同じ全円柱の前合成そのもの。 -/
lemma FamilyChainCompositeData.precomp_h {T U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} (D : FamilyChainCompositeData c) (j : T ⟶ U) :
    (D.precomp j).homotopy.h = (j ▷ (Δ[1] : SSet.{u})) ≫ D.homotopy.h := rfl

/-- 元の全合成三角形の前合成像を同じ順序で厳密に保持する。 -/
lemma FamilyChainCompositeData.precomp_triangles {T U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} (D : FamilyChainCompositeData c) (j : T ⟶ U) :
    familyChainCompositionTriangles (D.precomp j).witness =
      (familyChainCompositionTriangles D.witness).map ((j ▷ (Δ[2] : SSet.{u})) ≫ ·) :=
  familyChainWitnessPrecomp_triangles j D.witness

/-- 端点の表示だけを移し、同じ元の円柱と全合成木を保持したデータ。 -/
def FamilyChainCompositeData.endpointTransport {U E : SSet.{u}} {f g f' g' : U ⟶ E}
    {c : FamilyHomotopyChain f g} (D : FamilyChainCompositeData c) (hs : f' = f) (ht : g = g') :
    FamilyChainCompositeData
      (familyHomotopyChainSourceTransport (familyHomotopyChainTargetTransport c ht) hs) :=
  ⟨familyHomotopyEndpointTransport D.homotopy hs ht,
    familyChainWitnessEndpointTransport D.witness hs ht⟩

/-- 端点の表示移送でも、元の同じ実円柱全体を保持する。 -/
lemma FamilyChainCompositeData.endpointTransport_h {U E : SSet.{u}}
    {f g f' g' : U ⟶ E} {c : FamilyHomotopyChain f g}
    (D : FamilyChainCompositeData c) (hs : f' = f) (ht : g = g') :
    (D.endpointTransport hs ht).homotopy.h = D.homotopy.h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 端点の表示移送でも、元の同じ全合成三角形を保持する。 -/
lemma FamilyChainCompositeData.endpointTransport_triangles {U E : SSet.{u}}
    {f g f' g' : U ⟶ E} {c : FamilyHomotopyChain f g}
    (D : FamilyChainCompositeData c) (hs : f' = f) (ht : g = g') :
    familyChainCompositionTriangles (D.endpointTransport hs ht).witness =
      familyChainCompositionTriangles D.witness :=
  familyChainWitnessEndpointTransport_triangles D.witness hs ht

end SerrePositivity.KST.SConstruction
