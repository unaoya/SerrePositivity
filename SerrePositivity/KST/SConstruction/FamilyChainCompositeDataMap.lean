module
public import SerrePositivity.KST.SConstruction.FamilyChainWitnessPostcomposition
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeDataTransport

/-! # 元の全合成円柱と全木の同じ後合成
概要：保存済みの全円柱と全合成木を、同じ標的写像で後合成する。
方針：元の全証人を同じ写像で写し、全区間・全三角形の像を厳密に回収する。
規約：後合成後に合成し直さず、元の同じ実円柱を保持する。
使われ方：二入力の合成補正の前後部分を、元の単一射補正の全証人から構成する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の実円柱と全木を同じ標的写像で写したデータ。 -/
def FamilyChainCompositeData.map {U E B : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} (D : FamilyChainCompositeData c) (p : E ⟶ B) :
    FamilyChainCompositeData (familyHomotopyChainMap c p) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp D.homotopy p, familyChainWitnessPostcomp p D.witness⟩

/-- 後合成した全円柱は、元の同じ全円柱の後合成そのもの。 -/
lemma FamilyChainCompositeData.map_h {U E B : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} (D : FamilyChainCompositeData c) (p : E ⟶ B) :
    (D.map p).homotopy.h = D.homotopy.h ≫ p := rfl

/-- 後合成した全木の全入力区間は、元の同じ全 trace の同じ後合成像。 -/
lemma FamilyChainCompositeData.map_trace {U E B : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} (D : FamilyChainCompositeData c) (p : E ⟶ B) :
    familyChainCompositionInputTrace (D.map p).witness =
      (familyChainCompositionInputTrace D.witness).map (· ≫ p) :=
  familyChainWitnessPostcomp_trace p D.witness

/-- 後合成した全木の全二単体は、元の同じ全三角形の同じ後合成像。 -/
lemma FamilyChainCompositeData.map_triangles {U E B : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} (D : FamilyChainCompositeData c) (p : E ⟶ B) :
    familyChainCompositionTriangles (D.map p).witness =
      (familyChainCompositionTriangles D.witness).map (· ≫ p) :=
  familyChainWitnessPostcomp_triangles p D.witness

/-- 端点の表示移送でも、元の全 trace と区間順序は変わらない。 -/
lemma FamilyChainCompositeData.endpointTransport_trace {U E : SSet.{u}}
    {f g f' g' : U ⟶ E} {c : FamilyHomotopyChain f g}
    (D : FamilyChainCompositeData c) (hs : f' = f) (ht : g = g') :
    familyChainCompositionInputTrace (D.endpointTransport hs ht).witness =
      familyChainCompositionInputTrace D.witness := by
  simp only [familyChainCompositionInputTrace_eq, FamilyChainCompositeData.endpointTransport,
    familyHomotopyChainSourceTransport_trace, familyHomotopyChainTargetTransport_trace]

/-- 前合成した全証人の全 trace は、元の同じ全区間の前合成像。 -/
lemma FamilyChainCompositeData.precomp_trace {T U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} (D : FamilyChainCompositeData c) (j : T ⟶ U) :
    familyChainCompositionInputTrace (D.precomp j).witness =
      (familyChainCompositionInputTrace D.witness).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) :=
  familyChainWitnessPrecomp_trace j D.witness

end SerrePositivity.KST.SConstruction
