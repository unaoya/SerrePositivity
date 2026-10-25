module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceRetractionSpace
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.EdgeCosliceMappingFiber
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceModelEquivalence

/-!
概要：終対象の終域から出る閉包内辺の、恒等射上の前合成 fiber は可縮である。
方針：元の coslice の retraction 空間を左写像空間へ移し、構成済みの厳密な fiber 同型を使う。
規約：終対象の存在は仮定。一般の局所性へは pushout の基点比較を別に接続する。
使われ方：HTT 5.5.5.14 の上辺側の指定 fiber の可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の恒等余錐を、指定終点の左写像空間の基点として保持する。 -/
def identityCoconeMappingPoint (y : C _⦋0⦌) :
    (coconeMappingSpace (SSet.yonedaEquiv.symm y) y) _⦋0⦌ :=
  ⟨cosliceIdentityCone y, by
    rw [pinchedConstant_zero]
    exact cosliceIdentityCone_projection y⟩

/-- 恒等余錐と同じ全射を持つ任意の基点でも、元の前合成 fiber は可縮。 -/
lemma generatedSource_terminal_identityMappingFiber_contractible
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    {z : C _⦋0⦌} (v : C.Edge ((generatedSourceTarget edges x).app _ s) z)
    (hv : v.edge ∈ generatedEdges edges)
    (d : (coconeMappingSpace (SSet.yonedaEquiv.symm
      ((generatedSourceTarget edges x).app _ s)) ((generatedSourceTarget edges x).app _ s)) _⦋0⦌)
    (hd : d.val.val = SSet.const ((generatedSourceTarget edges x).app _ s)) :
    IsContractibleKan (vertexFiber (edgeCosliceSourceMapping v
      ((generatedSourceTarget edges x).app _ s)) d) := by
  have hd' : d.val = cosliceIdentityCone ((generatedSourceTarget edges x).app _ s) :=
    Subtype.ext hd
  have hright := generatedSource_terminal_retractionSpace_contractible edges x s hs v hv
  have hleft := (pinchedHomLeftRightEquivalence (edgeCosliceVertex v.toTruncated)
    (cosliceIdentityCone ((generatedSourceTarget edges x).app _ s))).isContractibleKan_iff.mpr hright
  have h : IsContractibleKan (pinchedHomLeft (edgeCosliceVertex v.toTruncated) d.val) :=
    hd'.symm ▸ hleft
  exact isContractibleKan_of_iso
    (edgeCosliceSourceMappingFiberIso v ((generatedSourceTarget edges x).app _ s) d).symm h

/-- 元の辺と始点図式の表示を指定したまま、恒等基点上の同じ fiber の可縮性を戻す。 -/
lemma generatedSource_terminal_normalizedMappingFiber_contractible
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    {z : C _⦋0⦌} (v : C.Edge ((generatedSourceTarget edges x).app _ s) z)
    (hv : v.edge ∈ generatedEdges edges)
    (e : (Δ[1] : SSet.{u + 1}) ⟶ C) (he : SSet.yonedaEquiv.symm v.edge = e)
    (a : (Δ[0] : SSet.{u + 1}) ⟶ C)
    (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a)
    (ha₀ : a = SSet.yonedaEquiv.symm ((generatedSourceTarget edges x).app _ s))
    (d : (coconeMappingSpace a ((generatedSourceTarget edges x).app _ s)) _⦋0⦌)
    (hd : d.val.val = SSet.const ((generatedSourceTarget edges x).app _ s)) :
    IsContractibleKan (vertexFiber (normalizedCoconeRestrictionFiber e
      (stdSimplex.δ (1 : Fin 2)) ha ((generatedSourceTarget edges x).app _ s)) d) := by
  subst e
  subst a
  exact generatedSource_terminal_identityMappingFiber_contractible edges x s hs v hv d hd

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
