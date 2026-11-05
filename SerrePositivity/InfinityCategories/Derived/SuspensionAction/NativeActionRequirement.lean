module
public import SerrePositivity.InfinityCategories.Derived.DGSuspensionCoherentActionInput
public import SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.NativeIntervalIso
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.NativeEpsilonDiskObstruction

/-!
概要：最終 map と edgeIso は、入力の native 同型を固定出力の native 同型へ送る。
方針：interval Hom の後合成、採用 edgeIso、標準 Hom 比較の同型反映を合成する。
規約：ε core を経由せず、最終採用入力そのものの必要帰結を示す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)
  (a : DGSuspensionCoherentActionInput R s)
  {A B : PerfDGInput.{u, max (u + 1) v} R} {f g : A ⟶ B}

/-- 最終作用は、元の native 同型を固定 data の辺の端点固定同型へ送る。 -/
def DGSuspensionCoherentActionInput.intervalIsoOfNativeIso
    (e : VertexIso (X := dgFunctorNativeMappingSpace R A B)
      (dgFunctorNativeMappingVertex R A B f.down)
      (dgFunctorNativeMappingVertex R A B g.down)) :
    VertexIso
      (intervalMappingVertexOfEdge (coherentNerveEdge
        (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (a.data f))))
      (intervalMappingVertexOfEdge (coherentNerveEdge
        (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (a.data g)))) := by
  have h := (dgNativeInputMapIsoToInterval R A B e).map
    (intervalMappingPostOfEq a.map (coherentNerveVertex A) (coherentNerveVertex B)
      (a.vertex A) (a.vertex B))
  rw [intervalMappingPostOfEq_vertex, intervalMappingPostOfEq_vertex] at h
  exact (a.edgeIso f).symm ≪≫ h ≪≫ a.edgeIso g

/-- 端点固定比較を認めても、最終作用は固定実商関手の native 頂点同型を要求する。 -/
def DGSuspensionCoherentActionInput.nativeIsoOfNativeIso
    (e : VertexIso (X := dgFunctorNativeMappingSpace R A B)
      (dgFunctorNativeMappingVertex R A B f.down)
      (dgFunctorNativeMappingVertex R A B g.down)) :
    VertexIso (X := dgFunctorNativeMappingSpace R
      (dgKappaSuspensionKInput R A (s A).cone) (dgKappaSuspensionKInput R B (s B).cone))
      (dgFunctorNativeMappingVertex R _ _
        (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (a.data f)).down)
      (dgFunctorNativeMappingVertex R _ _
        (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (a.data g)).down) :=
  dgIntervalInputMapIsoToNative R _ _ (a.intervalIsoOfNativeIso R s e)

section Disk
variable (κ₀ : Cardinal.{u}) [Fact κ₀.IsRegular] (hκ₀ : Cardinal.aleph0 < κ₀)

/-- ε を経由しない最終作用にも必要な、同じ零／disk 入力の実商関手間の native 比較。 -/
def nativeDiskSuspensionComparisonType :=
  VertexIso (X := dgFunctorNativeMappingSpace R
    (dgKappaSuspensionKInput R (nativeDiskSourceInput.{u, v} R)
      (dgKappaConeInput_unconditional' R (nativeDiskSourceInput.{u, v} R) κ₀ hκ₀))
    (dgKappaSuspensionKInput R (nativeDiskTargetInput.{u, v} R)
      (dgKappaConeInput_unconditional' R (nativeDiskTargetInput.{u, v} R) κ₀ hκ₀)))
    (dgFunctorNativeMappingVertex R _ _
      (dgSuspensionUnconditionalInputMap R κ₀ hκ₀ (nativeDiskZeroInputMap.{u, v} R)).down)
    (dgFunctorNativeMappingVertex R _ _
      (dgSuspensionUnconditionalInputMap R κ₀ hκ₀ (nativeDiskNonzeroInputMap.{u, v} R)).down)

/-- 採用最終 map と同じ二つの data から、必要な実商関手の native 比較を回収する。 -/
def nativeDiskSuspensionComparisonOfAction
    (a : DGSuspensionCoherentActionInput R (dgKappaUnconditionalStageProvider.{u, v} R κ₀ hκ₀))
    (hf : a.data (nativeDiskZeroInputMap.{u, v} R) =
      dgSuspensionUnconditionalMapData R κ₀ hκ₀ (nativeDiskZeroInputMap.{u, v} R))
    (hg : a.data (nativeDiskNonzeroInputMap.{u, v} R) =
      dgSuspensionUnconditionalMapData R κ₀ hκ₀ (nativeDiskNonzeroInputMap.{u, v} R)) :
    nativeDiskSuspensionComparisonType.{u, v} R κ₀ hκ₀ := by
  have h := a.nativeIsoOfNativeIso R (dgKappaUnconditionalStageProvider.{u, v} R κ₀ hκ₀)
    (nativeDiskInputMapVertexIso.{u, v} R)
  rw [hf, hg] at h
  exact h

end Disk
end SerrePositivity.InfinityCategories
