module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactSliceCoconeRecovery
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceImageTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeIteratedSliceIso
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceIdentityTerminal

/-!
概要：元の任意の固定点射上の μ-small compact 図式の全余錐を、像が終対象となる compact 頂点に取る。
方針：正規化した全余錐を元の固定点の厳密同型で戻す。
規約：元の全図式と元の固定対象を保持する。
使われ方：fiber の全小試験図式の第一成分余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の固定対象上の compact 図式に、compact 始域と終対象像を持つ全余錐を構成する。
方針：同じ対象の正規化した表示へ移し、可算交互回収後に全余錐を戻す。
規約：第二脚に小余極限保存を要求しない。
使われ方：元の fiber の μ-small 全試験余錐の第一成分。 -/
lemma exists_compactActualSliceCocone_image_terminal
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : HasSmallColimits E) (hB : HasSmallColimits B)
    (p : E ⟶ B) (hp : PreservesSmallColimits p)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ E)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ j : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up j)))
    (hpD : ∀ j : I _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ ((D ≫ p).app _ (ULift.up j)))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ (mapJoinCocone p c).vertex)
    (a : (Δ[0] : SSet.{u + 1}) ⟶ E) (ha : SSet.yonedaEquiv.symm c.vertex = a)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver a)
    (hr : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ
      ((r ≫ sliceOverProjection a).app (Opposite.op ⦋0⦌) k)) :
    ∃ d : JoinCocone r,
      Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection a).app (Opposite.op ⦋0⦌) d.vertex) ∧
      IsTerminalVertex ((sliceOverPostcomp a p).app (Opposite.op ⦋0⦌) d.vertex) := by
  let A := eqToIso (congrArg sliceOver ha)
  let rn := r ≫ A.inv
  have hprojInv : A.inv ≫ sliceOverProjection (SSet.yonedaEquiv.symm c.vertex) =
      sliceOverProjection a := sliceOver_eqToHom_projection ha.symm
  have hrn : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ
      ((rn ≫ sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) k) := by
    dsimp only [rn]
    rw [Category.assoc, hprojInv]
    exact hr
  obtain ⟨dn, hcn, ⟨hen⟩⟩ := exists_compactSliceCocone_image_identity_of_filteredPresentation
    hμ hK hE hB p hp D c hc hD hpD hv rn hrn
  let d : JoinCocone r := ⟨dn.val ≫ A.hom, by
    rw [← Category.assoc, dn.property]
    change (r ≫ A.inv) ≫ A.hom = r
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
  have hd : d.vertex = A.hom.app (Opposite.op ⦋0⦌) dn.vertex := by
    change (mapJoinCocone A.hom dn).vertex = _
    exact Ind.mapJoinCocone_vertex A.hom dn
  have hproj : A.hom ≫ sliceOverProjection a =
      sliceOverProjection (SSet.yonedaEquiv.symm c.vertex) := sliceOver_eqToHom_projection ha
  have hb : SSet.yonedaEquiv.symm (mapJoinCocone p c).vertex = a ≫ p :=
    (coconeSliceImagePoint_eq c p).symm.trans (congrArg (fun f ↦ f ≫ p) ha)
  let Bn := eqToIso (congrArg sliceOver hb)
  have hcomm : coconeSliceImageMap c p ≫ Bn.hom = A.hom ≫ sliceOverPostcomp a p :=
    coconeSliceImageMap_transport c p a ha
  have ht : IsTerminalVertex ((coconeSliceImageMap c p).app (Opposite.op ⦋0⦌) dn.vertex) :=
    (F1B.sliceIdentityCone_isTerminalVertex _).of_vertexIso hen.symm
  have ht' := ht.map_of_isIso Bn.hom
  change IsTerminalVertex ((coconeSliceImageMap c p ≫ Bn.hom).app (Opposite.op ⦋0⦌) dn.vertex) at ht'
  rw [hcomm] at ht'
  refine ⟨d, ?_, ?_⟩
  · rw [hd]
    have hh := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) dn.vertex) hproj
    change (sliceOverProjection a).app (Opposite.op ⦋0⦌)
      (A.hom.app (Opposite.op ⦋0⦌) dn.vertex) =
      (sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) dn.vertex at hh
    rw [hh]
    exact hcn
  · rw [hd]
    exact ht'

end SerrePositivity.InfinityCategories.F2.Presentable
