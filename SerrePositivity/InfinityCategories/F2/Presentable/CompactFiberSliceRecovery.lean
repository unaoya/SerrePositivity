module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceImageMap
public import SerrePositivity.InfinityCategories.F2.Presentable.PointIdentityConeTransport
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackSliceVertexCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.PointAccessibility
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeIteratedSliceIso

/-!
概要：正規化した固定標的 slice の恒等錐比較から元の fiber 内の compact 始域の射を回収する。
方針：固定点の厳密同型で元の slice へ戻し、同値持ち上げによる全 slice 引き戻し比較を使う。
規約：元の fiber の指定対象への実際の射を返す。
使われ方：可算交互構成の compact 射の終段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：像が恒等錐と同型な compact 始域の射は元の fiber の compact 始域の射へ移る。
方針：両側の固定点移送の全可換式と元の引き戻し slice 比較を合成する。
規約：第二脚は任意の点射で、全小余極限保存を要求しない。
使われ方：fiber の各対象上の compact 生成候補の回収。 -/
lemma exists_componentCompactFiberOver_of_normalized_slice
    {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    {K : SSet.{u + 1}} {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B) (hp : F1B.EquivalenceLifting p)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    {D : K ⟶ E} (c : JoinCocone D)
    (hx : SSet.yonedaEquiv.symm c.vertex = x ≫ pullback.fst p q)
    (v : (sliceOver (SSet.yonedaEquiv.symm c.vertex)) _⦋0⦌)
    (hv : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) v))
    (e : VertexIso ((coconeSliceImageMap c p).app (Opposite.op ⦋0⦌) v)
      (sliceIdentityCone (mapJoinCocone p c).vertex)) :
    ∃ w : (sliceOver x) _⦋0⦌,
      ComponentCompactVertex μ p q ((sliceOverProjection x).app (Opposite.op ⦋0⦌) w) := by
  have hb : SSet.yonedaEquiv.symm (mapJoinCocone p c).vertex =
      (x ≫ pullback.fst p q) ≫ p :=
    (coconeSliceImagePoint_eq c p).symm.trans (congrArg (fun f ↦ f ≫ p) hx)
  let a := eqToIso (congrArg sliceOver hx)
  let b := eqToIso (congrArg sliceOver hb)
  let vE := a.hom.app (Opposite.op ⦋0⦌) v
  let vD := pointIdentityCone (x ≫ pullback.snd p q)
  have hP : coconeSliceImageMap c p ≫ b.hom =
      a.hom ≫ sliceOverPostcomp (x ≫ pullback.fst p q) p := by
    apply sliceOverUncurry_injective ((x ≫ pullback.fst p q) ≫ p)
    change sliceOverUncurry (coconeSliceImageMap c p ≫ eqToHom (congrArg sliceOver hb)) =
      sliceOverUncurry (eqToHom (congrArg sliceOver hx) ≫
        sliceOverPostcomp (x ≫ pullback.fst p q) p)
    rw [sliceOverUncurry_eqToHom hb, sliceOverUncurry_postcomp]
    have ha := sliceOverUncurry_eqToHom hx (𝟙 (sliceOver (SSet.yonedaEquiv.symm c.vertex)))
    simp only [Category.id_comp] at ha
    rw [ha]
    simpa only [Category.id_comp] using coconeSliceImageMap_uncurry c p
      (𝟙 (sliceOver (SSet.yonedaEquiv.symm c.vertex)))
  have he := VertexIso.map e b.hom
  change VertexIso ((coconeSliceImageMap c p ≫ b.hom).app (Opposite.op ⦋0⦌) v)
    (b.hom.app (Opposite.op ⦋0⦌) (sliceIdentityCone (mapJoinCocone p c).vertex)) at he
  rw [hP] at he
  have hid : b.hom.app (Opposite.op ⦋0⦌) (sliceIdentityCone (mapJoinCocone p c).vertex) =
      pointIdentityCone ((x ≫ pullback.fst p q) ≫ p) := by
    rw [← pointIdentityCone_yoneda]
    exact pointIdentityCone_eqToHom hb
  rw [hid] at he
  have he' : VertexIso ((pullbackSliceBaseMap p q x).app (Opposite.op ⦋0⦌) vD)
      ((sliceOverPostcomp (x ≫ pullback.fst p q) p).app (Opposite.op ⦋0⦌) vE) := by
    dsimp only [vD]
    rw [pullbackSliceBaseMap_pointIdentityCone]
    exact he.symm
  have hvE : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌) vE) := by
    have ht := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v) (sliceOver_eqToHom_projection hx)
    change (sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌) vE =
      (sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) v at ht
    rw [ht]
    exact hv
  exact exists_componentCompactOverVertex_of_compatible_sources p q hp x vE vD he' hvE
    (Compact.isKappaCompact_of_isInitialVertex hμ (point_vertex_isInitial _))

end SerrePositivity.InfinityCategories.F2.Presentable
