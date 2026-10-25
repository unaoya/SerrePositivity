module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiberSliceCoconeRecovery
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionBaseEvaluation
public import SerrePositivity.InfinityCategories.F2.Presentable.PointFiberSliceTerminalImage
public import SerrePositivity.InfinityCategories.F2.Presentable.TerminalTargetCocones
public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.PointAccessibility
public import SerrePositivity.InfinityCategories.F2.Presentable.ComponentCompactOverCocones

/-!
概要：第一成分との全余錐同型を保持して、元の fiber 内の compact 全余錐を回収する。
方針：両像の全余錐を共通 coslice の終対象として比較し、同値持ち上げで厳密化する。
規約：第二脚の小余極限保存を要求しない。
使われ方：fiber の compact comma の μ-small 試験余錐。
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

/-- 概要：第一成分の compact 全余錐の像が終対象なら、元の fiber 内に compact 全余錐がある。
方針：点側の余錐像と全余錐同型で比較し、元の slice 引き戻しに貼り合わせる。
規約：元の全図式を固定し、第二脚に保存性を要求しない。
使われ方：全小試験図式による compact comma の filtered 判定。 -/
lemma exists_componentCompactFiberSliceCocone_comparison
    {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    {K : SSet.{u}} {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hB : HasSmallColimits B) (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : F1B.EquivalenceLifting p) (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x)
    (cE : JoinCocone (r ≫ sliceOverPostcomp x (pullback.fst p q)))
    (hcE : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌) cE.vertex))
    (htE : IsTerminalVertex ((sliceOverPostcomp (x ≫ pullback.fst p q) p).app
      (Opposite.op ⦋0⦌) cE.vertex)) :
    ∃ c : JoinCocone r,
      ComponentCompactVertex μ p q ((sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex) ∧
      Nonempty (VertexIso (X := sliceUnder (r ≫ sliceOverPostcomp x (pullback.fst p q)))
        (mapJoinCocone (sliceOverPostcomp x (pullback.fst p q)) c) cE) := by
  have : InnerFibration p := hp.innerFibration
  let P := sliceOverPostcomp (x ≫ pullback.fst p q) p
  let Q := pullbackSliceBaseMap p q x
  let s := pullbackSliceIso p q x
  let R := r ≫ s.hom
  have hR : R ≫ pullback.fst P Q = r ≫ sliceOverPostcomp x (pullback.fst p q) := by
    dsimp only [R, s, P, Q]
    rw [Category.assoc, pullbackSliceIso_hom_fst]
  let ce : JoinCocone (R ≫ pullback.fst P Q) := ⟨cE.val, by rw [hR]; exact cE.property⟩
  obtain ⟨cd, _⟩ := sliceOver_hasSmallColimits point_hasSmallColimits
    (x ≫ pullback.snd p q) K (R ≫ pullback.snd P Q)
  obtain ⟨cb, hcb⟩ := sliceOver_hasSmallColimits hB
    ((x ≫ pullback.fst p q) ≫ p) K ((R ≫ pullback.fst P Q) ≫ P)
  have hte : IsTerminalVertex (mapJoinCocone P ce).vertex := by
    rw [Ind.mapJoinCocone_vertex]
    exact htE
  have htd : IsTerminalVertex (JoinCocone.vertex (p := (R ≫ pullback.fst P Q) ≫ P)
      ((pullbackCoconeBaseMap P Q R).app (Opposite.op ⦋0⦌) cd)) := by
    rw [pullbackCoconeBaseMap_vertex]
    exact pullbackSliceBaseMap_point_isTerminal p q x cd.vertex
  let e := terminalTargetCoconeIso cb hcb
    ((pullbackCoconeBaseMap P Q R).app (Opposite.op ⦋0⦌) cd) (mapJoinCocone P ce) htd hte
  obtain ⟨d, ⟨hed⟩, _⟩ := exists_pullbackCocone_of_compatible_components P Q
    (sliceOverPostcomp_equivalenceLifting _ p hp) R ce cd e
  let c : JoinCocone r := ⟨d.val ≫ s.inv, by
    rw [← Category.assoc, d.property]
    change (r ≫ s.hom) ≫ s.inv = r
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  have hc : c.vertex = s.inv.app (Opposite.op ⦋0⦌) d.vertex := by
    change (mapJoinCocone s.inv d).vertex = _
    exact Ind.mapJoinCocone_vertex s.inv d
  have hf : s.inv ≫ sliceOverPostcomp x (pullback.fst p q) = pullback.fst P Q := by
    rw [← pullbackSliceIso_hom_fst p q x, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hproj : s.inv ≫ sliceOverProjection x ≫ pullback.fst p q =
      pullback.fst P Q ≫ sliceOverProjection (x ≫ pullback.fst p q) := by
    rw [← F1B.sliceOverPostcomp_projection x (pullback.fst p q), ← Category.assoc, hf]
  have hev : VertexIso ((pullback.fst P Q).app (Opposite.op ⦋0⦌) d.vertex) ce.vertex := by
    have hh := VertexIso.map hed (sliceUnderProjection (R ≫ pullback.fst P Q))
    change VertexIso (mapJoinCocone (pullback.fst P Q) d).vertex ce.vertex at hh
    rw [Ind.mapJoinCocone_vertex] at hh
    exact hh
  have hev' := VertexIso.map hev (sliceOverProjection (x ≫ pullback.fst p q))
  have hcompact : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌)
        ((pullback.fst P Q).app (Opposite.op ⦋0⦌) d.vertex)) :=
    (Compact.isKappaCompact_iff_of_iso hev').mpr hcE
  have hcompactC : ComponentCompactVertex μ p q
      ((sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex) := by
    refine ⟨?_, Compact.isKappaCompact_of_isInitialVertex hμ (point_vertex_isInitial _)⟩
    have hv := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) d.vertex) hproj
    change (pullback.fst p q).app (Opposite.op ⦋0⦌)
      ((sliceOverProjection x).app (Opposite.op ⦋0⦌) (s.inv.app (Opposite.op ⦋0⦌) d.vertex)) =
      (sliceOverProjection (x ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌)
        ((pullback.fst P Q).app (Opposite.op ⦋0⦌) d.vertex) at hv
    rw [hc, hv]
    exact hcompact
  let T := eqToIso (congrArg sliceUnder hR)
  have hval (v : (sliceUnder (R ≫ pullback.fst P Q)) _⦋0⦌) :
      (T.hom.app (Opposite.op ⦋0⦌) v).val = v.val := by
    have ht := sliceUnderUncurry_eqToHom hR (SSet.yonedaEquiv.symm v)
    rw [SSet.yonedaEquiv_symm_comp, sliceUnderUncurry_yoneda,
      sliceUnderUncurry_yoneda] at ht
    exact ht
  have hdmap : T.hom.app (Opposite.op ⦋0⦌) (mapJoinCocone (pullback.fst P Q) d) =
      mapJoinCocone (sliceOverPostcomp x (pullback.fst p q)) c := by
    apply Subtype.ext
    rw [hval]
    change d.val ≫ pullback.fst P Q = (d.val ≫ s.inv) ≫ _
    exact ((Category.assoc d.val s.inv (sliceOverPostcomp x (pullback.fst p q))).trans
      (congrArg (fun t ↦ d.val ≫ t) hf)).symm
  have hce : T.hom.app (Opposite.op ⦋0⦌) ce = cE := by
    apply Subtype.ext
    exact hval ce
  have hcomp := VertexIso.map hed T.hom
  rw [hdmap, hce] at hcomp
  exact ⟨c, hcompactC, ⟨hcomp⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
