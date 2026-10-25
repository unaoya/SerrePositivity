module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceEdges
public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismPointEdges
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Stable.CoconeFactorization

/-!
概要：固定始域の閉包内射を、閉包内の指定終域辺に沿って輸送する。
方針：全 coslice の同じ標準輸送辺を、脚の合成閉性によって全部分圏へ戻す。
規約：指定辺そのものを被覆する。終対象がある場合の戻り辺も同じ圏内で回収する。
使われ方：HTT 5.5.5.14 の終対象から局所性への準備。
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

/-- 元の閉包内終域辺を、固定始域の閉包内射圏の実辺へ持ち上げる。 -/
lemma generatedSource_lift_generatedEdge (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) {z : C _⦋0⦌}
    (u : C.Edge ((generatedSourceTarget edges x).app _ s) z)
    (hu : u.edge ∈ generatedEdges edges) :
    ∃ t : (generatedSourceCategory edges x) _⦋0⦌,
      ∃ k : (generatedSourceCategory edges x).Edge s t,
        (k.map (generatedSourceTarget edges x)).edge = u.edge := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let v := initialFiberVertexAt p s.val ((generatedSourceTarget edges x).app _ s) rfl
  let w := (edgeTransport p u).app (Opposite.op ⦋0⦌) v
  let k := standardTransportPointEdge p u v
  have hk : (k.map p).edge = u.edge := standardTransportPointEdge_projection p u v
  have ht : (JoinCocone.leg w.val (𝟙 Δ[0])).edge ∈ generatedEdges edges := by
    apply (stronglySaturatedClosure_stronglySaturated
      (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.2.1
      (JoinCocone.legCompStruct k.toTruncated (𝟙 Δ[0]))
      (fullSubcomplexOnVertices_vertex s)
    change (k.map p).edge ∈ generatedEdges edges
    rw [hk]
    exact hu
  let t : (generatedSourceCategory edges x) _⦋0⦌ :=
    ⟨w.val, by
      intro a
      have ha : a = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      change (JoinCocone.leg (((sliceUnder (SSet.yonedaEquiv.symm x)).map a.op) w.val)
        (𝟙 Δ[0])).edge ∈ generatedEdges edges
      rw [ha, op_id, Functor.map_id_apply]
      exact ht⟩
  let k' : (generatedSourceCategory edges x).Edge s t :=
    { edge := ⟨k.edge, by
        intro a
        change ⦋0⦌ ⟶ ⦋1⦌ at a
        generalize ha : a.toOrderHom 0 = j
        fin_cases j
        · have h : a = SimplexCategory.δ (1 : Fin 2) := by
            ext i
            fin_cases i
            exact congrArg Fin.val ha
          subst a
          change (JoinCocone.leg ((sliceUnder (SSet.yonedaEquiv.symm x)).δ 1 k.edge)
            (𝟙 Δ[0])).edge ∈ generatedEdges edges
          rw [k.src_eq]
          exact fullSubcomplexOnVertices_vertex s
        · have h : a = SimplexCategory.δ (0 : Fin 2) := by
            ext i
            fin_cases i
            exact congrArg Fin.val ha
          subst a
          change (JoinCocone.leg ((sliceUnder (SSet.yonedaEquiv.symm x)).δ 0 k.edge)
            (𝟙 Δ[0])).edge ∈ generatedEdges edges
          rw [k.tgt_eq]
          exact ht⟩
      src_eq := Subtype.ext k.src_eq
      tgt_eq := Subtype.ext k.tgt_eq }
  exact ⟨t, k', hk⟩

/-- 終対象から持ち上げた同じ辺は、元の固定始域圏内でホモトピー圏の戻り辺を持つ。 -/
lemma generatedSource_terminal_generatedEdge_retraction (edges : I → C _⦋1⦌)
    (x : C _⦋0⦌) (s : (generatedSourceCategory edges x) _⦋0⦌)
    (hs : IsTerminalVertex s) {z : C _⦋0⦌}
    (u : C.Edge ((generatedSourceTarget edges x).app _ s) z)
    (hu : u.edge ∈ generatedEdges edges) :
    ∃ t : (generatedSourceCategory edges x) _⦋0⦌,
      ∃ k : (generatedSourceCategory edges x).Edge s t,
      ∃ r : Truncated.Edge (X := (truncation 2).obj (generatedSourceCategory edges x)) t s,
        (k.map (generatedSourceTarget edges x)).edge = u.edge ∧
        Truncated.HomotopyCategory.homMk k.toTruncated ≫
          Truncated.HomotopyCategory.homMk r = 𝟙 (HomotopyCategory.mk s) := by
  obtain ⟨t, k, hk⟩ := generatedSource_lift_generatedEdge edges x s u hu
  obtain ⟨r⟩ := hs.nonempty_edge t
  exact ⟨t, k, r, hk, hs.isTerminalHo.hom_ext _ _⟩

/-- 終対象の終域から出る閉包内辺は、元のホモトピー圏で実際に分裂する。 -/
lemma generatedSource_terminal_generatedEdge_isSplitMono (edges : I → C _⦋1⦌)
    (x : C _⦋0⦌) (s : (generatedSourceCategory edges x) _⦋0⦌)
    (hs : IsTerminalVertex s) {z : C _⦋0⦌}
    (u : C.Edge ((generatedSourceTarget edges x).app _ s) z)
    (hu : u.edge ∈ generatedEdges edges) :
    IsSplitMono (Truncated.HomotopyCategory.homMk u.toTruncated) := by
  let p := generatedSourceTarget edges x
  obtain ⟨t, k, r, hk, hkr⟩ :=
    generatedSource_terminal_generatedEdge_retraction edges x s hs u hu
  have hm : Truncated.HomotopyCategory.homMk (k.map p).toTruncated ≫
      Truncated.HomotopyCategory.homMk (r.map ((truncation 2).map p)) =
        𝟙 (HomotopyCategory.mk (p.app _ s)) := by
    let F := (hoFunctor.map p).toFunctor
    calc
      _ = F.map (Truncated.HomotopyCategory.homMk k.toTruncated ≫
          Truncated.HomotopyCategory.homMk r) := (F.map_comp _ _).symm
      _ = F.map (𝟙 (HomotopyCategory.mk s)) := congrArg F.map hkr
      _ = _ := F.map_id _
  have htz : p.app _ t = z := by
    have ht := (k.map p).tgt_eq
    rw [hk] at ht
    exact ht.symm.trans u.tgt_eq
  have hmove := homMk_comp_eqToHom_of_edge_eq (k.map p).toTruncated u.toTruncated htz hk
  rw [← hmove]
  have : IsSplitMono (Truncated.HomotopyCategory.homMk (k.map p).toTruncated) :=
    ⟨⟨⟨Truncated.HomotopyCategory.homMk (r.map ((truncation 2).map p)), hm⟩⟩⟩
  infer_instance

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
