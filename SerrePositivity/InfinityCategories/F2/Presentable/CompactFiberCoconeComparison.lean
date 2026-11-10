module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactFiberOverProjection
public import SerrePositivity.InfinityCategories.F2.Presentable.FiberSliceCoconeComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.FullSubcomplexCosliceFaithful
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeIsoTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexCoconeLift

/-!
概要：compact 始域 slice 内の全余錐同型を保って、元の compact fiber comma の全余錐を回収する。
方針：周囲の slice で回収し、全部分包含上の coslice の充満忠実性で全同型を戻す。
規約：元の全図式と全余錐の同型を保持する。
使われ方：compact comma 射影の指定始点の下の cofinal 比較。
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

/-- 概要：終対象像を持つ第一成分の全余錐を、compact comma の全余錐と同型に回収する。
方針：元の fiber へ回収した全余錐を全部分圏へ持ち上げ、第一成分との全同型を反映する。
規約：第二脚の全小余極限保存は不要。
使われ方：指定した第一成分の coslice 余錐との貼り合わせ。 -/
lemma exists_compactFiberCocone_with_firstComparison
    {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) {K : SSet.{u}}
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits B) (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : F1B.EquivalenceLifting p) (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ componentCompactOver μ p q x)
    (ce : JoinCocone (r ≫ componentCompactOverFst μ p q x))
    (hte : IsTerminalVertex ((sliceOverPostcomp (x ≫ pullback.fst p q) p).app
      (Opposite.op ⦋0⦌) ce.vertex.val)) :
    ∃ c : JoinCocone r, Nonempty
      (VertexIso (X := sliceUnder (r ≫ componentCompactOverFst μ p q x))
        (mapJoinCocone (componentCompactOverFst μ p q x) c) ce) := by
  have : InnerFibration p := hp.innerFibration
  let P := fun v : (sliceOver x) _⦋0⦌ ↦
    ComponentCompactVertex μ p q ((sliceOverProjection x).app _ v)
  let Q := fun v : (sliceOver (x ≫ pullback.fst p q)) _⦋0⦌ ↦
    Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection (x ≫ pullback.fst p q)).app _ v)
  let jr := (fullSubcomplexOnVertices (sliceOver x) P).ι
  let je := (fullSubcomplexOnVertices (sliceOver (x ≫ pullback.fst p q)) Q).ι
  let F := componentCompactOverFst μ p q x
  let s := sliceOverPostcomp x (pullback.fst p q)
  have hF : F ≫ je = jr ≫ s := componentCompactOverFst_inclusion μ p q x
  let re := r ≫ jr
  have hbase : (r ≫ F) ≫ je = re ≫ s := by
    rw [Category.assoc, hF, ← Category.assoc]
  let ce' : JoinCocone (re ≫ s) := ⟨ce.val ≫ je, by
    rw [← Category.assoc, ce.property, hbase]⟩
  have hce : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ pullback.fst p q)).app _ ce'.vertex) := by
    change Q (mapJoinCocone je ce).vertex
    rw [Ind.mapJoinCocone_vertex]
    exact fullSubcomplexOnVertices_vertex ce.vertex
  have hte' : IsTerminalVertex ((sliceOverPostcomp (x ≫ pullback.fst p q) p).app
      (Opposite.op ⦋0⦌) ce'.vertex) := by
    change IsTerminalVertex ((sliceOverPostcomp (x ≫ pullback.fst p q) p).app _
      (mapJoinCocone je ce).vertex)
    rw [Ind.mapJoinCocone_vertex]
    exact hte
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_componentCompactFiberSliceCocone_comparison
    hμ hB p q hp x re ce' hce hte'
  let c := fullSubcomplexCoconeLift P r d hd
  have hc : c.val ≫ jr = d.val := congrArg Subtype.val
    (fullSubcomplexCoconeLift_inclusion P r d hd)
  have hv : (mapJoinCocone s d).val = (mapJoinCocone je (mapJoinCocone F c)).val := by
    change d.val ≫ s = (c.val ≫ F) ≫ je
    rw [Category.assoc, hF, ← Category.assoc, hc]
  let e' : VertexIso (X := sliceUnder ((r ≫ F) ≫ je))
      (mapJoinCocone je (mapJoinCocone F c)) (mapJoinCocone je ce) :=
    coconeVertexIso_transport_values hbase.symm hv rfl e
  have hff := fullSubcomplex_coslicePostcomp_isFullyFaithful Q
    (fun h ↦ compactSourceSlicePredicate_iff_vertexIso μ (x ≫ pullback.fst p q) h) (r ≫ F)
  let e'' : VertexIso (X := sliceUnder (r ≫ F)) (mapJoinCocone F c) ce :=
    hff.toHoFullyFaithful.preimageIso
      (X := HomotopyCategory.mk (mapJoinCocone F c)) (Y := HomotopyCategory.mk ce) e'
  exact ⟨c, ⟨e''⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
