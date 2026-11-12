module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-!
概要：可逆 path による関手の置換は inner fibration。
方針：両端と内ホーンの prism の和の inner anodyne 性で持ち上げる。
規約：両端の quasicategory 性を仮定する。
使われ方：HTT §2.1.2、Kerodon §4.5.3（Tag 032Y）、Theorem 4.8.4.1（Tag 01JX）。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：二次元以上のホーンは全頂点を含む。
方針：欠ける面の番号と頂点の番号の両方と異なる番号を選ぶ。
規約：外側のホーンも含む。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆な path の頂点条件の維持。 -/
lemma vertex_mem_horn (n : ℕ) (i : Fin (n + 3)) (v : (Δ[n + 2] : SSet.{u}) _⦋0⦌) :
    v ∈ (horn (n + 2) i).obj (Opposite.op ⦋0⦌) := by
  apply (mem_horn_iff_notMem_range v i).2
  obtain ⟨j, hji, hjv⟩ := Fin.exists_ne_and_ne_of_two_lt i (v 0) (by omega)
  refine ⟨j, hji, ?_⟩
  rintro ⟨k, hk⟩
  have hk0 : k = 0 := Fin.ext (by have := k.isLt; omega)
  subst k
  exact hjv hk.symm

/-- 概要：内ホーン上の prism は両端を固定したまま延長できる。
方針：区間の境界と内ホーンの pushout-product の inner anodyne 性を使う。
規約：可逆な辺という仮定はこの延長自体には不要。
使われ方：HTT §2.1.2、Kerodon §4.5.3（Tag 032Y） の評価の inner fibration 性。 -/
lemma prism_extend_innerHorn_with_endpoints {Y : SSet.{u}} [Quasicategory Y]
    {n : ℕ} (i : Fin (n + 1)) (h0 : 0 < i) (hn : i < Fin.last n)
    (H : (Δ[1] : SSet.{u}) ⊗ (horn n i : SSet.{u}) ⟶ Y)
    (f g : (Δ[n] : SSet.{u}) ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (horn n i : SSet.{u}) ≫ H = (horn n i).ι ≫ f)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (horn n i : SSet.{u}) ≫ H = (horn n i).ι ≫ g) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Y,
      (Δ[1] ◁ (horn n i).ι) ≫ F = H ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n] ≫ F = f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n] ≫ F = g := by
  let S := boundary.{u} 1
  let T := horn.{u} n i
  let q := Subcomplex.unionProd.isPushout S T
  have hw : (S.ι ▷ (T : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ T.ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, hf, hg]
  let a := q.desc H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g) hw
  have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S T ≫ a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g := q.inr_desc _ _ _
  have hi := innerAnodyneExtensions_unionProd_ι S T (innerAnodyneExtensions.horn_ι h0 hn)
  have := hi (terminal.from Y) (InnerFibration.mem (q := terminal.from Y))
  let sq : CommSq a (Subcomplex.unionProd S T).ι (terminal.from Y)
      (terminal.from (Δ[1] ⊗ Δ[n])) := ⟨terminalIsTerminal.hom_ext _ _⟩
  let F := sq.lift
  have hF : (Subcomplex.unionProd S T).ι ≫ F = a := sq.fac_left
  have hb : (S.ι ▷ (Δ[n] : SSet.{u})) ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g := by
    rw [← Subcomplex.unionProd.ι₂_ι S T, Category.assoc, hF, ha₂]
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, ha₁]
  · have h := congrArg (fun r ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 (Δ[n] : SSet.{u}) ≫ r) hb
    dsimp only [S] at h
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero] using h
  · have h := congrArg (fun r ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 (Δ[n] : SSet.{u}) ≫ r) hb
    dsimp only [S] at h
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one] using h

/-- 概要：可逆 path で置換した関手は inner fibration。
方針：元の始域で内ホーンを充填し、両端を固定した prism を標的で充填する。
規約：可逆な垂直辺の条件はホーンが全頂点を含むことから保たれる。
使われ方：Kerodon §4.5.3（Tag 032Y）、Theorem 4.8.4.1（Tag 01JX） の還元。 -/
instance equivalencePathReplacementMap_innerFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f) where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i h0 hn =>
      constructor
      intro a b sq
      obtain ⟨c, hc⟩ := Quasicategory.hornFilling h0 hn
        (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f)
      let a' := a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f
      let H := uncurry (a' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)
      have hC : curry H = a' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y := curry_uncurry _
      have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (horn (n + 2) i : SSet.{u}) ≫ H =
          (horn (n + 2) i).ι ≫ (c ≫ f) := by
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hC]
        change (a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0 = _
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f) ≫ f = _
        rw [hc, Category.assoc]
      have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (horn (n + 2) i : SSet.{u}) ≫ H =
          (horn (n + 2) i).ι ≫ b := by
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hC]
        exact sq.w
      obtain ⟨F, hF, hF₀, hF₁⟩ := prism_extend_innerHorn_with_endpoints i h0 hn H (c ≫ f) b h₀ h₁
      have he : (horn (n + 2) i).ι ≫ curry F = a' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y := by
        rw [← curry_natural_left, hF, hC]
      have hv : ∀ v : (Δ[n + 2] : SSet.{u}) _⦋0⦌,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((curry F).app (Opposite.op ⦋0⦌) v) := by
        intro v
        let x : (horn (n + 2) i : SSet.{u}) _⦋0⦌ := ⟨v, vertex_mem_horn n i v⟩
        have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a'.app (Opposite.op ⦋0⦌) x)
        have hx' := ConcreteCategory.congr_hom (NatTrans.congr_app he (Opposite.op ⦋0⦌)) x
        change (curry F).app (Opposite.op ⦋0⦌) v =
          (a'.app (Opposite.op ⦋0⦌) x).val at hx'
        exact hx'.symm ▸ hx
      let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (curry F) hv
      have hr : r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y = curry F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
      have hr₀ : r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0 = c ≫ f := by
        change r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
        rw [← Category.assoc, hr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hF₀]
      let l := pullback.lift r c hr₀
      refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
      · apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst]
          have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
          apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)).1
          rw [Category.assoc, hr]
          exact he
        · rw [Category.assoc, pullback.lift_snd]
          exact hc.symm
      · change l ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1 = b
        rw [← Category.assoc, pullback.lift_fst]
        change r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
        rw [← Category.assoc, hr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hF₁]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
