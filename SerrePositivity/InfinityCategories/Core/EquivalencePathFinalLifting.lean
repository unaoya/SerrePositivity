module

public import SerrePositivity.InfinityCategories.Core.PrismOpposite

/-!
概要：可逆 path の終点評価の持ち上げ性。
方針：始点を固定する延長を反転した quasicategory に適用する。
規約：終点と指定された部分複体上の prism を厳密に固定する。
使われ方：Kerodon Corollary 4.5.3.24 の終点側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：可逆な垂直辺を持つ prism は終点を固定して単射に沿って延長できる。
方針：prism を反転し、始点側の延長を使ってから元へ戻す。
規約：新しい垂直辺の可逆性はこの補題の結論には要求しない。
使われ方：Kerodon Corollary 4.5.3.24 の終点側の境界充填。 -/
lemma equivalenceHomotopy_extend_final {A B Y : SSet.{u}} [Quasicategory Y]
    (i : A ⟶ B) [Mono i] (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) (f : B ⟶ Y)
    (h₁ : prismEndpoint 1 A ≫ H = i ≫ f)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ B ⟶ Y,
      (Δ[1] ◁ i) ≫ F = H ∧ prismEndpoint 1 B ≫ F = f := by
  letI : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have h₀ : prismEndpoint 0 A.op ≫ reversePrism H =
      SSet.opFunctor.map i ≫ SSet.opFunctor.map f := by
    rw [reversePrism_endpoint]
    change SSet.opFunctor.map (prismEndpoint 1 A ≫ H) = _
    rw [h₁, CategoryTheory.Functor.map_comp]
  obtain ⟨F, hF, hF₀, _⟩ := equivalenceHomotopy_extend (SSet.opFunctor.map i)
    (reversePrism H) (SSet.opFunctor.map f) h₀ (reversePrism_vertical_isInvertible H hH)
  refine ⟨unreversePrism F, ?_, ?_⟩
  · rw [← unreversePrism_precomp, hF, unreversePrism_reversePrism]
  · rw [unreversePrism_endpoint]
    change (SSet.opFunctorCompOpFunctorIso.app B).inv ≫
      SSet.opFunctor.map (prismEndpoint 0 B.op ≫ F) ≫
        (SSet.opFunctorCompOpFunctorIso.app Y).hom = f
    rw [hF₀]
    have hn : SSet.opFunctor.map (SSet.opFunctor.map f) ≫
        (SSet.opFunctorCompOpFunctorIso.app Y).hom =
        (SSet.opFunctorCompOpFunctorIso.app B).hom ≫ f :=
      SSet.opFunctorCompOpFunctorIso.hom.naturality f
    rw [hn, Iso.inv_hom_id_assoc]

/-- 概要：可逆 path の終点評価は trivial Kan fibration。
方針：正次元では境界上の prism と終点の単体を延長し、全部分複体へ戻す。
規約：標的の quasicategory 性だけを仮定する。
使われ方：Kerodon Corollary 4.5.3.24 の終点側の評価。 -/
instance trivialKanFibration_equivalencePathEndpoint_one (Y : SSet.{u}) [Quasicategory Y] :
    TrivialKanFibration (equivalencePathEndpoint Y 1) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    refine CommSq.HasLift.mk' { l := b ≫ equivalencePathRefl Y, fac_left := ?_, fac_right := ?_ }
    · apply SSet.hom_ext
      rintro ⟨⟨d⟩⟩
      apply ConcreteCategory.hom_ext
      intro x
      have hx : x.val ∈ (boundary 0).obj (Opposite.op ⦋d⦌) := x.property
      generalize x.val = z at hx
      rw [boundary_zero] at hx
      exact False.elim hx
    · rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]
  | succ n =>
    let H := uncurry (a ≫ equivalencePathι Y)
    have hC : curry H = a ≫ equivalencePathι Y := curry_uncurry _
    have h₀ : (boundary (n + 1)).ι ≫ b =
        prismEndpoint 1 (boundary (n + 1) : SSet.{u}) ≫ H := by
      rw [← curry_evaluateFunctorAt_interval, hC]
      exact sq.w.symm
    have hH : ∀ x : (boundary (n + 1) : SSet.{u}) _⦋0⦌,
        IsInvertibleEdge (edgeOfSimplex
          (H.app (Opposite.op ⦋1⦌)
            (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
      intro x
      have hx := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
      change IsEquivalencePathVertex ((a ≫ equivalencePathι Y).app (Opposite.op ⦋0⦌) x) at hx
      rw [← hC] at hx
      unfold IsEquivalencePathVertex at hx
      rw [intervalFunctorVertexEdge_curry] at hx
      exact hx
    obtain ⟨F, hF, hF₀⟩ := equivalenceHomotopy_extend_final (boundary (n + 1)).ι H b h₀.symm hH
    have hc : (boundary (n + 1)).ι ≫ curry F = a ≫ equivalencePathι Y := by
      rw [← curry_natural_left, hF, hC]
    have hv : ∀ v : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
        IsEquivalencePathVertex ((curry F).app (Opposite.op ⦋0⦌) v) := by
      intro v
      let x : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
        ⟨v, by
          have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
          rw [Equiv.symm_apply_apply] at h
          exact h⟩
      have hx := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) x
      change (curry F).app (Opposite.op ⦋0⦌) v =
        (a.app (Opposite.op ⦋0⦌) x).val at he
      exact he.symm ▸ hx
    let g := fullSubcomplexLift IsEquivalencePathVertex (curry F) hv
    have hg : g ≫ equivalencePathι Y = curry F := fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · have : Mono (equivalencePathι Y) := by unfold equivalencePathι; infer_instance
      apply (cancel_mono (equivalencePathι Y)).1
      rw [Category.assoc, hg, hc]
    · change g ≫ equivalencePathι Y ≫ evaluateFunctorAt _ = b
      rw [← Category.assoc, hg, curry_evaluateFunctorAt_interval, hF₀]


end SerrePositivity.InfinityCategories
