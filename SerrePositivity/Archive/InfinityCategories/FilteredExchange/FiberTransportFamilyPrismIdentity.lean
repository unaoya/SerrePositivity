module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyComparisonComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoCurryIdentity

/-!
概要：元の実 prism の一致は全輸送証拠を同定し、同じ証拠との指定比較は恒等となる。
方針：終点 fiber の包含の単射性と、元の三比較の合成則を使う。
規約：元の指定比較を保持。使われ方：恒等係数での普遍輸送比較の余分な因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K L : SSet.{u}} (p : E ⟶ B) {a b : B _⦋0⦌}
  (f : K ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)

/-- 同じ元の実 prism を持つ二つの輸送族の実終点は厳密に一致する。 -/
lemma fiberTransportFamily_endpoint_eq_of_prism
    (T U : FiberTransportFamily (b := b) p f γ) (h : T.prism = U.prism) :
    T.endpoint = U.endpoint := by
  apply (cancel_mono (vertexFiberι p b)).mp
  exact T.finish.symm.trans ((congrArg (fun H ↦ prismEndpoint 1 (K ⊗ L) ≫ H) h).trans U.finish)

/-- 同じ元の実 prism を持つ二つの輸送族は、全データとして厳密に一致する。 -/
lemma fiberTransportFamily_eq_of_prism
    (T U : FiberTransportFamily (b := b) p f γ) (h : T.prism = U.prism) : T = U := by
  have he := fiberTransportFamily_endpoint_eq_of_prism p f γ T U h
  cases T
  cases U
  cases he
  cases h
  rfl

/-- 同じ元の輸送証拠との指定終点比較は、元の実終点の恒等比較。 -/
lemma fiberTransportFamily_endpointIso_refl [LeftFibration p]
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T : FiberTransportFamily (b := b) p f γ) :
    T.endpointIso p f γ h₁ T =
      Iso.refl (SSet.HomotopyCategory.mk (functorVertex T.endpoint)) := by
  let e := T.endpointIso p f γ h₁ T
  have h := fiberTransportFamily_endpointIso_trans p f γ h₁ T T T
  change e ≪≫ e = e at h
  have hh := congrArg (fun z ↦ e.symm ≪≫ z) h
  simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using hh

/-- 同じ元の輸送証拠との指定全作用比較も、元の全作用の恒等比較。 -/
lemma fiberTransportFamily_mapIso_refl [LeftFibration p]
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T : FiberTransportFamily (b := b) p f γ) :
    T.mapIso p f γ h₁ T = Iso.refl (SSet.HomotopyCategory.mk (functorVertex T.map)) := by
  haveI : KanComplex (vertexFiber p b) := vertexFiber_kanComplex_of_leftFibration p b
  unfold FiberTransportFamily.mapIso
  rw [fiberTransportFamily_endpointIso_refl p f γ h₁ T]
  exact functorIso_curry_refl T.endpoint

end SerrePositivity.InfinityCategories.F2
