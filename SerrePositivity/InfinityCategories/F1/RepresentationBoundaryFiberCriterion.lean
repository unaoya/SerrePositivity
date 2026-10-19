module

public import SerrePositivity.InfinityCategories.F1.LeftTransportRepresentation

/-!
概要：表現の fiber ごとの同値性を全頂点を含む部分底で検査する。
方針：引き戻しの fiber 同型で同値性を反映し、正次元の境界の頂点全射性を使う。
規約：比較射の厳密な延長の存在は別に証明する必要がある。
使われ方：Kerodon Theorem 5.6.5.12、境界を固定した延長後の表現条件の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance representationBoundaryPullbackLeftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) : LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：全頂点を被覆する底変換は fiber ごとの同値性を保ち、かつ反映する。
方針：被覆の頂点上で引き戻しの fiber 同型を消去する。
規約：底の quasicategory 性も底変換の単射性も不要。
使われ方：Kerodon §5.6.5、既存の境界表現から延長後の同値性を回収する。 -/
lemma fiberComparisonBaseChange_fibers_iff_of_vertexSurjective
    {E E' B D : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) (g : D ⟶ B)
    (hg : Function.Surjective (g.app (Opposite.op ⦋0⦌))) :
    (∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)) ↔
      ∀ d : D _⦋0⦌, IsQCatEquivalence (vertexFiberMap (pullback.snd p g) (pullback.snd q g)
        (fiberComparisonBaseChange p q f hf g)
        (fiberComparisonBaseChange_projection p q f hf g) d) := by
  constructor
  · intro h d
    exact fiberComparisonBaseChange_isQCatEquivalence_fibers p q f hf h g d
  · intro h b
    obtain ⟨d, rfl⟩ := hg b
    apply (qCatEquivalenceOfIso (vertexFiberPullbackIso p g d)).isQCatEquivalence.cancel_left
    change IsQCatEquivalence ((vertexFiberPullbackIso p g d).hom ≫
      vertexFiberMap p q f hf (g.app (Opposite.op ⦋0⦌) d))
    rw [← fiberComparisonBaseChange_fiber p q f hf g d]
    exact (h d).comp (qCatEquivalenceOfIso (vertexFiberPullbackIso q g d)).isQCatEquivalence

/-- 概要：正次元の標準単体上の比較の全 fiber の同値性は境界上で判定できる。
方針：境界が全頂点を含むことを頂点全射の判定に適用する。
規約：零次元の単体は含めず、比較射の延長自体の存在も主張しない。
使われ方：Kerodon Theorem 5.6.5.12、境界付き表現の延長の fiber 条件。 -/
lemma leftFibration_fiberEquivalence_iff_boundary {n : ℕ} {E E' : SSet.{u}}
    (p : E ⟶ Δ[n + 1]) (q : E' ⟶ Δ[n + 1]) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) :
    (∀ b : (Δ[n + 1] : SSet.{u}) _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)) ↔
      ∀ d : (boundary (n + 1) : SSet.{u}) _⦋0⦌,
        IsQCatEquivalence (vertexFiberMap (pullback.snd p (boundary (n + 1)).ι)
          (pullback.snd q (boundary (n + 1)).ι)
          (fiberComparisonBaseChange p q f hf (boundary (n + 1)).ι)
          (fiberComparisonBaseChange_projection p q f hf (boundary (n + 1)).ι) d) := by
  apply fiberComparisonBaseChange_fibers_iff_of_vertexSurjective
  intro b
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
  exact ⟨⟨stdSimplex.obj₀Equiv.symm i, vertex_mem_boundary n i⟩, rfl⟩

end SerrePositivity.InfinityCategories
