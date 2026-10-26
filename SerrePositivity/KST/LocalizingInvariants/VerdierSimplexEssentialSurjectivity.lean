module

public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexCoconeLift
public import SerrePositivity.KST.LocalizingInvariants.CoconeApexIsoNormalization
public import SerrePositivity.KST.LocalizingInvariants.LocalizationEssentialSurjectivity
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismEdgeLifting
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：元の Verdier 商の後合成は、全有限線型図式の関手圏で本質的に全射。
方針：前段を厳密化し、余錐頂点を商の像へ揃え、実右分数の余錐持ち上げを帰納的に適用する。
規約：全次数（零次を含む）と全 FunctorIso を扱う。core 逆像の亜群化同値は別の工程。
使われ方：c5 の同じ標準単体商比較の対象側の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

private lemma map_edge_target {E Y : SSet.{u}} (p : E ⟶ Y) (v : E _⦋1⦌) :
    p.app (Opposite.op ⦋0⦌) (E.δ 0 v) = Y.δ 0 (p.app (Opposite.op ⦋1⦌) v) :=
  ConcreteCategory.congr_hom (C := Type u)
    (p.naturality (SimplexCategory.δ (0 : Fin 2)).op) v

private lemma prefixIsoNormalization {K L X : SSet.{u}} [Quasicategory X]
    (j : K ⟶ L) [Mono j] (F : L ⟶ X) (G : K ⟶ X) (e : FunctorIso (j ≫ F) G) :
    ∃ F' : L ⟶ X, j ≫ F' = G ∧ Nonempty (FunctorIso F F') := by
  let a := SSet.Edge.ofTruncated (X := (ihom K).obj X) (FunctorIso.edge e)
  obtain ⟨F', l, hl, hli⟩ := pre_liftInvertibleEdge_source j F G a
    (FunctorIso.edge_isInvertible e)
  have hp : functorVertex (j ≫ F') = functorVertex G := by
    calc
      _ = ((pre j).app X).app (Opposite.op ⦋0⦌) (functorVertex F') := rfl
      _ = ((pre j).app X).app (Opposite.op ⦋0⦌)
          (((ihom L).obj X).δ 0 l.edge) := congrArg _ l.tgt_eq.symm
      _ = ((ihom K).obj X).δ 0 (((pre j).app X).app (Opposite.op ⦋1⦌) l.edge) :=
        @map_edge_target ((ihom L).obj X) ((ihom K).obj X) ((pre j).app X) l.edge
      _ = functorVertex G := by rw [hl]; exact a.tgt_eq
  have : IsIso (Truncated.HomotopyCategory.homMk l.toTruncated) := hli
  exact ⟨F', functorVertex_injective hp, ⟨asIso (Truncated.HomotopyCategory.homMk l.toTruncated)⟩⟩

private lemma pointDiagram_isEssentiallySurjective {B C : StableCategory.{u}}
    (q : ExactMap B C) (hq : IsEssentiallySurjective q.hom) :
    IsEssentiallySurjective ((ihom (Δ[0] : SSet.{u})).map q.hom) := by
  intro v
  obtain ⟨H, rfl⟩ := (functorVertexEquiv (Δ[0] : SSet.{u}) C.obj).surjective v
  let k := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  obtain ⟨x, ⟨e⟩⟩ := hq (H.app (Opposite.op ⦋0⦌) k)
  let D : (Δ[0] : SSet.{u}) ⟶ B.obj := SSet.const x
  have he : VertexIso
      ((evaluateFunctorAt (Y := C.obj) k).app (Opposite.op ⦋0⦌) (functorVertex (D ≫ q.hom)))
      ((evaluateFunctorAt (Y := C.obj) k).app (Opposite.op ⦋0⦌) (functorVertex H)) := by
    rw [evaluateFunctorAt_functorVertex, evaluateFunctorAt_functorVertex]
    change VertexIso (q.hom.app (Opposite.op ⦋0⦌) (PinchedHom.constant x 0))
      (H.app (Opposite.op ⦋0⦌) k)
    rw [pinchedConstant_zero]
    exact e
  let hf := (qCatEquivalenceOfIso (pointFunctorEvaluationIso C.obj)).isQCatEquivalence
    |>.isFullyFaithful
  refine ⟨functorVertex D, ⟨?_⟩⟩
  exact hf.toHoFullyFaithful.preimageIso he

/-- 元の商の余錐は、任意の頂点の場合も全余錐図式の同型を保って持ち上がる。 -/
lemma exists_verdierSimplexCoconeLift_arbitraryVertex {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) (d : JoinCocone (D ≫ q.hom)) :
    ∃ (D' : (Δ[n] : SSet.{u}) ⟶ B.obj) (c : JoinCocone D'),
      Nonempty (FunctorIso (c.val ≫ q.hom) d.val) := by
  obtain ⟨z, ⟨e⟩⟩ := localization_isEssentiallySurjective q.hom (weakEquivalences i)
    h.quotient d.vertex
  obtain ⟨d', hd', ⟨ed⟩⟩ := exists_cocone_apexIsoNormalization d e
  obtain ⟨D', _, c, _, _, ⟨ec⟩⟩ := exists_verdierSimplexCoconeLift h D z d' hd'
  exact ⟨D', c, ⟨ec ≪≫ ed⟩⟩

/-- 元の Verdier 商の後合成は、全次数の実標準単体図式において本質的に全射。 -/
lemma verdierProjectionSimplex_isEssentiallySurjective {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q) :
    ∀ n : ℕ, IsEssentiallySurjective ((ihom (Δ[n] : SSet.{u})).map q.hom) := by
  intro n
  induction n with
  | zero =>
    exact pointDiagram_isEssentiallySurjective q
      (localization_isEssentiallySurjective q.hom (weakEquivalences i) h.quotient)
  | succ n ih =>
    intro v
    obtain ⟨H, rfl⟩ := (functorVertexEquiv (Δ[n + 1] : SSet.{u}) C.obj).surjective v
    let J := (joinStdSimplexIso n 0).hom ≫ H
    obtain ⟨d, ⟨e⟩⟩ := ih (functorVertex (joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ J))
    obtain ⟨D, rfl⟩ := (functorVertexEquiv (Δ[n] : SSet.{u}) B.obj).surjective d
    change FunctorIso (D ≫ q.hom) (joinInl Δ[n] Δ[0] ≫ J) at e
    obtain ⟨J', hp, ⟨eJ⟩⟩ := prefixIsoNormalization (joinInl Δ[n] Δ[0]) J
      (D ≫ q.hom) e.symm
    let d' : JoinCocone (D ≫ q.hom) := ⟨J', hp⟩
    obtain ⟨D', c, ⟨ec⟩⟩ := exists_verdierSimplexCoconeLift_arbitraryVertex h D d'
    let L := (joinStdSimplexIso n 0).inv ≫ c.val
    have ei := FunctorIso.precomp (f := c.val ≫ q.hom) (g := J)
      (ec ≪≫ eJ.symm) (joinStdSimplexIso n 0).inv
    have hJ : (joinStdSimplexIso n 0).inv ≫ J = H := by
      dsimp [J]
      rw [Iso.inv_hom_id_assoc]
    rw [hJ] at ei
    refine ⟨functorVertex L, ⟨?_⟩⟩
    change FunctorIso (L ≫ q.hom) H
    simpa only [L, Category.assoc] using ei

end SerrePositivity.KST.LocalizingInvariants
