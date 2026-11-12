module

public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexCoconeLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeApexIsoNormalization
public import SerrePositivity.KST.LocalizingInvariants.LocalizationEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

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
    (j : K ⟶ L) [Mono j] (F : L ⟶ X) (G : K ⟶ X) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (j ≫ F) G) :
    ∃ F' : L ⟶ X, j ≫ F' = G ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F F') := by
  let a := SSet.Edge.ofTruncated (X := (ihom K).obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e)
  obtain ⟨F', l, hl, hli⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pre_liftInvertibleEdge_source j F G a
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible e)
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F') = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G := by
    calc
      _ = ((pre j).app X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F') := rfl
      _ = ((pre j).app X).app (Opposite.op ⦋0⦌)
          (((ihom L).obj X).δ 0 l.edge) := congrArg _ l.tgt_eq.symm
      _ = ((ihom K).obj X).δ 0 (((pre j).app X).app (Opposite.op ⦋1⦌) l.edge) :=
        @map_edge_target ((ihom L).obj X) ((ihom K).obj X) ((pre j).app X) l.edge
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G := by rw [hl]; exact a.tgt_eq
  have : IsIso (Truncated.HomotopyCategory.homMk l.toTruncated) := hli
  exact ⟨F', _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective hp, ⟨asIso (Truncated.HomotopyCategory.homMk l.toTruncated)⟩⟩

private lemma pointDiagram_isEssentiallySurjective {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective q.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective ((ihom (Δ[0] : SSet.{u})).map q.hom) := by
  intro v
  obtain ⟨H, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[0] : SSet.{u}) C.obj).surjective v
  let k := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  obtain ⟨x, ⟨e⟩⟩ := hq (H.app (Opposite.op ⦋0⦌) k)
  let D : (Δ[0] : SSet.{u}) ⟶ B.obj := SSet.const x
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) k).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ q.hom)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) k).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (q.hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0))
      (H.app (Opposite.op ⦋0⦌) k)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact e
  let hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso C.obj)).isQCatEquivalence
    |>.isFullyFaithful
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D, ⟨?_⟩⟩
  exact hf.toHoFullyFaithful.preimageIso he

/-- 元の商の余錐は、任意の頂点の場合も全余錐図式の同型を保って持ち上がる。 -/
lemma exists_verdierSimplexCoconeLift_arbitraryVertex {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ q.hom)) :
    ∃ (D' : (Δ[n] : SSet.{u}) ⟶ B.obj) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D'),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (c.val ≫ q.hom) d.val) := by
  obtain ⟨z, ⟨e⟩⟩ := localization_isEssentiallySurjective q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
    h.quotient d.vertex
  obtain ⟨d', hd', ⟨ed⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cocone_apexIsoNormalization d e
  obtain ⟨D', _, c, _, _, ⟨ec⟩⟩ := exists_verdierSimplexCoconeLift h D z d' hd'
  exact ⟨D', c, ⟨ec ≪≫ ed⟩⟩

/-- 元の Verdier 商の後合成は、全次数の実標準単体図式において本質的に全射。 -/
lemma verdierProjectionSimplex_isEssentiallySurjective {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    ∀ n : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective ((ihom (Δ[n] : SSet.{u})).map q.hom) := by
  intro n
  induction n with
  | zero =>
    exact pointDiagram_isEssentiallySurjective q
      (localization_isEssentiallySurjective q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.quotient)
  | succ n ih =>
    intro v
    obtain ⟨H, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[n + 1] : SSet.{u}) C.obj).surjective v
    let J := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ H
    obtain ⟨d, ⟨e⟩⟩ := ih (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ J))
    obtain ⟨D, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[n] : SSet.{u}) B.obj).surjective d
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (D ≫ q.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫ J) at e
    obtain ⟨J', hp, ⟨eJ⟩⟩ := prefixIsoNormalization (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0]) J
      (D ≫ q.hom) e.symm
    let d' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ q.hom) := ⟨J', hp⟩
    obtain ⟨D', c, ⟨ec⟩⟩ := exists_verdierSimplexCoconeLift_arbitraryVertex h D d'
    let L := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ c.val
    have ei := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (f := c.val ≫ q.hom) (g := J)
      (ec ≪≫ eJ.symm) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv
    have hJ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ J = H := by
      dsimp [J]
      rw [Iso.inv_hom_id_assoc]
    rw [hJ] at ei
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L, ⟨?_⟩⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ q.hom) H
    simpa only [L, Category.assoc] using ei

end SerrePositivity.KST.LocalizingInvariants
