module
public import SerrePositivity.KST.SConstruction.RelativeMcCarthySection

/-! # θ の相対 quotient の所属
概要：点ごとに可逆な θ の全時刻で quotient の B 所属が保たれる。
方針：可変時刻の図式を ρ の終端と関手同型で比較し、各 Ar 成分で replete 性を使う。
規約：θ の quotient を厳密に固定したとは主張しない。使われ方：相対左 fiber への θ の持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全 Ar 成分の所属条件は実図式の関手同型で保たれる。 -/
lemma ObjectSInClosed.of_functorIso {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {n : SimplexCategoryᵒᵖ} {v w : (objectSConstruction X.carrier).obj n}
    (hv : ObjectSInClosed P v) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (gappedDiagram v) (gappedDiagram w)) :
    ObjectSInClosed P w := by
  intro a
  have ea := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at ea
  exact P.of_iso (hv a) ea

/-- θ の quotient の全成分条件は元の fiber の quotient から同型で輸送される。 -/
lemma mcCarthyThetaObject_quotient_in_closed {X : StableModel.{u}} (B : ClosedStablePredicate X)
    {m n : ℕ} (a : (objectSConstruction X.carrier) _⦋m⦌)
    (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) (τ : (Δ[1] : SSet.{u}) _⦋n⦌)
    (he : ObjectSInClosed B ((cofiberLeftFiberQuotient X a).app (Opposite.op ⦋n⦌) e)) :
    ObjectSInClosed B ((objectSConstructionFunctor.map (cofiberStableQuotient X)).app
      (Opposite.op ⦋n⦌) (mcCarthyThetaObjectVertex X a e τ)) := by
  have hq := ConcreteCategory.congr_hom
    (NatTrans.congr_app (mcCarthyRhoTerminal_quotient X a) (Opposite.op ⦋n⦌)) e
  change (cofiberLeftFiberQuotient X a).app (Opposite.op ⦋n⦌)
      ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e) =
    (cofiberLeftFiberQuotient X a).app (Opposite.op ⦋n⦌) e at hq
  have ht : ObjectSInClosed B ((cofiberLeftFiberQuotient X a).app (Opposite.op ⦋n⦌)
      ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e)) := hq.symm ▸ he
  apply ObjectSInClosed.of_functorIso B ht
  rw [gappedDiagram_objectSFunctor_map, mcCarthyThetaObjectVertex_diagram]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (mcCarthyFiberDiagram X a ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e) ≫
      (cofiberStableQuotient X).val)
    (variableTimeImage (zeroSourceThetaHomotopy (objectSLastDiagonalZeroVertex a))
      (mcCarthyThetaDiagram X a e) (arTimeCoordinate τ) ≫ (cofiberStableQuotient X).val)
  rw [← mcCarthyThetaDiagram_ι]
  exact (variableTimeImageIso (zeroSourceThetaHomotopy (objectSLastDiagonalZeroVertex a))
    (zeroSourceThetaHomotopy_isInvertible (objectSLastDiagonalZeroVertex a))
      (mcCarthyThetaDiagram X a e) (arTimeCoordinate τ)).postcomp (cofiberStableQuotient X).val

/-- 周囲の θ を相対 fiber から前合成した族の quotient は全時刻で B に入る。 -/
lemma relativeMcCarthyTheta_quotient_in_closed {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌)
    (n : SimplexCategoryᵒᵖ) (x : (relativeCofiberSubobjectLeftFiber A B a ⊗ Δ[1]).obj n) :
    ObjectSInClosed B
      (((relativeCofiberLeftFiberForget A B a ▷ (Δ[1] : SSet.{u})) ≫
        mcCarthyThetaFiberMap X (relativeCofiberBaseSimplex A a) ≫
          cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a)).app n x) := by
  have hθ : mcCarthyThetaFiberMap X (relativeCofiberBaseSimplex A a) ≫
      cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a) =
    mcCarthyThetaObjectMap X (relativeCofiberBaseSimplex A a) ≫
      objectSConstructionFunctor.map (cofiberStableQuotient X) := by
    rw [cofiberLeftFiberQuotient, ← Category.assoc, mcCarthyThetaFiberMap_projection]
  rw [hθ]
  rcases n with ⟨⟨n⟩⟩
  exact mcCarthyThetaObject_quotient_in_closed B (relativeCofiberBaseSimplex A a)
    ((relativeCofiberLeftFiberForget A B a).app (Opposite.op ⦋n⦌) x.1) x.2
    (relativeCofiberLeftFiberForget_quotient_in_closed A B a x.1)

end SerrePositivity.KST.SConstruction
