module

public import SerrePositivity.InfinityCategories.F2.CoconeFiberTransport
public import SerrePositivity.InfinityCategories.F2.PointedHomTransportEquivalence
public import SerrePositivity.InfinityCategories.F2.WeakHomotopyPrecomposition

/-!
概要：元の全 Hom の相対合成を、fiber 写像による前合成として写像空間全体で表示する。
方針：輸送の評価同型を curry し、普遍輸送の作用と前合成の合成へ移す。
規約：元の余錐の fiber 写像を保持する。
使われ方：fiber 写像の弱同値性から native な余極限性を導く。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 概要：元の相対合成の fiber 比較は全 Hom の輸送作用の後の fiber 写像の前合成と同型。
方針：元の輸送評価の同型を全パラメータで curry する。
規約：頂点ごとの比較へ弱めない。使われ方：全 Hom の同値性の検証。 -/
def coconeFiberHomComparisonIso (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso (coconePointHomRelativeComposite c z ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom)
      ((pointedIntervalTransport (pinchedHomLeftToIntervalMappingSpace c.vertex z)).map ≫
        (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z)) := by
  have e := (coconeFiberTransportIso c z).curry
  rw [curry_uncurry] at e
  have h : curry (lift
      (fst (leftUnstraightening F) (pinchedHomLeft c.vertex z) ≫ coconeFiberMap c)
      (snd (leftUnstraightening F) (pinchedHomLeft c.vertex z)) ≫
        (pointedIntervalTransport (pinchedHomLeftToIntervalMappingSpace c.vertex z)).endpoint) =
      (pointedIntervalTransport (pinchedHomLeftToIntervalMappingSpace c.vertex z)).map ≫
        (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z) := by
    apply uncurry_injective
    rw [uncurry_curry, uncurry_pre_app]
    change _ = (coconeFiberMap c ▷ pinchedHomLeft c.vertex z) ≫
      uncurry (curry (pointedIntervalTransport
        (pinchedHomLeftToIntervalMappingSpace c.vertex z)).endpoint)
    rw [uncurry_curry]
    rfl
  rw [h] at e
  exact e

/-- 概要：元の余錐の fiber 写像が弱同値なら、その全 Hom の相対合成比較は同値。
方針：輸送作用の同値性と Kan 標的への弱同値の前合成同値を合成する。
規約：元の全空間の Kan 性は要求しない。使われ方：native な余極限性の十分条件。 -/
lemma coconeFiberHomComparison_homotopyEquivalence (c : JoinCocone F)
    (hc : IsWeakHomotopyEquivalence (coconeFiberMap c)) (z : SpaceInfinity.{u} _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coconePointHomRelativeComposite c z ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom) := by
  have hp := pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence
    (coconeFiberMap c) hc (vertexFiber pointedSpaceProjection z)
  have h := (pointedHomTransport_isQCatEquivalence c.vertex z).comp hp.isQCatEquivalence
  exact (h.ofFunctorIso (coconeFiberHomComparisonIso c z).symm).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
