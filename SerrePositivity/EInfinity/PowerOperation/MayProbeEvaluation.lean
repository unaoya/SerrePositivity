module

public import SerrePositivity.EInfinity.PowerOperation.MayProbeCycles
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FreeAlgebraAdjunction

/-!
# May の普遍代表元の自由 probe からの評価

May, Proposition 2.3 の代表元独立性の補助。
元の比較射・自由代数の単位・持ち上げを保持し、複体射のホモトピーを
評価代数射の全ホモロジーでの一致へ送る。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles
variable {k : Type u} [CommRing k] (X : (operad k).Algebra)

/-- 元の複体射を、同じ自由 probe からの代数射へ持ち上げる。 -/
def mayProbeLiftHom {K : Complex k} (f : K ⟶ X.carrier) :
    (freeProbeFunctor k).obj K ⟶ X :=
  X.liftHom (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k K ≫ f)

lemma mayProbeLiftHom_fac {K : Complex k} (f : K ⟶ X.carrier) :
    (freeProbeFunctor k).map f ≫ mayProbeLiftHom X (𝟙 X.carrier) = mayProbeLiftHom X f := by
  change (operad k).freeAlgebraFunctor.map ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor k).map f) ≫
    X.liftHom (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k X.carrier ≫ 𝟙 _) = _
  rw [Category.comp_id, X.liftHom_precomp]
  have h := (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparisonNatTrans k).naturality f
  change (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor k).map f ≫
    _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k X.carrier =
      _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k K ≫ f at h
  rw [h]
  rfl

/-- ホモトピックな複体射は、同じ自由 probe の評価のホモロジーで一致。 -/
lemma mayProbeLiftHom_homology_eq {K : Complex k} {f g : K ⟶ X.carrier}
    (H : Homotopy f g) (i : ℤ) :
    homologyMap (mayProbeLiftHom X f).hom i = homologyMap (mayProbeLiftHom X g).hom i := by
  rw [← mayProbeLiftHom_fac X f, ← mayProbeLiftHom_fac X g]
  change homologyMap (((freeProbeFunctor k).map f).hom ≫
      (mayProbeLiftHom X (𝟙 X.carrier)).hom) i =
    homologyMap (((freeProbeFunctor k).map g).hom ≫
      (mayProbeLiftHom X (𝟙 X.carrier)).hom) i
  rw [homologyMap_comp, homologyMap_comp, mayFreeProbeHomology_homotopy k H i]

/-- 指定閉元を同じ probe へ持ち上げ、自由代数の生成元として含める。 -/
def mayProbeFreeCycle (K : Complex k) (i : ℤ) (a : MayClosed K i) :
    MayClosed ((freeProbeFunctor k).obj K).carrier i :=
  mayClosedMap ((operad k).schurUnit ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor k).obj K)) i
    (mayProbeClosedLift k K i a)

/-- 同じ普遍閉元を評価すると、元の閉元の厳密な像を回収する。 -/
lemma mayProbeFreeCycle_evaluation {K : Complex k} (f : K ⟶ X.carrier)
    (i : ℤ) (a : MayClosed K i) :
    mayClosedMap (mayProbeLiftHom X f).hom i (mayProbeFreeCycle K i a) =
      mayClosedMap f i a := by
  apply Subtype.ext
  have hu := congrArg (fun h => h.f i (mayProbeClosedLift k K i a).val)
    (X.schurUnit_liftHom (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k K ≫ f))
  change (mayProbeLiftHom X f).hom.f i
      (((operad k).schurUnit ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor k).obj K)).f i
        (mayProbeClosedLift k K i a).val) =
    f.f i ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k K).f i
      (mayProbeClosedLift k K i a).val) at hu
  have hs := congrArg Subtype.val (mayProbeClosedLift_spec k K i a)
  exact hu.trans (congrArg (f.f i) hs)

end SerrePositivity.EInfinity.PowerOperation
