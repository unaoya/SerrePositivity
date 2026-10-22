module
public import SerrePositivity.KST.Fibration.WeakEquivalences
public import SerrePositivity.KST.SConstruction.RelativeAdditivity
public import SerrePositivity.InfinityCategories.Stable.ZeroTriangleVanishing

/-! # 商の核と相対 cofiber 図式

K-5 の完全関手の核を K-1 の閉じた安定頂点条件へ渡す。
cofiber が核に属する全図式に相対加法性を適用する。W 辺の列の実現との比較は別工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- K-5 の安定圏を K-1 の同じ底の単体集合を持つ模型として保持する。 -/
def sInputModel (B : StableCategory.{u}) : StableModel.{u} where
  carrier := B.obj
  quasicategory := B.isQuasicategory
  stable := B.isStable

/-- 完全関手の核は、同型・零・実 pushout・実 pullback に閉じている。 -/
def kernelClosedPredicate {B C : StableCategory.{u}} (q : ExactMap B C) :
    ClosedStablePredicate (sInputModel B) where
  predicate x := IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x)
  of_iso hx e := hx.of_vertexIso (e.map q.hom)
  zero_mem hz := IsExactFunctor.preservesZero (F := q.hom) _ hz
  pushout_mem F hF h00 h10 h01 :=
    (⟨F ≫ q.hom, h01⟩ : ZeroTriangle C.obj).zero_cofiber_of_zero_source_middle
      (IsExactFunctor.preservesPushoutSquare q.hom F hF) h00 h10
  pullback_mem F hF h10 h01 h11 :=
    (⟨F ≫ q.hom, h01⟩ : ZeroTriangle C.obj).zero_source_of_fiber_zero_middle_cofiber
      (IsExactFunctor.preservesPullbackSquare q.hom F hF) h10 h11

/-- Verdier 列では構成した閉じた条件が元の包含の本質像と一致する。 -/
lemma kernelClosedPredicate_iff_essentialImage
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) :
    (kernelClosedPredicate q).predicate x ↔ x ∈ essentialImage i := h.kernel x

/-- cofiber が商の核に属する、元の全 cofiber 図式の安定模型。 -/
def weakCofiberModel {B C : StableCategory.{u}} (q : ExactMap B C) : StableModel.{u} :=
  relativeCofiberStableModel (ClosedStablePredicate.top (sInputModel B))
    (kernelClosedPredicate q)

/-- 元の相対 subobject・quotient 射対の core S• 加法性。 -/
lemma weakCofiberAdditivity_localized_isIso {B C : StableCategory.{u}} (q : ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeCoreSAdditivityMap (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q))) :=
  relativeCoreSAdditivityMap_localized_isIso (ClosedStablePredicate.top (sInputModel B))
    (kernelClosedPredicate q)

end SerrePositivity.KST.Fibration
