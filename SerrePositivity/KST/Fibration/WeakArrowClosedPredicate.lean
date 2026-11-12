module
public import SerrePositivity.KST.Fibration.WeakArrowCategory
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationSection

/-! # W 辺条件の安定な閉性

元の全 cofiber 射影の厳密な切断は完全である。その cofiber 評価による核の逆像を使い、
W 辺の頂点条件が零・同型・pushout・pullback に閉じることを示す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 安定圏の実関手圏を、同じ全高次単体を持つ K-1 の入力として保持する。 -/
def ambientDiagramModel (K : SSet.{u}) (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : StableModel.{u} where
  carrier := (ihom K).obj B.obj
  quasicategory := inferInstance
  stable := inferInstance

/-- 元の全 cofiber 射影の厳密な切断。 -/
def arrowCofiberSection (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (ihom (Δ[1] : SSet.{u})).obj B.obj ⟶ cofiberDiagrams B.obj :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (cofiberProjection B.obj))

lemma arrowCofiberSection_projection (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    arrowCofiberSection B ≫ cofiberProjection B.obj = 𝟙 _ :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (cofiberProjection B.obj))

/-- 選択した cofiber は完全関手であり、元の底辺は厳密に固定されている。 -/
def arrowCofiberMap (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    ambientDiagramModel (Δ[1] : SSet.{u}) B ⟶ sInputModel B := by
  have hs := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_section_of_trivialKanFibration (cofiberProjection B.obj)
    (arrowCofiberSection B) (arrowCofiberSection_projection B)
  exact ⟨arrowCofiberSection B ≫ (cofiberStableQuotient (sInputModel B)).val,
    (show PreservesCofiberData (arrowCofiberSection B) from
      ⟨hs.preservesZero, hs.preservesCofiber⟩).comp
        (cofiberStableQuotient (sInputModel B)).property⟩

/-- cofiber の核条件は実関手圏上の閉じた安定条件。 -/
def weakArrowClosedPredicate {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    ClosedStablePredicate (ambientDiagramModel (Δ[1] : SSet.{u}) B) :=
  (kernelClosedPredicate q).comap (arrowCofiberMap B)

/-- 構成した閉じた条件は、元の辺の商での可逆性と一致する。 -/
lemma weakArrowClosedPredicate_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (v : ((ihom (Δ[1] : SSet.{u})).obj B.obj) _⦋0⦌) :
    (weakArrowClosedPredicate q).predicate v ↔ weakArrowPredicate q v := by
  let w := (arrowCofiberSection B).app (Opposite.op ⦋0⦌) v
  have hp := ConcreteCategory.congr_hom
    (NatTrans.congr_app (arrowCofiberSection_projection B) (Opposite.op ⦋0⦌)) v
  have he : (cofiberProjection B.obj).app (Opposite.op ⦋0⦌) w = v := hp
  have hleft : (weakArrowClosedPredicate q).predicate v ↔
      (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).predicate w := by
    change _ ↔ True ∧ (weakArrowClosedPredicate q).predicate v
    exact ⟨fun hv => ⟨trivial, hv⟩, fun hv => hv.2⟩
  exact hleft.trans ((weakCofiber_projection_predicate q w).trans
    (congrArg (weakArrowPredicate q) he).to_iff)

end SerrePositivity.KST.Fibration
