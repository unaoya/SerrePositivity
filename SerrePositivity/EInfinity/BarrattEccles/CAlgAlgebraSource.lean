module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgForgetDerivedValue

/-!
# 元の全 E 代数から既存 CAlg_R への実 ∞ 関手

概要：元の全代数の同じ関手的 cofibrant 置換を全単体で局所化写像へ送る。
方針：同じ通常の置換の後合成を単体ごとに定義し、元の頂点表示へ比較する。
規約：元の代数に cofibrancy を仮定しない。
使われ方：離散 ∞ 入力と実忘却 U の全源比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable (A : Type u) [CommRing A]

def algebraCAlgReplacementNerve :
    nerve (operad A).Algebra ⟶ nerve (cofibrantAlgebraRelativeCategory A).category where
  app _ := ↾fun Γ => Γ ⋙ cofibrantAlgebraDKReplacement A
  naturality := by
    intro d e α
    apply ConcreteCategory.hom_ext
    intro Γ
    rfl

lemma algebraCAlgReplacementNerve_vertex (X : (operad A).Algebra) :
    (algebraCAlgReplacementNerve A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((cofibrantAlgebraDKReplacement A).obj X) :=
  ComposableArrows.ext₀ rfl

def algebraCAlgSource : nerve (operad A).Algebra ⟶ CAlg_R A :=
  algebraCAlgReplacementNerve A ≫ cAlgLocalizationSource A

def algebraCAlgSource_vertexIso (X : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) (cAlgVertex A X) :=
  eqToIso (congrArg HomotopyCategory.mk
    (congrArg ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌))
      (algebraCAlgReplacementNerve_vertex A X))) ≪≫
        cAlgLocalizationSource_vertexIso A ((cofibrantAlgebraDKReplacement A).obj X)

def algebraCAlgSource_forgetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (algebraCAlgSource A ≫ cAlgForgetDerived A)
      (algebraCAlgReplacementNerve A ≫ cofibrantAlgebraUnderlyingDerivedSource A) := by
  simpa only [algebraCAlgSource, Category.assoc] using
    (cAlgForgetDerived_sourceIso A).precomp (algebraCAlgReplacementNerve A)

end SerrePositivity.EInfinity.BarrattEccles
