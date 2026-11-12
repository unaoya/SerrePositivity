module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoslicePinchedLeft

/-!
概要：反転した豊穣 Hom と coherent nerve の左 coslice fiber の実際の比較射。
方針：反対圏で右 Hom 比較を行い、coherent nerve の反対の同型で戻して反転する。
規約：始域は sHom(x,y) の反転であり、対象ごとの逆射の選択は用いない。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の錐の係数図式への比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：反対 nerve の逆射で移した右 Hom の二端点を標準頂点と同定する。
方針：逆射の頂点の計算を両端点へ適用する。
規約：元の x と y は反対側の右 Hom では逆順となる。
使われ方：Kerodon §4.6.7（Tag 01LA） の左 Hom の始域と終域の固定。 -/
noncomputable def coherentOppositeHomEndpointIso (x y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse C).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op y)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse C).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op x))) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := (SimplicialNerve C).op)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y))
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) :=
  eqToIso (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := (SimplicialNerve C).op) a b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse_vertex y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse_vertex x))

/-- 概要：豊穣 Hom を反転 nerve の右 Hom へ写す。
方針：反対圏の標準比較、nerve の反対の逆射、端点の同定を合成する。
規約：Kan 性なしで射を定義する。
使われ方：Kerodon §4.6.7（Tag 01LA） の左 Hom 比較を反転前に構成する段階。 -/
noncomputable def coherentOppositeRightHomComparison (x y : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := (SimplicialNerve C).op)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y))
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison (Opposite.op y) (Opposite.op x) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op x)) ≫
    (coherentOppositeHomEndpointIso x y).hom

/-- 概要：局所 Kan 性の下で反転前の右 Hom 比較はホモトピー同値。
方針：標準比較の同値と同型による Hom の移送の同値を合成する。
規約：全ての sHom の Kan 性だけを要求する。
使われ方：Kerodon §4.6.7（Tag 01LA） の左 Hom 比較の同値性。 -/
lemma coherentOppositeRightHomComparison_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (x y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coherentOppositeRightHomComparison x y) := by
  have : ∀ a b : Cᵒᵖ, KanComplex (SimplicialCategory.sHom a b) :=
    fun a b ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom b.unop a.unop))
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse C) := by
    change IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso C).inv
    infer_instance
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isSimplicialHomotopyEquivalence
    (Opposite.op y) (Opposite.op x)
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op x))))
  have h₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (coherentOppositeHomEndpointIso x y)).isQCatEquivalence
  exact h₁.comp (h₂.isSimplicialHomotopyEquivalence.comp h₃.isSimplicialHomotopyEquivalence)

/-- 概要：反転した豊穣 Hom を coherent nerve の左 Hom へ写す。
方針：右 Hom 比較の反転と ULift の反転の同型を合成する。
規約：始域の sHom は反転する。Kan 性なしで定義する。
使われ方：Kerodon §4.6.7（Tag 01LA） の左 coslice の係数への実際の比較射。 -/
noncomputable def coherentLeftHomComparison (x y : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y).op ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom x y)).hom ≫
    SSet.opFunctor.map (coherentOppositeRightHomComparison x y)

/-- 概要：局所 Kan 性の下で左 Hom 比較はホモトピー同値。
方針：反転前の同値の反転と始域の同型を合成する。
規約：全ての sHom の Kan 性だけを要求する。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の係数の値の比較。 -/
lemma coherentLeftHomComparison_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (x y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coherentLeftHomComparison x y) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom x y))).isQCatEquivalence
  exact h.isSimplicialHomotopyEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence
      (coherentOppositeRightHomComparison_homotopyEquivalence x y))

/-- 概要：反転した豊穣 Hom から左 coslice fiber への実際の比較射。
方針：左 Hom 比較の後で左 pinched 模型と coslice fiber の同型を合成する。
規約：始点は x、射影先の固定頂点は y。
使われ方：HTT 4.2.4.1 の coherent な錐と豊穣係数の接続。 -/
noncomputable def coherentCosliceFiberComparison (x y : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y).op ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y) :=
  coherentLeftHomComparison x y ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y)).hom

/-- 概要：局所 Kan 性の下で左 coslice fiber 比較はホモトピー同値。
方針：左 Hom 比較の同値に fiber の厳密な同型を合成する。
規約：係数図式全体の自然性はこの主張に含めない。
使われ方：HTT 4.2.4.1 の係数図式の比較の各頂点。 -/
lemma coherentCosliceFiberComparison_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (x y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coherentCosliceFiberComparison x y) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y))
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y))).isQCatEquivalence
  exact (coherentLeftHomComparison_homotopyEquivalence x y).comp
    h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
