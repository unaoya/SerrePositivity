module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelHammockLocalization
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelRightFrameSpecifiedInput
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameSpecifiedUnit

/-!
概要：一般モデル圏の実 right frame と指定された全圏の ∞ 局所化の写像空間比較。
方針：同じ bifibrant からの源移送で全圏普遍性を放電し、同じ六辺と指定二胞体を使う。
規約：第一の関手的分解と指定 right frame だけを追加し、全標的と元の単位を保持する。
使われ方：Sp の実 dg 代数モデルへの追加仮定のない特殊化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))

/-- 概要：指定局所化への比較関手と全二胞体を局所化普遍性から構成する。
方針：同じ実 hammock の全前合成同値から元の G を延長する。
規約：全圏普遍性や比較 K の存在を追加入力にしない。
使われ方：全 pinched Hom 比較の指定二胞体。 -/
def modelRightFrameLocalizationComparison :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CoherentLocalizationComparison
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.localizationComparisonData _ G _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization r) hG
    (SerrePositivity.KST.LocalizingInvariants.localizationDescend _ _
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization r) G hG.choose)
    (SerrePositivity.KST.LocalizingInvariants.localizationDescendIso _ _
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization r) G hG.choose)

variable (X : C) [IsCofibrant X]

/-- 概要：元の right frame Hom と指定全圏局所化の同じ pinched Hom の実 QCat 同値。
方針：全圏普遍性を証明済みの源移送で放電し、同じ指定二胞体で輸送する。
規約：元の標的 Y は任意、未証明の存在入力なし。
使われ方：全標的 coherent 比較の実写像空間成分。 -/
def modelRightFramePinchedEquivalence (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))
        (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockPinchedEquivalence
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := C)).atObject X) r
    (MorphismProperty.functorialFactorizationData _ _) Y).trans
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFrameLocalizationComparison r G hG).pinchedEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))

/-- 概要：全標的の同じ coherent 比較と指定局所化の全二胞体を一緒に公開する。
方針：同じ元の六辺の全関手同型と同じ局所化比較を組にする。
規約：点ごとの Hom 同値だけを結論としない。
使われ方：Sp が全図式の自然性と指定二胞体を同時に合成する入口。 -/
def modelRightFrameCoherentComparison :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := C)).atObject X) r 0)
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := C)).atObject X) r 6)) ×
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CoherentLocalizationComparison
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFrameHammockCoherentComparison r X, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFrameLocalizationComparison r G hG⟩

variable (K : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ⟶ Q)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ≫ K) G)

/-- 概要：既に指定された比較 K と二胞体 e でも同じ実 Hom 比較を使える。
方針：同じ証明済み全圏普遍性を指定データ版へ渡す。
規約：元の K と e を保持。使われ方：消費者の指定比較との coherent な合成。 -/
def modelRightFramePinchedEquivalenceWithComparison (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))
        (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFrameSpecifiedPinchedEquivalence r G hG (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization r) K e X Y

omit [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  [Quasicategory Q] [IsCofibrant X] in
/-- 概要：元の指定局所化射は同じ全二胞体の両端の共役で回収される。
方針：同じ二胞体の全射での自然性と成分の逆則を使う。
規約：元の通常射 f と指定二胞体 e を変更しない。
使われ方：同じ実 roof の単位正規化後の零単体の照合。 -/
lemma modelRightFrameOriginalArrow_conjugation {Y : C} (f : X ⟶ Y) :
    (e.toNatIso.app (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))).inv ≫
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ≫ K)).toFunctor.map
        (HomotopyCategory.homMk (nerve.edgeMk (AsSmall.up.map f)).toTruncated) ≫
      (e.toNatIso.app (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))).hom =
        (hoFunctor.map G).toFunctor.map
          (HomotopyCategory.homMk (nerve.edgeMk (AsSmall.up.map f)).toTruncated) := by
  let a : HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)) :=
    HomotopyCategory.homMk (nerve.edgeMk (AsSmall.up.map f)).toTruncated
  let ex := e.toNatIso.app (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))
  let ey := e.toNatIso.app (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))
  let g := (hoFunctor.map G).toFunctor.map a
  have h := congrArg (fun t => ex.inv ≫ t) (e.toNatIso.hom.naturality a)
  exact h.trans ((Category.assoc ex.inv ex.hom g).symm.trans
    ((congrArg (fun t => t ≫ g) ex.inv_hom_id).trans (Category.id_comp g)))

/-- 概要：指定 K と二胞体を保つ実比較の零単体を元の局所化射へ回収する。
方針：同じ一般単位公式の全圏普遍性を証明済みの源移送で放電する。
規約：局所化普遍性の追加入力なし。
使われ方：元の射の共役式と全 coherent 比較の整合。
-/
lemma modelRightFramePinchedEquivalenceWithComparison_unit_Q {Y : C} (f : X ⟶ Y) :
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := C)).atObject X)
        r f 0 ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFramePinchedEquivalenceWithComparison r G hG X K e Y).hom) =
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).weakEquivalences (AsSmall.up.map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
          _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)
            (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y) ≫
              ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameSpecifiedLocalizationData G hG
                (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization r) K e).pinchedEquivalence
                  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))
                  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y))).hom) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameSpecifiedPinchedEquivalence_unit_Q
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := C)).atObject X) r f
    (MorphismProperty.functorialFactorizationData _ _) G hG (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization r) K e

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
