module

public import SerrePositivity.DifferentialGraded.Algebras.FrameHammockCoherent
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelRightFrameComparison

/-!
概要：実 dg 代数の right frame と擬同型 ∞ 局所化の全写像空間比較。
方針：実自由 I/J の分解と源移送を代入し、全 coherent 比較と指定二胞体を保持する。
規約：局所モデルだけを選び、SSet モデルや追加の関手的分解仮定を残さない。
使われ方：Sp β6 f4c の全標的に自然な実導来比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.Opposite
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex
variable (R : Type u) [CommRing R]

/-- 概要：実全 dg 代数の hammock は同じ擬同型による ∞ 局所化。
方針：第一分解を同じ自由 I の小対象論法から放電し、同じ right frame を代入する。
規約：モデル・分解・源移送の追加入力なし。
使われ方：Sp の指定全圏局所化との全比較。 -/
lemma hammock_isLocalization :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))) := by
  let _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  have := _root_.SerrePositivity.DGAlgebra.modelCategory_hasFunctorialFactorization_cofibration_trivialFibration R
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R)

/-- 概要：実 cofibrant dg 代数の hammock も同じ擬同型による ∞ 局所化。
方針：同じ bifibrant からの源移送と実第一分解を使う。
規約：追加の分解仮定なし。使われ方：Sp の cofibrant 源局所化の版。 -/
lemma cofibrantHammock_isLocalization :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory (Mon (Complex R))))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory (Mon (Complex R)))) := by
  let _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  have := _root_.SerrePositivity.DGAlgebra.modelCategory_hasFunctorialFactorization_cofibration_trivialFibration R
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelCofibrantHammock_isLocalization (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R)

/-- 概要：実 dg 全圏の指定局所化への比較 K と全二胞体を構成する。
方針：実局所化普遍性で指定 G を延長する。
規約：K の存在や関手的分解を追加入力にしない。
使われ方：全 Hom 族の端点輸送と全自然性。 -/
def frameLocalizationComparison {Q : SSet.{u + 1}} [Quasicategory Q] :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    ∀ (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ⟶ Q),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))) →
        _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CoherentLocalizationComparison
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))) G := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  intro G hG
  have := _root_.SerrePositivity.DGAlgebra.modelCategory_hasFunctorialFactorization_cofibration_trivialFibration R
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFrameLocalizationComparison (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) G hG

/-- 概要：実 dg right Hom と指定局所化の同じ pinched Hom の実 QCat 同値。
方針：実全六辺の同じ成分と普遍性から構成した指定二胞体を合成する。
規約：係数環・指定局所化・cofibrant 源だけを要求する。
使われ方：Sp の任意標的の実 frame Hom 比較。 -/
def framePinchedEquivalence {Q : SSet.{u + 1}} [Quasicategory Q] :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    ∀ (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ⟶ Q),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))) →
      ∀ (X : Mon (Complex R)) (hX : IsCofibrant X),
        letI := hX
        ∀ (Y : Mon (Complex R)),
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (SSet.uliftFunctor.{u + 1, u}.obj
          ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) X).obj Y))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X)))
            (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) Y)))) := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  intro G hG X hX Y
  letI _sourceCofibrant := hX
  exact (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockPinchedEquivalence ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject X)
    (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) (_root_.SerrePositivity.DGAlgebra.cofibrantFactorization R) Y).trans
      ((_root_.SerrePositivity.DGAlgebra.frameLocalizationComparison R G hG).pinchedEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) Y)))

/-- 概要：実 dg の全 coherent 比較と同じ指定局所化の全二胞体を同時に公開する。
方針：同じ六辺の関手 ∞ 圏の同型と同じ K の比較を保持する。
規約：点ごとの Hom 同値だけで完成扱いしない。
使われ方：Sp の全標的図式と全二胞体の coherent な合成。 -/
def frameCoherentComparison {Q : SSet.{u + 1}} [Quasicategory Q] :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    ∀ (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ⟶ Q),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))) →
      ∀ (X : Mon (Complex R)), IsCofibrant X →
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
          (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject X)
            (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) 0)
          (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject X)
            (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) 6)) ×
        _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CoherentLocalizationComparison
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))) G := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  intro G hG X hX
  exact ⟨_root_.SerrePositivity.DGAlgebra.rightFrameHammockCoherentComparison R X hX, _root_.SerrePositivity.DGAlgebra.frameLocalizationComparison R G hG⟩

/-- 概要：実 dg 比較の単位点は同じ元の射の局所化点と指定成分の共役を回収する。
方針：実自由分解・同じ right frame・構成済みの局所化比較を一般単位公式へ代入する。
規約：関手的分解・全圏普遍性・比較 K の存在を追加入力にしない。
使われ方：Sp の元の dg 代数射と全標的比較の零単体照合。
-/
lemma framePinchedEquivalence_unit_Q {Q : SSet.{u + 1}} [Quasicategory Q] :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    ∀ (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ⟶ Q)
      (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))))
      (X : Mon (Complex R)) (hX : IsCofibrant X),
      letI := hX
      ∀ (Y : Mon (Complex R)) (f : X ⟶ Y),
        SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
          (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject X)
            (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) f 0 ≫ (_root_.SerrePositivity.DGAlgebra.framePinchedEquivalence R G hG X hX Y).hom) =
        SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).weakEquivalences
            (AsSmall.up.map f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
            _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))
              (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X)
              (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) Y) ≫
            ((_root_.SerrePositivity.DGAlgebra.frameLocalizationComparison R G hG).pinchedEquivalence
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X))
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) Y))).hom) := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  intro G hG X hX Y f
  letI _sourceCofibrant := hX
  have := _root_.SerrePositivity.DGAlgebra.modelCategory_hasFunctorialFactorization_cofibration_trivialFibration R
  have h := congrArg (fun t => t ≫ SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
    ((_root_.SerrePositivity.DGAlgebra.frameLocalizationComparison R G hG).pinchedEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) Y))).hom)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockPinchedEquivalence_unit_arrow_Q
      ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject X) (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) f (_root_.SerrePositivity.DGAlgebra.cofibrantFactorization R))
  simpa only [_root_.SerrePositivity.DGAlgebra.framePinchedEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans, Functor.map_comp,
    Category.assoc] using h

end SerrePositivity.DGAlgebra
