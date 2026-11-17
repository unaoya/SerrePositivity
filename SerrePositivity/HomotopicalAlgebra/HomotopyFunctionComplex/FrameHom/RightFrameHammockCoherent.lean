module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockKanSpan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation

/-!
概要：元の right frame Hom と同じ hammock Hom を全標的の coherent な関手同型で比較する。
方針：同じ六つの実弱自然変換を空間値の関手 ∞ 圏へ送り、同じ辺を順に反転する。
規約：指定 right frame と元の全図式を保持し、点ごとの逆の選択をしない。
使われ方：指定局所化の全 pinched Hom 族への接続と同じ二胞体の保持。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
attribute [local instance] _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram_kanComplex

/-- 概要：同じ七つの中間図式の coherent な空間値実現。
方針：同じ元の Kan 値図式を既存の実現へ渡す。
規約：同じ持ち上げた全源 nerve。使われ方：全比較の同じ始終域。 -/
def rightFrameHammockCoherentDiagram (i : Fin 7) :
    SSet.uliftFunctor.{max u v + 1, max u v}.obj (nerve (AsSmall.{max u v} C)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram q r i)

include cof in
/-- 概要：元の各弱自然変換は全標的の関手 ∞ 圏で同じ可逆な比較辺を与える。
方針：既存の全図式の同値判定へ同じ実 Kan 比較を代入する。
規約：順射は元の自然変換の実現の辺。使われ方：全族の coherent 反転。 -/
def rightFrameHammockCoherentEdgeIso (i : Fin 6) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram q r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeSource i))
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram q r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeTarget i)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramFunctorIsoOfPointwise
    (F := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram q r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeSource i), trivial⟩)
    (G := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram q r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeTarget i), trivial⟩)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanEdge q r i) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanEdge_isQCatEquivalence q r cof i)

omit [IsCofibrant X] in
/-- 概要：元の各 coherent 比較辺は全標的で元の Kan 比較成分へ評価される。
方針：同じ実自然変換の実現の評価公式をそのまま使う。
規約：元の辺自身の全成分。使われ方：零単体と全二胞体の追跡。 -/
lemma rightFrameHammockCoherentEdge_at (i : Fin 6) (Y : AsSmall.{max u v} C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge
      (F := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram q r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeSource i), trivial⟩)
      (G := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram q r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeTarget i), trivial⟩)
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanEdge q r i)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram q r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeSource i)).obj Y ⟶
          (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram q r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeTarget i)).obj Y from
            (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanEdge q r i).app Y)).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge_at _ Y

/-- 概要：元の right frame Hom と同じ hammock Hom は全標的で coherent に自然同型。
方針：同じ六つの全比較の可逆な辺を元の向きに従い合成する。
規約：全標的と任意の添字図式の自然性を保持する。
使われ方：指定 ∞ 局所化の全 pinched Hom 族との合成。 -/
def rightFrameHammockCoherentComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram q r 0)
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram q r 6) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentEdgeIso q r cof 0).trans
    ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentEdgeIso q r cof 1).trans
      ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentEdgeIso q r cof 2).symm.trans
        ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentEdgeIso q r cof 3).symm.trans
          ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentEdgeIso q r cof 4).trans
            (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentEdgeIso q r cof 5).symm))))

/-- 概要：同じ全 coherent 比較は任意の全図式に沿う前合成でも保持される。
方針：同じ一つの関手同型を任意のパラメータで前合成する。
規約：点ごとの自然性への置換なし。使われ方：Sp の全標的図式の比較。 -/
def rightFrameHammockCoherentComparison_precomp {K : SSet.{max u v + 1}}
    (f : K ⟶ SSet.uliftFunctor.{max u v + 1, max u v}.obj
      (nerve (AsSmall.{max u v} C))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram q r 0)
      (f ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram q r 6) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentComparison q r cof).precomp f

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
