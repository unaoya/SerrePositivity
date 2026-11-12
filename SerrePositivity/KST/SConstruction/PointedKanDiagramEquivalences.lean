module
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences
public import SerrePositivity.KST.Spectra.StrictDiagramTransformation

/-! # 点つき Kan 図式全体の coherent な同値
概要：成分が全基点 π_* 同型な自然変換を、関手 ∞ 圏の同型へ束ねる。
方針：元の strict な自然変換を円柱で実現し、各頂点での可逆性を反映する。
規約：全射列を含む実際の coherent な図式間の同型を返す。入力図式は小さい通常の圏。
使われ方：構造射の比較逆射の、個々の入力射に依存しない全体での選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の点つき自然変換を、同じ対象・射の Kan 全部分圏へ持ち上げる。 -/
def pointedKanDiagramNatTrans {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) : pointedKanDiagram F hF ⟶ pointedKanDiagram G hG where
  app i := ObjectProperty.homMk (η.app i)
  naturality _ _ f := ObjectProperty.hom_ext _ (η.naturality f)

/-- 元の自然変換の全射列にわたる円柱は点つき Kan 図式の実ホモトピー。 -/
def pointedKanDiagramHomotopy {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) :
    SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG) :=
  StrictDiagramTransformation.homotopy (pointedKanDiagramNatTrans hF hG η)

/-- 全基点 π 同型の自然変換は、点つき coherent 図式全体の関手同型。 -/
def pointedKanDiagramFunctorIso {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (η.app i).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG) :=
  StrictDiagramTransformation.functorIso (pointedKanDiagramNatTrans hF hG η)
    (fun i => pointedKanObject_edge_isInvertible_of_piIsomorphism _ (hη i))

/-- 比較の同型の逆辺を、入力の全高次単体で同時に選ぶ。 -/
def pointedKanDiagramInverseHomotopy {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (η.app i).right) :
    SSet.Homotopy (pointedKanCoherentDiagram G hG) (pointedKanCoherentDiagram F hF) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge (pointedKanDiagramFunctorIso hF hG η hη).symm)

end SerrePositivity.KST.SConstruction
