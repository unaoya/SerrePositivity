module

public import SerrePositivity.InfinityCategories.F1.SmallFiberStraighteningCounit
public import SerrePositivity.InfinityCategories.F1.SmallCartesianRepresentationExtension

/-!
概要：表現空間の比較の一意性と cartesian な制限。
方針：可縮な表現空間の終対象性で比較を同定し、前合成で制限する。
規約：図式を写す前の同じ表現空間内で比較の整合性を証明する。
使われ方：余単位の底変換と経路による選択の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：小さい次数 fiber の同じ二表現の間の頂点同型は一意。
方針：標的頂点がホモトピー圏で終対象であることを使う。
規約：表現を忘れた図式の同型全体が一意とは主張しない。
使われ方：同じ表現の三つの比較経路を同定する。 -/
lemma smallFiberTransportRepresentationVertexIso_unique {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasSmallSimplexFibers p)
    (R S : LeftTransportRepresentation p)
    (e f : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) : e = f := by
  apply Iso.ext
  exact ((smallFiberTransportWitnessSpace_isContractibleKan p hp).isTerminalVertex
    (transportWitnessVertex S)).isTerminalHo.hom_ext _ _

/-- 概要：表現の比較は任意の cartesian な制限へ写せる。
方針：実際の表現空間の前合成と頂点公式を使う。
規約：両表現の制限で同じ引き戻し正方形を使う。
使われ方：元の余単位を制限後の表現空間内で比較する。 -/
def LeftTransportRepresentation.cartesianRestrictVertexIso
    {E F B D : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ D}
    [LeftFibration p] [LeftFibration q] (R S : LeftTransportRepresentation p)
    (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))
    (e : F ⟶ E) (g : D ⟶ B) (h : IsPullback e q p g) :
    VertexIso (transportWitnessVertex (R.cartesianRestrict e g h))
      (transportWitnessVertex (S.cartesianRestrict e g h)) := by
  let f : Arrow.mk q ⟶ Arrow.mk p := Arrow.homMk e g h.w
  have : LeftFibration (Arrow.mk q).hom := by change LeftFibration q; infer_instance
  have : LeftFibration (Arrow.mk p).hom := by change LeftFibration p; infer_instance
  have v := VertexIso.map a (transportWitnessPre f h)
  have er := transportWitnessPre_cartesianRestrict_vertex f h R
  have es := transportWitnessPre_cartesianRestrict_vertex f h S
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk er)).symm ≪≫ v ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk es)

/-- 概要：標準の unstraightening 表現の cartesian 制限は制限先の標準表現。
方針：図式と pointed space への射の厳密な一致で表現を同定する。
規約：元と制限後の図式の一致を入力する。
使われ方：制限した余単位の終点を元の標準表現へ戻す。 -/
lemma unstraighteningTransportRepresentation_cartesianRestrict {B D : SSet.{u + 1}}
    (F : D ⟶ SpaceInfinity.{u}) (G : B ⟶ SpaceInfinity.{u})
    (g : D ⟶ B) (h : g ≫ G = F) :
    (unstraighteningTransportRepresentation G).cartesianRestrict
      (leftUnstraighteningMap F G g h) g (leftUnstraighteningMap_isPullback F G g h) =
      unstraighteningTransportRepresentation F := by
  apply LeftTransportRepresentation.ext
  · exact h
  · rw [LeftTransportRepresentation.cartesianRestrict_pointedMap]
    simp only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp, leftUnstraighteningMap_pointed]

/-- 概要：表現の頂点同型の合成は分類図式の同型の合成へ写る。
方針：ホモトピー圏の関手の同型への作用の合成則を使う。
規約：三つの表現は同じ射影を表す。
使われ方：表現空間での経路の一致を図式の合成式へ移す。 -/
lemma LeftTransportRepresentation.diagramIso_trans {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R S T : LeftTransportRepresentation p)
    (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))
    (b : VertexIso (transportWitnessVertex S) (transportWitnessVertex T)) :
    R.diagramIso T (a ≪≫ b) = R.diagramIso S a ≪≫ S.diagramIso T b := by
  apply Iso.ext
  simp [LeftTransportRepresentation.diagramIso, VertexIso.map]

/-- 概要：表現の頂点同型の合成は pointed な射の同型の合成へ写る。
方針：分類図式と同じ頂点同型を全空間の射へ写す。
規約：合成前後で新たな比較を選ばない。
使われ方：全空間側でも同じ自然性の三角形を回収する。 -/
lemma LeftTransportRepresentation.pointedIso_trans {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R S T : LeftTransportRepresentation p)
    (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))
    (b : VertexIso (transportWitnessVertex S) (transportWitnessVertex T)) :
    R.pointedIso T (a ≪≫ b) = R.pointedIso S a ≪≫ S.pointedIso T b := by
  apply Iso.ext
  simp [LeftTransportRepresentation.pointedIso, VertexIso.map]

/-- 概要：表現の等式による頂点同型は図式の等式による同型へ写る。
方針：表現の等式を消去し恒等同型の像を計算する。
規約：等式の移送を選択した比較に置き換えない。
使われ方：標準表現の制限を回収した後の端点の同定。 -/
lemma LeftTransportRepresentation.diagramIso_eqToIso {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R S : LeftTransportRepresentation p) (h : R = S) :
    R.diagramIso S
      (eqToIso (congrArg (fun T ↦ SSet.HomotopyCategory.mk (transportWitnessVertex T)) h)) =
      eqToIso (congrArg (fun T ↦ SSet.HomotopyCategory.mk (functorVertex T.diagram)) h) := by
  subst S
  apply Iso.ext
  simp [LeftTransportRepresentation.diagramIso, VertexIso.map]

end SerrePositivity.InfinityCategories
