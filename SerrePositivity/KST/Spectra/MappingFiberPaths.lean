module

public import SerrePositivity.KST.Spectra.MappingFiber
public import SerrePositivity.KST.Spectra.PathNaturality

/-!
概要：fiber の path・loop と全空間への包含の整合性。
方針：厳密な Hom–fiber 同型の射影等式と path の自然性を合成する。
規約：Kan 性は要求しない。単体の代表を変更しない。
使われ方：Goerss–Jardine I §8。連結射の比較ホーンを fiber 内の path として読む。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- loop を基点に始まる path として読む点つき射。 -/
def loopToPath (Y : PointedSimplicialSet.{u}) : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y ⟶ basedPathSpace Y :=
  (loopToEndpointHomIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y

/-- path fiber の同型の包含は loop の path としての表示に等しい。 -/
@[reassoc]
lemma loopToPath_fiber (Y : PointedSimplicialSet.{u}) :
    (loopBasedPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) = (loopToPath Y).right :=
  loopBasedPathFiberIso_hom_ι Y

/-- loop の path 表示の終点は基点で定数。 -/
@[reassoc (attr := simp)]
lemma loopToPath_endpoint (Y : PointedSimplicialSet.{u}) :
    (loopToPath Y).right ≫ (pathEndpoint Y).right = SSet.const Y.basepoint := by
  rw [← loopToPath_fiber, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, comp_const, pathEndpoint_basepoint]

/-- 概要：Hom と fiber の同型による包含後の射の一致で写像族を検出する。
方針：fiber 同型で移してから、通常の fiber の包含による一意性を使う。
規約：パラメータ T は任意。
使われ方：Goerss–Jardine I §8。fiber 内の path の面の等式。 -/
lemma fiberHom_ext (A : PointedSimplicialSet.{u}) {E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) {T : SSet.{u}}
    {f g : T ⟶ (PointedObject.basedHom A (pointedFiber p)).right}
    (h : f ≫ (PointedObject.basedHomMap A (pointedFiberι p)).right =
      g ≫ (PointedObject.basedHomMap A (pointedFiberι p)).right) : f = g := by
  apply (cancel_mono (fiberIso A p).hom.right).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext (PointedObject.basedHomMap A p).right _
  change (f ≫ (fiberIso A p).hom.right) ≫
    (pointedFiberι (PointedObject.basedHomMap A p)).right =
      (g ≫ (fiberIso A p).hom.right) ≫
        (pointedFiberι (PointedObject.basedHomMap A p)).right
  have he := congrArg Under.Hom.right (fiberIso_hom_ι A p)
  simp only [Under.comp_right] at he
  simpa only [Category.assoc, he] using h

/-- 概要：Hom–fiber 同型の逆を通した path の終点は元の終点へ含まれる。
方針：path の終点の自然性と同型の包含等式を合成する。
規約：点つき射の厳密な等式。
使われ方：Goerss–Jardine I §8。fiber 内の path の終点の計算。 -/
@[reassoc (attr := simp)]
lemma pathFiber_endpoint {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    (fiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p).inv ≫ pathEndpoint (pointedFiber p) ≫ pointedFiberι p =
      pointedFiberι (basedPathMap p) ≫ pathEndpoint E := by
  have hn := pathEndpoint_natural (pointedFiberι p)
  have he := fiberIso_inv_map_ι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p
  change (fiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval p).inv ≫ basedPathMap (pointedFiberι p) =
    pointedFiberι (basedPathMap p) at he
  rw [← hn, ← Category.assoc, he]

/-- 概要：loop–fiber 同型の逆を通してから path に含める射の全空間での表示。
方針：loop の path 表示の自然性と loop–fiber の射影式を使う。
規約：既存の loop–fiber 同型を用い、源の入れ替えをしない。
使われ方：Goerss–Jardine I §8。比較出力の一つの loop 面の同定。 -/
@[reassoc]
lemma loopFiber_toPath {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    (loopPointedFiberIso p).inv ≫ loopToPath (pointedFiber p) ≫ basedPathMap (pointedFiberι p) =
      pointedFiberι (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p) ≫
        loopToPath E := by
  have hn := loopToPath_natural (pointedFiberι p)
  change PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pointedFiberι p) ≫
    loopToPath E = loopToPath (pointedFiber p) ≫ basedPathMap (pointedFiberι p) at hn
  rw [← hn, ← loopPointedFiberIso_hom_ι, ← Category.assoc, Iso.inv_hom_id_assoc]

end
end SerrePositivity.KST.Spectra.PointedMapping
