module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.IteratedSliceOverRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationMappingSpan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：native な錐への射の比較 span を、錐の図式上の slice の頂点 fiber へ同定する。
方針：反復 slice の同型を錐の Yoneda 表示へ適用し、底と評価射を追跡する。
規約：任意の coherent な錐を扱い、strict な錐や Kan 性に制限しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の表現可能な極限判定と切断の制限の比較。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：同じ底の上の厳密な同型は各頂点の fiber の同型を誘導する。
方針：同型と逆を fiber の射へ移し、包含後に両逆則を確認する。
規約：充填性や同値の選択を使わない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の比較 span の中間空間を同じ頂点上で移す段階。 -/
def vertexFiberIsoOfOverIso {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (e : E ≅ F) (he : e.hom ≫ q = p) (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q e.hom he b
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p e.inv (by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]) b
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- 概要：同型で誘導した fiber の同型の順方向を包含すると元の同型の後合成になる。
方針：fiber の誘導射の包含の公式を使う。
規約：実際に定義した同型の順方向に関する式。
使われ方：HTT 4.2.4.1 の比較 span の評価の可換性。 -/
lemma vertexFiberIsoOfOverIso_hom_ι {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (e : E ≅ F) (he : e.hom ≫ q = p) (b : B _⦋0⦌) :
    (vertexFiberIsoOfOverIso p q e he b).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ e.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι p q e.hom he b

/-- 概要：固定図式の等式による slice の移送は可変頂点の射影と可換。
方針：図式の等式で置換して恒等射へ戻す。
規約：quasicategory 性を要求しない。
使われ方：Kerodon §4.3.6（Tag 018E） の錐の Yoneda 表示の正規化。 -/
lemma sliceOver_eqToHom_projection {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) :
    eqToHom (congrArg (fun f : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver f) h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p := by
  cases h
  exact Category.id_comp _

variable {K X : SSet.{u}} {p : K ⟶ X}

/-- 概要：coherent な錐 c の slice 内の零単体の Yoneda 表示。
方針：元の図式 p の slice と標準零単体を明示して Yoneda の同値を使う。
規約：始域は Δ[0]、終域は sliceOver p。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の c への反復 slice の固定図式。 -/
abbrev coneYonedaPoint (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p :=
  (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (n := ⦋0⦌)).symm c

/-- 概要：錐の Yoneda 表示を展開した図式の slice は元の錐の図式の slice と同型。
方針：Yoneda 射の uncurry が元の錐になる等式で移送する。
規約：錐は任意の join の錐。
使われ方：HTT 4.2.4.1 の native な錐の図式を正規化する段階。 -/
def coneSliceOverDiagramIso (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (coneYonedaPoint c)) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver c.val :=
  eqToIso (congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda 0 c))

/-- 概要：錐の図式の正規化は slice の可変頂点の射影を保つ。
方針：固定図式の等式による移送の射影の公式を使う。
規約：単体集合の射の等式として述べる。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の比較を同じ底の fiber へ制限する条件。 -/
lemma coneSliceOverDiagramIso_projection (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (coneSliceOverDiagramIso c).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection c.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (coneYonedaPoint c)) :=
  sliceOver_eqToHom_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda 0 c)

/-- 概要：錐への射の反復 slice は錐の図式上の slice と厳密に同型。
方針：一般の反復 slice の同型を錐の Yoneda 表示へ適用して図式を正規化する。
規約：sliceOver p 内の c への slice と、X 内の c.val の slice を比較する。
使われ方：HTT 4.2.4.1 の native な比較 span の中間空間の同定。 -/
def coneIteratedSliceIso (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (coneYonedaPoint c) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver c.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverIso (p := p) (coneYonedaPoint c) ≪≫ coneSliceOverDiagramIso c

/-- 概要：錐への反復 slice の同型は X への二重の可変頂点の射影を保つ。
方針：一般の反復 slice の射影の式と図式の正規化の射影の式を合成する。
規約：底 X の上の厳密な等式。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の native な比較 span の頂点 fiber の同定。 -/
lemma coneIteratedSliceIso_projection (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (coneIteratedSliceIso c).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection c.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (coneYonedaPoint c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverIso (p := p) (coneYonedaPoint c)).hom ≫
    (coneSliceOverDiagramIso c).hom) ≫ _ = _
  rw [Category.assoc, coneSliceOverDiagramIso_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverIso_projection]

/-- 概要：錐の図式上の slice を元の図式の slice に制限する射。
方針：錐の Yoneda 表示の正規化を戻して、展開した図式の標準制限を適用する。
規約：終域は元の sliceOver p そのもの。
使われ方：HTT 4.2.4.1 の native な始点評価の制限側の模型。 -/
def coneSliceOverRestriction (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver c.val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p :=
  (coneSliceOverDiagramIso c).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.uncurriedSliceOverRestriction (coneYonedaPoint c)

/-- 概要：錐への反復 slice の同型は元の図式への制限を反復 slice の射影に対応させる。
方針：図式の正規化の往復を消去し、一般の反復 slice の制限の可換式を使う。
規約：実際の評価射の等式を保持する。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の比較 span の始点評価と切断の制限の接続。 -/
lemma coneIteratedSliceIso_restriction (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (coneIteratedSliceIso c).hom ≫ coneSliceOverRestriction c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (coneYonedaPoint c) := by
  simp only [coneIteratedSliceIso, coneSliceOverRestriction, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverIso_restriction _

/-- 概要：錐の図式から元の図式への slice の制限は可変頂点を保つ。
方針：反復 slice の同型の順方向で消去し、その射影と制限の可換式を使う。
規約：底 X の上の射となることを結論する。
使われ方：HTT 4.2.4.1 の頂点 fiber 内の制限の誘導。 -/
lemma coneSliceOverRestriction_projection (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    coneSliceOverRestriction c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection c.val := by
  apply (cancel_epi (coneIteratedSliceIso c).hom).1
  rw [← Category.assoc, coneIteratedSliceIso_restriction]
  exact (coneIteratedSliceIso_projection c).symm

/-- 概要：native な比較 span の中間空間は錐の図式上の slice の頂点 fiber と厳密に同型。
方針：底 X の上の反復 slice の同型を同じ頂点 x の fiber へ移す。
規約：Kan 性も極限性も仮定せず、任意の coherent な錐を扱う。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の native な極限判定の中間空間の移送。 -/
def coneMappingTotalIso (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingTotal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c x ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection c.val) x :=
  vertexFiberIsoOfOverIso _ _ (coneIteratedSliceIso c) (coneIteratedSliceIso_projection c) x

/-- 概要：native な比較 span の始点評価は錐の図式からの制限の fiber 射へ対応する。
方針：fiber の包含後で比較し、反復 slice の同型と制限の厳密な可換式を使う。
規約：中間空間の同値だけでなく実際の評価射を同定する。
使われ方：HTT 4.2.4.1 の native な極限判定を切断の制限へ移す入力。 -/
lemma coneMappingTotalIso_evaluation (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    (coneMappingTotalIso c x).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection c.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)
          (coneSliceOverRestriction c) (coneSliceOverRestriction_projection c) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) x
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc]
  change ((vertexFiberIsoOfOverIso _ _ (coneIteratedSliceIso c)
    (coneIteratedSliceIso_projection c) x).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ x) ≫ _ = _
  rw [vertexFiberIsoOfOverIso_hom_ι, Category.assoc, coneIteratedSliceIso_restriction]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
