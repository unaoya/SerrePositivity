module

public import SerrePositivity.InfinityCategories.F2.Presentable.ConeTransportRelativeComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.ClassificationRetraction
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorIsPullbackIso

/-!
概要：底変換された全解図式に全錐があれば、その全分類関手は頂点の Hom 制限の retract。
方針：錐の全脚と標準輸送を底変換に束ね、元の相対比較から分裂三角形を得る。
規約：分裂は全分類関手の圏で行い、点ごとの retract の族で代用しない。
使われ方：accessible 関手の小さい compact 生成圏上の余表現可能性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
/-- 概要：単体集合の同型の往復は各頂点を厳密に固定する。
方針：元の同型の往復等式を零単体で評価する。
規約：同じ元の頂点を保持する。
使われ方：相対 Hom の同型で戻した比較の両端の正規化。 -/
lemma relativeHomIso_inv_hom_vertex {X Y : SSet.{u}} (e : X ≅ Y) (v : X _⦋0⦌) :
    e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) v) = v :=
  ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id (Opposite.op ⦋0⦌)) v

variable {A D E B : SSet.{u}}
  {f : A ⟶ E} {a : A ⟶ D} {p : E ⟶ B} {i : D ⟶ B}
  (hs : IsPullback f a p i) (c : JoinCone f)

/-- 概要：元の全錐の脚は、頂点の底の coslice の底変換への射を与える。
方針：同じ全脚の底の比較と元の全解射影を引き戻しに束ねる。
規約：元の pullback 表示と全錐を保持する。
使われ方：全分類関手の retract の包含側。 -/
def conePullbackComparison :
    A ⟶ pullback (sliceUnderProjection
      (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex))) i :=
  pullback.lift (conePointComparison p c) a
    ((conePointComparison_projection p c).trans hs.w)

/-- 概要：錐から作った底変換比較は元の全解射影を保つ。
方針：引き戻しの第二射影の式を使う。
規約：底は元の D。
使われ方：分類比較の底条件。 -/
lemma conePullbackComparison_projection :
    conePullbackComparison hs c ≫ pullback.snd _ i = a := pullback.lift_snd _ _ _

variable [Quasicategory B] [LeftFibration p]

/-- 概要：底変換された頂点の Hom の全空間を、指定解からの輸送で元の全解へ戻す。
方針：標準輸送と同じ底の射影を元の pullback の普遍性で束ねる。
規約：元の全空間 A へ戻す。
使われ方：全分類関手の retract の射影側。 -/
def conePullbackTransport :
    pullback (sliceUnderProjection
      (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex))) i ⟶ A :=
  hs.lift (pullback.fst _ i ≫ cosliceVertexTransport p c.vertex) (pullback.snd _ i) (by
    rw [Category.assoc, cosliceVertexTransport_projection]
    exact pullback.condition)

/-- 概要：輸送で戻す射は同じ元の底を保つ。
方針：元の pullback の第二射影公式を使う。
規約：指定した元の射影 a。
使われ方：分類する射影側の底条件。 -/
lemma conePullbackTransport_projection :
    conePullbackTransport hs c ≫ a = pullback.snd _ i := hs.lift_snd _ _ _

/-- 概要：包含と輸送の合成は元の全空間への写像後に同じ錐脚の輸送になる。
方針：元の pullback と標準引き戻しの第一射影公式を合成する。
規約：同じ全射の厳密な等式。
使われ方：相対関手空間の比較を元の底変換へ戻す。 -/
lemma conePullbackComparison_transport_map :
    (conePullbackComparison hs c ≫ conePullbackTransport hs c) ≫ f =
      conePointComparison p c ≫ cosliceVertexTransport p c.vertex := by
  rw [Category.assoc, conePullbackTransport, hs.lift_fst, ← Category.assoc,
    conePullbackComparison, pullback.lift_fst]

variable [Quasicategory D] [LeftFibration a]

/-- 概要：包含と輸送の合成は元の底変換上の恒等図式と相対関手空間で同型。
方針：元の全空間上の比較を相対 Hom の pullback 同型で戻す。
規約：全解の高次単体を保つ相対同型。
使われ方：分類した全関手の分裂三角形。 -/
def conePullbackRelativeRetraction :
    VertexIso
      (relativeFunctorVertex a a
        (conePullbackComparison hs c ≫ conePullbackTransport hs c)
        (by rw [Category.assoc, conePullbackTransport_projection,
          conePullbackComparison_projection]))
      (relativeFunctorVertex a a (𝟙 A) (Category.id_comp a)) := by
  let e := relativeFunctorIsPullbackIso hs a (f ≫ p) hs.w.symm
  have h := coneTransportRelativeComparison p c
  have h₀ : VertexIso
      (e.hom.app (Opposite.op ⦋0⦌) (relativeFunctorVertex a a (𝟙 A) (Category.id_comp a)))
      (e.hom.app (Opposite.op ⦋0⦌) (relativeFunctorVertex a a
        (conePullbackComparison hs c ≫ conePullbackTransport hs c)
        (by rw [Category.assoc, conePullbackTransport_projection,
          conePullbackComparison_projection]))) := by
    rw [relativeFunctorIsPullbackIso_vertex hs a (f ≫ p) hs.w.symm
      (𝟙 A) (Category.id_comp a),
      relativeFunctorIsPullbackIso_vertex hs a (f ≫ p) hs.w.symm
        (conePullbackComparison hs c ≫ conePullbackTransport hs c)
        (by rw [Category.assoc, conePullbackTransport_projection,
          conePullbackComparison_projection])]
    simpa only [Category.id_comp, conePullbackComparison_transport_map] using h
  let x := relativeFunctorVertex a a (𝟙 A) (Category.id_comp a)
  let y := relativeFunctorVertex a a (conePullbackComparison hs c ≫ conePullbackTransport hs c)
    (by rw [Category.assoc, conePullbackTransport_projection, conePullbackComparison_projection])
  have hm : VertexIso (e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) x))
      (e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) y)) := VertexIso.map h₀ e.inv
  exact (eqToIso (congrArg HomotopyCategory.mk (relativeHomIso_inv_hom_vertex e y))).symm ≪≫
    hm.symm ≪≫
    eqToIso (congrArg HomotopyCategory.mk (relativeHomIso_inv_hom_vertex e x))

/-- 概要：元の底変換の全分類図式は同じ頂点の Hom の底変換の全分類図式の retract。
方針：包含・輸送と相対 Hom 内の分裂同型を分類する。
規約：元の全関手圏での一つの retract。
使われ方：元の空間値関手の余表現可能性への接続。 -/
def conePullbackClassificationRetraction :
    Idempotent.VertexRetraction (functorVertex (leftStraighteningInfinityDiagram a))
      (functorVertex (leftStraighteningInfinityDiagram (pullback.snd
        (sliceUnderProjection (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex))) i))) := by
  have : LeftFibration (pullback.snd
      (sliceUnderProjection (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex))) i) :=
    ⟨leftFibrations.pullback_snd _ i (LeftFibration.mem (p := _))⟩
  exact leftClassificationRetraction a _ (conePullbackComparison hs c)
    (conePullbackComparison_projection hs c) (conePullbackTransport hs c)
    (conePullbackTransport_projection hs c) (conePullbackRelativeRetraction hs c)

end SerrePositivity.InfinityCategories.F2.Presentable
