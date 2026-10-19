module

public import SerrePositivity.InfinityCategories.F1.PrismEndpointPairPullback
public import SerrePositivity.InfinityCategories.F1.TransportRepresentationCartesianRestriction
public import SerrePositivity.InfinityCategories.F1.TransportCartesianSquare

/-!
概要：二つの表現を底と全空間の直和の表現へ貼り合わせる。
方針：二つの分類図式と pointed space への射をそれぞれ直和からまとめる。
規約：左右の表現を厳密に保ち互いの比較は要求しない。
使われ方：相対射の collage の両端に指定する表現。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：直和上の射の左成分は元の射の pullback。
方針：次数ごとの直和の左成分の一致を使う。
規約：左右の射は任意。
使われ方：直和上の表現条件を左成分で検査する。 -/
lemma isPullback_joinEndpointMap_inl {E F B D : SSet.{u}} (p : E ⟶ B) (q : F ⟶ D) :
    IsPullback (joinEndpointInl E F) p (joinEndpointMap p q) (joinEndpointInl B D) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    exact Sum.inl.inj h.1
  · intro x y h
    cases x with
    | inl x => exact ⟨x, rfl, Sum.inl.inj h⟩
    | inr x =>
      change Sum.inr (q.app d x) = (Sum.inl y : B.obj d ⊕ D.obj d) at h
      cases h

/-- 概要：直和上の射の右成分は元の射の pullback。
方針：次数ごとの直和の右成分の一致を使う。
規約：左右の射は任意。
使われ方：直和上の表現条件を右成分で検査する。 -/
lemma isPullback_joinEndpointMap_inr {E F B D : SSet.{u}} (p : E ⟶ B) (q : F ⟶ D) :
    IsPullback (joinEndpointInr E F) q (joinEndpointMap p q) (joinEndpointInr B D) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    exact Sum.inr.inj h.1
  · intro x y h
    cases x with
    | inl x =>
      change Sum.inl (p.app d x) = (Sum.inr y : B.obj d ⊕ D.obj d) at h
      cases h
    | inr x => exact ⟨x, rfl, Sum.inr.inj h⟩

/-- 概要：二つの表現の四角形を直和上へまとめる。
方針：底と全空間の射をそれぞれ直和から出す。
規約：元の比較の同値性はこの定義には不要。
使われ方：直和の表現の周囲の四角形。 -/
def LeftTransportSquare.sum {E F B D : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ D}
    (R : LeftTransportSquare p) (S : LeftTransportSquare q) :
    LeftTransportSquare (joinEndpointMap p q) where
  diagram := joinEndpointDesc R.diagram S.diagram
  pointedMap := joinEndpointDesc R.pointedMap S.pointedMap
  comm := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    cases x with
    | inl x => exact ConcreteCategory.congr_hom (NatTrans.congr_app R.comm d) x
    | inr x => exact ConcreteCategory.congr_hom (NatTrans.congr_app S.comm d) x

/-- 概要：表現条件は直和へ貼り合わせられる。
方針：左右の cartesian な包含の fiber 同型で元の条件へ戻す。
規約：直和の射影が left fibration である場合に使う。
使われ方：指定された二つの端点表現を同時に保持する。 -/
lemma LeftTransportSquare.sum_isRepresentation {E F B D : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ D} [LeftFibration p] [LeftFibration q]
    [LeftFibration (joinEndpointMap p q)]
    (R : LeftTransportSquare p) (S : LeftTransportSquare q)
    (hR : R.IsRepresentation) (hS : S.IsRepresentation) :
    (R.sum S).IsRepresentation := by
  have : LeftFibration (Arrow.mk p).hom := by change LeftFibration p; infer_instance
  have : LeftFibration (Arrow.mk q).hom := by change LeftFibration q; infer_instance
  have : LeftFibration (Arrow.mk (joinEndpointMap p q)).hom := by
    change LeftFibration (joinEndpointMap p q); infer_instance
  intro b
  cases b with
  | inl b =>
    let f : Arrow.mk p ⟶ Arrow.mk (joinEndpointMap p q) :=
      Arrow.homMk (joinEndpointInl E F) (joinEndpointInl B D) rfl
    have h := (R.sum S).preSquare_pointedFiberMap_isQCatEquivalence_iff f
      (isPullback_joinEndpointMap_inl p q) b
    have he : (R.sum S).preSquare f = R := by
      apply LeftTransportSquare.ext
      · apply SSet.hom_ext; intro d; rfl
      · apply SSet.hom_ext; intro d; rfl
    rw [he] at h
    exact h.mp (hR b)
  | inr b =>
    let f : Arrow.mk q ⟶ Arrow.mk (joinEndpointMap p q) :=
      Arrow.homMk (joinEndpointInr E F) (joinEndpointInr B D) rfl
    have h := (R.sum S).preSquare_pointedFiberMap_isQCatEquivalence_iff f
      (isPullback_joinEndpointMap_inr p q) b
    have he : (R.sum S).preSquare f = S := by
      apply LeftTransportSquare.ext
      · apply SSet.hom_ext; intro d; rfl
      · apply SSet.hom_ext; intro d; rfl
    rw [he] at h
    exact h.mp (hS b)

/-- 概要：指定された二つの表現の直和。
方針：直和の四角形の表現条件を実際の比較へ戻す。
規約：左右の分類図式と全空間の射を厳密に保持する。
使われ方：collage の境界への入力となる表現。 -/
def LeftTransportRepresentation.sum {E F B D : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ D} [LeftFibration p] [LeftFibration q]
    [LeftFibration (joinEndpointMap p q)]
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation q) :
    LeftTransportRepresentation (joinEndpointMap p q) :=
  (R.toSquare.sum S.toSquare).toRepresentation
    (R.toSquare.sum_isRepresentation S.toSquare R.toSquare_isRepresentation
      S.toSquare_isRepresentation)

/-- 概要：直和の表現の分類図式は指定した二つの図式の直和。
方針：表現へ戻す定義。
規約：射の厳密な一致。
使われ方：境界延長から元の両端図式を回収する。 -/
lemma LeftTransportRepresentation.sum_diagram {E F B D : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ D} [LeftFibration p] [LeftFibration q]
    [LeftFibration (joinEndpointMap p q)]
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation q) :
    (R.sum S).diagram = joinEndpointDesc R.diagram S.diagram := rfl

/-- 概要：直和の表現は指定した二つの pointed space への射を保持する。
方針：比較の pullback の第一射影。
規約：同値類でなく射そのものを回収する。
使われ方：境界固定延長の全空間の条件。 -/
lemma LeftTransportRepresentation.sum_pointedMap {E F B D : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ D} [LeftFibration p] [LeftFibration q]
    [LeftFibration (joinEndpointMap p q)]
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation q) :
    (R.sum S).pointedMap = joinEndpointDesc R.pointedMap S.pointedMap :=
  pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories
