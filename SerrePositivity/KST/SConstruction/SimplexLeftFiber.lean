module
public import SerrePositivity.KST.SConstruction.CofiberEvaluations

/-! # 単体上の左 fiber と McCarthy の射
概要：単体上の pullback と、subobject の左 fiber から quotient の object S への射を定義する。
方針：実際の単体の Yoneda 射で引き戻し、単体の制限に沿う射を普遍性で作る。
規約：homotopy fiber とは区別する。使われ方：Fiore–Pieper Theorem 1.15・Lemma 4.24。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open scoped Simplicial

/-- 概要：射 f の指定単体上の左 fiber。
方針：単体の Yoneda 射による実際の pullback を取る。
規約：Kan 条件や普遍性を追加仮定にしない。使われ方：単体積版 Quillen A の入力。 -/
def simplexLeftFiber {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ} (y : Y _⦋m⦌) : SSet.{u} :=
  pullback f (SSet.yonedaEquiv.symm y)

/-- 概要：左 fiber から元の単体集合への射影。
方針：pullback の第一射影。
規約：元の図式の単体を保持する。使われ方：McCarthy の quotient への射。 -/
def simplexLeftFiberProjection {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ} (y : Y _⦋m⦌) :
    simplexLeftFiber f y ⟶ X := pullback.fst f (SSet.yonedaEquiv.symm y)

/-- 概要：左 fiber のパラメーターである標準単体への射影。
方針：pullback の第二射影。
規約：単体の添字写像を保持する。使われ方：McCarthy の基底の収縮。 -/
def simplexLeftFiberParameter {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ} (y : Y _⦋m⦌) :
    simplexLeftFiber f y ⟶ Δ[m] := pullback.snd f (SSet.yonedaEquiv.symm y)

/-- 概要：左 fiber の元の単体とパラメーターは指定単体上で一致する。
方針：pullback の可換性。
規約：全単体での厳密な等号。使われ方：fiber 内のホモトピーの対象条件。 -/
lemma simplexLeftFiber_condition {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ} (y : Y _⦋m⦌) :
    simplexLeftFiberProjection f y ≫ f =
      simplexLeftFiberParameter f y ≫ SSet.yonedaEquiv.symm y := pullback.condition

/-- 概要：指定単体上の一致を持つ族は左 fiber に厳密に持ち上がる。
方針：pullback の普遍性。
規約：パラメーター A は任意。使われ方：McCarthy の切断とホモトピーの構成。 -/
def simplexLeftFiberLift {A X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ} (y : Y _⦋m⦌)
    (e : A ⟶ X) (a : A ⟶ Δ[m]) (h : e ≫ f = a ≫ SSet.yonedaEquiv.symm y) :
    A ⟶ simplexLeftFiber f y := pullback.lift e a h

/-- 概要：左 fiber の持ち上げは元の図式の族を回収する。
方針：pullback の第一射影の式。
規約：厳密な等号。使われ方：切断とホモトピーの射影の照合。 -/
lemma simplexLeftFiberLift_projection {A X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ}
    (y : Y _⦋m⦌) (e : A ⟶ X) (a : A ⟶ Δ[m])
    (h : e ≫ f = a ≫ SSet.yonedaEquiv.symm y) :
    simplexLeftFiberLift f y e a h ≫ simplexLeftFiberProjection f y = e :=
  pullback.lift_fst _ _ _

/-- 概要：左 fiber の持ち上げは指定したパラメーターを回収する。
方針：pullback の第二射影の式。
規約：厳密な等号。使われ方：基底の収縮との両立。 -/
lemma simplexLeftFiberLift_parameter {A X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ}
    (y : Y _⦋m⦌) (e : A ⟶ X) (a : A ⟶ Δ[m])
    (h : e ≫ f = a ≫ SSet.yonedaEquiv.symm y) :
    simplexLeftFiberLift f y e a h ≫ simplexLeftFiberParameter f y = a :=
  pullback.lift_snd _ _ _

/-- 概要：左 fiber への二つの射は二つの射影で等号を判定できる。
方針：pullback の射の外延性。
規約：対象の点だけの比較には弱めない。使われ方：単体恒等式とホモトピーの端点。 -/
lemma simplexLeftFiber_hom_ext {A X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ} (y : Y _⦋m⦌)
    {a b : A ⟶ simplexLeftFiber f y}
    (he : a ≫ simplexLeftFiberProjection f y = b ≫ simplexLeftFiberProjection f y)
    (ha : a ≫ simplexLeftFiberParameter f y = b ≫ simplexLeftFiberParameter f y) : a = b :=
  pullback.hom_ext he ha

/-- 概要：単体の制限は対応する左 fiber の間の射を誘導する。
方針：元の射影を保持し、パラメーターに標準単体の射を合成する。
規約：制限された単体の fiber から元の単体の fiber への向き。使われ方：Quillen A の単体的図式。 -/
def simplexLeftFiberMap {X Y : SSet.{u}} (f : X ⟶ Y) {l m : ℕ}
    (θ : ⦋l⦌ ⟶ ⦋m⦌) (y : Y _⦋m⦌) :
    simplexLeftFiber f (Y.map θ.op y) ⟶ simplexLeftFiber f y :=
  simplexLeftFiberLift f y (simplexLeftFiberProjection f (Y.map θ.op y))
    (simplexLeftFiberParameter f (Y.map θ.op y) ≫ stdSimplex.map θ) (by
      rw [simplexLeftFiber_condition, Category.assoc]
      congr 1
      exact (SSet.yonedaEquiv_symm_naturality_left θ y).symm)

/-- 概要：左 fiber の制限は元の単体の射影を保持する。
方針：持ち上げの第一射影の式。
規約：全単体での等号。使われ方：quotient の射との自然性。 -/
lemma simplexLeftFiberMap_projection {X Y : SSet.{u}} (f : X ⟶ Y) {l m : ℕ}
    (θ : ⦋l⦌ ⟶ ⦋m⦌) (y : Y _⦋m⦌) :
    simplexLeftFiberMap f θ y ≫ simplexLeftFiberProjection f y =
      simplexLeftFiberProjection f (Y.map θ.op y) := pullback.lift_fst _ _ _

/-- 概要：左 fiber の制限のパラメーターは標準単体の射との合成。
方針：持ち上げの第二射影の式。
規約：全単体での等号。使われ方：基底の収縮の自然性。 -/
lemma simplexLeftFiberMap_parameter {X Y : SSet.{u}} (f : X ⟶ Y) {l m : ℕ}
    (θ : ⦋l⦌ ⟶ ⦋m⦌) (y : Y _⦋m⦌) :
    simplexLeftFiberMap f θ y ≫ simplexLeftFiberParameter f y =
      simplexLeftFiberParameter f (Y.map θ.op y) ≫ stdSimplex.map θ := pullback.lift_snd _ _ _

/-- 概要：左 fiber の n 単体は元の n 単体と添字の n 単体の一致条件付きの対。
方針：Yoneda 同値と pullback の普遍性を互いに逆に使う。
規約：全ての次元での実際の同値。使われ方：原典の (e,α) 表示との厳密な照合。 -/
def simplexLeftFiberSimplexEquiv {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ}
    (y : Y _⦋m⦌) (n : ℕ) :
    (simplexLeftFiber f y) _⦋n⦌ ≃
      {p : X _⦋n⦌ × (Δ[m] : SSet.{u}) _⦋n⦌ //
        f.app (Opposite.op ⦋n⦌) p.1 = (SSet.yonedaEquiv.symm y).app (Opposite.op ⦋n⦌) p.2} where
  toFun s := ⟨((simplexLeftFiberProjection f y).app (Opposite.op ⦋n⦌) s,
    (simplexLeftFiberParameter f y).app (Opposite.op ⦋n⦌) s),
    ConcreteCategory.congr_hom (NatTrans.congr_app (simplexLeftFiber_condition f y)
      (Opposite.op ⦋n⦌)) s⟩
  invFun p := SSet.yonedaEquiv (simplexLeftFiberLift f y
    (SSet.yonedaEquiv.symm p.val.1) (SSet.yonedaEquiv.symm p.val.2) (by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact p.property))
  left_inv s := by
    apply SSet.yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    apply simplexLeftFiber_hom_ext f y
    · rw [simplexLeftFiberLift_projection, ← SSet.yonedaEquiv_symm_comp]
    · rw [simplexLeftFiberLift_parameter, ← SSet.yonedaEquiv_symm_comp]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change (simplexLeftFiberProjection f y).app (Opposite.op ⦋n⦌)
        (SSet.yonedaEquiv _) = p.val.1
      rw [← SSet.yonedaEquiv_comp, simplexLeftFiberLift_projection, Equiv.apply_symm_apply]
    · change (simplexLeftFiberParameter f y).app (Opposite.op ⦋n⦌)
        (SSet.yonedaEquiv _) = p.val.2
      rw [← SSet.yonedaEquiv_comp, simplexLeftFiberLift_parameter, Equiv.apply_symm_apply]

/-- 概要：左 fiber の制限は元の射の後合成で定める射と可換。
方針：元の単体への射影を保持する式に後合成する。
規約：標的 T と射 g は任意。使われ方：Quillen A の単体的比較。 -/
lemma simplexLeftFiberMap_postcomp {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {l m : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌) (y : Y _⦋m⦌) :
    simplexLeftFiberMap f θ y ≫ simplexLeftFiberProjection f y ≫ g =
      simplexLeftFiberProjection f (Y.map θ.op y) ≫ g := by
  rw [← Category.assoc, simplexLeftFiberMap_projection]

/-- 概要：subobject の固定単体上の McCarthy の左 fiber。
方針：cofiber 図式の完全な subobject 評価に object S を適用して引き戻す。
規約：原典の f/(m,A) に対応する strict pullback。使われ方：加法性の fiber の収縮。 -/
def cofiberSubobjectLeftFiber (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) : SSet.{u} :=
  simplexLeftFiber (objectSConstructionFunctor.map (cofiberStableSubobject X)) a

/-- 概要：McCarthy の左 fiber から quotient の object S への射。
方針：元の cofiber 図式への射影に quotient の完全関手の像を合成する。
規約：原典の r の実際の射、弱同値性はまだ含まない。使われ方：単体積版 Quillen A の仮定の証明。 -/
def cofiberLeftFiberQuotient (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    cofiberSubobjectLeftFiber X a ⟶ objectSConstruction X.carrier :=
  simplexLeftFiberProjection (objectSConstructionFunctor.map (cofiberStableSubobject X)) a ≫
    objectSConstructionFunctor.map (cofiberStableQuotient X)

end SerrePositivity.KST.SConstruction
