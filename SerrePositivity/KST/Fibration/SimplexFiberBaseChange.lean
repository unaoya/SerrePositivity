module
public import SerrePositivity.KST.SConstruction.SimplexLeftFiber

/-! # 単体左 fiber の元の引き戻しに沿う厳密な基底変換

元の引き戻しの普遍性で順逆の射を構成し、元の射影と単体パラメーターを回収する。
homotopy fiber や局所化後の引き戻しを仮定しない。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

variable {P X A Y : SSet.{u}} {p : P ⟶ X} {q : P ⟶ A} {f : X ⟶ Y} {u : A ⟶ Y}

/-- 基底変換後の単体左 fiber から、元の像の単体左 fiber への射。 -/
def simplexFiberBaseChangeHom (h : IsPullback p q f u) {m : ℕ} (a : A _⦋m⦌) :
    simplexLeftFiber q a ⟶ simplexLeftFiber f (u.app (Opposite.op ⦋m⦌) a) :=
  simplexLeftFiberLift f _ (simplexLeftFiberProjection q a ≫ p)
    (simplexLeftFiberParameter q a) (by
      rw [Category.assoc, h.w, ← Category.assoc, simplexLeftFiber_condition,
        Category.assoc, ← SSet.yonedaEquiv_symm_comp])

/-- 基底変換射は元の全入力への射影を厳密に保つ。 -/
lemma simplexFiberBaseChangeHom_projection (h : IsPullback p q f u) {m : ℕ} (a : A _⦋m⦌) :
    simplexFiberBaseChangeHom h a ≫ simplexLeftFiberProjection f (u.app (Opposite.op ⦋m⦌) a) =
      simplexLeftFiberProjection q a ≫ p := simplexLeftFiberLift_projection _ _ _ _ _

/-- 基底変換射は指定した元の単体パラメーターを保つ。 -/
lemma simplexFiberBaseChangeHom_parameter (h : IsPullback p q f u) {m : ℕ} (a : A _⦋m⦌) :
    simplexFiberBaseChangeHom h a ≫ simplexLeftFiberParameter f (u.app (Opposite.op ⦋m⦌) a) =
      simplexLeftFiberParameter q a := simplexLeftFiberLift_parameter _ _ _ _ _

/-- 元の引き戻しの普遍性による単体左 fiber の逆基底変換射。 -/
def simplexFiberBaseChangeInv (h : IsPullback p q f u) {m : ℕ} (a : A _⦋m⦌) :
    simplexLeftFiber f (u.app (Opposite.op ⦋m⦌) a) ⟶ simplexLeftFiber q a :=
  simplexLeftFiberLift q a
    (h.lift (simplexLeftFiberProjection f (u.app (Opposite.op ⦋m⦌) a))
      (simplexLeftFiberParameter f (u.app (Opposite.op ⦋m⦌) a) ≫ SSet.yonedaEquiv.symm a)
      (by rw [simplexLeftFiber_condition, Category.assoc, ← SSet.yonedaEquiv_symm_comp]))
    (simplexLeftFiberParameter f (u.app (Opposite.op ⦋m⦌) a)) (h.lift_snd _ _ _)

/-- 逆射の入力への射影は、元の引き戻しの同じ普遍的な持ち上げ。 -/
lemma simplexFiberBaseChangeInv_projection (h : IsPullback p q f u) {m : ℕ} (a : A _⦋m⦌) :
    simplexFiberBaseChangeInv h a ≫ simplexLeftFiberProjection q a =
      h.lift (simplexLeftFiberProjection f (u.app (Opposite.op ⦋m⦌) a))
        (simplexLeftFiberParameter f (u.app (Opposite.op ⦋m⦌) a) ≫ SSet.yonedaEquiv.symm a)
        (by rw [simplexLeftFiber_condition, Category.assoc, ← SSet.yonedaEquiv_symm_comp]) :=
  simplexLeftFiberLift_projection _ _ _ _ _

/-- 逆射も元の単体パラメーターを厳密に回収する。 -/
lemma simplexFiberBaseChangeInv_parameter (h : IsPullback p q f u) {m : ℕ} (a : A _⦋m⦌) :
    simplexFiberBaseChangeInv h a ≫ simplexLeftFiberParameter q a =
      simplexLeftFiberParameter f (u.app (Opposite.op ⦋m⦌) a) :=
  simplexLeftFiberLift_parameter _ _ _ _ _

/-- 元の単体・入力を保つ単体左 fiber の厳密な基底変換同型。 -/
def simplexFiberBaseChangeIso (h : IsPullback p q f u) {m : ℕ} (a : A _⦋m⦌) :
    simplexLeftFiber q a ≅ simplexLeftFiber f (u.app (Opposite.op ⦋m⦌) a) where
  hom := simplexFiberBaseChangeHom h a
  inv := simplexFiberBaseChangeInv h a
  hom_inv_id := by
    apply simplexLeftFiber_hom_ext q a
    · rw [Category.assoc, simplexFiberBaseChangeInv_projection, Category.id_comp]
      apply h.hom_ext
      · rw [Category.assoc, h.lift_fst, simplexFiberBaseChangeHom_projection]
      · rw [Category.assoc, h.lift_snd, ← Category.assoc,
          simplexFiberBaseChangeHom_parameter, simplexLeftFiber_condition]
    · rw [Category.assoc, simplexFiberBaseChangeInv_parameter,
        simplexFiberBaseChangeHom_parameter, Category.id_comp]
  inv_hom_id := by
    apply simplexLeftFiber_hom_ext f (u.app (Opposite.op ⦋m⦌) a)
    · rw [Category.assoc, simplexFiberBaseChangeHom_projection, ← Category.assoc,
        simplexFiberBaseChangeInv_projection, h.lift_fst, Category.id_comp]
    · rw [Category.assoc, simplexFiberBaseChangeHom_parameter,
        simplexFiberBaseChangeInv_parameter, Category.id_comp]

end SerrePositivity.KST.Fibration
