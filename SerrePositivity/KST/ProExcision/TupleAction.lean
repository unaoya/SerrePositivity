module
public import SerrePositivity.KST.ProExcision.ActionDescent
public import SerrePositivity.KST.Comparison.BarSegal

/-!
# 有限積の指定した座標への作用

概要：同じモノイドを、作用先の有限積の指定した座標だけに作用させる。
方針：指定外では恒等自己準同型、指定内では元の作用を使う。
規約：KST Proposition A.1 の行の比較。群状性は元の G だけに要求する。
使われ方：prefix の作用を有限個の群状作用の族に分解する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.KST.Comparison
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：単体的モノイドの有限積。
方針：各次数で関数のモノイドを取り、各座標へ単体射を適用する。
規約：KST Proposition A.1。使われ方：作用先 H^r のモノイド構造。 -/
def tupleMonoid (M : SimplicialObject MonCat.{u}) (r : ℕ) : SimplicialObject MonCat.{u} where
  obj n := MonCat.of (Fin r → M.obj n)
  map f := MonCat.ofHom
    { toFun := fun h j ↦ (M.map f).hom (h j)
      map_one' := by funext j; exact map_one (M.map f).hom
      map_mul' h k := by funext j; exact map_mul (M.map f).hom (h j) (k j) }
  map_id n := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro h
    funext j
    change (M.map (𝟙 n)).hom (h j) = h j
    rw [M.map_id]
    rfl
  map_comp f g := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro h
    funext j
    change (M.map (f ≫ g)).hom (h j) = (M.map g).hom ((M.map f).hom (h j))
    rw [M.map_comp]
    rfl

/-- 概要：有限積モノイドの台は既存の有限積単体的集合。
方針：各次数の同じ関数の型を同定する。
規約：KST Proposition A.1。使われ方：bar の行の座標と作用の族の接続。 -/
def tupleMonoidSpaceIso (M : SimplicialObject MonCat.{u}) (r : ℕ) :
    monoidSpace (tupleMonoid M r) ≅ monoidTupleSpace M r :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro _ _ _; rfl)

/-- 概要：有限積の一つの座標への射影。
方針：関数を指定した添字で評価する。
規約：KST Proposition A.1。使われ方：作用の族を与えるパラメータ。 -/
def tupleCoordinate (M : SimplicialObject MonCat.{u}) {r : ℕ} (i : Fin r) :
    monoidTupleSpace M r ⟶ monoidSpace M where
  app _ := ↾fun h ↦ h i

/-- 概要：指定した座標だけに作用する単体的モノイド作用。
方針：指定外は恒等写像、指定内は元の作用とする。
規約：KST Proposition A.1。各座標に独立の G を導入しない。
使われ方：行の prefix 作用を群状作用の有限合成へ分解する。 -/
def maskedTupleAction (A : SimplicialMonoidAction G H) {r : ℕ}
    (mask : Fin r → Prop) [DecidablePred mask] : SimplicialMonoidAction G (tupleMonoid H r) where
  action n :=
    { toFun := fun a ↦
        { toFun := fun h j ↦ if mask j then A.action n a (h j) else h j
          map_one' := by
            funext j
            change (if mask j then A.action n a (1 : H.obj n) else 1) = 1
            by_cases hj : mask j <;> simp [hj]
          map_mul' h k := by
            funext j
            change (if mask j then A.action n a (h j * k j) else h j * k j) =
              (if mask j then A.action n a (h j) else h j) *
                (if mask j then A.action n a (k j) else k j)
            by_cases hj : mask j <;> simp [hj] }
      map_one' := by
        apply MonoidHom.ext
        intro h
        funext j
        change (if mask j then A.action n 1 (h j) else h j) = h j
        by_cases hj : mask j <;> simp [hj]
      map_mul' a b := by
        apply MonoidHom.ext
        intro h
        funext j
        change (if mask j then A.action n (a * b) (h j) else h j) =
          if mask j then A.action n a (if mask j then A.action n b (h j) else h j)
            else (if mask j then A.action n b (h j) else h j)
        by_cases hj : mask j <;> simp [hj] }
  naturality {n m} f a h := by
    funext j
    change (H.map f).hom (if mask j then A.action n a (h j) else h j) =
      if mask j then A.action m ((G.map f).hom a) ((H.map f).hom (h j))
      else (H.map f).hom (h j)
    by_cases hj : mask j
    · simp only [ite_eq_left hj]
      exact A.naturality f a (h j)
    · simp only [ite_eq_right hj]

/-- 概要：第 i パラメータを H^r の座標 j≥i に作用させる。
方針：指定座標の作用と第 i 射影による作用の族を合成する。
規約：KST Proposition A.1 の逆順の nerve 座標。
使われ方：各行の prefix 比較の一段。 -/
def tupleActionStep (A : SimplicialMonoidAction G H) {r : ℕ} (i : Fin r) :
    monoidTupleSpace G r ⊗ monoidSpace (tupleMonoid H r) ⟶
      monoidTupleSpace G r ⊗ monoidSpace (tupleMonoid H r) :=
  actionFamily (maskedTupleAction A (fun j ↦ i ≤ j)) (tupleCoordinate G i)

/-- 概要：各段は群状な G の作用により局所化で可逆。
方針：指定座標への作用の族に既存のセル降下の定理を適用する。
規約：KST Proposition A.1。群状性は G にのみ要求する。
使われ方：prefix 比較を有限合成として同値と示す。 -/
theorem tupleActionStep_localized_isIso (A : SimplicialMonoidAction G H)
    (hG : SimplicialMonoid.IsGrouplike G) {r : ℕ} (i : Fin r) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (tupleActionStep A i)) :=
  actionFamily_localized_isIso (maskedTupleAction A (fun j ↦ i ≤ j)) hG _

end SerrePositivity.KST.ProExcision
