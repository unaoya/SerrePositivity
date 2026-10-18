module
public import SerrePositivity.KST.Comparison.PiZeroRing

/-!
# 単体的環の実射が成分環に誘導する準同型

概要：既存の Mathlib の π₀ と K-L2 の成分環上に、単体的環の射の実誘導写像を構成する。
方針：台の単体的集合の π₀ の写像を零次の代表で環準同型にする。
規約：KST Proposition 4.14 の係数比較。π₀ の新しい定義や高次 π_n は導入しない。
使われ方：反転・反対環・単位化の実同型による ĜL の単位条件の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial
variable {A B D : SimplicialObject RingCat.{u}}

/-- 概要：単体的環の射が既存の成分環に誘導する実環準同型。
方針：台の π₀ の実写像が零次の代表で四つの環演算を保つことを示す。
規約：KST Proposition 4.14 の係数比較。
使われ方：実成分行列の可逆性を係数比較に沿って移す。 -/
def componentRingMap (f : A ⟶ B) : π₀ (Comparison.ringSpace A) →+* π₀ (Comparison.ringSpace B) where
  toFun := mapπ₀ (Functor.whiskerRight f (forget RingCat))
  map_zero' := by
    change π₀.mk (X := Comparison.ringSpace B) ((f.app (op ⦋0⦌)).hom 0) = π₀.mk (X := Comparison.ringSpace B) (0 : B.obj (op ⦋0⦌))
    rw [map_zero]
  map_one' := by
    change π₀.mk (X := Comparison.ringSpace B) ((f.app (op ⦋0⦌)).hom 1) = π₀.mk (X := Comparison.ringSpace B) (1 : B.obj (op ⦋0⦌))
    rw [map_one]
  map_add' x y := by
    induction x using π₀.rec with | mk x => ?_
    induction y using π₀.rec with | mk y => ?_
    change A.obj (op ⦋0⦌) at x y
    change π₀.mk (X := Comparison.ringSpace B) ((f.app (op ⦋0⦌)).hom (x + y)) =
      π₀.mk (X := Comparison.ringSpace B) ((f.app (op ⦋0⦌)).hom x + (f.app (op ⦋0⦌)).hom y)
    rw [map_add]
  map_mul' x y := by
    induction x using π₀.rec with | mk x => ?_
    induction y using π₀.rec with | mk y => ?_
    change A.obj (op ⦋0⦌) at x y
    change π₀.mk (X := Comparison.ringSpace B) ((f.app (op ⦋0⦌)).hom (x * y)) =
      π₀.mk (X := Comparison.ringSpace B) ((f.app (op ⦋0⦌)).hom x * (f.app (op ⦋0⦌)).hom y)
    rw [map_mul]

/-- 概要：成分環の実誘導写像は零次の代表を対応する代表へ送る。
方針：既存の π₀ の写像を定義で評価する。
規約：KST Proposition 4.14。使われ方：実成分行列の計算。 -/
lemma componentRingMap_mk (f : A ⟶ B) (x : A.obj (op ⦋0⦌)) :
    componentRingMap f (π₀.mk x) = π₀.mk (X := Comparison.ringSpace B) ((f.app (op ⦋0⦌)).hom x) := rfl

/-- 概要：成分環の実誘導写像は恒等射を保つ。
方針：零次の代表で比較する。
規約：KST Proposition 4.14。使われ方：成分環の実同型の逆の法則。 -/
lemma componentRingMap_id (A : SimplicialObject RingCat.{u}) :
    componentRingMap (𝟙 A) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  induction x using π₀.rec with | mk x => rfl

/-- 概要：成分環の実誘導写像は射の合成を保つ。
方針：零次の代表の二回の像を比較する。
規約：KST Proposition 4.14。使われ方：実成分環比較の合成。 -/
lemma componentRingMap_comp (f : A ⟶ B) (g : B ⟶ D) :
    componentRingMap (f ≫ g) = (componentRingMap g).comp (componentRingMap f) := by
  apply RingHom.ext
  intro x
  induction x using π₀.rec with | mk x => rfl

/-- 概要：単体的環の実同型は既存の成分環の実環同型を誘導する。
方針：二つの誘導環準同型の合成を恒等射の保存で確認する。
規約：KST Proposition 4.14。使われ方：単位化の反対環との実同型の成分への移送。 -/
def componentRingEquiv (e : A ≅ B) : π₀ (Comparison.ringSpace A) ≃+* π₀ (Comparison.ringSpace B) where
  __ := componentRingMap e.hom
  invFun := componentRingMap e.inv
  left_inv x := by
    change ((componentRingMap e.inv).comp (componentRingMap e.hom)) x = x
    rw [← componentRingMap_comp, e.hom_inv_id, componentRingMap_id]
    rfl
  right_inv x := by
    change ((componentRingMap e.hom).comp (componentRingMap e.inv)) x = x
    rw [← componentRingMap_comp, e.inv_hom_id, componentRingMap_id]
    rfl

end SerrePositivity.KST.ProExcision
