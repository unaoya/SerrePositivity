module

public import SerrePositivity.KST.Comparison.BarEdge
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups

/-!
# 一対象圏の辺と基本群の積の向き

概要：モノイドの nerve の辺が基本群で反乗法的になることを二単体から証明する。
方針：境界定数一次単体を作り、二つの隣接射の二単体を MulStruct と照合する。
規約：SingleObj の合成は f≫g=g*f、K-L9 の π₁ の積は δ₂、δ₀ の順である。
使われ方：KST Lemma 2.13 の基本群の群演算との整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped _root_.Simplicial

/--
概要：一対象圏の nerve の基点。
方針：唯一の対象の零単体を選ぶ。
規約：単体次数ごとのモノイドを持ち込まない。
使われ方：境界定数な nerve の辺。
-/
def monoidNervePoint (T : MonCat.{u}) : (nerve (SingleObj T)) _⦋0⦌ :=
  ComposableArrows.mk₀ (SingleObj.star T)

/--
概要：モノイドの nerve の辺の両端は基点である。
方針：二つの頂点への制限を零次の射列で比較する。
規約：全ての元に適用する。
使われ方：一次単体の境界定数性。
-/
theorem monoidNerveEdge_face (T : MonCat.{u}) (a : T) (i : Fin 2) :
    (nerve (SingleObj T)).δ i (monoidEdgeSimplex T a) = monoidNervePoint T := by
  fin_cases i <;> exact ComposableArrows.ext₀ rfl

/--
概要：モノイドの各元から境界定数一次単体を作る。
方針：辺を Yoneda で表し、二つの端点を照合する。
規約：nerve の Kan 性は要求しない。
使われ方：Kan 複体への写像による基本群の元の代表。
-/
def monoidNerveLoop (T : MonCat.{u}) (a : T) :
    (nerve (SingleObj T)).PtSimplex 1 (monoidNervePoint T) where
  map := yonedaEquiv.symm (monoidEdgeSimplex T a)
  comm := by
    rw [Subcomplex.ofSimplex_ι, SSet.comp_const]
    apply boundary.hom_ext
    intro i
    rw [← Category.assoc, boundary.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm,
      monoidNerveEdge_face, SSet.comp_const]
    exact SSet.yonedaEquiv_symm_zero _

/--
概要：nerve の二単体は第一辺・第二辺・合成辺の積の充填である。
方針：隣接射 a、b の射列の三つの面を計算する。
規約：合成辺のラベルは b*a。
使われ方：基本群への辺の写像の反乗法性。
-/
def monoidNerveLoopMulStruct (T : MonCat.{u}) (a b : T) :
    PtSimplex.MulStruct (monoidNerveLoop T a) (monoidNerveLoop T b)
      (monoidNerveLoop T (b * a)) (Fin.last 0) where
  map := yonedaEquiv.symm (ComposableArrows.mk₂
    (show SingleObj.star T ⟶ SingleObj.star T from a)
    (show SingleObj.star T ⟶ SingleObj.star T from b))
  δ_castSucc_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    congr 1
  δ_succ_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    congr 1
    exact ComposableArrows.ext₁ rfl rfl (by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl)
  δ_succ_succ_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    congr 1
    exact ComposableArrows.ext₁ rfl rfl (by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl)
  δ_map_of_lt j hj := by fin_cases j <;> simp at hj
  δ_map_of_gt j hj := by fin_cases j <;> simp at hj

/--
概要：Kan 複体へ送った nerve の辺の基本群の類。
方針：境界定数単体を後合成して K-L9 の商へ送る。
規約：基点は元の唯一の頂点の実際の像。
使われ方：安定一般線形群から分類空間の基本群への比較。
-/
def monoidNerveFundamentalClass {X : SSet.{u}} [KanComplex X] (T : MonCat.{u})
    (f : nerve (SingleObj T) ⟶ X) (a : T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 (f.app _ (monoidNervePoint T)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex f rfl (monoidNerveLoop T a))

/--
概要：nerve の辺の基本群の類は反乗法的である。
方針：二単体の積の充填を後合成し K-L9 の積の計算則を使う。
規約：SingleObj の合成の向きに由来する反乗法性。
使われ方：群状成分の逆元を前合成した乗法的比較。
-/
theorem monoidNerveFundamentalClass_mul {X : SSet.{u}} [KanComplex X] (T : MonCat.{u})
    (f : nerve (SingleObj T) ⟶ X) (a b : T) :
    monoidNerveFundamentalClass T f (b * a) =
      monoidNerveFundamentalClass T f a * monoidNerveFundamentalClass T f b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct f rfl (monoidNerveLoopMulStruct T a b))).symm

/--
概要：単位の nerve の辺は境界定数単体としても定数である。
方針：Yoneda で一次単体を比較し、唯一の恒等射の射列と照合する。
規約：nerve の Kan 性は不要。
使われ方：基本群への辺の写像の単位保存。
-/
theorem monoidNerveLoop_one (T : MonCat.{u}) : monoidNerveLoop T 1 = .const := by
  apply RelativeMorphism.ext
  apply yonedaEquiv.injective
  change monoidEdgeSimplex T 1 = _
  exact ComposableArrows.ext₁ rfl rfl (by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl)

/--
概要：単位の辺の基本群の類は単位である。
方針：定数単体の後合成と基本群の単位の定義を使う。
規約：像の基点は nerve の基点の像。
使われ方：反乗法的比較を束ねる準同型。
-/
theorem monoidNerveFundamentalClass_one {X : SSet.{u}} [KanComplex X] (T : MonCat.{u})
    (f : nerve (SingleObj T) ⟶ X) : monoidNerveFundamentalClass T f 1 = 1 := by
  unfold monoidNerveFundamentalClass
  rw [monoidNerveLoop_one, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex_const]
  rfl

/--
概要：nerve の辺から基本群の反対群へのモノイド準同型。
方針：二単体による反乗法性を反対群の積へ読み替える。
規約：元の bar の辺の向きを保持する。
使われ方：群からの比較で逆元の前合成を明示する。
-/
def monoidNerveFundamentalOppositeHom {X : SSet.{u}} [KanComplex X] (T : MonCat.{u})
    (f : nerve (SingleObj T) ⟶ X) :
    T →* (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 (f.app _ (monoidNervePoint T)))ᵐᵒᵖ where
  toFun a := MulOpposite.op (monoidNerveFundamentalClass T f a)
  map_one' := congrArg MulOpposite.op (monoidNerveFundamentalClass_one T f)
  map_mul' a b := congrArg MulOpposite.op (monoidNerveFundamentalClass_mul T f b a)

/--
概要：群の元の逆元の辺を使った基本群への準同型。
方針：逆元の積の向きと nerve の反乗法性を組み合わせる。
規約：KST Lemma 2.13 の群同型の向きのための規約。
使われ方：安定一般線形群と分類空間の基本群の比較。
-/
def groupNerveFundamentalHom {X : SSet.{u}} [KanComplex X]
    (G : Type u) [Group G] (f : nerve (SingleObj G) ⟶ X) :
    G →* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 (f.app _ (monoidNervePoint (MonCat.of G))) where
  toFun a := monoidNerveFundamentalClass (MonCat.of G) f a⁻¹
  map_one' := by rw [inv_one]; exact monoidNerveFundamentalClass_one (MonCat.of G) f
  map_mul' a b := by
    rw [mul_inv_rev]
    exact monoidNerveFundamentalClass_mul (MonCat.of G) f a⁻¹ b⁻¹

end SerrePositivity.KST.Comparison
