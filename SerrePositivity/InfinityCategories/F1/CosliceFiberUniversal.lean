module

public import SerrePositivity.InfinityCategories.F1.CoslicePinchedIso

/-!
概要：coslice の頂点 fiber への任意の族と両端を固定した join 図式の対応。
方針：coslice の curry と uncurry を fiber の普遍性に制限する。
規約：パラメータと元の単体集合の Kan 性は不要。
使われ方：Kerodon Construction 4.6.5.1、§4.6.6、空間値 fiber 比較の相対的な族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coslice fiber への族を両端を固定した join からの射に展開する。
方針：fiber の包含を後合成し、coslice の uncurry を適用する。
規約：左の点は x、右のパラメータは y に固定する。
使われ方：Kerodon Construction 4.6.5.1、左写像空間の族の幾何的表示。 -/
def cosliceFiberUncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    join (Δ[0] : SSet.{u}) A ⟶ X :=
  sliceUnderUncurry (f ≫ vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)

/-- 概要：展開した族は左因子で始点 x に一致する。
方針：coslice の固定条件を使う。
規約：左因子は標準零単体。
使われ方：Kerodon Construction 4.6.5.1、族の固定始点。 -/
lemma cosliceFiberUncurry_inl {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    joinInl Δ[0] A ≫ cosliceFiberUncurry f = SSet.yonedaEquiv.symm x :=
  sliceUnderUncurry_fixed _

/-- 概要：展開した族は右因子で終点 y に定値。
方針：coslice の射影の式と fiber の固定条件を使う。
規約：パラメータ A は任意。
使われ方：Kerodon Construction 4.6.5.1、族の固定終点。 -/
lemma cosliceFiberUncurry_inr {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    joinInr Δ[0] A ≫ cosliceFiberUncurry f = SSet.const y := by
  rw [cosliceFiberUncurry, sliceUnderUncurry_projection, Category.assoc,
    vertexFiberι_comp, SSet.comp_const]

/-- 概要：両端を固定した join からの射を coslice fiber への族に戻す。
方針：coslice へ curry し、右因子の定値条件で fiber に持ち上げる。
規約：固定条件の証明の選択は結果に影響しない。
使われ方：Kerodon Construction 4.6.5.1、左写像空間の普遍性の逆向き。 -/
def cosliceFiberCurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (F : join (Δ[0] : SSet.{u}) A ⟶ X)
    (hx : joinInl Δ[0] A ≫ F = SSet.yonedaEquiv.symm x)
    (hy : joinInr Δ[0] A ≫ F = SSet.const y) :
    A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y :=
  vertexFiberLift _ y (sliceUnderCurry F hx) ((sliceUnderCurry_projection F hx).trans hy)

/-- 概要：固定した join 図式を curry して展開すると元の図式。
方針：fiber への持ち上げを消し、coslice の両逆の式を使う。
規約：両端の条件は任意の証明でよい。
使われ方：Kerodon Construction 4.6.5.1、普遍性の往復。 -/
lemma cosliceFiberUncurry_curry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (F : join (Δ[0] : SSet.{u}) A ⟶ X)
    (hx : joinInl Δ[0] A ≫ F = SSet.yonedaEquiv.symm x)
    (hy : joinInr Δ[0] A ≫ F = SSet.const y) :
    cosliceFiberUncurry (cosliceFiberCurry F hx hy) = F := by
  unfold cosliceFiberUncurry cosliceFiberCurry
  rw [vertexFiberLift_ι, sliceUnderUncurry_curry]

/-- 概要：coslice fiber への族は展開した join 図式で一意に決まる。
方針：fiber の包含の単射性と coslice の uncurry の単射性を使う。
規約：両族の始域は同じ任意のパラメータ A。
使われ方：Kerodon Construction 4.6.5.1、普遍性の一意性。 -/
lemma cosliceFiberUncurry_injective {A X : SSet.{u}} (x y : X _⦋0⦌) :
    Function.Injective (cosliceFiberUncurry (A := A) (x := x) (y := y)) := by
  intro f g h
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y
  exact sliceUnderUncurry_injective (SSet.yonedaEquiv.symm x) h

/-- 概要：fiber への族を展開して curry すると元の族。
方針：uncurry の単射性により図式の往復へ還元する。
規約：固定条件は展開した族の左右の制限の式。
使われ方：Kerodon Construction 4.6.5.1、普遍性の逆方向の往復。 -/
lemma cosliceFiberCurry_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    cosliceFiberCurry (cosliceFiberUncurry f)
      (cosliceFiberUncurry_inl f) (cosliceFiberUncurry_inr f) = f := by
  apply cosliceFiberUncurry_injective x y
  exact cosliceFiberUncurry_curry _ _ _

/-- 概要：fiber への族の展開はパラメータの前合成と可換。
方針：coslice の uncurry の前合成の自然性を使う。
規約：左因子の点は固定する。
使われ方：Kerodon §4.6.6、族の境界への制限。 -/
lemma cosliceFiberUncurry_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B)
    (f : B ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    cosliceFiberUncurry (i ≫ f) = joinMap (𝟙 Δ[0]) i ≫ cosliceFiberUncurry f := by
  unfold cosliceFiberUncurry
  rw [Category.assoc, sliceUnderUncurry_precomp]

/-- 概要：fiber への族と両端を固定した join 図式の型の同値。
方針：curry と uncurry の両逆の式をまとめる。
規約：相対的な持ち上げの問題に使えるよう任意の A を扱う。
使われ方：Kerodon Construction 4.6.5.1、§4.6.6、左右の写像空間の比較。 -/
def cosliceFiberHomEquiv (A X : SSet.{u}) (x y : X _⦋0⦌) :
    (A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) ≃
      {F : join (Δ[0] : SSet.{u}) A ⟶ X //
        joinInl Δ[0] A ≫ F = SSet.yonedaEquiv.symm x ∧
        joinInr Δ[0] A ≫ F = SSet.const y} where
  toFun f := ⟨cosliceFiberUncurry f, cosliceFiberUncurry_inl f, cosliceFiberUncurry_inr f⟩
  invFun F := cosliceFiberCurry F.val F.property.1 F.property.2
  left_inv := cosliceFiberCurry_uncurry
  right_inv F := Subtype.ext (cosliceFiberUncurry_curry F.val F.property.1 F.property.2)

end SerrePositivity.InfinityCategories
