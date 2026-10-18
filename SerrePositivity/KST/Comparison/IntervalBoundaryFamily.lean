module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryOne
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# 区間の両端に指定する単体的写像の族

概要：パラメータ付き区間の境界に二つの写像を貼り合わせる。
方針：境界が二つの頂点の余積であることを直積で保存する。
規約：Segal 1974 Proposition 1.6・Lemma 1.7 の基底付き変形の補助構成。
使われ方：anodyne 分解のファイバーごとの収縮。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

/--
概要：区間の境界の二つの頂点の余積を任意の単体集合と直積する。
方針：直積の左随伴性により余積の普遍性を保存する。
規約：Segal 1974 Lemma 1.7 の境界付き族。
使われ方：境界への二写像の貼り合わせと外延性。
-/
def intervalBoundaryTensorIsColimit (T : SSet.{u}) : IsColimit (BinaryCofan.mk
    (T ◁ SSet.boundary.ι.{u} (1 : Fin 2)) (T ◁ SSet.boundary.ι.{u} (0 : Fin 2))) :=
  mapIsColimitOfPreservesOfIsColimit (tensorLeft T) _ _
    HomotopyFunctionComplex.BoundaryOne.isColimit

/--
概要：パラメータ付き区間の二つの端点へ二写像を指定する。
方針：境界の余積の普遍性で貼り合わせる。
規約：Segal 1974 Lemma 1.7。始点が f、終点が g。
使われ方：基底上のホモトピーの境界データ。
-/
def intervalBoundaryMap {T E : SSet.{u}} (f g : T ⟶ E) : T ⊗ (SSet.boundary.{u} 1) ⟶ E :=
  (intervalBoundaryTensorIsColimit T).desc
    (BinaryCofan.mk (fst T (Δ[0] : SSet.{u}) ≫ f) (fst T (Δ[0] : SSet.{u}) ≫ g))

/--
概要：貼り合わせた区間の境界の始点では f を得る。
方針：余積への射の始点成分の計算則を使う。
規約：Segal 1974 Lemma 1.7 の端点の規約。
使われ方：相対ホモトピーの始点条件。
-/
@[reassoc] theorem intervalBoundaryMap_zero {T E : SSet.{u}} (f g : T ⟶ E) :
    T ◁ SSet.boundary.ι.{u} (1 : Fin 2) ≫ intervalBoundaryMap f g =
      fst T (Δ[0] : SSet.{u}) ≫ f :=
  (intervalBoundaryTensorIsColimit T).fac _ ⟨WalkingPair.left⟩

/--
概要：貼り合わせた区間の境界の終点では g を得る。
方針：余積への射の終点成分の計算則を使う。
規約：Segal 1974 Lemma 1.7 の端点の規約。
使われ方：相対ホモトピーの終点条件。
-/
@[reassoc] theorem intervalBoundaryMap_one {T E : SSet.{u}} (f g : T ⟶ E) :
    T ◁ SSet.boundary.ι.{u} (0 : Fin 2) ≫ intervalBoundaryMap f g =
      fst T (Δ[0] : SSet.{u}) ≫ g :=
  (intervalBoundaryTensorIsColimit T).fac _ ⟨WalkingPair.right⟩

/--
概要：パラメータの写像による制限は境界の貼り合わせと可換である。
方針：始点と終点の二成分で比較する。
規約：Segal 1974 Lemma 1.7 の相対的な境界データ。
使われ方：部分対象上でホモトピーを固定する条件。
-/
theorem intervalBoundaryMap_precomp {A T E : SSet.{u}} (i : A ⟶ T) (f g : T ⟶ E) :
    i ▷ (SSet.boundary.{u} 1) ≫ intervalBoundaryMap f g = intervalBoundaryMap (i ≫ f) (i ≫ g) := by
  apply (intervalBoundaryTensorIsColimit A).hom_ext
  rintro ⟨j⟩
  cases j
  all_goals simp only [BinaryCofan.ι_app_left, BinaryCofan.ι_app_right,
    BinaryCofan.mk_inl, BinaryCofan.mk_inr]
  · rw [whisker_exchange_assoc, intervalBoundaryMap_zero, intervalBoundaryMap_zero]
    exact whiskerRight_fst_assoc i _ f
  · rw [whisker_exchange_assoc, intervalBoundaryMap_one, intervalBoundaryMap_one]
    exact whiskerRight_fst_assoc i _ g

/--
概要：行き先への後合成は境界の貼り合わせと可換である。
方針：始点と終点の二成分で比較する。
規約：Segal 1974 Lemma 1.7 の基底への射影。
使われ方：基底上のホモトピーの整合性。
-/
theorem intervalBoundaryMap_postcomp {T E B : SSet.{u}} (f g : T ⟶ E) (p : E ⟶ B) :
    intervalBoundaryMap f g ≫ p = intervalBoundaryMap (f ≫ p) (g ≫ p) := by
  apply (intervalBoundaryTensorIsColimit T).hom_ext
  rintro ⟨j⟩
  cases j
  all_goals simp only [BinaryCofan.ι_app_left, BinaryCofan.ι_app_right,
    BinaryCofan.mk_inl, BinaryCofan.mk_inr]
  · rw [← Category.assoc, intervalBoundaryMap_zero, intervalBoundaryMap_zero, Category.assoc]
  · rw [← Category.assoc, intervalBoundaryMap_one, intervalBoundaryMap_one, Category.assoc]

/--
概要：二つの端点が同じ写像なら境界全体でその写像に定数である。
方針：パラメータ付き境界の二成分の射影を評価する。
規約：Segal 1974 Lemma 1.7 の固定境界。
使われ方：部分対象と基底を固定するホモトピー。
-/
theorem intervalBoundaryMap_self {T E : SSet.{u}} (f : T ⟶ E) :
    intervalBoundaryMap f f = fst T (SSet.boundary.{u} 1) ≫ f := by
  apply (intervalBoundaryTensorIsColimit T).hom_ext
  rintro ⟨j⟩
  cases j
  all_goals simp only [BinaryCofan.ι_app_left, BinaryCofan.ι_app_right,
    BinaryCofan.mk_inl, BinaryCofan.mk_inr]
  · rw [intervalBoundaryMap_zero]
    rfl
  · rw [intervalBoundaryMap_one]
    rfl

end SerrePositivity.KST.Comparison
