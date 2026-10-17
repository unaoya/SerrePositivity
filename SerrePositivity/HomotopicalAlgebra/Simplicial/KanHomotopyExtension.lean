module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyFaces
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# anodyne射への制限後のホモトピーから元の両射を結ぶKan値ホモトピーの存在を導く

## 概要
anodyne射への制限後のホモトピーから元の両射を結ぶKan値ホモトピーの存在を導く。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0414][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0414
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Homotopy extension into a Kan complex along an anodyne extension
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanHomotopyExtension
variable {A B K : SSet.{v}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hi hK in
/-- anodyne射に沿って指定したKan値の写像を延長する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
lemma exists_extension (f : A ⟶ K) : ∃ g : B ⟶ K, i ≫ g = f := by
  have : HasLiftingProperty i (terminal.from K) := hi _ hK
  let sq : CommSq f i (terminal.from K) (terminal.from B) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

lemma boundary_compatibility (f g : B ⟶ K) (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    i ▷ (SSet.boundary 1).toSSet ≫ LargeParameterHomotopy.boundaryMap f g =
      A ◁ (SSet.boundary 1).ι ≫ H.h := by
  apply (LargeParameterHomotopy.boundaryColimit A).hom_ext
  rintro ⟨j⟩
  cases j
  · change (A ◁ SSet.boundary.ι (1 : Fin 2)) ≫ _ =
      (A ◁ SSet.boundary.ι (1 : Fin 2)) ≫ _
    rw [← Category.assoc, whisker_exchange, Category.assoc,
      LargeParameterHomotopy.boundaryMap_zero]
    conv_rhs => rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      HomotopyEndpointComparison.face_zero]
    exact whiskerRight_fst_assoc i _ f
  · change (A ◁ SSet.boundary.ι (0 : Fin 2)) ≫ _ =
      (A ◁ SSet.boundary.ι (0 : Fin 2)) ≫ _
    rw [← Category.assoc, whisker_exchange, Category.assoc,
      LargeParameterHomotopy.boundaryMap_one]
    conv_rhs => rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      HomotopyEndpointComparison.face_one]
    exact whiskerRight_fst_assoc i _ g

include hi hK in
/-- anodyne射への制限後のホモトピーから元の両射を結ぶKan値ホモトピーの存在を導く。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
lemma exists_homotopy (f g : B ⟶ K) (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    Nonempty (SSet.Homotopy f g) := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.boundary 1).ι
  have ha : SSet.anodyneExtensions pp.ι := SSet.anodyneExtensions_pushoutObjObjι' pp hi
  have : HasLiftingProperty pp.ι (terminal.from K) := ha _ hK
  let b := pp.isPushout.desc (LargeParameterHomotopy.boundaryMap f g) H.h
    (boundary_compatibility i f g H)
  let sq : CommSq b pp.ι (terminal.from K) (terminal.from _) := ⟨by simp⟩
  have hb : B ◁ (SSet.boundary 1).ι ≫ sq.lift =
      LargeParameterHomotopy.boundaryMap f g := by
    rw [show B ◁ (SSet.boundary 1).ι = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  refine ⟨{ h := sq.lift, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
  · change SSet.ι₀ ≫ sq.lift = f
    rw [← LargeParameterHomotopy.section_zero B, Category.assoc,
      ← SSet.boundary.ι_ι (1 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_zero]
    rfl
  · change SSet.ι₁ ≫ sq.lift = g
    rw [← LargeParameterHomotopy.section_one B, Category.assoc,
      ← SSet.boundary.ι_ι (0 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_one]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

end SerrePositivity.SimplicialModel.KanHomotopyExtension
