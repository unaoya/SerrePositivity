module


public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource

/-!
概要：外側のパラメータを二つの源の内側へ移す内部 Hom の同型。
方針：二つの源を一つのテンソルへ戻し、パラメータと交換して再び curry する。
規約：パラメータに双対可能性を要求しない。
使われ方：Goerss–Jardine I §7、HA §1.4.2。任意の源を持つ二重 loop の交換の比較。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

/-- 概要：外側のパラメータを二つの源の内側へ移す自然同型。
方針：二つの源の uncurry、パラメータとの交換、二つの源の curry を合成する。
規約：内側の二つの源の順序は保つ。
使われ方：HA §1.4.2。標的にパラメータを含めて二重 loop の式を適用する。 -/
def pairNatIso (A K L : C) : (ihom L ⋙ ihom K) ⋙ ihom A ≅
    ihom A ⋙ (ihom L ⋙ ihom K) :=
  Functor.isoWhiskerRight (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natIso L K).symm (ihom A) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.naturalIso A (L ⊗ K) ≪≫
    Functor.isoWhiskerLeft (ihom A) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natIso L K)

/-- 概要：標的を固定したパラメータと二つの源の交換同型。
方針：自然同型の標的 Y の成分を取る。
規約：Hom(A,Hom(K,Hom(L,Y))) を Hom(K,Hom(L,Hom(A,Y))) へ移す。
使われ方：Goerss–Jardine I §7。写像空間の成分のパラメータを内側へ移す。 -/
def pairIso (A K L Y : C) :
    (ihom A).obj ((ihom K).obj ((ihom L).obj Y)) ≅
      (ihom K).obj ((ihom L).obj ((ihom A).obj Y)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairNatIso A K L).app Y

/-- 概要：パラメータと二つの源の交換の順写像の明示式。
方針：自然同型の三つの成分を取り出す。
規約：二つの源を一つのテンソルへ戻してから交換する。
使われ方：HA §1.4.2。源の交換と整数次数射との可換式の計算。 -/
theorem pairIso_hom (A K L Y : C) : (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A K L Y).hom =
    (ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso L K Y).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (L ⊗ K) Y).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso L K ((ihom A).obj Y)).hom := by
  change (ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso L K Y).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.naturalIso A (L ⊗ K)).app Y).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso L K ((ihom A).obj Y)).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.naturalIso_app]

/-- 概要：パラメータと二つの源の交換は標的の写像について自然。
方針：三つの自然同型の合成の自然性を使う。
規約：標的の写像は任意。
使われ方：HA §1.4.2。Ω 条件の射の後合成をパラメータの移動と交換する。 -/
theorem pairIso_post (A K L : C) {Y Z : C} (f : Y ⟶ Z) :
    (ihom A).map ((ihom K).map ((ihom L).map f)) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A K L Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A K L Y).hom ≫ (ihom K).map ((ihom L).map ((ihom A).map f)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairNatIso A K L).hom.naturality f

/-- 概要：二つの源の交換は外側のパラメータを内側へ移す同型と可換。
方針：二つの源をテンソルへ戻し、braiding の前合成の自然性を使う。
規約：二つの源を交換すると移動後の同じ二つの源が交換される。
使われ方：Goerss–Jardine I §7、HA §1.4.2。任意のパラメータを持つ loop の交換の符号。 -/
theorem pairIso_swap (A K L Y : C) :
    (ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K L Y).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A L K Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A K L Y).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K L ((ihom A).obj Y)).hom := by
  apply (cancel_epi ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso L K Y).hom)).mp
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso_hom, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso_hom]
  rw [← Functor.map_comp_assoc, ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_swap,
    Functor.map_comp_assoc]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right_assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_swap]

/-- 概要：内側の源の制限はパラメータを移す同型と可換。
方針：制限をテンソルの第一因子に戻し、源の制限の自然性で交換する。
規約：源の射 i は任意。
使われ方：Goerss–Jardine I §7。内側の円の符号反転をパラメータの移動と交換する。 -/
theorem pairIso_pre_inner (A K : C) {L' L : C} (i : L' ⟶ L) (Y : C) :
    (ihom A).map ((ihom K).map ((MonoidalClosed.pre i).app Y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A K L' Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A K L Y).hom ≫
        (ihom K).map ((MonoidalClosed.pre i).app ((ihom A).obj Y)) := by
  apply (cancel_epi ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso L K Y).hom)).mp
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso_hom, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso_hom]
  rw [← Functor.map_comp_assoc, ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_left,
    Functor.map_comp_assoc]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right_assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_left]

/-- 概要：外側の源の制限はパラメータを移す同型と可換。
方針：制限をテンソルの第二因子へ戻して交換する。
規約：パラメータ A 自体の位置は最後に内側となる。
使われ方：HA §1.4.2。外側の円の制限とパラメータ付き比較の整合性。 -/
theorem pairIso_pre_outer (A : C) {K' K : C} (j : K' ⟶ K) (L Y : C) :
    (ihom A).map ((MonoidalClosed.pre j).app ((ihom L).obj Y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A K' L Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A K L Y).hom ≫
        (MonoidalClosed.pre j).app ((ihom L).obj ((ihom A).obj Y)) := by
  apply (cancel_epi ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso L K Y).hom)).mp
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso_hom, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso_hom]
  rw [← Functor.map_comp_assoc, ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right,
    Functor.map_comp_assoc]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right_assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right]

end

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
