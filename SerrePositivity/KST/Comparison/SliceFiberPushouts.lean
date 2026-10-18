module

public import SerrePositivity.KST.Comparison.SliceAdjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Over

/-!
# スライスのファイバー関手と pushout

概要：単体集合のスライスで固定した全空間との積を取る関手は pushout を保つ。
方針：構成済みのスライスの閉構造による左随伴性を使う。
規約：Segal 1974 Lemma 1.7 の厳密な引き戻しの貼り合わせの補助。homotopy 引き戻しへの移行は別項目。
使われ方：実際の二重写像円筒の pushout と厳密なファイバーの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：固定した全空間とのスライス内の積を取り基底を忘れる関手は全ての小さい余極限を保つ。
方針：スライスの閉構造から得た左随伴性を使う。
規約：基底や全空間の Kan 性は不要。
使われ方：厳密なファイバーと貼り合わせの交換。
-/
instance sliceFiberFunctor_preservesColimits {E B : SSet.{u}} (p : E ⟶ B) :
    PreservesColimits (sliceFiberFunctor p) := inferInstance

/--
概要：スライスの pushout は固定したファイバー関手で単体集合の pushout に送られる。
方針：pushout の余極限保存の一般定理を使う。
規約：Segal Lemma 1.7 の厳密な引き戻しの部分。
使われ方：スライスで作った二重写像円筒の厳密な比較。
-/
theorem sliceFiberFunctor_isPushout {E B : SSet.{u}} (p : E ⟶ B)
    {A C D P : Over B} {f : A ⟶ C} {g : A ⟶ D} {i : C ⟶ P} {j : D ⟶ P}
    (h : IsPushout f g i j) :
    IsPushout ((sliceFiberFunctor p).map f) ((sliceFiberFunctor p).map g)
      ((sliceFiberFunctor p).map i) ((sliceFiberFunctor p).map j) := h.map (sliceFiberFunctor p)

/--
概要：スライスの pushout のファイバーと、各ファイバーの pushout の標準的な比較同型。
方針：左随伴性による pushout 保存の標準同型を使う。
規約：同型の向きはファイバーたちの pushout から元の pushout のファイバー。
使われ方：二重写像円筒とファイバーの実際の射の比較。
-/
def sliceFiberPushoutIso {E B : SSet.{u}} (p : E ⟶ B)
    {A C D : Over B} (f : A ⟶ C) (g : A ⟶ D) :
    pushout ((sliceFiberFunctor p).map f) ((sliceFiberFunctor p).map g) ≅
      (sliceFiberFunctor p).obj (pushout f g) :=
  PreservesPushout.iso (sliceFiberFunctor p) f g

end SerrePositivity.KST.Comparison
