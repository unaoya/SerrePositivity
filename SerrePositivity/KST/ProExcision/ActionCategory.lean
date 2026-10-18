module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.CategoryTheory.SingleObj
public import SerrePositivity.CategoryTheory.NerveHomotopy

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# モノイド作用の圏と正則作用の収縮

概要：KST Appendix A の E_X G の次数ごとの作用の圏を構成する。
方針：対象は X の元、射はその元を移す G のラベルとする。
規約：合成のラベルは後のラベルを左から掛ける。
使われ方：Prop A.1 の二重作用 bar、EG の収縮、半直積 bar との比較。
-/

universe u v w z
namespace SerrePositivity.KST.ProExcision
open CategoryTheory

/-- 概要：モノイド作用の圏の対象。
方針：作用先の元に型タグを付ける。
規約：G を型に含めて作用圏を区別する。
使われ方：KST Appendix A の作用の圏 E_X G。 -/
@[ext] structure ActionObject (G : Type u) (X : Type v) where
  /-- 概要：作用先の元。方針：型タグの値。規約：X の元。使われ方：KST App. A の対象。 -/
  val : X

variable (G : Type u) (X : Type v) [Monoid G] [MulAction G X]

/-- 概要：モノイド作用の圏。
方針：射 x→y を g•x=y となるラベル g とし、積で合成する。
規約：逆元は要求しない。使われ方：KST Appendix A の E_X G の nerve。 -/
instance actionObjectCategory : Category (ActionObject G X) where
  Hom x y := {g : G // g • x.val = y.val}
  id x := ⟨1, one_smul G x.val⟩
  comp f g := ⟨g.val * f.val, by rw [mul_smul, f.property, g.property]⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

variable {G X}

/-- 概要：作用の圏から作用するモノイドの一対象圏への射影。
方針：対象を唯一の対象へ、射をラベルへ送る。
規約：SingleObj の合成順序と一致する。
使われ方：KST App. A の E_X G → BG。 -/
def actionCategoryProjection : ActionObject G X ⥤ SingleObj G where
  obj _ := SingleObj.star G
  map f := f.val

/-- 概要：同変な写像が作用の圏の間に誘導する関手。
方針：対象とラベルを写し、同変性で射の条件を移す。
規約：作用先の写像は集合の写像でよい。
使われ方：KST Prop A.1 の全ての単体方向での作用 bar の自然性。 -/
def actionCategoryMap {G' : Type w} {X' : Type z} [Monoid G'] [MulAction G' X']
    (f : G →* G') (g : X → X') (hg : ∀ a x, g (a • x) = f a • g x) :
    ActionObject G X ⥤ ActionObject G' X' where
  obj x := ⟨g x.val⟩
  map h := ⟨f h.val, by rw [← hg, h.property]⟩
  map_id x := Subtype.ext (map_one f)
  map_comp h k := Subtype.ext (map_mul f k.val h.val)

/-- 概要：恒等な同変写像から作用圏の恒等関手を得る。
方針：対象とラベルを定義通り比較する。
規約：同変性の証明に依存しない。使われ方：KST Prop A.1 の作用 bar の恒等則。 -/
@[simp] theorem actionCategoryMap_id :
    actionCategoryMap (MonoidHom.id G) (id : X → X) (fun _ _ ↦ rfl) =
      𝟭 (ActionObject G X) := by rfl

/-- 概要：作用圏の誘導関手は同変写像の合成を保つ。
方針：対象とラベルの合成が定義通り一致することを使う。
規約：作用先の写像は集合の写像でよい。
使われ方：KST Prop A.1 の二重作用 bar の関手性。 -/
theorem actionCategoryMap_comp {G' G'' X' X'' : Type*}
    [Monoid G'] [Monoid G''] [MulAction G' X'] [MulAction G'' X'']
    (f : G →* G') (g : X → X') (hg : ∀ a x, g (a • x) = f a • g x)
    (f' : G' →* G'') (g' : X' → X'') (hg' : ∀ a x, g' (a • x) = f' a • g' x) :
    actionCategoryMap f g hg ⋙ actionCategoryMap f' g' hg' =
      actionCategoryMap (f'.comp f) (g' ∘ g) (by
        intro a x
        dsimp
        rw [hg, hg']) := by rfl

/-- 概要：正則作用の単位の対象から恒等関手への自然変換。
方針：各 x へラベル x の射 1→x を取る。
規約：一般のモノイドに成立。使われ方：KST Appendix A の EG の収縮。 -/
def regularActionObjectContraction (M : Type u) [Monoid M] :
    (Functor.const (ActionObject M M)).obj ⟨1⟩ ⟶ 𝟭 (ActionObject M M) where
  app x := ⟨x.val, mul_one x.val⟩
  naturality x y f := by
    apply Subtype.ext
    change y.val * 1 = f.val * x.val
    rw [mul_one]
    exact f.property.symm

/-- 概要：正則作用の nerve の定数写像と恒等写像の間の実ホモトピー。
方針：単位からの自然変換を nerve のホモトピーへ送る。
規約：KST Appendix A の EG の可縮性。逆元は不要。
使われ方：Prop A.1 の作用 bar とホモロジー係数の比較。 -/
def regularActionObjectNerveContraction (M : Type u) [Monoid M] :
    SSet.Homotopy (nerveMap ((Functor.const (ActionObject M M)).obj ⟨1⟩))
      (nerveMap (𝟭 (ActionObject M M))) :=
  SerrePositivity.NerveHomotopy.homotopy (regularActionObjectContraction M)

end SerrePositivity.KST.ProExcision
