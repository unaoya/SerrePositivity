module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Category.MonCat.Basic

@[expose] public section

/-!
# モノイド作用による半直積と群ホモロジーへの入口

概要：群状単体モノイドの半直積の、次数ごとの代数模型を構成する。
方針：モノイドの作用と積の保存だけから半直積モノイドを作る。
規約：KST Appendix A の順序 G ⋉ H。各作用の可逆性は要求しない。
使われ方：Prop A.1・Lemma A.2・A.4、Construction A.5・A.6 の基礎。
-/

universe u v w
namespace SerrePositivity.KST.ProExcision

/-- 概要：モノイド G の群 H への作用による半直積の台。
方針：G 成分と H 成分に専用の型を付ける。
規約：積の順は KST Appendix A の (gg′,h·g(h′))。
使われ方：Prop A.1・Lemma A.2 の単体次数ごとの半直積。 -/
@[ext] structure ActionProduct (G : Type u) (H : Type v) where
  /-- 概要：作用するモノイド成分。方針：型タグの第一成分。規約：G。使われ方：KST App. A の射影。 -/
  base : G
  /-- 概要：作用される群成分。方針：型タグの第二成分。規約：H。使われ方：KST App. A の積。 -/
  fiber : H

variable {G : Type u} {H : Type v} [Monoid G] [Monoid H] [MulDistribMulAction G H]

/-- 概要：一般のモノイド作用による半直積モノイド。
方針：作用の乗法保存と合成律で結合法則を示す。
規約：G・H の逆元も作用の自己同型性も不要。
使われ方：KST Prop A.1 の G ⋉ H の次数ごとの積。 -/
instance actionProductMonoid : Monoid (ActionProduct G H) where
  one := ⟨1, 1⟩
  mul x y := ⟨x.base * y.base, x.fiber * (x.base • y.fiber)⟩
  one_mul x := by
    apply ActionProduct.ext
    · change 1 * x.base = x.base
      exact one_mul _
    · change 1 * (1 • x.fiber) = x.fiber
      simp
  mul_one x := by
    apply ActionProduct.ext
    · change x.base * 1 = x.base
      exact mul_one _
    · change x.fiber * (x.base • (1 : H)) = x.fiber
      rw [MulDistribMulAction.smul_one, mul_one]
  mul_assoc x y z := by
    apply ActionProduct.ext
    · exact mul_assoc _ _ _
    · change (x.fiber * (x.base • y.fiber)) * ((x.base * y.base) • z.fiber) =
        x.fiber * (x.base • (y.fiber * (y.base • z.fiber)))
      simp only [mul_smul, smul_mul', mul_assoc]

/-- 概要：半直積から作用するモノイドへの射影。
方針：第一成分を取る。
規約：モノイド準同型。使われ方：KST Appendix A の分裂相対ホモロジー。 -/
def actionProductProjection : ActionProduct G H →* G where
  toFun x := x.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- 概要：作用するモノイドの半直積への標準包含。
方針：群成分を単位にする。
規約：モノイド準同型。使われ方：KST Appendix A の相対項の基準。 -/
def actionProductSection : G →* ActionProduct G H where
  toFun g := ⟨g, 1⟩
  map_one' := rfl
  map_mul' g g' := by
    apply ActionProduct.ext
    · rfl
    · change 1 = 1 * (g • (1 : H))
      rw [MulDistribMulAction.smul_one, one_mul]

/-- 概要：作用される群の半直積への標準包含。
方針：作用するモノイド成分を単位にする。
規約：ここでは H はモノイドでもよい。
使われ方：KST Prop A.1 の半直積のファイバー側。 -/
def actionProductFiber : H →* ActionProduct G H where
  toFun h := ⟨1, h⟩
  map_one' := rfl
  map_mul' h h' := by
    apply ActionProduct.ext
    · change 1 = (1 : G) * 1
      simp
    · change h * h' = h * ((1 : G) • h')
      simp

/-- 概要：半直積の射影は標準包含の左逆。
方針：二つの準同型を各元で評価する。
規約：作用に追加条件はない。使われ方：KST Appendix A の相対項が分裂余核であること。 -/
@[simp] theorem actionProductProjection_section :
    (actionProductProjection (G := G) (H := H)).comp actionProductSection = MonoidHom.id G := by
  rfl

/-- 概要：半直積の各元は群側とモノイド側の標準包含の積。
方針：定義の積を計算する。
規約：群側を先に掛ける。使われ方：KST Prop A.1 の bar の積座標。 -/
theorem actionProduct_decomposition (x : ActionProduct G H) :
    actionProductFiber x.fiber * actionProductSection x.base = x := by
  apply ActionProduct.ext
  · change 1 * x.base = x.base
    simp
  · change x.fiber * ((1 : G) • (1 : H)) = x.fiber
    simp

/-- 概要：半直積上の作用による台写像。
方針：G 成分を保ち、H 成分へその G 元を作用させる。
規約：一般にはモノイド準同型ではない。
使われ方：KST Lemma A.2 の ψ(g,h)=(g,g(h))。 -/
def actionProductTwist (x : ActionProduct G H) : ActionProduct G H :=
  ⟨x.base, x.base • x.fiber⟩

/-- 概要：同変な二つの準同型が半直積の準同型を誘導する。
方針：両成分へ準同型を適用し、群側の積には作用の同変性を使う。
規約：各作用の可逆性は不要。
使われ方：KST Prop A.1 の単体構造と自然性。 -/
def actionProductMap {G' : Type w} {H' : Type*} [Monoid G'] [Monoid H']
    [MulDistribMulAction G' H'] (f : G →* G') (g : H →* H')
    (h : ∀ a b, g (a • b) = f a • g b) : ActionProduct G H →* ActionProduct G' H' where
  toFun x := ⟨f x.base, g x.fiber⟩
  map_one' := by
    apply ActionProduct.ext <;> exact map_one _
  map_mul' x y := by
    apply ActionProduct.ext
    · exact map_mul _ _ _
    · change g (x.fiber * (x.base • y.fiber)) = g x.fiber * (f x.base • g y.fiber)
      rw [map_mul, h]

/-- 概要：半直積の誘導射は恒等準同型を保つ。
方針：各成分を比較する。
規約：同変性の証明の選択に依存しない。
使われ方：KST Prop A.1 の単体的半直積の恒等射。 -/
@[simp] theorem actionProductMap_id :
    actionProductMap (MonoidHom.id G) (MonoidHom.id H) (fun _ _ ↦ rfl) =
      MonoidHom.id (ActionProduct G H) := by
  rfl

/-- 概要：半直積の誘導射は準同型の合成を保つ。
方針：台写像の二つの成分が定義通り一致する。
規約：同変な射のみを合成する。
使われ方：KST Prop A.1 の単体的半直積の合成律。 -/
theorem actionProductMap_comp {G' G'' H' H'' : Type*}
    [Monoid G'] [Monoid G''] [Monoid H'] [Monoid H'']
    [MulDistribMulAction G' H'] [MulDistribMulAction G'' H'']
    (f : G →* G') (g : H →* H') (hf : ∀ a b, g (a • b) = f a • g b)
    (f' : G' →* G'') (g' : H' →* H'') (hf' : ∀ a b, g' (a • b) = f' a • g' b) :
    (actionProductMap f' g' hf').comp (actionProductMap f g hf) =
      actionProductMap (f'.comp f) (g'.comp g) (by
        intro a b
        change g' (g (a • b)) = f' (f a) • g' (g b)
        rw [hf, hf']) := by
  rfl

/-- 概要：台の作用写像 ψ は半直積の誘導射に自然。
方針：第二成分の作用の同変性を使う。
規約：ψ 自体がモノイド準同型であるとは仮定しない。
使われ方：KST Lemma A.2 の ψ の単体性と関手性。 -/
theorem actionProductTwist_natural {G' H' : Type*} [Monoid G'] [Monoid H']
    [MulDistribMulAction G' H'] (f : G →* G') (g : H →* H')
    (h : ∀ a b, g (a • b) = f a • g b) (x : ActionProduct G H) :
    actionProductMap f g h (actionProductTwist x) =
      actionProductTwist (actionProductMap f g h x) := by
  apply ActionProduct.ext
  · rfl
  · exact h x.base x.fiber

end SerrePositivity.KST.ProExcision
