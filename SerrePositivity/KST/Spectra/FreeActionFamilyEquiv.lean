module

public import SerrePositivity.KST.Spectra.FreeActionFamily

/-!
概要：自由 G 集合上の同変族と通常の族との実際の同値。
方針：第一座標 1 への制限と作用による拡張が両逆であることを示す。
規約：単体パラメーターと係数の Kan 性を仮定しない。
使われ方：Goerss–Jardine VIII §2。自由作用の cochain の内部 Hom 表示。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G : Type u} [Group G] (S : Type u) (B : Action SSet.{u} G)

/-- 概要：作用で拡張して第一座標 1 に戻すと元の族になる。
方針：単位元の作用が恒等射であることを各単体で使う。
規約：族全体の厳密な等式。
使われ方：Goerss–Jardine VIII §2。自由軌道の同変族の表示の一方の逆。 -/
lemma restrict_extend {A : SSet.{u}}
    (s : (Functor.const (SimplexCategoryᵒᵖ)).obj S ⊗ A ⟶ B.V) :
    restrict S B (extend S B s) = s := by
  ext n x
  change ((B.ρ 1).asHom.app n) (s.app n (x.1, x.2)) = s.app n x
  rw [map_one]
  rfl

/-- 概要：同変族を第一座標 1 に制限して作用で拡張すると元の同変族になる。
方針：第一座標 g を持つ射に対する図式の自然性を (1,s) で評価する。
規約：第一座標を掛ける方向は左作用の規約に従う。
使われ方：Goerss–Jardine VIII §2。自由軌道の同変族の表示の他方の逆。 -/
lemma extend_restrict {A : SSet.{u}}
    (s : weight S ⊗ (Functor.const (AsSmall.{u} (SingleObj G))).obj A ⟶ coefficients B) :
    extend S B (restrict S B s) = s := by
  apply NatTrans.ext
  funext i
  apply NatTrans.ext
  funext n
  ext x
  let g : G := x.1.1
  let f : AsSmall.up.obj (SingleObj.star G) ⟶ i := ULift.up g
  have h := congr($(congr_app (s.naturality f) n) (((1 : G), x.1.2), x.2))
  change (s.app i).app n ((g * 1, x.1.2), x.2) =
    ((B.ρ g).asHom.app n)
      ((s.app (AsSmall.up.obj (SingleObj.star G))).app n (((1 : G), x.1.2), x.2)) at h
  change ((B.ρ g).asHom.app n)
    ((s.app (AsSmall.up.obj (SingleObj.star G))).app n (((1 : G), x.1.2), x.2)) =
      (s.app i).app n x
  simpa only [g, mul_one, Prod.eta] using h.symm

/-- 概要：自由 G 集合のパラメーター付き同変族は通常の族と同値。
方針：制限と拡張を両逆として束ねる。
規約：同値は集合の同値であり、後続で単体集合の同型へ移す。
使われ方：Goerss–Jardine VIII §2。自由作用の cochain の表現の普遍性。 -/
def equiv (A : SSet.{u}) :
    (weight S ⊗ (Functor.const (AsSmall.{u} (SingleObj G))).obj A ⟶ coefficients B) ≃
      ((Functor.const (SimplexCategoryᵒᵖ)).obj S ⊗ A ⟶ B.V) where
  toFun := restrict S B
  invFun := extend S B
  left_inv := extend_restrict S B
  right_inv := restrict_extend S B

/-- 概要：自由軌道への制限は単体パラメーターの前合成と可換。
方針：第一座標 1 での評価の定義を各単体で展開する。
規約：パラメーターの射に条件はない。
使われ方：Goerss–Jardine VIII §2。同変族の同値の自然性。 -/
lemma restrict_pre {A A' : SSet.{u}} (f : A ⟶ A')
    (s : weight S ⊗ (Functor.const (AsSmall.{u} (SingleObj G))).obj A' ⟶ coefficients B) :
    restrict S B ((weight S ◁ (Functor.const (AsSmall.{u} (SingleObj G))).map f) ≫ s) =
      ((Functor.const (SimplexCategoryᵒᵖ)).obj S ◁ f) ≫ restrict S B s := by
  ext n x
  rfl

/-- 概要：自由軌道への拡張は単体パラメーターの前合成と可換。
方針：作用がパラメーターの変数を変えないことを各単体で確認する。
規約：パラメーターの射は任意。
使われ方：Goerss–Jardine VIII §2。同変内部 Hom の同型の自然性。 -/
lemma extend_pre {A A' : SSet.{u}} (f : A ⟶ A')
    (s : (Functor.const (SimplexCategoryᵒᵖ)).obj S ⊗ A' ⟶ B.V) :
    extend S B (((Functor.const (SimplexCategoryᵒᵖ)).obj S ◁ f) ≫ s) =
      (weight S ◁ (Functor.const (AsSmall.{u} (SingleObj G))).map f) ≫ extend S B s := by
  apply NatTrans.ext
  funext i
  ext n x
  rfl

end

end SerrePositivity.KST.Spectra.FreeActionFamily
