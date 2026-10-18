module

public import SerrePositivity.KST.Spectra.GroupActionCochains
public import Mathlib.CategoryTheory.Action.Monoidal

/-!
概要：自由 G 集合の離散重みから作用図式へのパラメーター付き自然変換の表示。
方針：第一座標が 1 の部分へ制限し、逆に作用で全ての第一座標へ広げる。
規約：係数は単体集合の厳密な G 作用。パラメーターの Kan 性は不要。
使われ方：Goerss–Jardine VIII §2。自由作用の cochain の関数空間表示。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G : Type u} [Group G] (S : Type u) (B : Action SSet.{u} G)

/-- 概要：G × S の自由作用の離散重み。
方針：左正則作用と S の自明作用の積を単体集合の図式に送る。
規約：G は第一因子にだけ左乗法で作用する。
使われ方：Goerss–Jardine VIII §2。自由軌道の重み。 -/
abbrev weight : AsSmall.{u} (SingleObj G) ⥤ SSet.{u} :=
  (GroupActionCochains.actionWeightFunctor G).obj (Action.leftRegular G ⊗ Action.trivial G S)

/-- 概要：単体集合の作用を小さい一対象圏上の作用図式にする。
方針：通常の作用と図式の同値を使う。
規約：各対象の値は元の B.V。
使われ方：Goerss–Jardine VIII §2。同変な族の係数。 -/
abbrev coefficients : AsSmall.{u} (SingleObj G) ⥤ SSet.{u} :=
  AsSmall.down ⋙ Action.FunctorCategoryEquivalence.functor.obj B

/-- 概要：パラメーター付き同変族を第一座標 1 の部分へ制限する。
方針：各次数で (1,s) に評価する。
規約：第二座標と単体のパラメーターはそのまま保持する。
使われ方：Goerss–Jardine VIII §2。非斉次 cochain の表示。 -/
def restrict {A : SSet.{u}}
    (s : weight S ⊗ (Functor.const (AsSmall.{u} (SingleObj G))).obj A ⟶ coefficients B) :
    (Functor.const (SimplexCategoryᵒᵖ)).obj S ⊗ A ⟶ B.V where
  app n := ↾fun x ↦ (s.app (AsSmall.up.obj (SingleObj.star G))).app n (((1 : G), x.1), x.2)
  naturality i j f := by
    ext x
    exact congr($((s.app (AsSmall.up.obj (SingleObj.star G))).naturality f)
      (((1 : G), x.1), x.2))

/-- 概要：第一座標 1 の族を作用で自由 G 集合全体へ広げる。
方針：(g,s) の値を g が (1,s) の値へ作用したものとする。
規約：余分な同変性の仮定は不要。
使われ方：Goerss–Jardine VIII §2。同変 cochain を非斉次 cochain から戻す。 -/
def extend {A : SSet.{u}} (s : (Functor.const (SimplexCategoryᵒᵖ)).obj S ⊗ A ⟶ B.V) :
    weight S ⊗ (Functor.const (AsSmall.{u} (SingleObj G))).obj A ⟶ coefficients B where
  app _ :=
    { app n := ↾fun x ↦ ((B.ρ x.1.1).asHom.app n) (s.app n (x.1.2, x.2))
      naturality i j f := by
        ext x
        have h₁ := congr($((B.ρ (x.1.1 : G)).asHom.naturality f)
          (s.app i ((x.1.2 : S), x.2)))
        have h₂ := congr($(s.naturality f) ((x.1.2 : S), x.2))
        exact (congrArg (((B.ρ x.1.1).asHom).app j) h₂).trans h₁ }
  naturality i j f := by
    ext n x
    let g : G := f.down
    let h : G := x.1.1
    change ((B.ρ (g * h)).asHom.app n) (s.app n (x.1.2, x.2)) =
      ((B.ρ g).asHom.app n) (((B.ρ h).asHom.app n) (s.app n (x.1.2, x.2)))
    rw [map_mul, End.mul_asHom]
    rfl

end

end SerrePositivity.KST.Spectra.FreeActionFamily
