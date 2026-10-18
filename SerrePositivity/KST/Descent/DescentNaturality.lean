module

public import SerrePositivity.KST.Descent.Axioms

/-!
# 同変な可換正方形による降下比較の移行

## 概要
同変な射の引き戻しを不変部分へ制限し、被約化前後の指定比較を可換にする。

## 方針
反変関手の合成保存だけで自然性を証明する。
縦の引き戻しが全単射なら、同変性から逆像も不変になり、不変部分での全単射を得る。

## 規約
G の有限性や平均作用素はこの移行には不要。
全次数の指定写像の全単射性を移し、抽象同型の存在には弱めない。

## 使われ方
論文 定理 3.1 の「一般 → 被約」の還元と、(3.7) の比較の自然性。
-/

@[expose] public section

universe u v w t

open CategoryTheory Opposite

namespace SerrePositivity.KST.Descent.GradedPresheaf

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable (L : GradedPresheaf.{u, v, w, t} C Coefficient)
variable {G : Type*} [Group G]

/-- 概要：同変な幾何射の引き戻しは群作用の引き戻しと可換（論文 (3.7)）。
方針：幾何学的な可換式に反変関手を適用する。
規約：不変条件のため各 g 自身による引き戻しを使う。
使われ方：不変部分への制限と、その全単射性の証明。 -/
theorem pullback_action_comm (H : Coefficient) (n : ℤ) {X Y : C} (f : X ⟶ Y)
    (actionX : G →* Aut X) (actionY : G →* Aut Y)
    (equivariant : ∀ g, (actionX g).asIso.hom ≫ f = f ≫ (actionY g).asIso.hom) (g : G) :
    (L.pullback H n (actionX g).asIso.hom).comp (L.pullback H n f) =
      (L.pullback H n f).comp (L.pullback H n (actionY g).asIso.hom) := by
  simpa only [pullback_comp] using congrArg (L.pullback H n) (equivariant g)

/-- 概要：同変な幾何射の引き戻しを不変部分へ制限（論文 (3.7)）。
方針：作用との可換性により不変元の像も不変になる。
規約：元の引き戻しと同じ値を持つ。
使われ方：reduction の包含の比較を固定部分へ移す。 -/
def invariantPullback (H : Coefficient) (n : ℤ) {X Y : C} (f : X ⟶ Y)
    (actionX : G →* Aut X) (actionY : G →* Aut Y)
    (equivariant : ∀ g, (actionX g).asIso.hom ≫ f = f ≫ (actionY g).asIso.hom) :
    L.invariantSubmodule H n actionY →ₗ[ℚ] L.invariantSubmodule H n actionX :=
  ((L.pullback H n f).comp (L.invariantSubmodule H n actionY).subtype).codRestrict _
    (fun x g ↦ by
      have h := LinearMap.congr_fun (L.pullback_action_comm H n f actionX actionY equivariant g)
        x.val
      change L.pullback H n (actionX g).asIso.hom (L.pullback H n f x.val) = _ at h
      exact h.trans (congrArg (L.pullback H n f) (x.property g)))

/-- 概要：全単射な同変引き戻しは不変部分でも全単射（論文 定理 3.1）。
方針：単射性で元の一意性と逆像の不変性を示す。
規約：G の有限性は不要で、平均による全射の保存とは別の議論。
使われ方：冪零不変性を G 固定部分の比較へ移す。 -/
theorem invariantPullback_bijective (H : Coefficient) (n : ℤ) {X Y : C} (f : X ⟶ Y)
    (actionX : G →* Aut X) (actionY : G →* Aut Y)
    (equivariant : ∀ g, (actionX g).asIso.hom ≫ f = f ≫ (actionY g).asIso.hom)
    (bijective : Function.Bijective (L.pullback H n f)) :
    Function.Bijective (L.invariantPullback H n f actionX actionY equivariant) := by
  constructor
  · intro x y h
    exact Subtype.ext (bijective.1 (congrArg Subtype.val h))
  · intro y
    obtain ⟨x, hx⟩ := bijective.2 y.val
    have fixed : x ∈ L.invariantSubmodule H n actionY := by
      intro g
      apply bijective.1
      have h := LinearMap.congr_fun (L.pullback_action_comm H n f actionX actionY equivariant g) x
      change L.pullback H n (actionX g).asIso.hom (L.pullback H n f x) = _ at h
      exact (h.symm.trans (by rw [hx]; exact y.property g)).trans hx.symm
    exact ⟨⟨x, fixed⟩, Subtype.ext hx⟩

/-- 概要：同変な正方形の不変部分への指定比較は可換（論文 (3.7)）。
方針：反変合成の保存を部分型の値で検査する。
規約：平方の四辺は前層の定義域の幾何射。
使われ方：被約化前後の指定降下写像の同型性を移す。 -/
theorem invariantComparison_naturality (H : Coefficient) (n : ℤ) {X Y X' Y' : C}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (square : a ≫ f = f' ≫ b) (action : G →* Aut X) (action' : G →* Aut X')
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f)
    (over_base' : ∀ g, (action' g).asIso.hom ≫ f' = f')
    (equivariant : ∀ g, (action' g).asIso.hom ≫ a = a ≫ (action g).asIso.hom) :
    (L.invariantPullback H n a action' action equivariant).comp
        (L.invariantComparison H n f action over_base) =
      (L.invariantComparison H n f' action' over_base').comp (L.pullback H n b) := by
  ext x
  change L.pullback H n a (L.pullback H n f x) =
    L.pullback H n f' (L.pullback H n b x)
  have h := LinearMap.congr_fun (congrArg (L.pullback H n) square) x
  simpa only [pullback_comp, LinearMap.comp_apply] using h

/-- 概要：両縦辺が全次数同型な同変正方形で降下の成否は同値（定理 3.1）。
方針：指定比較の可換性と、不変部分への縦比較の全単射性を使う。
規約：主定理の結論を仮定せず、二つの別の幾何射の降下を比較する。
使われ方：公理 (3) による「一般 → 被約」の還元。 -/
theorem piDescent_iff_of_bijective_square {X Y X' Y' : C}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (square : a ≫ f = f' ≫ b) (action : G →* Aut X) (action' : G →* Aut X')
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f)
    (over_base' : ∀ g, (action' g).asIso.hom ≫ f' = f')
    (equivariant : ∀ g, (action' g).asIso.hom ≫ a = a ≫ (action g).asIso.hom)
    (bijective_a : ∀ H n, Function.Bijective (L.pullback H n a))
    (bijective_b : ∀ H n, Function.Bijective (L.pullback H n b)) :
    L.PiDescent f action over_base ↔ L.PiDescent f' action' over_base' := by
  have comm H n :
      L.invariantPullback H n a action' action equivariant ∘
          L.invariantComparison H n f action over_base =
        L.invariantComparison H n f' action' over_base' ∘ L.pullback H n b := by
    funext x
    exact LinearMap.congr_fun
      (L.invariantComparison_naturality H n f f' a b square action action'
        over_base over_base' equivariant) x
  constructor
  · intro h H n
    have hh := (L.invariantPullback_bijective H n a action' action equivariant
      (bijective_a H n)).comp (h H n)
    rw [comm H n] at hh
    exact (Function.Bijective.of_comp_iff _ (bijective_b H n)).mp hh
  · intro h H n
    have hh := (h H n).comp (bijective_b H n)
    rw [← comm H n] at hh
    exact (Function.Bijective.of_comp_iff'
      (L.invariantPullback_bijective H n a action' action equivariant (bijective_a H n)) _).mp hh

end SerrePositivity.KST.Descent.GradedPresheaf
