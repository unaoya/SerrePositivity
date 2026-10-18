module

public import Mathlib.CategoryTheory.Whiskering

public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
概要：閉モノイダル圏の内部 Hom と end の交換同型。
方針：各 end 射影を内部 Hom に送り、逆射は各射影を uncurry して end に持ち上げる。
規約：必要な二つの end の存在だけを仮定する。
使われ方：HA §1.4.2、BF 1978 §2。hG と Tot の loop とレベルごとの end の交換。
-/

@[expose] public section

universe u v w z

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite

namespace SerrePositivity.KST.Spectra.EndInternalHom

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {J : Type w} [Category.{z} J]

/-- 概要：end の二変数の図式を同じ関手で後合成する。
方針：内側の図式への後合成関手を外側にも適用する。
規約：内部 Hom 以外の関手にも定義する。
使われ方：HA §1.4.2。end と内部 Hom の交換の標的の図式。 -/
def postDiagram (F : C ⥤ C) (D : Jᵒᵖ ⥤ J ⥤ C) : Jᵒᵖ ⥤ J ⥤ C :=
  D ⋙ (Functor.whiskeringRight J C C).obj F

variable (A : C) (D : Jᵒᵖ ⥤ J ⥤ C)
  [HasEnd D] [HasEnd (postDiagram (ihom A) D)]

/-- 概要：内部 Hom を施した end から各段の内部 Hom の end への比較。
方針：元の end の各射影を内部 Hom に送り end へ持ち上げる。
規約：通常の圏の実際の射。
使われ方：HA §1.4.2。loop と end の順序の交換。 -/
def homToEnd : (ihom A).obj (end_ D) ⟶ end_ (postDiagram (ihom A) D) :=
  end_.lift (fun j ↦ (ihom A).map (end_.π D j)) (fun i j f ↦ by
    change (ihom A).map (end_.π D i) ≫ (ihom A).map ((D.obj (op i)).map f) =
      (ihom A).map (end_.π D j) ≫ (ihom A).map ((D.map f.op).app j)
    rw [← Functor.map_comp, ← Functor.map_comp, end_.condition D f])

/-- 概要：各段の内部 Hom の end から内部 Hom を施した end への逆比較。
方針：各射影を uncurry し、元の end への持ち上げを curry する。
規約：tensor の左因子が A。
使われ方：HA §1.4.2、BF 1978 §2。end の loop 表示を戻す。 -/
def endToHom : end_ (postDiagram (ihom A) D) ⟶ (ihom A).obj (end_ D) :=
  curry (end_.lift (fun j ↦ uncurry (end_.π (postDiagram (ihom A) D) j)) (fun i j f ↦ by
    rw [← uncurry_natural_right, ← uncurry_natural_right]
    apply congrArg uncurry
    exact end_.condition (postDiagram (ihom A) D) f))

/-- 概要：順比較の各射影は元の射影への内部 Hom の作用。
方針：end への持ち上げの射影式を使う。
規約：厳密な等式。
使われ方：HA §1.4.2。交換同型の自然性の検査。 -/
@[reassoc (attr := simp)]
theorem homToEnd_π (j : J) :
    homToEnd A D ≫ end_.π (postDiagram (ihom A) D) j = (ihom A).map (end_.π D j) :=
  end_.lift_π _ _ j

/-- 概要：逆比較を uncurry して射影すると元の内部 Hom の射影の uncurry。
方針：curry と uncurry を相殺し end の射影式を使う。
規約：tensor の左因子が A。
使われ方：HA §1.4.2。二つの比較の逆関係の検査。 -/
@[reassoc (attr := simp)]
theorem uncurry_endToHom_π (j : J) :
    uncurry (endToHom A D) ≫ end_.π D j =
      uncurry (end_.π (postDiagram (ihom A) D) j) := by
  simp only [endToHom, uncurry_curry, end_.lift_π]

/-- 概要：内部 Hom と end の交換は通常の圏の同型。
方針：end の各射影と随伴の単射性で両合成が恒等であることを検証する。
規約：ホモトピー極限やモデル構造の仮定は不要。
使われ方：HA §1.4.2、BF 1978 §2。Tot の Ω 条件の形式的な交換部分。 -/
def iso : (ihom A).obj (end_ D) ≅ end_ (postDiagram (ihom A) D) where
  hom := homToEnd A D
  inv := endToHom A D
  hom_inv_id := by
    apply uncurry_injective
    apply end_.hom_ext
    intro j
    rw [uncurry_natural_left, Category.assoc, uncurry_endToHom_π,
      ← uncurry_natural_left, homToEnd_π]
    simpa only [Category.id_comp] using
      (uncurry_natural_right (𝟙 ((ihom A).obj (end_ D))) (end_.π D j))
  inv_hom_id := by
    apply end_.hom_ext
    intro j
    rw [Category.assoc, homToEnd_π, Category.id_comp]
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_endToHom_π]

end

end SerrePositivity.KST.Spectra.EndInternalHom
