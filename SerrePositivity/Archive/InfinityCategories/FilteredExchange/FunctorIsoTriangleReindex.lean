module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：同じ指定単位と余単位の三角恒等式を、任意の全係数へ移す。
方針：前後合成の交換と二段前合成の結合則を、抽象的な射で使う。
規約：指定因子を保つ。使われ方：元の大きい pointed 値比較への小さい証明の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ指定第一三角恒等式は、任意の全始点係数での値の式を保持する。 -/
lemma functorIso_triangle_precomp {X Y P : SSet.{u}} (V : X ⟶ Y) (R : Y ⟶ X)
    (u : FunctorIso (V ≫ R) (𝟙 X)) (c : FunctorIso (R ≫ V) (𝟙 Y))
    (h : u.postcomp V = c.precomp V) (x : P ⟶ X) :
    (u.precomp x).postcomp V = c.precomp (x ≫ V) := by
  rw [functorIso_precomp_postcomp, h, functorIso_precomp_precomp]

/-- 同じ指定第二三角恒等式は、任意の全標的係数での逆射の式を保持する。 -/
lemma functorIso_triangle_inverse_precomp {X Y P : SSet.{u}} (V : X ⟶ Y) (R : Y ⟶ X)
    (u : FunctorIso (V ≫ R) (𝟙 X)) (c : FunctorIso (R ≫ V) (𝟙 Y))
    (h : u.precomp R = c.postcomp R) (x : P ⟶ Y) :
    u.precomp (x ≫ R) = (c.precomp x).postcomp R := by
  rw [← functorIso_precomp_precomp, h, functorIso_precomp_postcomp]

end SerrePositivity.InfinityCategories.F2
