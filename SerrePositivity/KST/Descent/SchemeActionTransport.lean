module

public import SerrePositivity.KST.Descent.EquivariantPullbackComparison
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# 同変なスキームの同型による点の推移性の移行

## 概要
始域と基底を同型で比較し、点の各ファイバーの推移性を指定作用へ移す。

## 方針
逆同型で二点を戻し、基底側の単射性で同じファイバーにあることを確認する。

## 規約
通常の点の推移性の任意の底変換での保存は主張しない。

## 使われ方
論文 補題 3.2 のテンソル積モデルから実際のアフィン底変換への推移性の移行。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：同変な単射の正方形で点のファイバーの推移性を移す（論文 補題 3.2）。
方針：正方形で元のファイバーへ移し、同変性と始域側の単射性で戻す。
規約：基底側の射の単射性は不要。
使われ方：有限型の圏の指定引き戻しと underlying scheme の引き戻しの比較。 -/
theorem schemeFiberTransitivity_of_injective_square {X Y X' Y' : Scheme.{u}}
    {G : Type u} [Group G] (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (square : a ≫ f = f' ≫ b) (action : G →* Aut X) (action' : G →* Aut X')
    (equivariant : ∀ g, (action' g).asIso.hom ≫ a = a ≫ (action g).asIso.hom)
    (injective : Function.Injective a)
    (transitive : ∀ x y : X, f x = f y → ∃ g : G, (action g).asIso.hom x = y)
    (x y : X') (same_base : f' x = f' y) :
    ∃ g : G, (action' g).asIso.hom x = y := by
  have comm (z : X') : f (a z) = b (f' z) :=
    congrArg (fun k : X' ⟶ Y ↦ k z) square
  obtain ⟨g, hg⟩ := transitive (a x) (a y)
    ((comm x).trans ((congrArg b same_base).trans (comm y).symm))
  refine ⟨g, injective ?_⟩
  have equiv := congrArg (fun k : X' ⟶ X ↦ k x) (equivariant g)
  exact equiv.trans hg

/-- 概要：同変な同型の正方形で点のファイバーの推移性を移す（論文 補題 3.2）。
方針：二点を逆同型で戻し、基底同型の単射性と始域の同変性を使う。
規約：元の幾何射と移行先の指定作用を保持する。
使われ方：実際の引き戻しの指定作用への幾何的推移性の帰結。 -/
theorem schemeFiberTransitivity_of_iso {X Y X' Y' : Scheme.{u}} {G : Type u} [Group G]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (e : X ≅ X') (b : Y ≅ Y')
    (square : e.hom ≫ f' = f ≫ b.hom) (action : G →* Aut X) (action' : G →* Aut X')
    (equivariant : ∀ g, (action g).asIso.hom ≫ e.hom = e.hom ≫ (action' g).asIso.hom)
    (transitive : ∀ x y : X, f x = f y → ∃ g : G, (action g).asIso.hom x = y)
    (x y : X') (same_base : f' x = f' y) :
    ∃ g : G, (action' g).asIso.hom x = y := by
  have back (z : X') : e.hom (e.inv z) = z :=
    congrArg (fun k : X' ⟶ X' ↦ k z) e.inv_hom_id
  have comm (z : X') : b.hom (f (e.inv z)) = f' z := by
    have h := congrArg (fun k : X ⟶ Y' ↦ k (e.inv z)) square
    change f' (e.hom (e.inv z)) = b.hom (f (e.inv z)) at h
    exact h.symm.trans (congrArg f' (back z))
  have same_model : f (e.inv x) = f (e.inv y) :=
    b.hom.homeomorph.injective ((comm x).trans (same_base.trans (comm y).symm))
  obtain ⟨g, hg⟩ := transitive _ _ same_model
  refine ⟨g, ?_⟩
  have heq := congrArg (fun k : X ⟶ X' ↦ k (e.inv x)) (equivariant g)
  change e.hom ((action g).asIso.hom (e.inv x)) =
    (action' g).asIso.hom (e.hom (e.inv x)) at heq
  exact (congrArg (action' g).asIso.hom (back x)).symm.trans
    (heq.symm.trans ((congrArg e.hom hg).trans (back y)))

end SerrePositivity.KST.Descent
