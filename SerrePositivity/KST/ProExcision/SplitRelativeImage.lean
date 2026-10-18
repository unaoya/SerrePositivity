module
public import SerrePositivity.KST.ProExcision.RelativeModule

/-!
# 分裂相対項の零化と像上の作用

概要：相対写像の零化から絶対写像の基底への因子化と像上の作用の不変性を導く。
方針：余核の代表の零性を像への所属へ戻し、分裂射影と可換正方形で整理する。
規約：KST Proposition 4.14、SW92 Proposition 1.5 の加群部分。
使われ方：実アフィン比較の零化から整数行列の作用の自明性への移行。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {M N M' N' : ModuleCat.{u} ℤ}

/-- 概要：相対写像が零なら、分裂した標的の基底へ絶対写像が因子化する。
方針：各代表の像が標的の包含の像に入ることを商の零性から取り出す。
規約：SW92 Proposition 1.5、実加群の余核模型。
使われ方：絶対写像の像を基底の像へ制限する。 -/
lemma relativeModuleMap_factor_of_zero (f : M ⟶ N) (f' : M' ⟶ N')
    (a : M ⟶ M') (b : N ⟶ N') (h : f ≫ b = a ≫ f')
    (r' : N' ⟶ M') (hsplit : f' ≫ r' = 𝟙 M')
    (hz : relativeModuleMap f f' a b h = 0) : b = b ≫ r' ≫ f' := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have hq := congrArg (fun t ↦ t.hom (Submodule.Quotient.mk y)) hz
  change (Submodule.Quotient.mk (b.hom y) : N' ⧸ f'.hom.range) = 0 at hq
  obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
  have hs := congrArg (fun t ↦ t.hom x) hsplit
  change r'.hom (f'.hom x) = x at hs
  change b.hom y = f'.hom (r'.hom (b.hom y))
  rw [← hx, hs]

/-- 概要：相対零化と二つの射影の自然性から絶対写像は基底射と射影で表示される。
方針：像への因子化の式に射影の可換性を代入する。
規約：KST Proposition 4.14、SW92 Proposition 1.5。
使われ方：アフィン射影を固定する共役の作用の比較。 -/
lemma relativeModuleMap_factor_of_split_square (f : M ⟶ N) (f' : M' ⟶ N')
    (a : M ⟶ M') (b : N ⟶ N') (h : f ≫ b = a ≫ f')
    (r : N ⟶ M) (r' : N' ⟶ M') (hsplit : f' ≫ r' = 𝟙 M')
    (hp : b ≫ r' = r ≫ a) (hz : relativeModuleMap f f' a b h = 0) :
    b = r ≫ a ≫ f' := by
  rw [relativeModuleMap_factor_of_zero f f' a b h r' hsplit hz, ← Category.assoc, hp, Category.assoc]

/-- 概要：射影を固定する可換な二つの作用は相対零化した基底の像上で自明。
方針：絶対写像を基底に因子化して、始域側の作用の射影不変性を使う。
規約：KST Proposition 4.14、SW92 Proposition 1.5 の像上の主張。
使われ方：実アフィン比較から整数 elementary 行列の共役へ移す。 -/
lemma splitRelative_action_image (f : M ⟶ N) (f' : M' ⟶ N')
    (a : M ⟶ M') (b : N ⟶ N') (h : f ≫ b = a ≫ f')
    (r : N ⟶ M) (r' : N' ⟶ M') (hsplit : f' ≫ r' = 𝟙 M')
    (hp : b ≫ r' = r ≫ a) (hz : relativeModuleMap f f' a b h = 0)
    (α : N ⟶ N) (β : N' ⟶ N') (hc : α ≫ b = b ≫ β) (hr : α ≫ r = r) :
    a ≫ f' ≫ β = a ≫ f' := by
  have hb := relativeModuleMap_factor_of_split_square f f' a b h r r' hsplit hp hz
  have hβ : b ≫ β = b := by
    rw [← hc, hb, ← Category.assoc, ← Category.assoc, hr, Category.assoc]
  calc
    a ≫ f' ≫ β = (f ≫ b) ≫ β := by rw [h, Category.assoc]
    _ = f ≫ b := by rw [Category.assoc, hβ]
    _ = a ≫ f' := h

end SerrePositivity.KST.ProExcision
