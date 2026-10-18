module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
概要：離散的な単体の族と標準単体を使うパラメーター付き Yoneda の具体式。
方針：標準単体の恒等単体で評価して族を貼り合わせ、逆に単体の制限で族を作る。
規約：全て通常の単体集合の射であり Kan 条件は不要。
使われ方：Goerss–Jardine VIII §1 の Tot の式 (1.1)。EG の end との比較の基礎。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet Opposite

namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (S A Y : SSet.{u})

/-- 概要：各次数の単体に沿うパラメーター付きの族と次数間の整合条件。
方針：単体の引き戻しと標準単体の後合成が同じ値を与えることを要求する。
規約：単体の離散化は定数単体集合の関手で表す。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。Tot の二重の評価を展開する。 -/
structure Family where
  app (n : SimplexCategory) :
    (Functor.const (SimplexCategoryᵒᵖ)).obj (S.obj (op n)) ⊗
      (SSet.stdSimplex.obj n ⊗ A) ⟶ Y
  condition {n m : SimplexCategory} (f : n ⟶ m)
      (k : SimplexCategoryᵒᵖ) (x : S.obj (op m))
      (α : (SSet.stdSimplex.obj n).obj k) (a : A.obj k) :
    (app n).app k (S.map f.op x, (α, a)) =
      (app m).app k (x, ((SSet.stdSimplex.map f).app k α, a))

/-- 概要：整合する族を恒等単体で評価して単体集合の射を得る。
方針：族の自然性と次数の整合式を恒等単体に適用する。
規約：パラメーターは直積の右因子。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。Tot から単体集合の end への順射。 -/
def diagonal (s : Family S A Y) : S ⊗ A ⟶ Y where
  app k := ↾fun x ↦ (s.app k.unop).app k
    (x.1, (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 k.unop), x.2))
  naturality k l f := by
    ext x
    have h := congr($((s.app k.unop).naturality f)
      (x.1, (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 k.unop), x.2)))
    change (s.app k.unop).app l
        (x.1, ((SSet.stdSimplex.obj k.unop).map f
          (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 k.unop)), A.map f x.2)) =
      Y.map f ((s.app k.unop).app k
        (x.1, (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 k.unop), x.2))) at h
    change (s.app l.unop).app l
        (S.map f x.1, (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 l.unop), A.map f x.2)) =
      Y.map f ((s.app k.unop).app k
        (x.1, (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 k.unop), x.2)))
    rw [← h]
    simpa only [SSet.stdSimplex.map_apply, ← SSet.stdSimplex.objEquiv_symm_comp,
      Equiv.apply_symm_apply, Category.comp_id, Category.id_comp, Quiver.Hom.op_unop] using
      s.condition f.unop l x.1 (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 l.unop))
        (A.map f x.2)

end

end SerrePositivity.KST.Spectra.SimplexDensity
