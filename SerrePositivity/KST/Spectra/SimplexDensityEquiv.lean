module

public import SerrePositivity.KST.Spectra.SimplexDensityFamilies

/-!
概要：標準単体に沿う整合的な族とパラメーター付き単体集合の射との両逆。
方針：単体を引き戻すことで族を展開し、恒等単体で評価して復元する。
規約：単体集合の射の通常の同値でありホモトピー類を取らない。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。通常の Tot の密度による比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet Opposite

namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S A Y : SSet.{u}}

/-- 概要：単体集合の射を全ての標準単体上の整合する族へ展開する。
方針：標準単体の単体に対応する射で重みの単体を引き戻す。
規約：パラメーターはそのまま保つ。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。密度比較の逆の公式。 -/
def expand (t : S ⊗ A ⟶ Y) : Family S A Y where
  app n :=
    { app k := ↾fun x ↦ t.app k
        (S.map (SSet.stdSimplex.objEquiv.{u} x.2.1).op x.1, x.2.2)
      naturality k l f := by
        ext x
        have h := congr($(t.naturality f)
          (S.map (SSet.stdSimplex.objEquiv.{u} x.2.1).op x.1, x.2.2))
        change t.app l
            (S.map (SSet.stdSimplex.objEquiv.{u}
              ((SSet.stdSimplex.obj n).map f x.2.1)).op x.1, A.map f x.2.2) =
          Y.map f (t.app k
            (S.map (SSet.stdSimplex.objEquiv.{u} x.2.1).op x.1, x.2.2))
        change t.app l
            (S.map f (S.map (SSet.stdSimplex.objEquiv.{u} x.2.1).op x.1), A.map f x.2.2) =
          Y.map f (t.app k
            (S.map (SSet.stdSimplex.objEquiv.{u} x.2.1).op x.1, x.2.2)) at h
        simpa only [SSet.stdSimplex.map_apply, Equiv.apply_symm_apply, op_comp,
          CategoryTheory.Functor.map_comp, types_comp_apply, Quiver.Hom.op_unop] using h }
  condition f k x α a := by
    change t.app k (S.map (SSet.stdSimplex.objEquiv.{u} α).op (S.map f.op x), a) =
      t.app k (S.map (SSet.stdSimplex.objEquiv.{u} ((SSet.stdSimplex.map f).app k α)).op x, a)
    rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
    rfl

@[ext]
lemma Family.ext {s t : Family S A Y} (h : ∀ n, s.app n = t.app n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

/-- 概要：射の展開を恒等単体で評価すると元の射に戻る。
方針：恒等射による単体の制限が恒等であることを使う。
規約：射の厳密な等式。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。密度比較の一方の逆。 -/
lemma diagonal_expand (t : S ⊗ A ⟶ Y) : diagonal S A Y (expand t) = t := by
  ext k x
  change t.app k (S.map (SSet.stdSimplex.objEquiv.{u}
    (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 k.unop))).op x.1, x.2) = t.app k x
  simp only [Equiv.apply_symm_apply, op_id, CategoryTheory.Functor.map_id,
    types_id_apply, Prod.eta]

/-- 概要：整合する族の対角評価を展開すると元の族を得る。
方針：整合条件を標準単体の単体に対応する射と恒等単体に適用する。
規約：各次数の射の厳密な等式。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。密度比較の他方の逆。 -/
lemma expand_diagonal (s : Family S A Y) : expand (diagonal S A Y s) = s := by
  apply Family.ext
  intro n
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  change (s.app k.unop).app k
      (S.map (SSet.stdSimplex.objEquiv.{u} x.2.1).op x.1,
        (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 k.unop), x.2.2)) =
    (s.app n).app k x
  simpa only [← SSet.stdSimplex.objEquiv_symm_comp, Category.id_comp,
    Equiv.symm_apply_apply, Prod.eta] using
    s.condition (SSet.stdSimplex.objEquiv.{u} x.2.1) k x.1
      (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 k.unop)) x.2.2

/-- 概要：パラメーター付きの射と標準単体上の整合する族との同値。
方針：展開と対角評価の両逆を束ねる。
規約：Kan 性を要求しない集合の同値。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。Tot の密度比較。 -/
def familyEquiv : (S ⊗ A ⟶ Y) ≃ Family S A Y where
  toFun := expand
  invFun := diagonal S A Y
  left_inv := diagonal_expand
  right_inv := expand_diagonal

end

end SerrePositivity.KST.Spectra.SimplexDensity
