module

public import SerrePositivity.KST.LocalizingInvariants.DGBimodulePostnikov
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：集中双加群間の実 cochain 射の作用保存は、底の Postnikov 切断上で判定できる。
方針：元の左右作用の回収式と tensor 全射性で同じ二つの等式を比較する。
規約：作用保存を追加入力して逆を主張しない。使われ方：共通底の τ₀ 上の係数逆判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R)) [A.X.IsStrictlyLE 0]
  (M N : Bimod A A) (k : ℤ) [M.X.IsStrictlyGE k] [M.X.IsStrictlyLE k]
  [N.X.IsStrictlyGE k] [N.X.IsStrictlyLE k] (n : ℤ) (hn : 0 ≤ n)

lemma postnikovBimodule_left_hom_iff (u : M.X ⟶ N.X) :
    (postnikovBimodule R A M k n hn).actLeft ≫ u =
      ((postnikov R A n).X ◁ u) ≫ (postnikovBimodule R A N k n hn).actLeft ↔
    M.actLeft ≫ u = (A.X ◁ u) ≫ N.actLeft := by
  let q := postnikovQuotient R A n
  have : Epi q.hom := TruncationDesc.projection_epi A.X (-n)
  have : Epi (q.hom ▷ M.X) := by
    rw [← tensorHom_id]
    exact TruncationDesc.tensor_epi _ _
  have h₁ : (q.hom ▷ M.X) ≫ ((postnikovBimodule R A M k n hn).actLeft ≫ u) =
      M.actLeft ≫ u := (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ u) (postnikovBimodule_left_projection R A M k n hn))
  have he : (q.hom ▷ M.X) ≫ ((postnikov R A n).X ◁ u) =
      (A.X ◁ u) ≫ (q.hom ▷ N.X) := by
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  have h₂ : (q.hom ▷ M.X) ≫ (((postnikov R A n).X ◁ u) ≫
      (postnikovBimodule R A N k n hn).actLeft) = (A.X ◁ u) ≫ N.actLeft :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ (postnikovBimodule R A N k n hn).actLeft) he).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t => (A.X ◁ u) ≫ t)
            (postnikovBimodule_left_projection R A N k n hn))))
  constructor
  · intro h
    exact h₁.symm.trans ((congrArg (fun t => (q.hom ▷ M.X) ≫ t) h).trans h₂)
  · intro h
    apply (cancel_epi (q.hom ▷ M.X)).1
    exact h₁.trans (h.trans h₂.symm)

lemma postnikovBimodule_right_hom_iff (u : M.X ⟶ N.X) :
    (postnikovBimodule R A M k n hn).actRight ≫ u =
      (u ▷ (postnikov R A n).X) ≫ (postnikovBimodule R A N k n hn).actRight ↔
    M.actRight ≫ u = (u ▷ A.X) ≫ N.actRight := by
  let q := postnikovQuotient R A n
  have : Epi q.hom := TruncationDesc.projection_epi A.X (-n)
  have : Epi (M.X ◁ q.hom) := by
    rw [← id_tensorHom]
    exact TruncationDesc.tensor_epi _ _
  have h₁ : (M.X ◁ q.hom) ≫ ((postnikovBimodule R A M k n hn).actRight ≫ u) =
      M.actRight ≫ u := (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ u) (postnikovBimodule_right_projection R A M k n hn))
  have he : (M.X ◁ q.hom) ≫ (u ▷ (postnikov R A n).X) =
      (u ▷ A.X) ≫ (N.X ◁ q.hom) := by
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  have h₂ : (M.X ◁ q.hom) ≫ ((u ▷ (postnikov R A n).X) ≫
      (postnikovBimodule R A N k n hn).actRight) = (u ▷ A.X) ≫ N.actRight :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ (postnikovBimodule R A N k n hn).actRight) he).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t => (u ▷ A.X) ≫ t)
            (postnikovBimodule_right_projection R A N k n hn))))
  constructor
  · intro h
    exact h₁.symm.trans ((congrArg (fun t => (M.X ◁ q.hom) ≫ t) h).trans h₂)
  · intro h
    apply (cancel_epi (M.X ◁ q.hom)).1
    exact h₁.trans (h.trans h₂.symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
