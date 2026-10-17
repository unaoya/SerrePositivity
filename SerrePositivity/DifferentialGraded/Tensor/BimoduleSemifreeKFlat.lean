module
public import SerrePositivity.DifferentialGraded.Bimodule.RestrictedFree
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleRestrictionKFlat
public import SerrePositivity.DifferentialGraded.Tensor.ObjectwiseKFlat

/-! # 相手側local HomのK-flat性から得るsemifree bimodule解像度の右相対K-flat性

## 概要
相手側local HomのK-flat性から得るsemifree bimodule解像度の右相対K-flat性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleResolution.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma restrictedFree_relativeKFlat (hC : localHomKFlat A C) (b₀ : B) (c₀ c : C)
    (K : Complex A) (hK : complexKFlat A K) :
    moduleRelativeKFlat A B (ForgetEnrichment.to (Complex A)
      ((tensorRightRestriction A B C c).obj
        ((freeAt (A := A) (D := (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
          (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))).obj K))) :=
  moduleRelativeKFlat_of_iso A B (restrictedFreeIso A B C b₀ c₀ c K)
    (freeAt_relativeKFlat A B b₀ (K ⊗ (c₀ ⟶[Complex A] c))
      (complexKFlat_tensor A hK (hC c₀ c)))

lemma restrictedSphere_relativeKFlat (hC : localHomKFlat A C) (c : C)
    (x : (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (n : ℤ) :
    moduleRelativeKFlat A B (ForgetEnrichment.to (Complex A)
      ((tensorRightRestriction A B C c).obj (freeSphere A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ x n))) :=
  restrictedFree_relativeKFlat A B C hC x.unop.1.unop x.unop.2 c
    (complexSphere A n) (complexSphere_kFlat A n)

/-- 相手側Cのlocal Hom条件だけを使う。Bのlocal Hom条件は不要。 -/
lemma BimoduleSemifreeResolution.rightRelativeKFlat
    (hC : localHomKFlat A C) {M : BimoduleCategory A B C}
    (P : BimoduleSemifreeResolution A B C M) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P.obj) :=
  P.rightRelativeKFlat_of_cells A B C (restrictedSphere_relativeKFlat A B C hC)

theorem exists_rightRelativeKFlat_bimodule_resolution (hC : localHomKFlat A C)
    (M : BimoduleCategory A B C) :
    ∃ (P : BimoduleCategory A B C) (q : P ⟶ M),
      Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P) ∧
        BimoduleCategory.quasiIso A B C q := by
  let P := bimoduleCanonicalSemifreeResolution A B C M
  exact ⟨P.obj, P.π, P.rightRelativeKFlat A B C hC, P.quasiIso⟩

end SerrePositivity.DifferentialGraded
