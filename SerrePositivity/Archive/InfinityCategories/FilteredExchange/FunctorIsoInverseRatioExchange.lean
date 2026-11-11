module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
/-!
概要：元の中間同型に沿って、同じ比の逆を交換する。
方針：実三端点と指定値を保持して前後合成の交換則を適用する。
規約：元の二同型と表示変更の証拠を保持する。
使われ方：Ncomp の native 中間像と最後辺値の比の貼り合わせ。
-/

@[expose] public section
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
noncomputable section
universe u
/-- 概要：元の native 像と比の逆は中間比較の逆側で交換できる。
方針：三端点の表示変更を除いて同じ交換正方形を使う。
規約：元の指定値を保持。使われ方：raw 二辺値の中間での貼り合わせ。 -/
lemma functorIso_inverse_ratio_exchange_heq {X A Z : SSet.{u}}
    [Quasicategory A] [Quasicategory Z] {f₀ f₁ : X ⟶ A} {g₀ g₁ : A ⟶ Z}
    (e : FunctorIso f₀ f₁) (R : FunctorIso g₀ g₁)
    {h₀ h₁ k₀ : X ⟶ Z} (N : FunctorIso h₀ h₁) (S : FunctorIso k₀ h₁)
    (h₀e : h₀ = f₀ ≫ g₁) (h₁e : h₁ = f₁ ≫ g₁) (k₀e : k₀ = f₁ ≫ g₀)
    (hN : HEq N (e.postcomp g₁)) (hS : HEq S (R.precomp f₁)) :
    HEq (N ≪≫ S.symm) ((R.precomp f₀).symm ≪≫ e.postcomp g₀) := by
  subst h₀ h₁ k₀
  cases eq_of_heq hN
  cases eq_of_heq hS
  have h := functorIso_whisker_exchange e R.symm
  rw [functorIso_precomp_symm, functorIso_precomp_symm] at h
  exact heq_of_eq h
/-- 概要：同じ native 像の値は元の中間比較の同じ値射による像。
方針：実両端を揃え、後合成の結合則で元の指定値を保つ。
規約：元の三射と比較を保持。使われ方：比の逆との交換への代入。 -/
lemma functorIso_postcomp_heq_native_value {X A B Z : SSet.{u}} {f g : X ⟶ A}
    (e : FunctorIso f g) (n : A ⟶ B) {h₀ h₁ : X ⟶ B} (N : FunctorIso h₀ h₁)
    (hf : f ≫ n = h₀) (hg : g ≫ n = h₁) (hN : HEq N (e.postcomp n)) (V : B ⟶ Z)
    {k : A ⟶ Z} (hk : n ≫ V = k) :
    HEq (N.postcomp V) (e.postcomp k) := by
  cases hk
  have h := functorIso_postcomp_heq_of_heq (e.postcomp n) N hf hg hN V
  exact h.trans (heq_of_eq (functorIso_postcomp_postcomp e n V))
/-- 概要：同じ中間交換に元の前後因子を続けても指定値を保持する。
方針：元の二端点を揃えて同じ交換正方形を合成する。
規約：元の四因子を保持。使われ方：raw 二辺値全体の中間での貼り合わせ。 -/
lemma functorIso_inverse_ratio_exchange_paste_heq {X A Z : SSet.{u}}
    [Quasicategory A] [Quasicategory Z] {f₀ f₁ : X ⟶ A} {g₀ g₁ : A ⟶ Z}
    (e : FunctorIso f₀ f₁) (R : FunctorIso g₀ g₁)
    {h₀ h₁ w z : X ⟶ Z} (L : FunctorIso w h₀) (N : FunctorIso h₀ h₁)
    (S : FunctorIso (f₁ ≫ g₀) h₁) (F : FunctorIso (f₁ ≫ g₀) z)
    (h₀e : h₀ = f₀ ≫ g₁) (h₁e : h₁ = f₁ ≫ g₁)
    (hN : HEq N (e.postcomp g₁)) (hS : HEq S (R.precomp f₁)) :
    HEq (L ≪≫ N ≪≫ S.symm ≪≫ F)
      (functorIsoOfEq L rfl h₀e ≪≫ (R.precomp f₀).symm ≪≫ (e.postcomp g₀ ≪≫ F)) := by
  subst h₀ h₁
  cases eq_of_heq hN
  cases eq_of_heq hS
  have h := functorIso_whisker_exchange e R.symm
  rw [functorIso_precomp_symm, functorIso_precomp_symm] at h
  have hh : L ≪≫ e.postcomp g₁ ≪≫ (R.precomp f₁).symm ≪≫ F =
      L ≪≫ (R.precomp f₀).symm ≪≫ (e.postcomp g₀ ≪≫ F) := by
    simpa only [Iso.trans_assoc] using congrArg (fun k => L ≪≫ k ≪≫ F) h
  convert heq_of_eq hh using 1
  rfl
end
end SerrePositivity.InfinityCategories.F2
