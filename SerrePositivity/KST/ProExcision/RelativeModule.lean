module

public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 相対ホモロジーの余核における誘導射

概要：分裂包含の余核として現れる相対ホモロジーの代数部分を扱う。
方針：加群の像による通常商と、その商へ降りる線形写像を使う。
規約：ホモロジー関手そのものを定義しない。所有レーンの出力へ適用する。
使われ方：KST Appendix A、Lemma A.4 の相対項の零化。
-/

universe u r
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {R : Type r} [Ring R]

/-- 概要：加群の写像の余核の具体的な商模型。
方針：写像の像による商を取る。
規約：写像の単射性はこの定義には不要。
使われ方：KST App. A の分裂包含から得る相対ホモロジー。 -/
def relativeModule {M N : ModuleCat.{u} R} (f : M ⟶ N) : ModuleCat.{u} R :=
  ModuleCat.of R (N ⧸ f.hom.range)

/-- 概要：可換正方形が余核の通常商へ誘導する射。
方針：右側の線形写像を二つの像による商へ降ろす。
規約：可換性は射の等式として指定する。
使われ方：KST Lemma A.4 の相対ホモロジーの誘導射。 -/
def relativeModuleMap {M N M' N' : ModuleCat.{u} R}
    (f : M ⟶ N) (f' : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : f ≫ b = a ≫ f') : relativeModule f ⟶ relativeModule f' :=
  ModuleCat.ofHom (Submodule.mapQ _ _ b.hom (by
    rintro _ ⟨x, rfl⟩
    refine ⟨a.hom x, ?_⟩
    exact (congrArg (fun g ↦ g.hom x) h).symm))

/-- 概要：基準部分加群へ因子化する写像は相対項で零となる。
方針：商の代表元の像が標的の包含の像に入ることを使う。
規約：分裂性は不要。使われ方：KST Lemma A.4 の定数写像に由来する部分の零化。 -/
theorem relativeModuleMap_zero_of_factor {M N M' N' : ModuleCat.{u} R}
    (f : M ⟶ N) (f' : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : f ≫ b = a ≫ f') (t : N ⟶ M') (ht : b = t ≫ f') :
    relativeModuleMap f f' a b h = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨t.hom x, ?_⟩
    exact (congrArg (fun g ↦ g.hom x) ht).symm

/-- 概要：標的への二つの写像が等しければ、相対項への誘導射も等しい。
方針：商の代表元で右側の写像の等式を使う。
規約：左側の写像は異なってもよい。
使われ方：KST Lemma A.4 のホモトピーによる絶対写像の比較から相対写像への移行。 -/
theorem relativeModuleMap_eq_of_right_eq {M N M' N' : ModuleCat.{u} R}
    (f : M ⟶ N) (f' : M' ⟶ N') (a a' : M ⟶ M') (b b' : N ⟶ N')
    (h : f ≫ b = a ≫ f') (h' : f ≫ b' = a' ≫ f') (hb : b = b') :
    relativeModuleMap f f' a b h = relativeModuleMap f f' a' b' h' := by
  subst b'
  rfl

/-- 概要：相対項の誘導射は可換正方形の合成を保つ。
方針：通常商の代表元で線形写像の合成を計算する。
規約：三つの包含を明示する。使われ方：KST App. A の相対ホモロジーの自然性。 -/
theorem relativeModuleMap_comp {M N M' N' M'' N'' : ModuleCat.{u} R}
    (f : M ⟶ N) (f' : M' ⟶ N') (f'' : M'' ⟶ N'')
    (a : M ⟶ M') (b : N ⟶ N') (h : f ≫ b = a ≫ f')
    (a' : M' ⟶ M'') (b' : N' ⟶ N'') (h' : f' ≫ b' = a' ≫ f'') :
    relativeModuleMap f f' a b h ≫ relativeModuleMap f' f'' a' b' h' =
      relativeModuleMap f f'' (a ≫ a') (b ≫ b') (by
        rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc]) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

end SerrePositivity.KST.ProExcision
