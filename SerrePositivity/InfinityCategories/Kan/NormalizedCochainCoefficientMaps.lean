module

public import SerrePositivity.InfinityCategories.Kan.NormalizedCochainComplex

/-!
概要：通常の正規化 cochain の係数射と交代微分の可換性。
方針：正規化鎖群の Hom の後合成を生成子の関数表示へ移す。
規約：幾何的微分との比較とは独立した代数的な自然性。
使われ方：Goerss–Jardine III §2、VIII §1。比較先の通常の cochain の係数射。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.NormalizedSimplicialCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{v} C]
  (K : SSet.{v}) (R : C) {M N : C} (f : M ⟶ N)

/-- 概要：係数の Hom の後合成を非退化単体ごとに施す加法群の射。
方針：各座標で前加法圏の後合成を使う。
規約：単体集合と始域の係数 R は固定。
使われ方：Goerss–Jardine VIII §1。通常の cochain の係数自然性。 -/
def post (n : ℕ) : (K.nonDegenerate n → (R ⟶ M)) →+
    (K.nonDegenerate n → (R ⟶ N)) where
  toFun a s := a s ≫ f
  map_zero' := by funext s; exact zero_comp
  map_add' a b := by funext s; exact Preadditive.add_comp _ _ _ _ _ _

lemma extend_post (n : ℕ) (a : K.nonDegenerate n → (R ⟶ M)) :
    extend K R N n (post K R f n a) = extend K R M n a ≫ f := by
  apply K.normalizedChainComplex_hom_ext
  intro s hs
  rw [inclusion_extend K R N n _ ⟨s, hs⟩, ← Category.assoc,
    inclusion_extend K R M n a ⟨s, hs⟩]
  rfl

/-- 概要：正規化 cochain 微分は係数の後合成と可換。
方針：生成子の延長と後合成の可換式を微分の定義へ適用する。
規約：交代面の和と同じ微分そのものについて証明する。
使われ方：Goerss–Jardine III §2、VIII §1。通常の複体の自然性。 -/
lemma differential_natural (n : ℕ) (a : K.nonDegenerate n → (R ⟶ M)) :
    differential K R N n (post K R f n a) = post K R f (n + 1) (differential K R M n a) := by
  funext s
  change K.ιNormalizedChainComplex s.val ≫
      ((K.normalizedChainComplex R).d (n + 1) n ≫ extend K R N n (post K R f n a)) =
    (K.ιNormalizedChainComplex s.val ≫
      ((K.normalizedChainComplex R).d (n + 1) n ≫ extend K R M n a)) ≫ f
  rw [extend_post]
  simp only [Category.assoc]

/-- 概要：係数射を通常の正規化 cochain 複体の射へ束ねる。
方針：各次数の座標ごとの後合成と微分の自然性を使う。
規約：値は加法群の圏の cochain 複体。
使われ方：Goerss–Jardine VIII §1。係数の群準同型による cochain の比較。 -/
def complexMap : complex K R M ⟶ complex K R N :=
  CochainComplex.ofHom
    (fun n ↦ AddCommGrpCat.ofHom (post K R f n))
    (fun n ↦ by
      simp only [complex, CochainComplex.of_d]
      apply ConcreteCategory.hom_ext
      intro a
      exact differential_natural K R f n a)

end

end SerrePositivity.KST.Spectra.NormalizedSimplicialCochains
