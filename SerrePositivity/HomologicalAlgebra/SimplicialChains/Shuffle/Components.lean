module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.RawBilinear
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.BilinearDescent

/-!
# 一般の正規化 shuffle 成分

概要：Berger–Fresse §1.1.3 の shuffle を任意の二つの正規化鎖の成分間の射にする。
方針：自由双線形写像を Moore 正規化へ降ろし加群テンソルの普遍性で束ねる。
規約：ここでは次数成分を構成し、鎖写像の条件と AW 適合性は別途検証する。
使われ方：一般の shuffle が AW 余代数の射であることの成分表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：正規化鎖の shuffle 双線形成分（Berger–Fresse §1.1.3）。
方針：両入力を Moore 部分加群へ制限する。
規約：一般の小さい単体集合と任意の可換係数環を使う。
使われ方：テンソル成分と生成元公式を構成する。 -/
def bilinear (X Y : SSet.{0}) (p q : ℕ) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p →ₗ[A]
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X q →ₗ[A]
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q) :=
  _root_.SerrePositivity.SimplicialChains.Shuffle.normalizedBilinear ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X)
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Y) p q (_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y p q)

/-- 概要：正規化生成元での shuffle 双線形成分の公式（Berger–Fresse §1.1.3）。
方針：二変数の退化消滅による降下補題に自由生成元を代入する。
規約：入力単体の非退化性を仮定しない。
使われ方：微分・自然性・AW 適合性を単体の有限和へ帰着する。 -/
lemma bilinear_generators (X Y : SSet.{0}) (p q : ℕ)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p x)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y q y) = _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x y := by
  have hn := _root_.SerrePositivity.SimplicialChains.Shuffle.normalizedBilinear_normalization
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X) ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Y)
    p q (_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y p q)
    (fun k e i => by
      cases e
      simpa only [eqToHom_refl, Category.comp_id] using _root_.SerrePositivity.SimplicialChains.Shuffle.σ_rawBilinear_left A X Y k q i)
    (fun k e i => by
      cases e
      simpa only [eqToHom_refl, Category.comp_id] using _root_.SerrePositivity.SimplicialChains.Shuffle.σ_rawBilinear_right A X Y p k i)
    (ModuleCat.freeMk (ULift.up x)) (ModuleCat.freeMk (ULift.up y))
  exact hn.trans (_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear_freeMk A X Y p q x y)

/-- 概要：二つの正規化鎖から積の鎖への shuffle 成分（Berger–Fresse §1.1.3）。
方針：双線形成分を加群テンソルからの射へ線形化する。
規約：次数 p,q を p+q に送る。
使われ方：一般の shuffle 鎖写像と AW 適合性の構成。 -/
def component (X Y : SSet.{0}) (p q : ℕ) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p ⊗ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X q ⟶
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q) :=
  ModuleCat.ofHom (TensorProduct.lift (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p q))

/-- 概要：shuffle 成分の純テンソル上の評価（Berger–Fresse §1.1.3）。
方針：加群テンソルの普遍性の評価公式を使う。
規約：入力は任意の正規化鎖の元。
使われ方：成分の射の等式を双線形写像の等式へ移す。 -/
@[simp] lemma component_tmul (X Y : SSet.{0}) (p q : ℕ)
    (x : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p) (y : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X q) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y p q (x ⊗ₜ[A] y) = _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p q x y :=
  TensorProduct.lift.tmul _ _

/-- 概要：shuffle 成分の正規化生成元での公式（Berger–Fresse §1.1.3）。
方針：純テンソルの評価と降下後の生成元公式を使う。
規約：退化した入力にも同じ有限和公式が成り立つ。
使われ方：AW 対角との可換性を生成元で検査する。 -/
@[simp] lemma component_generators (X Y : SSet.{0}) (p q : ℕ)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y p q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p x ⊗ₜ[A]
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y q y) = _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x y := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.component_tmul, _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear_generators]

/-- 概要：双線形写像は正規化生成元の対上の値で決まる（Berger–Fresse §1.1.3）。
方針：二つの変数に生成元による射の外延性を適用する。
規約：終域は任意の係数加群。
使われ方：shuffle 成分の法則を生成元で証明する。 -/
lemma bilinear_hom_ext (X Y : SSet.{0}) (p q : ℕ) {Z : ModuleCat.{u} A}
    {b c : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p →ₗ[A]
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X q →ₗ[A] Z}
    (h : ∀ (x : X _⦋p⦌) (y : Y _⦋q⦌),
      b (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p x) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y q y) =
        c (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p x) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y q y)) : b = c := by
  have he : ModuleCat.ofHom b = ModuleCat.ofHom c := by
    apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A X p
    intro x
    have hy : ModuleCat.ofHom (b (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p x)) =
        ModuleCat.ofHom (c (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p x)) := by
      apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A Y q
      exact h x
    exact congrArg ModuleCat.Hom.hom hy
  exact congrArg ModuleCat.Hom.hom he

/-- 概要：正規化鎖のテンソルからの射は生成元の純テンソルで決まる（Berger–Fresse §1.1.3）。
方針：加群テンソルの普遍性で双線形写像に戻して二変数の外延性を使う。
規約：入力単体集合に有限性を仮定しない。
使われ方：shuffle の鎖写像条件と AW 適合性の成分を検査する。 -/
lemma tensor_generator_hom_ext (X Y : SSet.{0}) (p q : ℕ) {Z : ModuleCat.{u} A}
    {f g : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p ⊗ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X q ⟶ Z}
    (h : ∀ (x : X _⦋p⦌) (y : Y _⦋q⦌),
      f (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p x ⊗ₜ[A] _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y q y) =
        g (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p x ⊗ₜ[A] _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y q y)) :
    f = g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear_hom_ext A X Y p q
  exact h

/-- 概要：一般の shuffle 成分は単体集合の射の対に自然（Berger–Fresse §1.1.3）。
方針：正規化生成元の純テンソルで shuffle 和の自然性を使う。
規約：二つの入力の射は独立に変わる。
使われ方：shuffle 鎖写像の自然性と単体的合成との接続。 -/
lemma component_natural {X X' Y Y' : SSet.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ) :
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f).f p ⊗ₘ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A g).f q) ≫
        _root_.SerrePositivity.SimplicialChains.Shuffle.component A X' Y' p q =
      _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y p q ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A (f ⊗ₘ g)).f (p + q) := by
  apply _root_.SerrePositivity.SimplicialChains.Shuffle.tensor_generator_hom_ext A X Y p q
  intro x y
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap_generator, _root_.SerrePositivity.SimplicialChains.Shuffle.component_generators]
  exact (_root_.SerrePositivity.SimplicialChains.Shuffle.value_natural A f g p q x y).symm

end SerrePositivity.SimplicialChains.Shuffle
