module

public import SerrePositivity.KST.Spectra.ContravariantChainHom
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
概要：全単体上の通常の cochain の余単体図式と交代微分。
方針：単体集合の作用への前合成で余単体図式を作り、整数鎖の生成子の Hom と比較する。
規約：係数は前加法圏の Hom 群。退化単体でも値を零に限定しない。
使われ方：Goerss–Jardine III §2、VIII §2。非正規化群 cochain との比較。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SimplicialHomCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{v} C]
  (K : SSet.{v}) (R M : C)

def extend (n : ℕ) (a : K _⦋n⦌ → (R ⟶ M)) : (K.chainComplex R).X n ⟶ M :=
  (K.isColimitChainComplexXCofan R n).desc (Cofan.mk M a)

@[reassoc]
lemma inclusion_extend (n : ℕ) (a : K _⦋n⦌ → (R ⟶ M)) (s : K _⦋n⦌) :
    K.ιChainComplex s ≫ extend K R M n a = a s :=
  (K.isColimitChainComplexXCofan R n).fac (Cofan.mk M a) (Discrete.mk s)

/-- 概要：全単体の鎖群からの Hom は全単体上の係数の関数群。
方針：余積の生成子への制限と延長を逆にする。
規約：係数群は任意の前加法圏の Hom。
使われ方：Goerss–Jardine III §2。通常の cochain の全単体の表示。 -/
def coefficientEquiv (n : ℕ) : ((K.chainComplex R).X n ⟶ M) ≃+ (K _⦋n⦌ → (R ⟶ M)) where
  toFun f s := K.ιChainComplex s ≫ f
  invFun := extend K R M n
  left_inv f := by
    apply K.chainComplex_hom_ext
    intro s
    exact inclusion_extend K R M n _ s
  right_inv a := by
    funext s
    exact inclusion_extend K R M n a s
  map_add' f g := by
    funext s
    exact Preadditive.comp_add _ _ _ _ f g

/-- 概要：単体集合の全単体上の係数の関数群の余単体図式。
方針：単体の顔と退化の作用への前合成を取る。
規約：係数の値の群は固定。
使われ方：Goerss–Jardine VIII §2。BG の全単体からの群 cochain の図式。 -/
def diagram : CosimplicialObject AddCommGrpCat.{v} where
  obj n := AddCommGrpCat.of (K.obj (op n) → (R ⟶ M))
  map θ := AddCommGrpCat.ofHom {
    toFun a s := a (K.map θ.op s)
    map_zero' := rfl
    map_add' _ _ := rfl }
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro a
    funext s
    change a (K.map (𝟙 (op n)) s) = a s
    rw [K.map_id]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    funext s
    change a (K.map (g.op ≫ f.op) s) = a (K.map f.op (K.map g.op s))
    rw [K.map_comp]
    rfl

/-- 概要：全単体の余単体 cochain の交代余面複体。
方針：Mathlib の交代余面複体関手を通常の関数の図式へ適用する。
規約：正規化の条件は課していない。
使われ方：Goerss–Jardine III §2、VIII §2。群の非斉次 cochain の比較先。 -/
def complex : CochainComplex AddCommGrpCat.{v} ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (diagram K R M)

omit [HasCoproducts.{v} C] in
lemma differential_apply (n : ℕ) (a : K _⦋n⦌ → (R ⟶ M)) (s : K _⦋n + 1⦌) :
    (complex K R M).d n (n + 1) a s =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a (K.δ i s) := by
  dsimp only [complex, AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  change (AddCommGrpCat.homAddEquiv
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (diagram K R M).δ i)) a s = _
  simp only [map_sum, map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (fun t : K _⦋n + 1⦌ ↦ a (K.δ i t))) s = _
  simp only [Finset.sum_apply, Pi.smul_apply]

end

end SerrePositivity.KST.Spectra.SimplicialHomCochains
