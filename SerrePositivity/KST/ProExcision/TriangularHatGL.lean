module
public import SerrePositivity.KST.ProExcision.NonUnitalHatGL

/-!
# 三角ブロック群から一般線形モノイドへの実比較

概要：Lemma 4.16 の実三角ブロック群を非単位環の ĜL へ自然に写す。
方針：実単位の像は π₀ でも単位となり、差の係数イデアル条件は整数射影で消える。
規約：KST Claim 4.15。ĜL の一般の元に次数ごとの逆元を要求しない。
使われ方：実帰納ホモトピーの値域から一般線形モノイドへの因子化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：整数単位化の三角ブロック群の整数成分は恒等行列。
方針：1 からの差の各成分が核イデアルに入ることを使う。
規約：KST Claim 4.15 の三角群の実包含。
使われ方：非単位環の ĜL の整数核条件。 -/
lemma triangularBlockGroup_fst (J : Type u) [NonUnitalRing J] (n m : ℕ)
    (g : triangularBlockGroup n m (integerUnitizationIdeal J)) :
    (Unitization.fstHom ℤ J).mapMatrix (g.val :
      Matrix (Fin (n + m)) (Fin (n + m)) (Unitization ℤ J)) = 1 := by
  have hz := g.property.1.2
  have he : (Unitization.fstHom ℤ J).mapMatrix ((g.val :
      Matrix (Fin (n + m)) (Fin (n + m)) (Unitization ℤ J)) - 1) = 0 := by
    apply Matrix.ext
    intro i j
    exact (mem_integerUnitizationIdeal J _).mp (hz i j)
  rw [map_sub, map_one] at he
  exact sub_eq_zero.mp he

/-- 概要：実三角ブロック群から非単位環の ĜL の各次数への準同型。
方針：実単位の π₀ への像の単位性と整数成分の恒等性を証明する。
規約：KST Claim 4.15、非可換な係数を許す。
使われ方：単体的な比較射の各次数。 -/
def NonUnitalSimplicialRing.triangularHatGLHom (I : NonUnitalSimplicialRing.{u})
    (n m q : ℕ) :
    triangularBlockGroup n m (integerUnitizationIdeal (I.obj (op ⦋q⦌))) →*
      I.hatGLSubmonoid (n + m) q where
  toFun g := ⟨g.val.val, by
    constructor
    · change IsUnit (Comparison.matrixToComponents I.standardIdeal.ambient (n + m) q g.val.val)
      exact g.val.isUnit.map _
    · exact triangularBlockGroup_fst _ n m g⟩
  map_one' := rfl
  map_mul' g h := rfl

/-- 概要：三角ブロック群から非単位環の ĜL への実単体射。
方針：行列の係数写像と包含の可換性を各成分で確かめる。
規約：KST Claim 4.15。単体的群から単体的モノイドへの射。
使われ方：相対 bar 比較の値域への後合成。 -/
def NonUnitalSimplicialRing.triangularHatGLMap (I : NonUnitalSimplicialRing.{u})
    (n m : ℕ) :
    I.standardIdeal.triangularGroup n m ⋙ forget₂ GrpCat MonCat ⟶ I.hatGL (n + m) where
  app k := MonCat.ofHom (I.triangularHatGLHom n m k.unop.len)
  naturality {k l} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    rfl

/-- 概要：三角群の比較射は各次数で単射。
方針：部分群・単位の外延性を行列の値の等式に適用する。
規約：KST Claim 4.15 の実包含。
使われ方：実行列模型の同一視。 -/
lemma NonUnitalSimplicialRing.triangularHatGLHom_injective
    (I : NonUnitalSimplicialRing.{u}) (n m q : ℕ) :
    Function.Injective (I.triangularHatGLHom n m q) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val he

end SerrePositivity.KST.ProExcision
