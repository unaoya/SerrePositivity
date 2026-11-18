module

public import SerrePositivity.EInfinity.BarrattEccles.OperadAugmentation
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.UnitRigidity

/-!
# H⁰ の演算に使う E(n) の係数とホモトピー

概要：BF §1 の各 arity の可縮性から、augmentation が同じ係数射のホモトピーを得る。
方針：構成済みの鎖ホモトピー同値の逆射と三角形を使う。
規約：対称群同変な切断や Com → E の射は主張しない。
使われ方：H⁰ の単位・結合性・可換性の証明。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：H⁰ の n 入力演算を指定する E(n) の係数射（BF §1）。
方針：実際の収縮の逆向きの射を取る。
規約：対称群同変性は要求しない。全 arity。
使われ方：H⁰ の単位と二項積の係数。 -/
def aritySection (n : ℕ) : 𝟙_ (Complex A) ⟶ (operad A).arity n :=
  (complexContraction A n).inv

/-- 概要：選んだ係数射の augmentation は恒等射（BF §1）。
方針：収縮の単位側のホモトピーを単位複体の自己射の等式へ移す。
規約：単位側の三角形のみを厳密な等式として述べる。
使われ方：H⁰ の演算の係数が一であることの保証。 -/
lemma aritySection_augmentation (n : ℕ) :
    aritySection A n ≫ (augmentation A).map.app (FiniteBijection.of n) = 𝟙 _ :=
  _root_.SerrePositivity.HomologyZero.unit_homotopy_eq (complexContraction A n).homotopyInvHomId

/-- 概要：augmentation が同じ E(n) への二射はホモトピック（BF §1）。
方針：両射を収縮と切断を通る射へホモトピーで移す。
規約：始域は任意の非有界複体。cofibrancy は不要。
使われ方：H⁰ の結合性と可換性の係数の比較。 -/
def coefficientHomotopy (n : ℕ) {T : Complex A} (f g : T ⟶ (operad A).arity n)
    (hfg : f ≫ (augmentation A).map.app (FiniteBijection.of n) =
      g ≫ (augmentation A).map.app (FiniteBijection.of n)) : Homotopy f g := by
  change f ≫ (complexContraction A n).hom = g ≫ (complexContraction A n).hom at hfg
  let e := complexContraction A n
  have heq : f ≫ e.hom ≫ e.inv = g ≫ e.hom ≫ e.inv :=
    (Category.assoc f e.hom e.inv).symm.trans
      ((congrArg (fun k => k ≫ e.inv) hfg).trans (Category.assoc g e.hom e.inv))
  exact (e.homotopyHomInvId.compLeft f).symm.trans
    ((Homotopy.ofEq heq).trans (e.homotopyHomInvId.compLeft g))

end SerrePositivity.EInfinity.BarrattEccles
