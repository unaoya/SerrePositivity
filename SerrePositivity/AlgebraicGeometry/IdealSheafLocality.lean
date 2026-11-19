module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SpecIdeal

/-!
概要：KST §5、Stacks 080Y の中心の降下に使うイデアル層の局所性と乗法。
方針：環同型でのイデアルの逆像の乗法性と、アフィン開被覆での等式検出を使う。
規約：実際の IdealSheafData の等式を扱う。
使われ方：チャート上の中心の降下等式を blowup 全体へ移す。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

/--
概要：環同型によるイデアルの逆像は積を保存する。
方針：逆同型による像へ書き換えて乗法性を使う。
規約：KST §5、Stacks 080Y、任意の可換環。
使われ方：Spec のイデアル対応と開制限の乗法性。
-/
theorem ideal_comap_mul_equiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I J : Ideal B) : (I * J).comap e = I.comap e * J.comap e := by
  simpa only [Ideal.map_symm] using Ideal.map_mul e.symm I J

/--
概要：Spec のイデアル対応はイデアル層の積を保存する。
方針：全切断上の積と ΓSpec 同型による逆像の乗法性を使う。
規約：KST §5、Stacks 080Y、環イデアルの実際の積。
使われ方：チャート上で例外イデアルの冪による捻りを計算する。
-/
theorem specIdealEquiv_mul (A : CommRingCat.{u}) (I J : (Spec A).IdealSheafData) :
    specIdealEquiv A (I * J) = specIdealEquiv A I * specIdealEquiv A J := by
  simp only [specIdealEquiv_apply, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  exact ideal_comap_mul_equiv (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv _ _

/--
概要：Spec のイデアル対応は自然数冪を保存する。
方針：積の保存と単位イデアルの保存から帰納する。
規約：KST §5、Stacks 080Y、零乗を含む。
使われ方：例外イデアルの任意の次数のチャート計算。
-/
theorem specIdealEquiv_pow (A : CommRingCat.{u}) (I : (Spec A).IdealSheafData) (n : ℕ) :
    specIdealEquiv A (I ^ n) = specIdealEquiv A I ^ n := by
  induction n with
  | zero =>
    simpa only [pow_zero, show (1 : (Spec A).IdealSheafData) = ⊤ from rfl,
      Ideal.one_eq_top] using (specIdealEquiv A).map_top
  | succ n ih => rw [pow_succ, specIdealEquiv_mul, ih, pow_succ]

set_option backward.isDefEq.respectTransparency false in
/--
概要：開埋め込みによるイデアル層の逆像は積を保存する。
方針：各アフィン切断の逆像公式と切断環同型の乗法性を使う。
規約：KST §5、Stacks 080Y、開埋め込みの逆像についての等式。
使われ方：チャートでの中心の積と例外イデアルの捻り。
-/
theorem idealSheaf_comap_mul_of_openImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I J : Y.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact ideal_comap_mul_equiv (f.appIso U).symm.commRingCatIsoToRingEquiv _ _

/--
概要：開埋め込みによるイデアル層の逆像は自然数冪を保存する。
方針：積と単位イデアルの逆像の保存から帰納する。
規約：KST §5、Stacks 080Y、零乗も含む。
使われ方：例外イデアルの冪を標準チャートへ制限する。
-/
theorem idealSheaf_comap_pow_of_openImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I : Y.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero =>
    simpa only [pow_zero, show (1 : X.IdealSheafData) = ⊤ from rfl,
      show (1 : Y.IdealSheafData) = ⊤ from rfl] using Scheme.IdealSheafData.comap_top f
  | succ n ih => rw [pow_succ, idealSheaf_comap_mul_of_openImmersion, ih, pow_succ]

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン開被覆への逆像が等しいイデアル層は等しい。
方針：開制限のアフィン切断公式を切断環同型で戻し、被覆で等式を検出する。
規約：KST §5、Stacks 080Y、被覆は実際のアフィン開被覆。
使われ方：中心の降下をチャート等式から大域のイデアル層等式へ移す。
-/
theorem idealSheaf_ext_of_affineOpenCover {X : Scheme.{u}} (𝒰 : X.AffineOpenCover)
    {I J : X.IdealSheafData} (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by
  let V (i : 𝒰.I₀) : X.affineOpens :=
    ⟨(𝒰.f i) ''ᵁ ⊤, (isAffineOpen_top (Spec (𝒰.X i))).image_of_isOpenImmersion (𝒰.f i)⟩
  have hV (i : 𝒰.I₀) : (V i).1 = (𝒰.f i).opensRange := by
    ext x
    change (x ∈ (𝒰.f i) '' Set.univ) ↔ x ∈ Set.range (𝒰.f i)
    rw [Set.image_univ]
  have hcover : (⨆ i, (𝒰.f i).opensRange) = ⊤ := 𝒰.openCover.iSup_opensRange
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V
    (by simpa only [hV] using hcover)
  intro i
  let W : (Spec (𝒰.X i)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hi := congrArg (fun K : (Spec (𝒰.X i)).IdealSheafData => K.ideal W) (h i)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hi
  exact Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso W).inv).2 hi

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
