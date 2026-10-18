module

public import SerrePositivity.KST.Spectra.RationalUnitNaturality
public import SerrePositivity.KST.Spectra.RationalTensorNaturality

/-!
概要：実際の有理化写像の整数次数の誘導準同型とテンソル積の自然な比較。
方針：単位の自然性と a⊗1 上の公式をテンソル群の一意性へ渡す。
規約：有理化の射への作用は実際の BF 射から誘導されたもの。
使われ方：BF 1978 §2、HA §1.4.2。定理 3.1 の有理 π_* 表示。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped TensorProduct

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：線形なテンソル表示でも実際の単位は a⊗1 を与える。
方針：乗法表示の公式を標準の加法表示へ読み替える。
規約：標準の ℤ 加群構造。
使われ方：HA §1.4.2。自然性の加法群での計算の入力。 -/
theorem rationalizationUnitTensorEquiv_unit (X : OmegaSpectrum.{u}) (j : ℤ)
    (a : Additive (homotopyGroup X j)) :
    rationalizationUnitTensorEquiv X j
      ((homotopyMap (rationalizationUnit X) j).toAdditive a) = a ⊗ₜ[ℤ] (1 : ℚ) := by
  change Multiplicative.toAdd
    (rationalizationUnitHomotopyEquiv X j
      (homotopyMap (rationalizationUnit X) j a.toMul)) = _
  exact congrArg Multiplicative.toAdd (rationalizationUnit_homotopy X j a.toMul)

/-- 概要：単位の自然性を標準の加法群の準同型で述べる。
方針：実際の BF 射の合成の π_* 公式と型タグの定義を使う。
規約：全整数次数。
使われ方：BF 1978 §2、HA §1.4.2。テンソルの自然性の可換図式。 -/
theorem rationalizationUnit_additive_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ)
    (a : Additive (homotopyGroup X j)) :
    (homotopyMap (rationalizationMap f) j).toAdditive
      ((homotopyMap (rationalizationUnit X) j).toAdditive a) =
    (homotopyMap (rationalizationUnit Y) j).toAdditive ((homotopyMap f j).toAdditive a) := by
  have h := DFunLike.congr_fun (rationalizationUnit_natural f j) a.toMul
  rw [homotopyMap_comp, homotopyMap_comp, MonoidHom.comp_apply, MonoidHom.comp_apply] at h
  exact congrArg Additive.ofMul h.symm

/-- 概要：実際の有理化の射はテンソル表示で元の射の ℚ テンソルを誘導する。
方針：単位の自然性とテンソル群の準同型の一意性を組み合わせる。
規約：全整数次数で自然。群の写像を抽象的に移送して実際の射を定義していない。
使われ方：BF 1978 §2、HA §1.4.2。有理 π_* の自然なテンソル表示。 -/
theorem rationalizationUnitTensorEquiv_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ)
    (a : Additive (homotopyGroup (rationalization X) j)) :
    rationalizationUnitTensorEquiv Y j ((homotopyMap (rationalizationMap f) j).toAdditive a) =
      (TensorProduct.map (homotopyMap f j).toAdditive.toIntLinearMap
        (LinearMap.id : ℚ →ₗ[ℤ] ℚ)) (rationalizationUnitTensorEquiv X j a) :=
  rationalTensor_realization_natural
    (rationalizationUnitTensorEquiv X j).toAddEquiv
    (rationalizationUnitTensorEquiv Y j).toAddEquiv
    (homotopyMap (rationalizationUnit X) j).toAdditive
    (homotopyMap (rationalizationUnit Y) j).toAdditive
    (homotopyMap f j).toAdditive (homotopyMap (rationalizationMap f) j).toAdditive
    (rationalizationUnitTensorEquiv_unit X j) (rationalizationUnitTensorEquiv_unit Y j)
    (rationalizationUnit_additive_natural f j) a

/-- 概要：有理化対象の群準同型は元の群からの単位上で決まる。
方針：実際の単位に適合するテンソル表示へ移して一意性を適用する。
規約：全整数次数の群準同型を比較する。
使われ方：HA §1.4.2。有理化の恒等・合成法則の検査。 -/
theorem rationalization_homotopyMap_ext (X Y : OmegaSpectrum.{u}) (j : ℤ)
    (f g : homotopyGroup (rationalization X) j →* homotopyGroup (rationalization Y) j)
    (h : ∀ a, f (homotopyMap (rationalizationUnit X) j a) =
      g (homotopyMap (rationalizationUnit X) j a)) : f = g := by
  have he : f.toAdditive = g.toAdditive :=
    rationalTensor_realization_ext (rationalizationUnitTensorEquiv X j).toAddEquiv
      (rationalizationUnitTensorEquiv Y j).toAddEquiv
      (homotopyMap (rationalizationUnit X) j).toAdditive
      (rationalizationUnitTensorEquiv_unit X j) f.toAdditive g.toAdditive
      (fun a ↦ congrArg Additive.ofMul (h a.toMul))
  apply MonoidHom.ext
  intro a
  exact congrArg Additive.toMul (DFunLike.congr_fun he (Additive.ofMul a))

/-- 概要：有理化の実際の恒等射への作用は π_* 上で恒等。
方針：単位上の自然性と有理化群の準同型の一意性を使う。
規約：選んだ BF 射の厳密な恒等法則は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。有理 π_* の関手法則。 -/
theorem rationalizationMap_homotopy_id (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyMap (rationalizationMap (𝟙 X)) j = MonoidHom.id _ := by
  apply rationalization_homotopyMap_ext X X j
  intro a
  have h := rationalizationUnit_additive_natural (𝟙 X) j (Additive.ofMul a)
  rw [homotopyMap_id] at h
  exact congrArg Additive.toMul h

/-- 概要：有理化の実際の射への作用は π_* 上で合成を保つ。
方針：単位上の二つの自然性の可換式を合成し、一意性を使う。
規約：全整数次数での群準同型の関手法則。
使われ方：BF 1978 §2、HA §1.4.2。有理 π_* の関手性。 -/
theorem rationalizationMap_homotopy_comp {X Y Z : OmegaSpectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (j : ℤ) :
    homotopyMap (rationalizationMap (f ≫ g)) j =
      (homotopyMap (rationalizationMap g) j).comp (homotopyMap (rationalizationMap f) j) := by
  apply rationalization_homotopyMap_ext X Z j
  intro a
  have hf := rationalizationUnit_additive_natural f j (Additive.ofMul a)
  have hg := rationalizationUnit_additive_natural g j ((homotopyMap f j).toAdditive (Additive.ofMul a))
  have hfg := rationalizationUnit_additive_natural (f ≫ g) j (Additive.ofMul a)
  rw [homotopyMap_comp] at hfg
  change Additive.ofMul (homotopyMap (rationalizationMap (f ≫ g)) j
    (homotopyMap (rationalizationUnit X) j a)) = _ at hfg
  apply Additive.ofMul.injective
  change (homotopyMap (rationalizationMap (f ≫ g)) j).toAdditive
      ((homotopyMap (rationalizationUnit X) j).toAdditive (Additive.ofMul a)) =
    (homotopyMap (rationalizationMap g) j).toAdditive
      ((homotopyMap (rationalizationMap f) j).toAdditive
        ((homotopyMap (rationalizationUnit X) j).toAdditive (Additive.ofMul a)))
  rw [hf, hg]
  exact hfg

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
