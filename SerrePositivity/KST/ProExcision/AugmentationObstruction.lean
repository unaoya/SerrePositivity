module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.NormNum

@[expose] public noncomputable section

/-!
# 非被約な鎖複体の零次の障害

概要：ℤ[0] の恒等写像とその二倍の間に鎖ホモトピーがないことを確認する。
方針：H₀ の同一視で整数加群へ移し、1 と 2 の不一致へ帰着する。
規約：これは KST Construction A.5 の非被約な通常和の解釈の検証であり、修正版の実装ではない。
使われ方：augmentation の補正項を省いた A.5 を誤って定理化しないための設計検証。
-/

namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：整数加群を零次に置いた一項鎖複体。
方針：Mathlib の single 複体を用いる。
規約：homological な自然数次数。
使われ方：KST Construction A.5 の零次 augmentation の障害の最小模型。 -/
abbrev augmentationTestChains : ChainComplex (ModuleCat ℤ) ℕ :=
  (single (ModuleCat ℤ) (.down ℕ) 0).obj (ModuleCat.of ℤ ℤ)

/-- 概要：ℤ[0] の恒等写像とその二倍は鎖ホモトピックでない。
方針：鎖ホモトピーによる H₀ 写像の一致を、整数の 1=2 という矛盾へ移す。
規約：追加公理なし。A.5 の補正版の存在はここでは主張しない。
使われ方：非被約 C(H) の通常の加法に必要な augmentation 補正の設計検証。 -/
theorem no_homotopy_identity_doubleIdentity :
    ¬ Nonempty (Homotopy (𝟙 augmentationTestChains)
      (𝟙 augmentationTestChains + 𝟙 augmentationTestChains)) := by
  rintro ⟨h⟩
  have he := h.homologyMap_eq 0
  rw [homologyMap_id, homologyMap_add, homologyMap_id] at he
  let e := singleObjHomologySelfIso (.down ℕ) 0 (ModuleCat.of ℤ ℤ)
  have hh := congrArg (fun f ↦ e.inv ≫ f ≫ e.hom) he
  simp only [Category.id_comp, Preadditive.comp_add, Preadditive.add_comp, Iso.inv_hom_id] at hh
  have hn := congrArg (fun f ↦ f.hom (1 : ℤ)) hh
  norm_num at hn

end SerrePositivity.KST.ProExcision
