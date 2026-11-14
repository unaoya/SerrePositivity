module

public import SerrePositivity.Archive.KST.DescentConditional.WeightedCechDerivedComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyLimit
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Čech 添字の随伴の実際の局所化

## 概要
添字関手の前合成を点ごとの弱同値で実際に局所化し、添字随伴を局所化後の随伴へ移す。

## 方針
前合成が点ごとの弱同値を保存することを検査し、Mathlib の局所化と随伴の移送を使う。

## 規約
通常の極限の保存をホモトピー極限の保存へ読み替えない。前合成そのものと指定比較を保持する。

## 使われ方
論文 補題 3.2 の分裂余単体対象の降下と細分。τ 位相の層論の代わりの Čech 計算の準備。
-/

@[expose] public section

noncomputable section

universe u vD uD vE uE vH uH

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DiagramModel

namespace SerrePositivity.KST.Descent.CechReindex

variable {K L : Type u} [SmallCategory K] [SmallCategory L]
  [ModelCategory SSet.{u}]
  {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  (QK : (K ⥤ SSet.{u}) ⥤ D)
  [QK.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u}))]
  (QL : (L ⥤ SSet.{u}) ⥤ E)
  [QL.IsLocalization (Projective.objectwise L (weakEquivalences SSet.{u}))]

/-- 概要：添字関手による実際の前合成（補題 3.2）。
方針：関手圏の前合成関手を使う。規約：全ての図式射も写す。
使われ方：分裂余単体対象の添字変更。 -/
abbrev precomp (a : K ⥤ L) : (L ⥤ SSet.{u}) ⥤ (K ⥤ SSet.{u}) :=
  (Functor.whiskeringLeft K L SSet.{u}).obj a

/-- 概要：前合成は実際の点ごとの弱同値を保存（補題 3.2）。
方針：元の各点の弱同値を添字関手の像で検査する。
規約：添字の随伴性は不要。使われ方：前合成の実際の局所化。 -/
lemma precomp_inverts (a : K ⥤ L) :
    (Projective.objectwise L (weakEquivalences SSet.{u})).IsInvertedBy
      (precomp a ⋙ QK) := by
  intro F G f hf
  exact Localization.inverts QK (Projective.objectwise K (weakEquivalences SSet.{u}))
    _ (fun k ↦ hf (a.obj k))

/-- 概要：点ごとの弱同値で局所化した実際の前合成（補題 3.2）。
方針：Mathlib の局所化の普遍性で構成する。
規約：局所化後の関手の存在は追加入力にしない。使われ方：導来添字随伴。 -/
def localized (a : K ⥤ L) : E ⥤ D :=
  Localization.lift (precomp a ⋙ QK) (precomp_inverts QK a) QL

/-- 概要：元の前合成と局所化後の前合成の指定比較（補題 3.2）。
方針：実際の局所化の因子化同型を使う。
規約：随伴の移送と同じ同型を使う。使われ方：指定比較の整合性。 -/
def comparison (a : K ⥤ L) : precomp a ⋙ QK ≅ QL ⋙ localized QK QL a :=
  (Localization.fac (precomp a ⋙ QK) (precomp_inverts QK a) QL).symm

/-- 概要：添字随伴から実際の局所化後の前合成随伴を構成（補題 3.2）。
方針：前合成の随伴と、同じ指定局所化比較を Mathlib の随伴移送に渡す。
規約：随伴の向きは前合成により反転する。使われ方：分裂降下の添字変更。 -/
def adjunction {a : K ⥤ L} {b : L ⥤ K} (adj : a ⊣ b) :
    localized QL QK b ⊣ localized QK QL a := by
  letI : CatCommSq (precomp b) QK QL (localized QL QK b) := ⟨comparison QL QK b⟩
  letI : CatCommSq (precomp a) QL QK (localized QK QL a) := ⟨comparison QK QL a⟩
  exact (adj.whiskerLeft SSet.{u}).localization QK
    (Projective.objectwise K (weakEquivalences SSet.{u})) QL
    (Projective.objectwise L (weakEquivalences SSet.{u})) _ _

variable {H : Type uH} [Category.{vH} H]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]

/-- 概要：定数図式は局所化後の前合成でも定数図式に一致（補題 3.2）。
方針：元の厳密な定数図式の一致と指定因子化同型を局所化で持ち上げる。
規約：通常の極限を用いない。使われ方：実際の導来定数随伴の合成。 -/
def constantIso (a : K ⥤ L) :
    HomotopyLimit.localizedConstant L Λ QL ⋙ localized QK QL a ≅
      HomotopyLimit.localizedConstant K Λ QK := by
  let F := (Functor.const L : SSet.{u} ⥤ _) ⋙ precomp a ⋙ QK
  let e₁ : Λ ⋙ HomotopyLimit.localizedConstant L Λ QL ⋙ localized QK QL a ≅ F :=
    Functor.isoWhiskerRight (HomotopyLimit.constantComparison L Λ QL).symm
      (localized QK QL a) ≪≫
      Functor.isoWhiskerLeft (Functor.const L) (comparison QK QL a).symm
  let e₂ : Λ ⋙ HomotopyLimit.localizedConstant K Λ QK ≅ F :=
    (HomotopyLimit.constantComparison K Λ QK).symm
  letI : Localization.Lifting Λ (weakEquivalences SSet.{u}) F
      (HomotopyLimit.localizedConstant L Λ QL ⋙ localized QK QL a) := ⟨e₁⟩
  letI : Localization.Lifting Λ (weakEquivalences SSet.{u}) F
      (HomotopyLimit.localizedConstant K Λ QK) := ⟨e₂⟩
  exact Localization.liftNatIso Λ (weakEquivalences SSet.{u}) F F _ _ (Iso.refl F)

end SerrePositivity.KST.Descent.CechReindex
