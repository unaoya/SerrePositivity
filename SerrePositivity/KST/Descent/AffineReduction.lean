module

public import SerrePositivity.KST.Descent.ReducedClosedSubscheme
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# アフィン Noetherian スキームの実際の被約化と公理 (3)

## 概要
全体の閉集合に被約閉部分スキーム構造を入れることで reduction を構成する。
アフィン Noetherian の場合、その包含が冪零 thickening であることを証明する。

## 方針
Noetherian 環の nilradical の冪零性を、アフィンスキームのイデアル層の全体上での判定に移す。
被約化の包含の核はスキームの nilradical そのもの。

## 規約
非アフィンの場合の一様な冪零指数や Zariski 貼り合わせは、このファイルでは未証明。
前層 L の冪零不変性は公理 (3) の明示的な引数から使う。

## 使われ方
論文 補題 3.3 と定理 3.1 の「一般 → 被約」の還元のアフィン部分。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

/-- 概要：全体の被約閉部分スキームとしての reduction（論文 §3）。
方針：全体の閉集合の消滅イデアル層を使う。
規約：元のスキームが被約であることは要求しない。
使われ方：被約な基底への降下の還元。 -/
noncomputable def schemeReduction (X : Scheme.{u}) : Scheme.{u} :=
  reducedClosedSubscheme (⊤ : Closeds X)

/-- 概要：reduction から元のスキームへの包含（論文 §3）。
方針：全体の被約閉部分スキームの包含を使う。
規約：台上で同じでも、スキームの射として同型とは仮定しない。
使われ方：公理 (3) に適用する指定射。 -/
noncomputable def schemeReductionInclusion (X : Scheme.{u}) : schemeReduction X ⟶ X :=
  reducedClosedInclusion (⊤ : Closeds X)

/-- 概要：構成した reduction は被約（論文 §3）。
方針：消滅イデアル層による閉部分スキームの被約性を使う。
規約：アフィン性や Noether 性はこの事実には不要。
使われ方：次元帰納での被約な基底の入力。 -/
instance schemeReduction_isReduced (X : Scheme.{u}) : IsReduced (schemeReduction X) := by
  change IsReduced (reducedClosedSubscheme (⊤ : Closeds X))
  infer_instance

/-- 概要：アフィン Noetherian スキームの nilradical イデアル層は冪零（論文 §3）。
方針：全体上の nilradical の冪零性を、アフィンイデアル層の全体上での判定で移す。
規約：Noether 性は全体の切断環に明示している。
使われ方：reduction の包含が公理 (3) の幾何条件を満たすことの検証。 -/
theorem affine_nilradical_isNilpotent (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] : IsNilpotent X.nilradical := by
  obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(X, ⊤)
  refine ⟨n, Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  change nilradical Γ(X, ⊤) ^ n = 0
  exact hn

/-- 概要：アフィン Noetherian スキームの reduction は冪零 thickening（論文 §3）。
方針：包含の核を nilradical と同定し、その冪零性を使う。
規約：一般の非アフィンの場合はこの instance に含まない。
使われ方：前層 L の公理 (3) を実際の被約化射に適用する。 -/
instance schemeReductionInclusion_isNilpotentThickening (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] : IsNilpotentThickening (schemeReductionInclusion X) where
  toIsClosedImmersion := reducedClosedInclusion_isClosedImmersion _
  nilpotent_ker := by
    change IsNilpotent (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.vanishingIdeal_top]
    exact affine_nilradical_isNilpotent X

/-- 概要：アフィン Noetherian な有限型対象の被約化の引き戻しは全次数同型（論文 §3）。
方針：実際の reduction の核の冪零性を証明済みの instance とし、公理 (3) を適用する。
規約：前層が冪零不変であるという仮定を明示し、任意の前層への結論とはしない。
使われ方：一般の基底を被約な基底へ還元する際のアフィン計算。 -/
theorem Nilinvariant.affineReduction_pullback_bijective {S : Scheme.{u}} {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient) [Nilinvariant S L]
    (X : FiniteTypeSchemes S) [IsAffine X.obj.left] [IsNoetherianRing Γ(X.obj.left, ⊤)]
    (H : Coefficient) (n : ℤ) :
    Function.Bijective (L.pullback H n (reducedClosedAsFiniteTypeInclusion X ⊤)) := by
  have : IsNilpotentThickening (reducedClosedAsFiniteTypeInclusion X ⊤).hom.left :=
    schemeReductionInclusion_isNilpotentThickening X.obj.left
  exact Nilinvariant.pullback_bijective (S := S) (L := L)
    (reducedClosedAsFiniteTypeInclusion X ⊤) H n

end SerrePositivity.KST.Descent
