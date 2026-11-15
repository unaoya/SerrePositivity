-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Interface.Assembly（仮）と、SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean の定理の証明の置き換え
-- 設計書：formalization-plans/bhatt-scholze/a9-design.md、単位 A9-1。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface

-- 本ファイルは drafts/A4/InterfaceFields.lean、drafts/A5/InterfaceLimitCone.lean、drafts/A6/Excision.lean、drafts/A7/UniversalProperty.lean、
-- drafts/A8/IntegralDiscreteness.lean を import する。

/-!
# 界面の組み立てと E3 の消去

## 概要
A4〜A8 の八つの欄から `TheoryPerfectoidizationInterface R p hR` の項を作り、`nonempty_e3_of_theory` で D(R) 版の存在を得る。
Inputs の `exists_perfectoidizationInterfaceE3` の証明をこれに置き換える。

## 方針
欄の定理を項に詰めるだけ。界面の型は変えない。

## 規約
Inputs/ の書き換えは中身の段階（暦に載せてから）。監査の許可一覧の更新を調整役に知らせる。

## 使われ方
`Perfectoidization/Derived/{IntegralExistence,Excision}`、CLMST、主定理（公開名・型は不変）。
-/

@[expose] public section
noncomputable section
universe u

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- 概要：CAlg 版の界面の項。
方針：A4-3（perfd・unit・h0）、A7-2（universal）、A5-1（limitCone・limit_isLimit）、A8-4（integral）、A6-4（excision）。
規約：`TheoryPerfectoidizationInterface` の型そのまま。
使われ方：以下。 -/
def perfectoidizationInterfaceCAlg : TheoryPerfectoidizationInterface (E := E) R p hR where
  perfd := e3Perfd (E := E) p R (hR := hR)
  unit := e3Unit (E := E) p R (hR := hR)
  h0 := e3H0RingData (E := E) p R (hR := hR)
  universal := e3Universal (E := E) p R (hR := hR)
  limitCone := e3LimitCone (E := E) p R (hR := hR)
  limit_isLimit := e3LimitCone_isLimit (E := E) p R (hR := hR)
  integral := e3Integral (E := E) p R (hR := hR)
  excision := e3Excision (E := E) p R (hR := hR)

/-- 概要：CAlg 版の界面の存在。 -/
theorem nonempty_perfectoidizationInterfaceCAlg : Nonempty (TheoryPerfectoidizationInterface (E := E) R p hR) :=
  ⟨perfectoidizationInterfaceCAlg (E := E) R p hR⟩

include E in
/-- 概要：D(R) 版の界面の存在（既存 `nonempty_e3_of_theory`）。Inputs の `exists_perfectoidizationInterfaceE3` の証明はこれに置き換える。
方針：`nonempty_e3_of_theory`。
規約：公開名・型は Inputs のまま。
使われ方：E3 の消去。 -/
theorem exists_perfectoidizationInterfaceE3' : Nonempty (PerfectoidizationInterfaceE3 R p hR) :=
  nonempty_e3_of_theory (E := E) R p (hR := hR) (nonempty_perfectoidizationInterfaceCAlg (E := E) R p hR) -- hR は暗黙引数（W9-III-13）

end SerrePositivity.BhattScholze.Perfectoidization.Derived
