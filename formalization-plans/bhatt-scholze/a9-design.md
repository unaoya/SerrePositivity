# A9 の設計：界面の組み立てと E3 の消去（2026-11-02）

概要：E3 を消す道筋の最後の単位 A9。A4〜A8 で骨組みを置いた八つの欄（`perfd`・`unit`・`h0`・`universal`・`limitCone`・`limit_isLimit`・`integral`・
`excision`）から `PerfectoidizationInterfaceCAlg R p hR` の項を組み立て、既存の `nonempty_e3_of_cAlg`（EInfinity/Perfectoidization/DerivedCorollary）で
D(R) 版 `PerfectoidizationInterfaceE3` の存在を得て、唯一の引用 `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`（Inputs/PerfectoidizationInterface.lean:52、
`sorry`）を証明済みの定理に置き換える。
方針：界面の型は変えない（10-26 以降の規約）。組み立ては各欄の定理を項に詰めるだけ。Inputs の定理は同じ公開名・型のまま `nonempty_e3_of_cAlg ⟨…⟩` を
証明にする（下流の `Perfectoidization/Derived/{IntegralExistence,Excision}` は `Classical.choice (exists_perfectoidizationInterfaceE3 …)` で取り出しているので変更不要）。
規約：BS 側で `Inputs/` を書き換えるのは中身の段階（暦に載せてから）。そのとき監査（`make_area_audits.py` の許可一覧、Prop 8.10 の引用 3 件と結晶の黒箱）の更新を
調整役に知らせる。
使われ方：Serre positivity の perfectoid 側の `sorry` の消去。残るのは K 理論側の二件。

## 1. 欄と供給元

| 欄 | 供給する定理（drafts） | 単位 |
| --- | --- | --- |
| `perfd : algebraNerve R ⟶ CAlg_R R` | `e3Perfd p R`（A4/InterfaceFields） | A4-3 |
| `unit : FunctorHom (algebraEmbedding R) perfd` | `e3Unit p R` | A4-3 |
| `h0 : H0RingData R (perfd ≫ U) (underlyingUnit R unit)` | `e3H0RingData p R` | A4-3 |
| `universal` | `e3Universal p R`（A7/UniversalProperty） | A7-2 |
| `limitCone`・`limit_isLimit` | `e3LimitCone p R`・`e3LimitCone_isLimit p R`（A5/InterfaceLimitCone） | A5-1 |
| `integral` | `e3Integral p R`（A8/IntegralDiscreteness） | A8-4 |
| `excision` | `e3Excision p R`（A6/Excision） | A6-4 |

## 2. 形

- `def perfectoidizationInterfaceCAlg (R) (p) (hR) : PerfectoidizationInterfaceCAlg R p hR := { perfd := e3Perfd p R, unit := e3Unit p R, h0 := e3H0RingData p R,
  universal := e3Universal p R, limitCone := e3LimitCone p R, limit_isLimit := e3LimitCone_isLimit p R, integral := e3Integral p R, excision := e3Excision p R }`。
- `theorem nonempty_perfectoidizationInterfaceCAlg : Nonempty (PerfectoidizationInterfaceCAlg R p hR) := ⟨perfectoidizationInterfaceCAlg R p hR⟩`。
- `theorem exists_perfectoidizationInterfaceE3 … : Nonempty (PerfectoidizationInterfaceE3 R p hR) := nonempty_e3_of_cAlg R p (hR := hR) (nonempty_perfectoidizationInterfaceCAlg R p hR)`
  （hR は `nonempty_e3_of_cAlg` の暗黙引数、W9-III-13）— Inputs の定理の証明をこれに置き換える。docstring の「唯一の文献入力」の記述を更新し、原典の経路（A0〜A9）と
  **恒久的な引用**（下の §3 の表。W9-III-12 で D68 後の形に更新）を列挙する。

## 3. 依存の全体像（E3 の消去に要るもの）

- ∞ 側の一般論：S1〜S8（層・RΓ・脚注 10・層化・CAlg 値・κ・D(A) への適用・空間値の層、M12 系。S8 の前提に G13（𝒮 の presentable 性）と S4 の非安定版、W9-III-12）、G3・G4・G6〜G10、DerivedGeneral（M13）、P⁰（M14）、
  descendability（M15）、F2 の P_Σ・Kan 延長。
- 論文の層の整理 2b の後：HA/DerivedCompletion の名前（完備化、Tot、Koszul）、Shared（cup 積・Bockstein・de Rham）。
- **恒久的な引用**（`sorry`、監査の許可一覧へ。W9-III-12 で D68 後の形に更新）：

  | 引用 | 宣言 | 出典 | 備考 |
  | --- | --- | --- | --- |
  | 結晶側（唯一） | `crystalline_deRham_polynomial_Zp`（A1/CrystallineInput） | Thm 5.2 β の de Rham 形、D68 | 仕様つき（自然性・乗法・Bockstein・根の遷移）。`hodgeTate_iso_polynomial_Zp` は**その系**（引用ではない） |
  | v 降下 | `cech_exact_of_vCover_perfect`（G-A6-1a） | [BS17, Thm 4.1 (i)] | 完全スキーム、被覆側も完全 |
  | arc 層の判定 | `arcSheaf_of_vSheaf_of_valuationSquares`（G-A6-1b） | [BM18, Thm 1.7] | 共変 Ring_{F_p} → D(ℤ)^{≥0} |
  | 完全付値環の Milnor 四角形 | `valuationRing_milnorSquare_perfect`（G-A6-1c） | [BS17, Lemma 6.3] | **暫定**：初等補題 `valuationRing_milnorSquare` から証明予定なので恒久的ではない |
  | P⁰ の性質 | `powerOperationZero_pos`（G-A4-1） | [Lur11, Rem 2.2.7] | 共有補題の仕様。G-A4-1 の中で定理にする予定なら恒久的ではない |

- **証明予定で引用ではないもの**（残存引用に数えない、W9-III-12）：G-A3-7（Ex 7.9 の p 反転の議論、[Bha12, Claim 3.30] の計算。W9 で計算 ○、証明予定の補題）、
  G-A6-1c の一般版（初等）、Lemma 10.12（A8-3、古典的可換環論の独立単位）、付値環の tilt・untilt（G-A6-3・6）、有限エタール代数の perfectoid 性（G-A8-6）、
  有限積の perfectoid 性（G-A6-12、直接証明）。
- **基盤依存**（引用ではなく ∞ 側・論文の層の窓の供給）：S1〜S8（S8 の前提 G13 を含む）、G3・G4・G6〜G10、DerivedGeneral、P⁰（M14）、descendability（M15）、
  HA/DerivedCompletion（2b 後の名前）。未実装の一般論の `sorry` を「残る文献入力」とは数えない。

## 4. 原典との差

界面の型そのものの原典との差は Inputs の docstring の六点 (i)〜(vi)（10-26）のまま。A9 は差を増やさない。

## 5. 単位と順序

A9-1：組み立て（骨組みのみ、drafts/A9/Assembly.lean）。中身の段階では A4〜A8 の全欄の中身が揃ってから Inputs を書き換える。

## 6. 決定事項

相談事項なし。Inputs の書き換えの時期は中身の段階で暦に載せる。

## 7. E3 非依存性と import の順序（W9-III-08・09、2026-11-03）

**致命（W9-III-08）**：本体の実 import に、Assembly の上流から消去対象の `Inputs/PerfectoidizationInterface` へ戻る経路がある：
`drafts/A6/ArcSite`・`ArcSheafProperty` → `Perfectoidization/CompletedTensor` → `Perfectoidization/Derived/IntegralExistence` → `Inputs`、および
`drafts/A8/AlmostConnectivity` → `Almost/Lemma103` → `CompletedTensor` → 同じ経路。Inputs の証明を Assembly に置き換えると
`Inputs → Assembly → IntegralDiscreteness → AlmostConnectivity → Lemma103 → CompletedTensor → IntegralExistence → Inputs` の閉路になる。
原因は `CompletedTensor.lean` の `isIntegralPerfectoid_finPi`（有限直積）が `Inputs.exists_perfectoidization_of_integral` を使っていること（同ファイルの規約「有限直積は今 E3 に依存」）。
Fontaine 表示による完備テンソルの前半（`integralPerfectoid_completedTensor_pure_and_h0`）は E3 非依存で、Lemma 10.3 の数学的証明が Thm 10.11 を要するわけではない。

**決定（推奨 (a)）**：
1. CompletedTensor の Fontaine による芯を E3 非依存のモジュール（仮称 `Perfectoidization/CompletedTensorCore`。2a の Perfectoid/ への統合に合わせて名前は調整役）へ切り出し、
   `Almost/Lemma103`・A6・A8 の依存をそこへ向ける。
2. 有限直積の perfectoid 性は直接証明（G-A6-12：有限積と tilt・Witt の可換性、各核生成元の組、空積は零環）に替え、E3 を使う版は削除（または E3 後に隔離）。
3. **時期**：BhattScholze/ の Lean は 2a の取り込みまで触らない（調整役の指示、11-02）。2a は Perfectoidization* 12 本を Perfectoid/ へ統合するので、この分割は 2a に
   含めてもらうか、2a 直後の最初の作業にする（design-status §3.1 の依頼）。drafts 側は import 行のコメントで分割後の名前を指す。
4. **受入条件**：A0〜A9 の drafts と、それらが import する本体のモジュールから `Inputs/PerfectoidizationInterface` へ到達する経路がないこと（`scripts/` の import 到達性で確認、
   中身の段階で `lake build` の前に）。

**配置（W9-III-09）**：数学的循環ではなくファイル単位の順序。定義を先行ファイルへ、後段の定理を後に：
- `A1/CrystallineInput`（黒箱と Cartier）→ `A1/HodgeTateComparison` → `A1/DeRhamComparisonPoly`
- `A5/RootAdjunction`（根添加の定義）→ `A5/StrongDescent`（A1-5 を使う）→ `A5/WeaklyInitialAndDescent`（SemiperfectoidCase・StrongDescent を使う）→ `A5/PerfectSiteComparison`（Prop 8.5 と系、A5 の最後）
- `A5/PerfectSite`（site・Lemma 4.8・比較写像）→ `A5/SemiperfectoidCase`（DiscreteCore を使う）→ 上の WeaklyInitialAndDescent
- `A4/{Perfectoidization,InterfaceFields}`（定義、A5 より先）→ `A4/AfterComparison`（`e3Perfd_eq_direct`・Example 8.3、Prop 8.5 系 4 を使う）
- `A7/AnimatedDomain`・`A7/DiscreteCore`（A5 より先、W9-II-24）→ `A7/{AnimatedPerfectoidization,UniversalProperty}`
全体の DAG は drafts/README の「ファイル順序」に記す。所有単位の A 番号は変えない。
