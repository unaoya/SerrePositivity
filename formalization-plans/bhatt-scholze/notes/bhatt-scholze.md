# Bhatt–Scholze：perfectoid 化の形式化

作成：2026-10-14。全面改稿：2026-10-18（旧版の計画と実施記録は [archive/bhatt-scholze-log.md](../../archive/bhatt-scholze-log.md)）。

この文書は、Bhatt–Scholze（以下 BS）の結果について、引用の現状、原典の依存関係、
現在の入力の正確な形、原典と経路が異なる箇所を記す正本である。
数学の説明は [解説](../../../exposition/ja/exposition-ja.tex) の付録 A（`par:bs-thm74`、`par:bs-andre`、
`par:bs-cor812` ほか）に置き、ここでは繰り返さない。
残る入力（E3）を ∞ 圏の基盤で解消する計画は [∞ 圏の計画](../../archive/stage-i/infinity-lanes/infinity-categories.md) が正本である。

## 0. 現在地（2026-10-25）

主定理が依存する BS の入力は 1 件：`BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`（導来 perfectoid 化の界面 E3 の存在、
`Inputs/PerfectoidizationInterface.lean`）。旧二入力 `exists_perfectoidization_of_integral`・`perfectoidization_excision_isPullback`
（§2）は、E3 から導いた定理になっている（`PerfectoidizationInterface/IntegralExistence`・`Excision`）。E3 を消す計画は
[bhatt-scholze-stage2.md](bhatt-scholze-stage2.md)（BS-0、A0〜A9）、学習ノートは `exposition/ja/bs/`。
§2 以下の「二入力」の記述は、E3 の中身（integral・excision 欄）の説明として読む。

証明済みで引用を外したもの：

| 段 | 内容 | 主な入口 |
| --- | --- | --- |
| B0〜B2 | δ 環、prism、完全 prism と perfectoid 環の対応（§2・§3、Thm 3.10） | `BhattScholze/DeltaRing.lean`、`PerfectOrientedPrism.lean`、`PerfectPrismQuotientPerfectoid.lean` |
| B3 | Cor 7.3：semiperfectoid 商の perfectoid 化の存在と普遍性 | `exists_perfectoidization_of_semiperfectoid_quotient` |
| B4 | Thm 7.4：導来 p 完備な全射商の任意の perfectoid 化は全射（原典どおり André 経由。旧経路は `…_of_rootEnvelope`） | `surjective_of_isPerfectoidization_of_semiperfectoid_quotient` |
| B5 | Lemma 10.3（perfectoid 環の完備導来テンソルは離散で perfectoid）、Remark 10.7（`perfectoidIdealMod_idempotent`、全 N） | `BhattScholze.PerfectoidAlmost`、`lemma103_perfectoidTensor` |
| André | Thm 7.14：絶対整閉な perfectoid 環への p 完全忠実平坦な拡大 | `BhattScholze/Andre/AndreFlatness.lean`（証明済み） |
| Prop 8.13 環版 | 指定済みの perfectoid 化をもつ図式での完備導来テンソルとの可換性 | `prop813CompletedTensorMap_isPerfectoidization` |

CLMST の Prop 2.4.7・Cor 4.0.4 はこれらから証明済み（2026-10-17）。

## 1. 原典と版

正本は著者公開版 [prisms.pdf](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf)（2026-10-14 取得）。
手元の写しは `paper/refs/BS-prisms-author.pdf`（sha256 `4cb49a42c80fc734fb7585da273538e09632431ba06709ae05a11ded6673c27a`、
[SOURCE](../../../paper/SOURCE.md)）。arXiv:1905.08229v3 とは §1・§2、§7.3 以降の §7、§8・§9 の番号がずれる。
例：著者版 Thm 1.17 は perfectoid 化だが、v3 の Thm 1.17 は Z_p(n) の主張。André の補題は著者版 Thm 7.14（v3 では 7.12）。
以下の番号とコードの引用番号はすべて著者版に従う。

perfectoid の定義は `IsIntegralPerfectoid`（[BMS18, §3] と同じ条件、CLMST Def 2.4.1）。
普遍性は環の圏での `IsPerfectoidization` で述べる。導来版の perfectoid 化はまだ定義していない（∞ 圏の計画で定義する）。

## 2. 残る二つの入力の正確な形と使われ方

### 2.1 Thm 1.17(1)

```lean
theorem exists_perfectoidization_of_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f
```

利用先は `Section2.MixedPerfectoid`（= `CLMST.RPerfd`）の C_D = (A∞ ⊗_A D)_perfd。
A∞ ⊗_A D は A∞ の商ではない有限代数なので、本質的にこの入力を要する
（ある g の外で有限エタールで、Thm 10.9 の状況にあたる）。
`perfectoidIdeal`（(g)_perfd）の側は R/(g) が semiperfectoid なので Cor 7.3（B3）で足り、この入力から切り離してある。
引用を「有限かつ有限表示な代数」に狭める案（CLMST Notation 4.0.1 の適用形）は検討したが採らない。
∞ 圏の界面は整代数版を前提にする（2026-10-18 確認）。

### 2.2 Cor 8.12

```lean
theorem perfectoidization_excision_isPullback
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : S →ₐ[R] T) (I : Ideal S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hI : IsModuleComplete S (p : S) (ModuleCat.of S I))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) → ∃! l : T →+* V, l.comp f.toRingHom = k)
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S →+* C} {ηT : T →+* D} {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE) :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hC hD f.toRingHom))
      (CommRingCat.ofHom (IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)))
      (CommRingCat.ofHom (IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))))
      (CommRingCat.ofHom (IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map)))
```

付値環条件 `harc` は原典の条件そのもの（脚注 14 の「整写像で V(I) の外で同型」に弱めない）。
引用の範囲：原典の E∞-S 代数の引き戻しから、ファイバー列の長完全列、coconnectivity による H⁻¹ の消滅、
perfectoid 環への写像による導来極限の H⁰ 表示と普遍性を経て得る環の帰結までをまとめて引用とする。
差写像の全射性は含めない（∞ 圏の界面からは導ける）。

使う形への系（`BhattScholze/PerfectoidizationExcision.lean`、引用以外は証明済み）：

- `klCanonicalExcisionSquare_of_excision`（明示引数 R,p,hR,A,B,C,D,q,a,f,g,hf,hg,hA,hB,hI,harc）
- `klCanonicalExcisionSquare_of_integral_away`（q が整で、a の外で `Localization.awayMap` が全単射）

どちらも B3 の閉側の実射を使い、CLMST の `KLCanonicalExcisionSquare` と同じ四辺の `IsPullback` を結論する。
CLMST を import しない。∞ 圏の計画の Π3 は、この二つの供給元を界面由来の定理に付け替える。

## 3. 原典の依存関係（残る入力の解消に要るもの）

- **Thm 10.11（Thm 1.17(1)）**：有限表示有限代数への帰着、Lemma 10.12 による層別、g_1 に関する帰納法。
  使うもの：Cor 8.14、Prop 8.13、Lemma 10.5、Cor 8.11・8.12（arc 降下と切除）、Thm 10.9 の J-almost 版。
  これらは §8 の導来 perfectoid 化（Def 8.2、Prop 8.5、Lemma 8.6）に依存する。
  原典の外から要るもの：[BS17, Thm 4.1]（完全スキームの v 降下）、[BM18, Thm 1.6]（arc 降下）、
  [Mat16]（descendability）、[Lur11]（E∞-F_p 代数の P^0）、[And18b, Prop 1.9.1]、[GR03]。
  原典の主張（Δ_{S/A,perf} の離散性）は導来 prismatic コホモロジーなしには書けない。
- **Cor 8.12**：Prop 8.10（arc 層性）→ Cor 8.11 → Cor 8.12。Lemma 8.4（coconnectivity）、Prop 8.5（普遍性）。
- **André（Thm 7.14）の原典の証明**：Prop 7.11(2) と Prop 7.10 前半を経由し、導来 prismatic コホモロジー
  （Construction 7.6、∞ 圏の左 Kan 拡張）と Hodge–Tate 比較（Thm 4.11、§5–6、さらに結晶比較 Thm 5.2、
  [Ber06]、Cartier 同型、[BMS19, §4.4]、[Lur09, §5.5.9]）に依存する。形式化はこの経路を使わない（§4）。

∞ 圏の界面（[infinity-categories.md](../../archive/stage-i/infinity-lanes/infinity-categories.md) §0）の欄との対応：
`coconnective` = Lemma 8.4、`universal` = Prop 8.5、`integral` = Thm 1.17(1)、`excision` = Cor 8.12。
界面には Def 8.2 の perfectoid 化そのものと、Thm 1.17(1)・Cor 8.12 の証明を保留する。

## 4. 原典と経路が異なる箇所

主張は原典どおりの一般性で述べ、経路だけが異なる。

| 箇所 | 原典 | 形式化 |
| --- | --- | --- |
| Lemma 2.25 の逆 | 局所化による証明 | 極大イデアルでの計算。δ(d) を含む極大イデアルで p=ad+bφ(d) から矛盾を出す。rad(A) は Jacobson 根基（nilradical ではない） |
| Lemma 2.28 | δ(p) の単元性を使う | p·φ(x)=0 と δ(p)−1∈(p) による消去。p 局所性を仮定しない |
| §2 全般 | Z_(p) 代数 | 合同式と p ねじれの計算は任意の可換環上の δ 構造で証明 |
| Cor 7.3（B3） | Prop 7.2：全 prism の始対象を超限反復で作る | 除算 → 完全化（Lemma 3.9）→ 実 PD 完備化の順で、完全試験 prism の始対象を直接構成。Prop 7.2 の一般形・ω₁ 反復・一般の Lemma 4.8 は証明していない |
| Thm 7.4（B4）手順 1 | 有向余極限で有限生成に、帰納法で単項に帰着 | 不要：André の補題で絶対整閉にすると全ての元が同時に根を持つ |
| Thm 7.4（B4）手順 2 | André の補題で根をもつ拡大へ | 原典どおり（2026-10-25 から）。André を使わない旧経路（完全 prism 上の根の割り算包）は別証明 `…_of_rootEnvelope` として `Semiperfectoid/RootEnvelope/` に保存（解説 `par:bs-thm74`） |
| Rem 7.15 | cover 性を pd 表示で述べる | cover 性は Prop 7.10 に依存するので、pd 表示だけを忠実性の証明として使わない。忠実性は別に証明した |
| Thm 7.14（André） | Prop 7.11 経由 | 一元拡大はモニック根の割り算包（PD 経路）。任意の族は後続基数 c=succ(#σ ⊔ ℵ₀) による一元ずつの飽和、ω₁ 反復は `SmallObject.SuccStruct.iterationFunctor`。終段は可算個の証人の降下で自動的に p 進完備 |
| Thm 7.14 の step | — | 定数モニック 1 に根を要求すると不整合なので、`0 < natDegree` を仮定に加えた（利用者承認） |
| Lemma 10.3 の Tor 独立性 | [BS17, Lemma 3.16]：単体的 bar 構成と Frobenius | 平坦な全射表示による代数的証明（`perfectRing_tor_subsingleton`） |
| Prop 10.4（B5 で使う部分） | 相対 tensor の結合等式 | 商加群作用から得る retract と絶対 tensor の結合則 |
| Prop 8.13 | prismatic コホモロジーの対称モノイダル性 | 指定済みの環の perfectoid 化をもつ図式に限った環版。環の普遍性・G2 の H⁰ 主元完備化比較・perfectoid 完備テンソル定理の合成 |

導来底変換についての注意：S の完全平坦性だけでは、S/p と T/p を通常の商で書いた導来底変換の比較は成り立たない。
両側の導来剰余の離散性が要り、prism 側の p 正則性からそれを供給する。
完備化後の離散性だけから `PDCompletionH0 (B,p,0)` との比較も推論しない。

## 5. Prop 8.13 の環版の公開 API

- 一般の図式 S1←S3→S2：`prop813CompletedTensorMap_isPerfectoidization`、比較の環同型 `prop813ComparisonEquiv`
  （`_comp`・`_symm_comp`・`prop813CompletedTensorMap_unit_tmul` が標準射の公式）。
- perfectoid な底変換：`prop813BaseChange_exists_algEquiv`（新しい基底 B 上の作用を保つ）、
  B 線形版 `prop813BaseChange_exists_linearEquiv`、通常 tensor の perfectoid 化だけを入力とする
  `prop813BaseChange_exists_algEquiv_of_tensor`。
- 商への入口：`exists_prop813BaseChange_of_perfectoid_quotient`（B3）、
  `exists_prop813BaseChange_of_semiperfectoid_quotient`（B4 で全射性も付く）。

ここでの (−)_perfd は指定済みの環の `IsPerfectoidization` を意味し、任意の環で導来 perfectoid 化が離散だとは主張しない。
完全な型は `BhattScholze/Prop813PerfectoidBaseChange.lean` とその監査にある。

## 6. 証明していない範囲

- Prop 7.2 の一般形（全 prism の始対象、ω₁ 反復、一般の Lemma 4.8）。
- Thm 7.14 の mod p ind-syntomic への強化、一般の Cartier イデアルの降下、基底 prism を動かす一般化。
- Prop 10.4 全体（任意の非有界複体）、Prop 10.2 の圏同値全体、Remark 10.7 の Galois 比較と平坦性の部分。
- 導来 perfectoid 化（Def 8.2）と §8 全般。Thm 1.17(1)・Cor 8.12 は ∞ 圏の計画で扱う。

## 7. 関連する文書

- [BS のリファクタリング](bhatt-scholze-refactoring.md)：証明済みの BS を共通 API へ載せ替える計画（§13 が現行）。
- [∞ 圏の計画](../../archive/stage-i/infinity-lanes/infinity-categories.md)：界面 `PerfectoidizationInterface` と、残る二入力の解消。
- [設計段階の状態と要確認](../design/design-status.md)（2026-11-02）：A0〜A5 の設計書・骨組みの到達点、要確認の分類（A 名前探し／B BS の決定／C ∞ 側／D 2b 後／E 結晶の黒箱）、決定の所在。
- [A0 の設計](../design/a0-design.md)・[A1 の設計](../design/a1-design.md)（2026-11-02）：原典 §4.1・§4.3（§3 の前提を含む）と §4.2・§5・§6 の項目表・定義の形・証明の筋・差。
- [A2 の設計](../design/a2-design.md)・[A3 の設計](../design/a3-design.md)・[A4 の設計](../design/a4-design.md)・[A5 の設計](../design/a5-design.md)・[A6 の設計](../design/a6-design.md)・[A7 の設計](../design/a7-design.md)・[A8 の設計](../design/a8-design.md)・[A9 の設計](../design/a9-design.md)（2026-11-02）：原典 Construction 7.6、Lemma 7.7〜Prop 7.10、Def 8.2〜Lemma 8.4、Prop 8.5・Lemma 8.6、Def 8.7〜Cor 8.12、Prop 8.13・Cor 8.14、Lemma 10.5〜Lemma 10.12 の項目表・定義の形・証明の筋・差（D31〜D67）・決定事項。
- [∞ 層の一般論の設計](../design/infinity-sheaves-design.md)（2026-11-02）：原典 Not 4.16・Prop 8.5・Prop 8.10 の RΓ を定義のまま形式化するための
  D(A) 値前層の層条件・層化・Γ・RΓ、脚注 10 の補題、基数 κ の切り落とし、必要な基盤の前提（G1〜G12）。A0 の設計書はこれを前提にする。
- 実施記録（将来削除）：[旧主計画](../../archive/bhatt-scholze-log.md)、[B3](../../archive/bhatt-scholze-b3-execution.md)、
  [Prop 7.2 の接続](../../archive/bhatt-scholze-prop72-construction.md)、[F3 受領後](../../archive/bhatt-scholze-f3-next.md)、
  [B4](../../archive/bhatt-scholze-b4-execution.md)、[André](../../archive/andre-flatness.md)、[Tor 独立性](../../archive/tor-independence.md)、
  [引用解消の旧計画](../../archive/bs-clmst-citation-elimination.md)。

## 8. 受入条件

- 各段階で対象ビルドと公理監査が通り、新しい `sorry`・引用を追加しない。
- 引用を外したら利用先を含めて公理監査で確認し、この文書の §0 と解説の引用表を更新する。
- docstring は README の Conventions に従い、数学の説明は解説に置く。実施記録はこの文書に書かず、コミットメッセージに書く。

## 9. 変更記録

- 2026-10-25：BS 作業チャットを開始（引き継ぎ書 `bhatt-scholze-handover-2026-10-25.md`）。方針：HT 比較を迂回せず原論文の経路で E3 を消す。
  原典との差は「Lean が簡略化なら保ち、原典が簡単なら揃える」（ノート各章末の「原典との差の評価」）。
- 2026-10-25：BS-W1（`9095aff46`・`e039377a6`・`2d288b899`・`afbd30ef5`）。監査 838 行の修正、Q10（既存の `precomp_ringEquiv` の適用）、
  直下 616 本の主題別分割（外から import される 32 本は旧名の転送スタブ）。
- 2026-10-25：BS-W2（`c9d5fea53`・`6c13fe6be`）。760 本を原典の節ごとに再配置（Delta/・Prism/・Perfectoidization/・Semiperfectoid/・Almost/・
  Andre/{Remark715,Variants}/）。
- 2026-10-25：BR9 の決定と BS-W3（`f4dcf1d1a`・`7b82e02aa`）。B4（Thm 7.4）を原典どおり André 経由で証明。旧証明と B4 専用の 32 本は
  `Semiperfectoid/RootEnvelope/` に保存。`scripts/audit_clmst_b3.lean` の禁止リストから証明済みの André 入口を外した。公理は標準三公理のみ。
- 2026-10-25：リポジトリを Apache-2.0 にした（`ee1404187`・`d3e4f0ce0`）。
- 2026-10-25：ノートの「原典の項目一覧」と「原典との差の評価」を独立ファイルから各章末へ移した（ユーザー指示）。
- 2026-10-25：BS-W4（`a8d77f61f`・`65d7b8d74`・`05bbd64d6`）。Thm 7.14 が使う根付き拡大 108 本を `Andre/RootedExtension/` へ、
  主定理に使われない 98 本を `Andre/RootedExtension/Supplement/` へ。`Inputs/` は E3 だけ（＋転送スタブ `AndreFlatness`）にし、
  証明済みの旧入力 4 本と直下の `Perfectoidization.lean` を各章へ。`CommutativeAlgebra/` 4 本の import を切り替えて転送スタブ 4 本を削除。
  残る転送スタブ 32 本は root（30 行）と `audit_f5`・`audit_f7` の旧名 import の切り替え待ち。
- 2026-10-25：進捗確認チャットが root と `audit_f5`・`audit_f7` の旧名 import を切り替えた（`f4968ad5d`）ので、転送スタブ 32 本を削除した（`201b022cc`）。
  BS の直下は集約 `PerfectoidizationInterface.lean` だけ、`Inputs/` は E3 だけになった。領域監査は終了 0（976 モジュール）。
- 2026-10-25：E3 の `coconnective` 欄（Lemma 8.4）がどの橋からも読まれていないことを確認。外して入力を弱める調整案を
  `bhatt-scholze-e3-coconnective.md` にまとめた（EInfinity 側の変更を含むので進捗確認チャット経由）。
  記録のみ：E3 の目標の型を D(R) 版のまま残すか、原典 Def 8.2 に近い CAlg 版（EInfinity）に一本化するかは、A4 以降の設計で決める。
- 2026-10-25：ユーザーの決定。(1) 直下の集約 `BhattScholze/PerfectoidizationInterface.lean` は削除する（root と BS 監査の import を
  統合後の 3 本へ直してから）。(2) `PerfectoidizationInterface/`（W7 後は Interface・IntegralExistence・Excision の 3 本）は
  §8 の導来 perfectoid 化とその環への帰結なので `Perfectoidization/Derived/` へ移す（案 B）。EInfinity が
  `PerfectoidizationInterface.Interface` を import しているので、旧名の書き換えは進捗確認チャット経由。文献入力
  `Inputs/PerfectoidizationInterface.lean` は Inputs に残す。いずれも W7 の完了後、W8 の最初の作業として行う。
- 2026-10-25：ユーザーの決定。転送スタブを無くし、今後も生まない。BS が所有する集約 `SerrePositivity/BhattScholze.lean` を作り
  （中身は今のルートが import している BS のモジュールを新しい名前で）、ルートの BS の 32 行と `audit_f5`・`audit_f7` の BS の import を
  この 1 行に替えてもらう（進捗確認チャット経由）。その後 BS 側で W6・W7 の転送スタブと直下の集約 `PerfectoidizationInterface.lean` を削除する。
  以後の整理では BS が自分の集約を直すだけでよい。例外は EInfinity が直接 import する E3 の型のモジュールで、W8 で名前を決めたら以後変えない。
- 2026-10-26：進捗確認チャットが `e660efe6b` で root・`audit_f5`・`audit_f7` の BS の import を集約 `SerrePositivity.BhattScholze` の 1 行に、EInfinity の import を `Perfectoidization.Derived.Interface` に書き換え、E3 と CAlg 版から `coconnective` 欄を削除（文献入力が Lemma 8.4 の分だけ弱くなった）。W8b（転送スタブ 29 本と直下の集約の削除）を Codex へ。
- 2026-10-26：W8（André・RootEnvelope の整理）の方針を決定。主経路は `Andre/{OrdinaryRoots,Envelope,Perfection,Transfinite}` と `AndreFlatness` に。`Remark715` は Rem 7.15 の結論（ind-syntomic）を証明していないため `Andre/PowerRootEnvelope` に改名（原典どおりの一元拡大と Rem 7.15 の途中の pd 比較）。Variants は残してまとめる。Supplement は (a) p で割る δ 除算 24 本・(c) δ 関係の Koszul 計算 10 本・(b) 根の関係の生の包 10 本＋依存 4 本を `Andre/Envelope` へ残し、(d) δ 完全化の重複 6 本と旧 B4 経路のつなぎ 26 本を削除（`MonicPowerFamilyCompleteFlat` は OrdinaryRoots へ）。Supplement ディレクトリはなくなる。
- 2026-10-26：BS-W8b は `efc1dc638`。W8 の計画（`bhatt-scholze-codex-w8.md`、530 本 → 52 本、監査 4 本の移動、31 本の削除）を作成。使い捨て worktree（efc1dc638 と同じ状態、`.lake` は APFS のクローン複製）で作業 A〜C を通しで適用し、André・RootEnvelope の全モジュール・BS の集約・CLMST 2 本・KST 1 本・専用監査 4 本のビルド、削除の影響を受ける監査 4 本、宣言の前後比較を確認。試験で見つけて直したこと：section 行より前の `open` が落ちる（Transfinite 13 本）、無名 section の閉じ忘れ（1 本）、専用監査の対象モジュール配列の重複。`Andre/MonicRelationRegularSequence` は KST が import しているのでまとめない（置き場所は進捗確認チャットと相談）。
- 2026-10-26：BS-W8 の作業 A `5a6e3285a`・作業 B `397c6a492`。構造監査で `audit_bhatt_scholze_andre_conditional` に削除したモジュールの import が残っていた（まとめ用スクリプトの不具合：import 行だけを外したファイルを書き戻していなかった。worktree の試験では古い olean が残っていて `lake env lean` が通ったため見逃した）。スクリプトを直し、残りは作業 C の中で Codex が直す。
- 2026-10-26：W8 の受入確認で `scripts/audit_andre_initial_coefficient.lean`・`audit_andre_unoriented.lean` も対象モジュール配列の重複で落ちた（worktree の試験では scripts/ の André 監査を走らせていなかった）。重複除去スクリプトを配列の変数名によらない形に直した。所有範囲の監査でほかに重複はない。
- 2026-10-26：BS-W8 の作業 C `19655cbd1`。進捗確認チャットが `d6169a9df` で `MonicRelationRegularSequence` を `CommutativeAlgebra/` へ移した（KST の import も同時に）。BS 側の import 元 `Andre/Envelope/MonicCandidate` を `ebf510bcc` で直した（それまで main の BS のビルドが壊れていた）。W9（`Delta/DividedPower`・`Delta/Division` の 133 本 → 11 本）の計画を作り、worktree で受入確認を全部通した。
- 2026-10-26：W9（`1e070183d`）完了。BS 作業チャットで prism の射の剛性を一本化（ノート BR27）：`DerivedCompletion.mem_jacobson_bot_of_isModuleComplete` で向き付き prism の p と d は Jacobson 根基に属するので、生成元の distinguished 性（`OrientedPrism.isDistinguished_generator`）、生成元の像の単元係数、IB = J、I ⊗ B ≅ J、商による同型判定を、p 正則・完全・有界の仮定なしの一本にした（p 正則版・完全版・André の有界版の 22 宣言を削除、呼び出し 62 か所を置換）。使わなくなった仮定 `hW`・`hP` は `InputCategory`（向きなし入力圏との同値）と `…_ordinaryQuotientIso` 2 本から外した。`Prism/Basic/OrientedPrism` の節は原典の順に並べ替えた。worktree で BS・CLMST の全ビルド・全監査・構造監査を確認。
- 2026-11-02：BS を**設計のみ**再開（ビルドなし。Lean の骨組みは `drafts/` に置き、`SerrePositivity/` に触れない。coordination.md §1）。
  道筋は stage2 の A 案、最初の範囲は A0〜A1。ユーザー決定：**定義は原典のまま**入れ、定理だけ E3 に要る特別な場合に絞る
  （Def 4.1 の site、Not 4.16 の RΓ、Prop 3.13 の envelope の普遍性をそのまま定義に。Čech–Alexander 複体や自由 δ 環の模型は定理）。
  RΓ は ∞ 圏的に、D(A) 値前層の層化と大域切断で定義する（β 案。層である前層にだけ lim で定義する γ 案は不採用）。大きい site は
  濃度 ≤ κ = (#A + #R + ℵ₀)^{ℵ₀} で切り落とす（宇宙は上げない）。層は HTT 6.2.2.6 の Čech 層（hypersheaf との差は離散な層では
  消える。ノート D17、設計書 §2.1）。向き付き有界基底（ノート D5）と導来完備化の H⁰ は既存の規約を保つ。
  設計書 [infinity-sheaves-design.md](../design/infinity-sheaves-design.md) を作成し、ノート第 4 章に方針と D16〜D18 を追記。∞ 層の一般論の
  置き場所と ∞ レーンの窓は調整役が判断（infinity-foundation-plan.md 段 G の M12）。
