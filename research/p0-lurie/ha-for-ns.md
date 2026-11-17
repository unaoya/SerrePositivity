# Nikolaus–Scholze を使う前提で、HA のどこが要るか

作成：2026-11-15（調整役）。NS（arXiv:1707.01799）の本文から [Lur17]（HA）・[Lur09]（HTT）・[Lur11]（DAG XIII）の引用を節ごとに拾い、P⁰ に要る節に絞った。対応表の状態は `research/ha-coverage/review/ch*.csv`（検収済み）から。HA の番号は NS が使う 2017 年版。

## 1. P⁰ のために NS のどの節を使うか

| NS の節 | 中身 | P⁰ に要るか |
| --- | --- | --- |
| I.1 The Tate construction for finite groups | norm 写像（Constr I.1.7、Def I.1.10）、Tate 構成（Def I.1.13） | **要る** |
| I.2 Tate orbit lemma | 円群の場合の orbit と Tate | 要らない |
| I.3 Multiplicativity of the Tate construction | −^{tG} の lax 対称モノイダル構造 | **一部**（R^{tC_p} を k^{tC_p} 加群と見るため。φ を E∞ の射にするのには要るが、P⁰ にはそこまで要らない） |
| III.1 The Tate diagonal | T_p の exact 性（Prop III.1.1）、Tate 対角（Prop III.1.2・Def III.1.4） | **要る** |
| III.3 Functoriality of the Tate diagonal | Tate 対角の lax 対称モノイダル性 | 要らない（φ を E∞ の射にするときだけ） |
| IV.1 The Tate valued Frobenius | φ_R : R → (R^{⊗p})^{tC_p} → R^{tC_p}（Def IV.1.1）、π_0 で a ↦ a^p（Ex IV.1.2 (i)）、冪作用・Steenrod 作用との関係（Cor IV.1.10、Thm IV.1.15） | **要る**（Def IV.1.1 と Ex IV.1.2、IV.1.15 は確認用） |
| II、III.2・III.4〜6、IV.2〜4 | TC・円分スペクトル・THH | 要らない |

NS は **球スペクトルの上の** Frobenius を作る。Lurie の P⁰ は k 加群の中で作り、k^{tC_p} の次数 1 の類で次数 0 の成分を取り出す（DAG XIII Ex 2.2.5・Constr 2.2.6）。この最後の一歩は NS にない（`README.md` §1.3）。

## 2. 節ごとに NS が引く HA・HTT

### 2.1 I.1（norm と Tate 構成）

| 引用 | NS での使い方 | 対応表 |
| --- | --- | --- |
| HA Ch. 1（安定 ∞ 圏）、Def I.1.1 の pointed・preadditive・additive・stable | 前提の言葉 | 1.1：partial 19・own 16・mathlib 6・none 5（ほぼ揃う） |
| HTT 4.3.3.7 | f_!・f_* を Kan 延長と同一視 | Kerodon の Kan 延長は揃う（HTT の表で確認済み） |
| **HA 6.1.6**（norm の章。NS は「closely follow」と書く） | norm の段階的な構成 | **6.1.6：none 24・partial 5** |
| HA Lemma 6.1.6.3 | homotopy pullback に沿う Beck–Chevalley（f^*f_* → p_{0*}p_1^* が同値） | none |
| HA Def 4.7.4.13 | 右随伴可能な四角形の定義 | partial（Mathlib の mates、通常圏だけ） |
| HA Prop 6.1.6.7（Lemma I.1.8） | pointed なら (−1) 切断の f で norm は同値 | none |
| HA Prop 6.1.6.12（Lemma I.1.9） | preadditive なら有限ファイバーの f で norm は同値 | partial（Mathlib の biproduct、通常圏） |
| HA Prop 6.1.6.3 | 正規部分群の残りの作用 | none（P⁰ では G = C_p だけなので要らない） |

### 2.2 III.1（Tate 対角）

| 引用 | NS での使い方 | 対応表 |
| --- | --- | --- |
| DAG XIII Prop 2.2.3 | T_p の exact 性（NS も独立に証明） | — |
| **HA Cor 1.4.2.23** | Fun^Ex(Sp, Sp) ≃ Fun^Lex(Sp, S)（Ω^∞ との合成）。Yoneda と合わせて「id → F の自然変換は F(S) の点」 | **none** |
| （暗黙）HA 4.8.2：Sp の smash 積、X^{⊗p} とその Σ_p 作用 | T_p(X) = (X ⊗ … ⊗ X)^{tC_p} の定義そのもの | **4.8.2：none 20・partial 2**（4.8.2.19 は none） |
| （暗黙）HA 2 章：対称モノイダル ∞ 圏から X^{⊗p} の Σ_p 等変な対象を取り出す | 同上 | **2.0〜2.4 ほぼすべて none**（2.0.0.7 の対称モノイダル ∞ 圏の定義も none） |

### 2.3 IV.1（Tate 値の Frobenius）

| 引用 | NS での使い方 | 対応表 |
| --- | --- | --- |
| （暗黙）HA 2.1.3・3 章：E∞ 環 = CAlg(Sp) | R の定義 | 2.1.3：none 8・partial 2 |
| （暗黙）HA 3.2.4.7：CAlg のテンソルは余積。乗法 m : R^{⊗p} → R が C_p 等変な E∞ の射 | Def IV.1.1 の m | partial（Mathlib の CommAlgCat、通常圏） |
| I.3（−^{tG} の lax 対称モノイダル性）→ HA 7.3.2.7、HTT 5.2.7.4・5.5.2.9 ほか | φ を E∞ の射にする。R^{tC_p} が k^{tC_p} の加群になる | 7.3.2.7：partial（Mathlib、通常圏） |
| HA Def 7.5.0.4（étale） | 例 IV.1.2 (ii) だけ | 要らない |

### 2.4 Lurie の F_p 上の一歩（NS にない部分）で要る HA

| 引用 | 使い方 | 対応表 |
| --- | --- | --- |
| HA 7.1（E∞ 環の加群 Mod_k）、7.1.2.13（Mod_{Hk} ≃ D(k)、対称モノイダル） | 構成を Mod_k の中で行う。私たちの D(k) と結ぶ | 7.1：none 53・partial 20。**7.1.2.13 は none** |
| HA 4.5（可換代数の上の加群、相対テンソル ⊗_k） | R^{⊗_k p} | 4.5：none 19・partial 7 |
| HA 4.8.4.1（Eilenberg–Watts：余極限を保つ k 線形関手は双加群） | T_p ≃ k^{tC_p} ⊗_k −（DAG XIII が「A.7.1.2.4」として引くもの） | **none** |
| HA 7.2.4（perfect な加群）と HTT 5.3（Ind） | T_p を perfect な対象から左 Kan 延長 | 7.2.4：partial 11・none 20（`moduleCompact_iff_perfect` などはある） |

## 3. まとめ：要る HA の範囲

**A. いちばん大きい不足：対称モノイダル ∞ 圏（HA 2 章・3 章の一部）**
- 2.0〜2.1（∞-オペラッド、N(Fin_*)、対称モノイダル ∞ 圏の定義、CAlg）、2.4（Cartesian・余 Cartesian 構造）、3.2.4（CAlg のテンソルは余積）。
- 対応表ではほぼすべて none。`einfinity-gaps.md`（HA の方向で CAlg(D(R)) を作る場合の不足）と同じ範囲。
- P⁰ のために要るのは、ここから取り出す次の三つだけ：(i) 対象 X の Σ_p 等変な p 重テンソル X^{⊗p} ∈ Fun(BΣ_p, C)、(ii) 可換代数 R の乗法 R^{⊗p} → R の Σ_p 等変性、(iii) −^{tG} の lax 対称モノイダル性の最低限（R^{tC_p} への k^{tC_p} の作用）。

**B. norm の一般論（HA 6.1.6 の前半）**
- 6.1.6.3（Beck–Chevalley）・6.1.6.7・6.1.6.12 と 4.7.4.13（随伴可能な四角形）。none か通常圏だけの partial。
- 有限群 C_p の場合だけでよい。NS I.1 の短い書き方で足りる。Kerodon の Kan 延長の上に作れる。

**C. 安定化と Sp の普遍性（HA 1.4.2.23、4.8.2）**
- Tate 対角を「Sp 上の exact 関手の自然変換は S での値で決まる」で作るには 1.4.2.23 と Sp の smash 積（4.8.2.19）が要る。どちらも none。KST の Sp は安定性が条件つき（`spectra.md`）。
- **Mod_k（= D(F_p)）の中で作るなら**、1.4.2.23 の代わりに 4.8.4.1（Eilenberg–Watts）と 7.2.4（perfect）を使う（DAG XIII Ex 2.2.5 の道）。Sp の側の不足を避けられる。

**D. 加群の ∞ 圏（HA 4.5、7.1）**
- 相対テンソル ⊗_k と、D(k) を対称モノイダル ∞ 圏として見ること（7.1.2.13）。none。私たちの D(k) は安定・presentable は済み、テンソルは固定した対象とのテンソルだけ（`spectra.md` §2.3）。

## 4. 選び方の材料

- **Sp で NS をそのまま追う道**：A・B・C・（P⁰ のために）D が全部要る。C の Sp の側は KST の Sp を直すか、HA 1.4 の Sp(S_*) を作り直すか。
- **D(F_p) の中で作る道**（DAG XIII の順序）：A・B・D が要り、C の代わりに 4.8.4.1・7.2.4。Sp は最後の結果を述べる先だけ。私たちの D(F_p) は安定・presentable が無条件にあるので、出発点が強い。
- どちらでも **A（D(F_p) か Sp を対称モノイダル ∞ 圏にすること）は避けられない**。ここが基盤の整理の中心になる。HA 2 章を正面から作るか、D(F_p) の対称モノイダル構造を BE の模型（複体のテンソル）から作って、P⁰ に要る三つ（§3 A の (i)〜(iii)）だけを取り出すか、が次の判断になる。
