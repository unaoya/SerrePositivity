# BS・CLMST の引用解消計画（perfectoid 側）

> **アーカイブ（2026-10-18）**：CLMST の命題と BS Lemma 10.3・Remark 10.7・Thm 7.14 は証明済み。残る引用と決定事項は [BS 主計画](../bhatt-scholze/notes/bhatt-scholze.md)、∞ 圏による解消は [∞ 圏の計画](stage-i/infinity-lanes/infinity-categories.md)。将来は削除する予定で、以下は当時の計画と実施記録のまま。


作成日：2026-10-16。状態：計画のみ（未着手）。
着手時期：現在進行中の CLMST の作業（G2 系列の合流）が完了してから。
対象とする版：Bhatt–Scholze *Prisms and prismatic cohomology* は著者公開版
（`paper/refs/BS-prisms-author.pdf`、番号は[BS計画 §1](../bhatt-scholze/bhatt-scholze.md)に従う）。
CLMST は arXiv:2209.04046v4（`paper/refs/CLMST-2209.04046v4.pdf`）。

この計画は、[BS計画](../bhatt-scholze/notes/bhatt-scholze.md)と[CLMST計画](clmst.md)の両方にまたがる
「引用解消」の作業順を一つにまとめたものである。δ環・prism・perfectoid 化の原典の証明経路は
引き続き BS 計画を正本とし、本計画は「どの引用を、どの順で、どの主張の形で外すか」だけを扱う。
K 理論側（定理 3.1・補題 4.6）は本計画と独立であり、[k-theory.md](../k-theory.md) で扱う。

## 1. 前提と大前提

ユーザー指定（2026-10-16）：

- 最終的にはすべての `sorry` を外す。
- 発表の時点で残してよい引用は、**BS に書かれている命題だけ**。CLMST の命題は引用として残さない。
- BS の命題も、できるだけ証明をつける。
- **Lean の主張は原典のままにする。** 証明の経路が原典と異なる箇所は §6 に列挙し、ユーザーが判断する。
  原典にない経路を採る場合も、置き換える主張は原典どおりの一般性で述べる。
- ∞ 圏は導入しない。導来圏・導来完備化・完備導来テンソル（G2）など既存の共通基盤は使う。

## 2. 現在地（2026-10-16 18:07 の公理監査）

主定理の未証明入力は 5 件。B4（Thm 7.4 の全射性）が完成し、B-S の引用は外れた
（`17152f82`）。

| 入力 | 原典 | 状態 |
| --- | --- | --- |
| `BhattScholze.Inputs.exists_perfectoidization_of_integral` | BS Thm 1.17(1) = Thm 10.11 の環としての帰結（B-I） | 主定理の経路上 |
| `CLMST.Inputs.proposition_2_4_7` | CLMST Prop 2.4.7 | 主定理の経路上 |
| `CLMST.Inputs.corollary_4_0_4` | CLMST Cor 4.0.4 | 主定理の経路上 |
| `Section4.supportedRankK0_descent`、`theorem_3_1_K0` | 主論文 §3・§4 | K 理論側。本計画の対象外 |

主定理の経路外にある BS 関連の `sorry`：

| 入力 | 原典 | 状態 |
| --- | --- | --- |
| `BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed` | BS Thm 7.14（André） | 条件付き成果 `AndreCompatibleRootsConditional` 等が依存 |
| `CLMST.Inputs.perfectoidIdealMod_idempotent`（N+1 の場合） | BS Remark 10.7（B-R） | `CLMST/NormalizedAlmostLength` が依存 |

既に証明済みで再利用するもの：B0〜B4（δ環、prism、Cor 7.3、Thm 7.4）、
`exists_rootedPerfectoidExtension_of_perfectPrism`（任意の元族に p 冪根を添加する p 完全忠実平坦 perfectoid 拡大）、
D1〜D6（`moduleMapConeIsogeny_descent`：p 完全忠実平坦写像に沿う isogeny 降下）、
E1〜E5（Claim 2.4.8）、KL1〜KL6（`conditional_corollary_4_0_4`）、G2（完備導来テンソル）、
`CommutativeAlgebra/Almost/`、`PerfectoidizationUniqueness`、`AbsolutelyIntegrallyClosed`、`CompletelyFlat`。

## 3. 目標の段階

| 段階 | 残る名前付き入力 |
| --- | --- |
| 目標 1（発表時の最低線） | BS の 3 件：Thm 1.17(1)、Thm 7.14、Cor 8.12。CLMST の 2 件、Remark 10.7、Lemma 10.3 は証明する |
| 目標 2 | Thm 7.14 も証明（E 系列） |
| 目標 3 | Cor 8.12 と Thm 1.17(1) も証明（F 系列。arc 降下か、その古典的な代替） |

## 4. 名前付き入力の設計（すべて BS、原典の主張のまま）

| ID | 原典 | Lean での形 | 扱い |
| --- | --- | --- | --- |
| I1 | Thm 1.17(1) / 10.11 | 既存 `exists_perfectoidization_of_integral` | 維持 |
| I2 | Thm 7.14 | 既存 `exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed` | 型はそのまま。主定理の経路に入る |
| I3 | Cor 8.12 | 新規（下記） | 発表時は引用。目標 3 で証明 |
| I4 | Lemma 10.3 | 新規（下記） | C 系列で証明する |
| I5 | Remark 10.7 | 既存 `perfectoidIdealMod_idempotent` | C 系列で証明する（I4 と Thm 7.4 から） |

I4・I5 を証明すれば、発表時に残る引用は I1・I2・I3 の 3 件になる。
Thm 10.9・Prop 10.8・[And18b]・[GR03] は入力に現れない。

### 4.1 I3：Cor 8.12 の環版

原典：導来 p 完備環の射 S → S′ と導来 p 完備イデアル I ⊂ S について、
「p 完備な階数 1 の付値環 V への S → V が I を消さないなら S′ → V へ一意に延びる」とき、
S_perfd → S′_perfd、(S/I)_perfd → (S′/I)_perfd の四角形は E∞-S 代数（特に D(S)）の引き戻しである。

Lean での形（案）：

- 仮定：S、S′ は可換環で `DerivedCompletion.IsModuleComplete` について p 完備。φ : S →+* S′。
  I : Ideal S は導来 p 完備。
  付値環条件は原典どおり、∀ V（`CommRing`、`IsDomain`、`ValuationRing`、`IsAdicComplete (span {p})`、
  `ringKrullDim V = 1`）と ψ : S →+* V について、I.map ψ ≠ ⊥ なら ∃! ψ′ : S′ →+* V, ψ′.comp φ = ψ。
- 四つの perfectoid 化 f : S →+* P、f′ : S′ →+* P′、g : S/I →+* Q、g′ : S′/I →+* Q′ を
  `IsPerfectoidization p` のデータとして受け取る。
- 結論：(1) P → P′ ×_{Q′} Q が環の同型（引き戻し四角形）、(2) P′ ⊕ Q → Q′ が全射。

四つが離散（環）であるとき、(1)(2) は原典の「D(S) での引き戻し」と同値である
（離散対象の導来引き戻しの H⁰ が集合の引き戻し、H¹ が余核）。
I1 により、S、S′ が perfectoid 環上整なら四つの perfectoid 化は存在する。

派生する補題（Lean で証明する）：

- 脚注 14：φ が整写像で Spec S′ → Spec S が V(I) の外で同型なら付値環条件を満たす
  （付値環の整閉性と Frac V への一意延長）。
- 核・余核の消滅：ker(P → P′)・coker(P → P′) は I_perfd := ker(S → Q) で消える
  （原典の「In particular」の主張）。

### 4.2 I4：Lemma 10.3 の環版

原典の証明の中の一般主張を本体にする：perfectoid 環の図式 S ← R → T について、
G2 の完備導来テンソル S ⊗̂ᴸ_R T は次数 0 に集中し、H⁰ は perfectoid 環である。
そこから原典の三主張（J_perfd ⊗̂ᴸ J_perfd → J_perfd、(R/J)_perfd ⊗̂ᴸ (R/J)_perfd → (R/J)_perfd が擬同型、
J_perfd ⊗̂ᴸ (R/J)_perfd = 0）と、Prop 8.13 の環版（p 完全平坦な底変換との可換性）を導く。
(R/J)_perfd の存在は B3（Cor 7.3）で足り、入力を増やさない。

## 5. 作業パッケージと依存関係

行数は粗い見積もり。「忠実度」は、主張が原典のままか、証明が原典と同じかを示す。

### A 系列：入力の宣言と型の固定（最初に、短期）

| ID | 内容 | 依存 | 規模 |
| --- | --- | --- | --- |
| A1 | I3・I4 を §4 の型で宣言し、docstring と専用監査を付ける。I3 から核・余核の消滅を証明 | なし | 0.5〜1k |
| A2 | 脚注 14 の補題 | A1 | 0.3〜0.5k |
| A3 | 受渡し表：Prop 2.4.7・Cor 4.0.4 の実際の対象（R = A∞、S = A∞ ⊗_A D、J = (g)）と既存 D1〜6・E1〜5・KL1〜6 の入力の対応を正確な型で記す | なし | 0.2k |

A1 が終われば、以降の全系列が宣言済みの入力に対してコードを書ける。

### B 系列：古典補題（独立、並行可）

| ID | 内容 | 依存 | 規模 | 忠実度 |
| --- | --- | --- | --- | --- |
| B1 | 絶対整閉な局所環は henselian で剰余体も絶対整閉。henselian 局所環上の有限エタール代数は R^r に分解する | なし | 1〜2k | 原典は「well known」。証明する |
| B2 | 絶対整閉環の局所化は絶対整閉。茎での分解を近傍 D(gh) へ広げる（有限表示性） | B1 | 0.8〜1.5k | 同上 |
| B3 | Prop 10.2：J-almost 零な導来 p 完備加群の核・余核・拡大での閉性、⊗ イデアル性、導来 p 完備 (R/J)_perfd 加群との同値 | I4 の型（A1） | 1〜2k | BS の命題。証明する |

### C 系列：B5（Lemma 10.3・Remark 10.7 の証明）（独立、並行可）

| ID | 内容 | 依存 | 規模 | 忠実度 |
| --- | --- | --- | --- | --- |
| C1 | 完全 F_p 環の Tor 独立性（[BS17, Lemma 3.16] 相当、初等的） | なし | 0.5〜1k | 原典の引用先を自前証明 |
| C2 | I4 本体：対応する完全 prism の B ⊗̂ᴸ_A C が次数 0 集中かつ完全 δ 環。mod p で C1 に帰着。D/ID = S ⊗̂ᴸ_R T | C1、既存 B2・G2 | 1.5〜2.5k | 原典どおり |
| C3 | Lemma 10.3 の三主張と Prop 8.13 の環版 | C2 | 0.5k | 原典どおり |
| C4 | Remark 10.7：R/J_perfd = (R/J)_perfd（Thm 7.4）と Tor₁ = K/K² の消滅から mod pⁿ の冪等性へ。完備化と mod pⁿ への移送を明示 | C3 | 0.5〜1k | 原典どおり |

### D 系列：CLMST の証明の組み立て（本線）

| ID | 内容 | 依存 | 規模 | 忠実度 |
| --- | --- | --- | --- | --- |
| D1 | 分解した場合の almost 同型。絶対整閉な R̃ 上で S̃[1/f] ≅ R̃[1/f]^r のとき、S″ := S̃·R̃^r ⊂ R̃[1/f]^r を作り、S̃ → S″ ← R̃^r の両方に I3（脚注 14 版）を当てて S̃_perfd ≈ S″_perfd ≈ R̃^r（f-almost）。(R̃^r)_perfd = R̃^r は普遍性 | A1、A2、B2 | 0.8〜1.2k | §6 J2 参照 |
| D2 | 底変換：(S ⊗_R R̃)^∧ の perfectoid 化と S_perfd ⊗̂ᴸ R̃ の比較（Prop 8.13 環版 + Lemma 2.3.5）。Prop 2.4.7 証明の α/β 図式 | C3（または I4 の型）、共通層 | 0.5〜1k | 原典どおり |
| D3 | rank 一定の Prop 2.4.7：D1・D2・Claim 2.4.8（E1〜5）を `moduleMapConeIsogeny_descent` に接続 | D1、D2 | 0.4〜0.7k | 原典どおり |
| D4 | 一般 rank への帰着：Spec R ∖ V(J) の開閉分解 U_i、R → ∏(R_i)_perfd が J-almost 同型（I3 の付値環条件版 + I1）、S_perfd ≈ ∏(S_i)_perfd | A1、I1 | 1〜2k | 原典どおり（Thm 10.9 証明の最終段落） |
| D5 | Prop 2.4.7 完成（一般の S・J。Lean の主張を変えない） | D3、D4 | 0.3k | 原典どおり |
| D6 | Prop 2.4.9(a)：絶対整閉へ底変換し、D1 の almost 同型から Tor の almost 消滅、p 完全忠実平坦降下。一般 rank は D4 | D1、D4 | 0.8〜1.2k | 原典どおり |
| D7 | Thm 4.0.3(a)（全 A 加群版）：pⁿ ねじれは A → A∞ の平坦性で D6 から。一般の有限生成 M は Milnor 列と Prop 10.2（B3） | D6、B3 | 0.5〜1k | §6 J4 参照 |
| D8 | Cor 4.0.4 完成：`conditional_corollary_4_0_4`（KL1〜6）に D7 の Tor 消滅・I5 の冪等性・標準列の Koszul 分解を供給。両結論とも証明 | D7、C4 | 0.5〜1k | 原典どおり |

D 系列の合計は約 5〜8k 行。

### E 系列：André（Thm 7.14）の証明（目標 2、並行可）

| ID | 内容 | 依存 | 規模 | 忠実度 |
| --- | --- | --- | --- | --- |
| E1 | モニック f(Y) ∈ R[Y] について、(R⟨Y^{1/p^∞}⟩/(f))_perfd への写像が p 完全忠実平坦。B4-6 の X−b の計算を f(Y) に一般化。mod ϖ の pd 包が R/ϖ[Y^{1/p^∞}]/(f^p) 上自由であること（Remark 7.15(1)）を使う | 既存 B4-6 | 4〜8k | 主張は同じ。証明は Remark 7.15 の計算に沿う（Prop 7.11・Hodge–Tate 比較は使わない） |
| E2 | 有限個（または任意族）のモニック多項式を同時に添加した版 | E1 | 1〜2k | 同上 |
| E3 | 超限反復と余極限の p 完備化：perfectoid 性・p 完全忠実平坦性・絶対整閉性の保存。宇宙の管理 | E2 | 3〜5k | 原典どおり（原典も超限反復） |

合計 8〜15k 行。E3 の「filtered 余極限の p 完備化が perfectoid」は、既存の `IsIntegralPerfectoid`
（ker θ 単項）と BMS の Frobenius 判定の同値が要るかもしれない。ここが E 系列の主なリスク。

### F 系列：Cor 8.12・Thm 10.11 の証明（目標 3、研究から）

| ID | 内容 | 規模 | 備考 |
| --- | --- | --- | --- |
| F1（原典どおり） | §8.2：Prop 8.10（arc 層性）→ Cor 8.11 → Cor 8.12。離散の場合は集合値の層で足りる（原典自身が「pushout は離散なので集合の層で計算できる」と述べる）ので ∞ 圏は不要。ただし Prop 8.10 は [BS17 Thm 4.1]（完全スキームの v 降下）と [BM18] に依存し、自前証明には blowup・Raynaud–Gruson・[TT90] 近似が要る | 4〜8 万行 | 発表時は引用で残す |
| F2（古典的代替、研究） | 標数 p では「整写像で V(f) の外で同型なら perfection は f^{1/p^∞}-almost 同型」が初等的に示せる。混標数へ移す方法（tilt、perfectoid 化の Frobenius 安定性）を紙で検討 | 不明 | 原典にない経路。成立すれば I3 を外せる |
| F3 | Thm 10.11：Cor 8.11〜8.14・Lemma 10.5・Lemma 10.12・Thm 10.9（J-almost 版）。F1 ができれば Lemma 10.12（Noether 近似・層別、5〜10k）と合わせて到達 | +2〜3 万行 | F1 の後 |

（参考）∞ 圏を導入して §4〜§8・§10 を原典どおりに形式化する案は、BS 固有部分だけで
23〜41 万行と見積もられた（2026-10-16 の調査）。本計画の範囲外とし、必要が生じたときに別計画にする。

## 6. 判断を要する点（原典どおり vs 迂回）

| # | 論点 | (a) 原典どおり | (b) 迂回 | 推奨 | 状態 |
| --- | --- | --- | --- | --- | --- |
| J1 | I3（Cor 8.12）の仮定の形 | 付値環条件そのまま。D4（一般 rank）に必要 | 脚注 14（整写像・V(I) の外で同型）だけ。主張が弱まる | (a) | 未決 |
| J2 | Remark 2.4.6 の Σ_r Galois 閉包 | [And18b, 1.9.1・1.9.2] と Prop 10.8、[GR03] の almost 有限射影の理論を自前で証明（+0.5〜1 万行、BS 以外の結果の証明） | 絶対整閉環上で有限エタール被覆を直接分解し I3 を当てる（D1）。Prop 2.4.7 の主張は変わらず、証明だけ短くなる | (b) | 未決 |
| J3 | Prop 2.4.7 の一般 rank | D4 を実装し Lean の主張を維持 | rank 一定（主定理の場合）に限定し、主張を弱める | (a) | 未決 |
| J4 | Thm 4.0.3(a) の範囲（中間主張） | 全 A 加群版。Prop 10.2 を証明（B3） | pⁿ ねじれ加群だけ。Cor 4.0.4 にはこれで足りる | (a) | 未決 |
| J5 | Thm 7.14 の証明方法 | 原典は Prop 7.11（導来 prismatic cohomology）経由で、∞ 圏なしでは不可能 | Remark 7.15 の pd 包計算で忠実平坦性を示す（E 系列）。主張は同じ | (b) を実施 | 未決 |
| J6 | Cor 8.12・Thm 10.11 の証明 | arc 降下（F1・F3、6〜11 万行、[BS17]・[BM18] の自前証明を含む） | 古典的代替（F2、未確立） | 発表時は引用で残す。F2 の検証だけ先行 | 未決 |
| J7 | Stacks・[BS17 3.16] などの古典的な引用 | — | — | すべて証明する（B・C1）。BS 以外の引用は残さない | 方針 |

J1〜J4 を (a)・(b)・(a)・(a) で進めると、発表時の perfectoid 側の引用は BS の 3 件になり、
Lean の追加は D 系列と B・C 系列で合計 1.2〜2 万行。E 系列（+0.8〜1.5 万行）が終われば 2 件になる。

## 7. 並列化：レーンと合流点

現在の分担を無視した割り当て。各レーンは別ファイル群で作業し、共有層への追加は A1 で決めた型に対して行う。

| レーン | 担当 WP | 開始条件 |
| --- | --- | --- |
| L1：入力と本線の組み立て | A1 → A2 → A3 → D3 → D5 → D8 | 即時 |
| L2：古典補題 | B1 → B2 → B3 | 即時 |
| L3：B5 | C1 → C2 → C3 → C4 | 即時 |
| L4：almost 同型と底変換 | D1 → D2 | A1 の後（I4 は宣言済みの型に対して書く） |
| L5：一般 rank と平坦性 | D4 → D6 → D7 | A1 の後。D7 は B3 の後 |
| L6：André | E1 → E2 → E3 | 即時（B4-6 の延長） |
| L7：研究 | F2 の紙での検証、F1 の規模の精査、E3 の perfectoid 判定の同値の確認、§8 の検証項目 | 即時 |

合流点：

1. S1（A1 完了）：全レーンが I3・I4 の型に対してコードを書ける。
2. S2（D1・D2・B2 完了）：D3。
3. S3（D4 完了）：D5（Prop 2.4.7 完成）、D6。
4. S4（C4・B3・D7 完了）：D8（Cor 4.0.4 完成）。ここで目標 1 に到達。
5. S5（E3 完了）：I2 を証明に置き換え、目標 2。
6. S6（F 系列の判断）：目標 3 へ進むか決める。

既存作業への影響：

- CLMST の G2-H（PDCompletionH0 との環比較の BS への受け渡し）は、B4 が完成したので利用先がない。停止候補。
  G2 の本体（完備導来テンソル）は C2・D2 で使う。
- B4-6 の根付き拡大の機構は E1 の土台になる。
- K 理論とは共有層の一般補題以外に接点がない。

## 8. 着手前に紙で確かめる点（L7 の最初の仕事）

- D1 の S″ = S̃·R̃^r の構成で、S̃ → S″ と R̃^r → S″ の両方が「整かつ V(f) の外で同型」になること。
- D4 で、R → ∏(R_i)_perfd が I3 の付値環条件を満たすこと（原典の記述どおりだが、(R_i)_perfd の存在に I1 を使う点を明示）。
- E3 の「filtered 余極限の p 完備化は perfectoid」を既存の定義で直接示せるか、BMS の Frobenius 判定との同値を先に作るか。
- F2 の標数 p の初等的切除を混標数へ持ち上げる筋があるか。

## 9. 既存計画との関係（変更点の明記）

- [BS計画 §5](../bhatt-scholze/notes/bhatt-scholze.md)の「B4c の経路」は B4-6 として完成した。本計画の E 系列はその延長で Thm 7.14 の完全版を扱う。
- [CLMST計画](clmst.md)の D-app1〜3・KL-app1〜3（2026-10-15 の「G 系列 → KL → D」の順）は、
  本計画の D 系列（D3〜D8）に置き換わる。KL-app・D-app が前提としていた「深い入力の供給」は I2・I3 で行う。
- B-I の扱い（BS計画 §5 項目 2「B5 の後に再検討」）は、目標 3（F 系列）として本計画に統合する。
- 2026-10-16 の調査で提案された「下流を (I)(K) を満たす任意の代数 C へ一般化し、C を正規化で具体的に作る」経路は、
  C_D の主張を原典から変えるため採用しない（§1 の方針）。
