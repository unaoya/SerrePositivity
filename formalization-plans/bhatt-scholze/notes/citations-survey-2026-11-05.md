# 恒久の引用 3 件を証明するための調査（2026-11-05 夜）

作成：段階 II の調整役（調査は読み取りだけの 3 エージェント。原典は prisms 論文 `paper/refs/BS-prisms-author.pdf`、BS17 arXiv:1507.06490、BM18 arXiv:1807.04725、BST13 arXiv:1307.3763）。
背景：段階 II の終わりの条件は sorry 0（ユーザー、11-05 夜）。a9-design §3 の「恒久的な引用」3 件も証明する（計画 A-7）。**本書は調査の記録で、設計の決定ではない**。規模は既存コードからの類推で、確度は低い。

## 1. 結晶側 D68：`crystalline_deRham_polynomial_Zp`（drafts/A1/CrystallineInput）

- **主張（drafts）**：関手 ∞ 圏の同型 `FunctorIso zpDelta zpForms`（Q ↦ Δ_{(Q mod p)/ℤ_p} と Q ↦ Ω̂^•_{Q/ℤ_p}、N(Poly ℤ_p) → CAlg(ℤ_p)）。仕様 4 欄（完備性 2、Bockstein、根の遷移）は、Bockstein を除いて同型から出る。
- **使う側**：実際に使うのは `hodgeTate_of_deRham_cartier` → `hodgeTate_iso_polynomial_Zp` だけで、要るのは**対象ごと・模型の上の命題** `HodgeTateIsoStatement`（Čech–Alexander 模型 Tot(C^•/p) の H^i で η^i が全単射）。`deRham_iso_polynomial_crystalline` はどこからも参照されていない。
- **原典の証明**（Thm 5.2、I = (p)）：Berthelot の結晶サイト、Cor 2.39、Lemma 5.4、導来 Nakayama、Frobenius 両立のスケッチ（原典の外）。β 形は RΓ_crys を定義しないので、Berthelot と de Rham–Witt への依存は消える。
- **対象ごと・mod p の直接の道**（∞ 不要）：C^•/p → D^•/p（Lemma 5.4、mod p なので Nakayama 不要）→ D_0^•/p（G-A1-16）→ Ω^•_{F_p[X]}（pd Poincaré・BdJ の行の収縮 G-A1-14）→ Cartier → 生成元での照合。外部入力は pd Poincaré・BdJ・Cartier で、どれも初等。**8,000〜15,000 行**。最も重いのは Tot と cup 積の両立。
- **関手同型の形を残す道**：∞ 側に `totEInfinityFunctor`、関手としての比較、Tot の CAlg 化が要り、さらに 5,000〜15,000 行以上。`polyDeltaData` の仕様（1 単体まで）だけからは示せない恐れがある。
- **推奨**：D68 を改め、黒箱を対象ごとの HT の命題に置き換えて直接証明する（「定理は特別な場合だけ」）。未使用の `deRham_iso_polynomial_crystalline` は外す。
- **別件の穴の候補**：D69 側の `deRham_iso_polynomial_universal` は対象ごとの同型を G-A1-17 で FunctorIso に貼る予定だが、高次の整合性の扱いが設計にない。

## 2. arc 層の判定 G-A6-1b：`arcSheaf_of_vSheaf_of_valuationSquares`（[BM18, Thm 1.7]、drafts/A6/ArcSheafProperty:170）

- **使う側**：同じファイルの G-A6-1 `cech_exact_of_arcCover_perfect`（完全 F_p 代数の有限 arc 被覆で O の通常の Čech 複体が完全）だけ。F = (A ↦ A_perf) に 1a・1b・1c を当てる。その先は Prop 8.10 → Cor 8.12 → E3 の `excision`。
- **一般形の証明**（BM18 Thm 4.1 (3)⇒(1)、Prop 4.8）：βT 上の層の stalk 判定と hypercomplete 性、v-hypercover 降下、Tot と filtered 余極限の交換、Rydh Thm 3.12 とネーター近似。1 万行超。
- **特別な場合の道（経路 B）**：G-A6-1 を F = O の場合の Prop 4.8 として 1 圏で直接示す。Lemma 3.25 は ultrafilter の初等的な議論に、Lemma 4.4 は Milnor 列と完全環の Tor の消滅（既存 `CommutativeAlgebra/PerfectTorIndependence`）に、Lemma 4.5（Rydh）は aic 付値環の剰余体が代数閉であることと Nullstellensatz による切断に置き換える（**最後の二つは調査役の考察で、紙の確認が要る**）。**3,200〜5,900 行**、∞ 不要。**残る入力は 1a（BS17）**。
- **脚注 13 の v 版の迂回**：Prop 8.10 の tilt の段で、高い階数の付値環に対して arc 型の被覆（V → V_𝔮 × V/𝔮）が要るので通らない見込み（確度は中）。定義の変更にもなる。
- **推奨**：経路 B。一般形の G-A6-1b は主経路から外す（D56・D59 の改訂）。

## 3. v 降下 G-A6-1a：`cech_exact_of_vCover_perfect`（[BS17, Thm 4.1 (i)]、drafts/A6/ArcSheafProperty:108）

- **主張（drafts）**：完全環 A と完全環の有限族 B_i、affine 版の v 被覆の族で、A → ∏B_i の通常の Čech 複体が完全。
- **原典の証明**：Cor 2.14（v 層の判定法 ← Thm 2.9 の h 層の判定法：Rydh Thm 3.12、Raynaud–Gruson の平坦化、ネーター近似）と、抽象ブローアップ四角形の [BST13, Lemma 3.9]（固有射の連接コホモロジー、Artin–Rees のコホモロジー版、Stein 分解、Kollár の商）。BM18 も O_perf の v 降下は BS17 を引用しており、別証明はない。
- **可換環論で示せる部品**：(a) 付値環自身の v 被覆の Amitsur 複体の完全性、(b) 付値環の超積と Boolean 層での茎の判定、(c) 有限・整で V(I) の外で同型な場合（完全環の弱正規性と Milnor 四角形）。
- **核心**：A → ∏V_t（全付値の代表の積）の降下。完全性が本質的で（k[ε] では偽）、pure でもなく、定理そのものとほぼ同等。**初等的な証明は見つかっていない**（無いとは断言できない）。原典どおりなら Mathlib に無いスキームのコホモロジー論の土台から作ることになり、**5〜15 万行規模**（根拠は粗い）。
- **迂回の候補（推奨①、紙の検討が先）**：主定理の側で実際に使う excision は、CLMST の KL 標準 excision（有限・整で a の外で同型）だけに見える（`BhattScholze/Perfectoidization/Excision.lean`）。その場合だけなら (c) と tilt で Cor 8.12 を直接示し、arc 層性と 1a・1b をまとめて迂回できる可能性がある。ただし E3 の `excision` 欄は一般の `ArcOutside` で型が固定されている（10-26 以降の規約）ので、欄の特殊化はユーザーの決定。perfd は非 perfectoid 環で導来的に振る舞うので、直接証明が通るかは**未確認**。

## 4. 全体の見立て

| 件 | 推奨 | 規模 | ∞ 基盤 | 決定が要るもの |
| --- | --- | --- | --- | --- |
| D68 | 対象ごとの HT の命題に置き換えて直接証明 | 0.8〜1.5 万行 | 不要 | D68 の改訂 |
| BM18（1b） | G-A6-1 を O の場合に 1 圏で直接（経路 B） | 0.3〜0.6 万行 | 不要 | D56・D59 の改訂 |
| BS17（1a） | まず excision の欄を KL 標準の場合に絞る迂回を紙で検討 | 迂回できれば小〜中、できなければ 5〜15 万行 | 不要（迂回）／不要だがスキーム論が大 | E3 の `excision` 欄の特殊化 |

- 律速は BS17。迂回が通れば arc site の層性（A6 の大部分）と 1a・1b がまとめて主経路から外れ、A 全体が軽くなる可能性がある。
- 1 と 2 は ∞ の段階 II と独立に、古典的な単位として先行できる。
