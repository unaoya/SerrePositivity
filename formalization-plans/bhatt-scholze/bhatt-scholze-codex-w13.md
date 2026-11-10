# Codex 作業指示書 BS-W13：§10 の古典的な部分（A8-1・A8-3 と、A8-2・A8-4 の perfd に依らない入力）

作成：2026-11-07 夜（段階 II の調整役）。宛先：⑤a BS 実装の Codex（BS-W12 の続き、同じチャット・worktree `../SerrePositivity-bs-impl`・枝 `math/bs-impl`）。検収：調整役。設計は `a8-design.md`（§1 の表、§3、§4 の G-A8-1〜11、§7 の決定）。

## 0. 目標と範囲

BS 著者版 §10.2 のうち、**導来の perfectoid 化（A4〜A7 の perfd）に依らない部分**を本体に入れる。perfd を使う組み立て（Thm 10.9 の J-almost 連結性、Thm 10.11、E3 の `integral`）は、A6・A7 が main に入るまで drafts に残す（BS-W12 の B6 と同じ扱い）。

当初の予定（BS-W11 §7 の 2）は「A8-1・A8-2」だったが、A8-2 は A6（Cor 8.12）と A7 に依るので組み立ては先に進めない。代わりに、独立した古典的な単位 A8-3（Lemma 10.12）と、A8-2・A8-4 の入力のうち perfd に依らないものを入れる。

| 部品 | 内容 | 原典 | 置き場所 |
| --- | --- | --- | --- |
| **C1**（A8-1） | Prop 10.4 の複体版（導来 p 完備な複体 M について、全 H^i が J-almost 零 ⇔ J_perfd ⊗̂^L_R M = 0）、Lemma 10.5（連結 ⇔ M ⊗̂^L R/J_perfd が連結かつ J-almost 連結）、G-A8-1 の系（J-almost 連結 ⇔ K ⊗̂^L M が連結）、J-almost の √J 不変性。drafts `A8/AlmostConnectivity.lean` の型 | Prop 10.4、Lemma 10.5 | `BhattScholze/Almost/`（既存の `PerfectoidAlmost`・`Lemma103` の隣） |
| C1′ | J-almost の「生成元ごと」と「忠実平坦な底変換で反映」（G-A8-2）。Prop 8.5 系 4・Prop 8.13 を使う部分は drafts に残す。使わずに済む部分があれば本体へ | Rem 10.7 の隣 | 同上 |
| **C2**（A8-3） | Lemma 10.12（有限表示有限 R → S（Z_(p) 代数）の層別 g_1..g_n、原典どおり）と G-A8-4（普遍同相の定義と標数 p での判定：核は nil、各元の p 冪が像に入る）・G-A8-5（完全 F_p 環から被約環への普遍同相は同型）・G-A8-7（層別の底変換不変性） | Lemma 10.12 | `CommutativeAlgebra/` の新しい下位ディレクトリ（例 `UniversalHomeomorphism/`、`FiniteEtaleStratification/`） |
| **C3** | perfd に依らない入力：G-A8-6（perfectoid 環上の有限エタール代数は perfectoid）、G-A8-8（perfectoid 環の p 完備化した filtered 余極限は perfectoid、導来完備化は離散）、G-A8-9（整代数は有限表示有限代数の filtered 余極限）、G-A8-11（局所化を固定した有限表示有限近似）、G-A8-3′・3″（比較環の有限性・完備性、整写像の `ArcOutside`）、G-A8-10 のうち環論の部分（S → T の整性、S → T・S → T̂ の ArcOutside、T̂ の離散性と完備性。§3 の 3） | Thm 10.9・10.11 の証明の部品 | `BhattScholze/Perfectoid/` などの隣、一般性があれば `CommutativeAlgebra/` |
| C4 | Thm 10.9 の J-almost 連結性と Thm 10.11 の組み立ての型を drafts で整え、C1〜C3 の型と合っているかを確かめる | Thm 10.9、Thm 10.11 | **drafts に残す** |

## 1. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | 紙の確認：C1′ のどこが Prop 8.13 なしで示せるか、C2 の主張の型（drafts に型がないので新しく書く）、C3 の各部品の型と置き場所、規模の見込み | **停止点 0**：調整役が確かめる |
| 段 1 | C1（と、本体に入れられる C1′） | 停止点 1 |
| 段 2 | C2 | 停止点 2 |
| 段 3 | C3 | 停止点 3 |
| 段 4 | C4 | **停止点 4**：BS-W13 の区切り |

- 停止点 0 は承認を待つ。段 1〜4 は BS-W12 §3 と同じ条件（対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない）なら、報告してそのまま次へ進んでよい。取り込みは調整役が停止点ごとに行う。
- 型を drafts から変える必要があれば止める。

## 2. 規則

BS-W11 §6・BS-W12 §4 と同じ（新規ファイルだけ、本体に sorry を残さない、閉じられない宣言は drafts に残す、E3 非依存、入口と監査への登録は調整役、docstring は日本語の 概要／方針／規約／使われ方 と論文の番号、小さなビルドだけ、鍵を通す）。報告は `report-codex-w13.md`。

追加の規則（11-07 夜）：**E∞ の作り方が未決**（`research/einfinity-route/README.md`）。CAlg_R の模型の中身（Barratt–Eccles の作用、cofibrant な代表、hammock の単体）に新しく触れる宣言は作らない。§10 は D(R) と環の議論で足りるはずなので、CAlg_R が要りそうになったら止めて報告する。

## 3. 追記（2026-11-07 夜、調整役）：停止点 0 の承認

**承認**：段 0 の報告（`report-codex-w13.md`、52d962dc3）。段 1 に進んでよい。段 1〜4 は §1 の条件で、報告してそのまま次へ進んでよい。

1. **C1′**：完備テンソルで、生成元ごとの判定と完備忠実平坦な底変換での反映を Prop 8.13 なしで示す経路でよい。`CompletedTensor.lean` の模型と drafts の `DVertex` の完備テンソルの比較が段 1 で取れなければ、そこで止めて報告する。
2. **C2**：Lemma 10.12（`EtaleStratification/Stratification.lean` の `exists_finiteEtaleStratification`、BS-W10 B-3）と G-A8-4・5・7（`UniversalHomeomorphism/`・`EtaleStratification/`）は本体にある。新しく書くのは C4 で要る包装だけ。G-A8-6 も BS-W11 の `isIntegralPerfectoid_of_finiteEtale` で済み。段 2 は包装が要るときだけ行い、要らなければ段 3 へ進む。
3. **G-A8-10 の整性**：報告の反例のとおり、S → T̂ は整とは限らない。§0 の表の C3 の行の初版の「S → T・S → T̂ の整性と ArcOutside」は誤りで（表は直した）、正しくは「S → T は整、S → T と S → T̂ は ArcOutside、T̂ は完備」（a8-design §4 と drafts のとおり）。Cor 8.12 の界面（`perfectoidization_excision_of_disc`）が要求するのは完備性と ArcOutside だけで、整性は要らないので、Thm 10.11 の組み立てに影響しない。
