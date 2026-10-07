# 調査ノート

元論文の書誌は `paper/SOURCE.md`。形式化の計画は `notes/PLAN.md`。詳しい調査メモは Claude Doc「Serre の交点重複度の正値性（OpenAI math 193）：調査メモ」（2026-10-07）。

## 主張（Theorem 1.1）

(R, m) を正則局所環、M, N を 0 でない有限生成 R 加群とする。length(M ⊗ N) < ∞ かつ dim M + dim N = dim R なら χ^R(M, N) = Σ(−1)ⁱ length Tor_i^R(M, N) > 0。標数・分岐の制限なし。

等標数は Serre を引用するだけ（Lemma 5.1）。新しいのは剰余標数 p > 0 の混標数の場合。

## 証明の流れ

1. 帰着（Lemma 5.1）：D = R/P、E = R/Q（正次元の完備局所整域、h + l = d、P + Q は m-準素）へ。Serre（等標数）と Roberts–Gillet–Soulé（消滅）を使う。
2. 置き換え1（Lemma 5.2）：D → C_D（perfectoid 化／完全化、正規化長さ λ の目で CM）。|G_D| a_D a_E χ(D, E) = Σ_σ c_σ。降下 Theorem 3.1 → Lemma 3.5。
3. 置き換え2（式 5.18）：パラメータ商 U = C_D/xC_D の有限近似 Mₙ（Lemma 5.3–5.4）、極小分解の切り詰め（Lemma 5.5）、ランク無視の圏（§4）。|G_E| c_σ = Σ_γ b_{σ,γ}。降下 Theorem 3.1 → Theorem 4.7。
4. 正値性（Lemma 5.6）：両側が λ の目で CM なので 0 次の項だけが残り、b_{σ,γ} > 0。

## 形式化の3層

| 層 | 中身 | 扱い |
| --- | --- | --- |
| 1. 論文固有の議論 | §5 全体、Lemma 3.4/3.5 の形式的部分 | sorry なしで形式化する第一目標 |
| 2. 論文の新しい一般定理 | Theorem 3.1、Theorem 4.7（§4） | 当面は名前つき axiom。人手の検証を最優先 |
| 3. 文献からの入力 | Serre、Roberts–Gillet–Soulé、Cohen–Gabber、Monsky、Roberts、CLMST、Land–Tamme、Bhatt–Scholze | `class` と `axiom` インスタンスで置く |

第一マイルストーン：主定理が層 2・3 の名前つき仮定だけから sorry なしで出る（`#print axioms` に名前つき仮定だけが出る）。

## 検証の重点

- [ ] Theorem 3.1（特に Lemma 3.2–3.3）：台つき有理 K 理論の有限忠実平坦降下と有限全射への拡張
- [ ] §4：商をとった後にだけ台をもつ対象・冪等元の像の上での長さの well-definedness（Lemma 4.2、Prop. 4.3、4.5）、Lemma 4.6 の dg 商
- [ ] Theorem 2.5 の混標数部分：CLMST Prop. 4.0.4 / 4.0.10 / 4.0.14 の仮定との照合
- [ ] 引用の照合：Land–Tamme、Skalit、Kurano–Roberts
- [ ] Editan の公開ポスト（2025-12-09）と Bhatt–Hochster–Ma の路線との比較

## Mathlib の現状（2026-10-07、mathlib `e6bbacd0`）

あるもの：

- 正則局所環 `IsRegularLocalRing`（`RingTheory/RegularLocalRing/Defs.lean`。定義は (maximalIdeal R).spanFinrank = ringKrullDim R）
- 加群の次元 `Module.supportDim`（`RingTheory/KrullDimension/Module.lean`）、環の `ringKrullDim`
- 長さ `Module.length`（ℕ∞ 値、`RingTheory/Length.lean`）、`FiniteLength`
- Tor：`CategoryTheory.Tor C n`（`CategoryTheory/Monoidal/Tor.lean`）。モノイド的アーベル圏の第2成分の左導来関手として定義。API はほぼなく、第1成分で導来した `Tor'` との同型も未証明
- Ext と射影次元（`Algebra/Category/ModuleCat/Ext/`、`ProjectiveDimension.lean`）、正則列（`RingTheory/Regular/RegularSequence.lean`）
- Noether 正規化、完備化（`AdicCompletion`）、`Perfection`、perfectoid の初歩（untilt、Fontaine θ、B_dR）
- 三角圏とその局所化、導来圏、スペクトル系列（SpectralObject）
- `HomologicalComplex.eulerChar`（ただし finrank ベースで、長さではない）

ないもの：

- Koszul 複体、パラメータ系、Hilbert–Samuel 重複度、Cohen–Macaulay 環
- 極小自由分解、Cohen の構造定理、優秀環
- 長さで測る Euler 特性、Serre の交点重複度
- 代数的 K 理論、perfectoid 化と almost 数学、正規化長さ

主張を書くための方針案：`Tor (ModuleCat R) i` の対象を R 加群として見て `Module.length` をとり、χ を i ≤ dim R の有限和として自前で定義する。`Tor` の API 不足（対称性、長完全列、平坦基底変更）は層 3 の仮定として置くか、必要な分だけ証明する。

## 次にやること

- [x] Mathlib の現状調査（上記）
- [x] Theorem 1.1 の Lean での主張を書く（`SerrePositivity/Statement.lean`。未コミット）
- [x] 命題の依存グラフと各命題の層の割り当て（`notes/PLAN.md` §4）
- [x] M0：主張をソースに置く（`Tor.lean`、`EulerChar.lean`、`Statement.lean`）
- [x] M3 の骨格：§5.1 のデータ `CoreData` と `c_σ` の定義、Lemma 5.2・(5.18)・Lemma 5.6 の主張から核の場合を出す `chi_pos`（`SerrePositivity/Core/`）
- [ ] M0：`Inputs/` の骨格と公理監査の CI を足す（`notes/PLAN.md` §9）
- [x] Lemma 5.2 トラックの定義と主張（`notes/PLAN.md` §10）：Koszul 複体、パラメータ系、重複度、台つき完全複体と評価、ひねり、幾何ファイバーの推移性、Theorem 2.5・Cor 2.6・Lemma 3.4・3.5 の主張、`IsPaperData`
- [x] Lemma 3.4 の抽象版 `lemma_3_4_of_isWeaklyRegular` を標準公理のみで証明（`notes/PLAN.md` §11）。Koszul 複体の完全性・分解・基底変更・`Tor` との同一視、Tor の長完全列（写像錐による）、Tor が消去イデアルで消えることを含む
- [ ] `Setup34` 版 `lemma_3_4` と Cor 2.6 の 1・2 が依存する層 3a の二つの `sorry`（A1：正則パラメータ系は正則列、`m_T^N ≤ m_A T`）の証明、Cor 2.6 の 3
- [ ] K₀ と Theorem 3.1、Lemma 5.2 の証明の骨格（`notes/PLAN.md` §10.2–10.3）
