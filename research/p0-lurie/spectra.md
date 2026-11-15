# スペクトルの ∞ 圏 Sp：文献での扱いと、現状の形式化

作成：2026-11-15（調整役）。`README.md` の §3.1 で「Sp の模型が弱い」とした点の掘り下げ。原典は HA（math.ias.edu/~lurie/papers/HA.pdf、11-15 取得）§1.4.2〜1.4.4・§4.8。コードの棚卸しは読み取りの調査（11-15）。

## 1. 文献での扱い

### 1.1 HA の定義（∞ 圏の側）

- **安定化 Sp(C)**（Def 1.4.2.8）：有限極限を持つ ∞ 圏 C に対し、C の**スペクトル対象**は縮約かつ切除的な関手 X : S^fin_* → C。Sp(C) := Exc_*(S^fin_*, C)。Rem 1.4.2.9：Sp(Fun(K, C)) ≃ Fun(K, Sp(C))。
- **Sp(C) は安定**（Cor 1.4.2.17）。Rem 1.4.2.18：Sp(C_*) ≃ Sp(C)。普遍性（Lemma 1.4.2.19 以下）。
- **別の表し方**（Rem 1.4.2.24–25、Ex 4.8.1.23）：Sp(C) は塔 … → C_* →^Ω C_* →^Ω C_* のホモトピー極限。つまり「点つき対象の列 X(n) と同値 X(n) ≃ ΩX(n+1)」= Ω スペクトル。Prop 1.4.3.6 (3) の証明もこの描像を使う。
- **Sp := Sp(S_*)**（Def 1.4.3.1）。Rem 1.4.3.2：hSp は古典的な安定ホモトピー圏。
- **Prop 1.4.3.6**：(1) Sp は安定、(2) Ω^∞ X が可縮な X のなす Sp_{≤−1} が accessible な t 構造を定める、(3) 左右に完備で、heart は Ab。
- **Prop 1.4.4.4**：C が presentable なら Sp(C) は presentable、Ω^∞ は左随伴 Σ^∞_+ を持つ。Cor 1.4.4.5：Σ^∞ : S → Sp の普遍性（Sp は S を安定にした自由なもの。安定 presentable な D への余極限保存関手は Sp での評価で決まる）。
- **smash 積**（Prop 4.8.2.18、Cor 4.8.2.19）：(Sp, S) は Pr^L の idempotent 対象。Sp には、⊗ が各変数で小さい余極限を保ち、単位が球スペクトル S であることで一意に決まる対称モノイダル構造がある。安定 presentable で各変数が余極限を保つ対称モノイダル C への対称モノイダル関手 Sp^⊗ → C^⊗ が一意に存在する。Rem 4.8.2.20：安定 presentable な ∞ 圏はすべて Sp 上にテンソルされる。
- **Mod_k**（HA 7.1）：E∞ 環 k の加群スペクトルの ∞ 圏。k が離散可換環なら Mod_k ≃ D(k)（HA 7.1.2.13）。Mod_k は安定 presentable 対称モノイダル（相対テンソル）。DAG XIII の P⁰ の構成はこの Mod_k の上で行われ、結果をスペクトルの射と見る（`README.md` §1.3）。

### 1.2 模型（モデル圏の側）

- **Bousfield–Friedlander（1978）**：点つき単体集合の列 X_n と構造射 ΣX_n → X_{n+1}（BF スペクトル）に安定モデル構造。fibrant–cofibrant な対象は「各段が Kan、構造射が単射、随伴 X_n → ΩX_{n+1} が弱同値」の Ω スペクトル。KST の `OmegaSpectrum` はこれ（§2.1）。
- **対称スペクトル（Hovey–Shipley–Smith 2000）**：対称列の Day 畳み込みの上の球スペクトルの加群。smash 積がモデル圏の段で対称モノイダル（BF スペクトルでは smash 積が点ごとに作れない、という問題の解決）。安定モデル構造は level モデル構造の左 Bousfield 局所化。`Spectra/SymmetricSpectrum` はこれ（§2.2）。
- **MMSS（Mandell–May–Schwede–Shipley 2001）**：直交スペクトル・対称スペクトル・W 空間などの模型の比較。安定ホモトピー圏の同値。
- **HA の対称モノイダル構造との関係**：対称スペクトルの安定モデル構造を局所化した ∞ 圏は Sp に同値で、smash 積は Cor 4.8.2.19 の構造を与える（HA 4.1.7.4 と 4.8.2.19 の一意性）。この比較を形式化するには、モデル圏の局所化と ∞ 圏の対称モノイダル構造の両方が要る。

### 1.3 原典の P⁰ に Sp が要る形

DAG XIII §2.2（`README.md` §1）で使うのは次の性質だけ：C = Mod_k が安定・有限 groupoid 添字の極限と余極限を持つ・対称モノイダルでテンソルが exact・perfect な対象からの左 Kan 延長（Ind）が取れること。結果 P⁰ を「スペクトルの射」と見るのは、k 線形でないから（Warning 2.2.8）。**構成そのものに Sp の対称モノイダル構造は要らず、要るのは Mod_k の対称モノイダル構造**である。

## 2. 現状の形式化

### 2.1 KST の `Sp`（BF 型 Ω スペクトルの coherent nerve、1,451 ファイル）

| 項目 | 状態 |
| --- | --- |
| `OmegaSpectrum` | 段 `level n : PointedKanComplex`、`sigma n : Σ(level n) ⟶ level (n+1)`、`sigma_mono`、`omega_condition`（随伴 X_n → ΩX_{n+1} が全基点で π_* 同型）。BF の fibrant–cofibrant な Ω スペクトル |
| `Sp := SimplicialNerve OmegaSpectrum`、`sp_quasicategory` | 写像空間は段ごとの点つき Hom の塔の逆極限。局所 Kan 性から準圏（HTT 1.1.5.10） |
| 零対象・有限極限 | `sp_hasZeroVertex`、`sp_hasFiniteLimits`、`sp_fiber_exists`（coherent な cospan の極限から） |
| **安定性** | `sp_isStable (hB : NativeLoopComparison)`。**条件つき**。`NativeLoopComparison` は `FunctorIso (coherentNerveMap commonRefinedEnriched) (commonNativeLoopEndpoint ≫ nativeLoop)` の型で、その値（B）は未供給。`nativeLoopComparisonOfBoundaryHomLift` は `boundaryComparisonHomLiftSquare.HasLift`（境界つきの相対関手 Hom の延長）を仮定する。KST のレーン Sp-2（L9b）・Sp-2b（L9d）は 10-28 からこの入力待ちで止まっている |
| 有限余極限・cofiber・Σ・presentable | **なし**（安定性が出れば cofiber と Σ は従う） |
| smash 積・対称モノイダル・D(A) によるテンソル | **なし** |
| HA の Sp（縮約切除関手）との比較 | なし（cite の注記にそう書いてある） |
| ホモトピー群 | `SpectrumHo.piFunctor (j : ℤ)`、`stableFiberLongExact` |
| 利用者 | KST の局所化不変量（`IsLocalizingInvariant (E : StableInfinity ⟶ Sp)`）、S 構成の K 理論の値（約 120 ファイル）、`EInfinityTheory.toSpectra`、EInfinity/PowerOperation の EM 関手 |
| 主定理との関係 | 主定理の import 閉包（Paper/、Statement、1,162 モジュール）に KST・Spectra・EInfinity は**含まれない**。主定理は Sp に依存しない |

**無条件の安定性に欠けているのは `NativeLoopComparison` の値一つ**。零対象・有限極限・`nativeTailEquivalence`・一般の判定 `isStable_of_loopEquivalence` はそろっている。

### 2.2 `Spectra/`（対称スペクトル、モデル圏、279 ファイル）

| 項目 | 状態 |
| --- | --- |
| `SymmetricSpectrum`、`GeneralSymmetricSpectrum C K` | 対称列（Day 畳み込み）の上の球スペクトルの加群。C = 点つき単体集合、K = 円で旧版と一致 |
| smash 積 | `sphereTensorMonoidalCategory`・`sphereTensorSymmetricCategory`・`spectrumMonoidalClosed`。**1 圏として**対称モノイダル閉。単体的豊穣、tensor・cotensor、`suspensionLoopAdjunction` |
| level モデル構造 | `levelModelCategoryOfGenerators`、`exists_leftProper_combinatorial_levelModel`。グローバルな instance は登録せず |
| 安定モデル構造 | `StableModelPresentation`（左 Bousfield 局所化の提示）と `exists_stableModelPresentation : Nonempty …`。**存在補題で instance ではない**。`fibrant_iff … ↔ IsFibrantOmegaSpectrum` |
| 懸垂とループ | `exists_ordinarySuspensionLoopEquivalence`（ホモトピー圏 `W.Localization` の上、1 圏の主張） |
| **前提** | これらは `[ModelCategory SSet]` と cofibration・fibration・弱同値のクラスの同定を仮定引数に取る。具体化は `kanQuillen_model_exists := by sorry`（Hovey 3.6.5 の引用）だけ。`no-model-structure-on-sset` の方針（主経路に `[ModelCategory SSet]` を置かない）と衝突する |
| ∞ 圏化、KST の Sp との比較 | **なし**。Spectra/ から coherent nerve や局所化で ∞ 圏を取り出す構成はない。外部の利用は `ModelCategoryComparison/Inputs/SimplicialLevel` 一か所（level モデルの具体化、利用者なし） |

### 2.3 D(A) の側（代替の候補）

| 項目 | 状態 |
| --- | --- |
| `derivedInfinityCategory_isStable`、`derivedInfinityCategory_isPresentable` | **無条件**で済 |
| 対称モノイダル構造 | `Tensor/Fixed.lean` の `tensorWith`・`tensorWithSymmetry`（固定した対象とのテンソル関手と対称性）だけ。(∞,1) の対称モノイダル構造（coherent な結合子・単位子、N(Fin_*) 上の構造）は**なし** |
| D(A) の中の群作用・BG 添字の極限と余極限 | 一般の小さい図式の極限・余極限はある（presentable）。群作用を BG → D(A) として扱う部品はない（G10 系は Δ・Δᵒᵖ の図式） |

## 3. 整理

### 3.1 P⁰ のために Sp に何を求めるか

原典の構成（§1.3）は Mod_k = D(k) の上で行う。Sp は「P⁰ は k 線形でないので、スペクトルの射として述べる」ために最後に出てくるだけ。したがって **P⁰ の定義のために Sp の対称モノイダル構造や presentable 性は要らない**。要るのは：
1. D(F_p) の上の、Tate 構成（BG 添字の極限・余極限と norm）、拡大冪（対称モノイダル構造）、Ind・compact からの左 Kan 延長。
2. D(F_p) → Sp の忘却 V（既存の `eilenbergMacLaneDerived`）が、P⁰ を運ぶ先として使えること。P⁰ の値の計算（Rem 2.2.7）は π_n の上で行うので、V の π/H 比較（済）で足りる。
3. BS の利用（Lemma 8.4）で、V が実現・Tot・完備化の極限・余極限を保つこと（M10）。これは Sp の安定性（cofiber・極限の存在と保存）を使う場面があり、`sp_isStable` が条件つきなことが響きうる。

### 3.2 Sp の弱さがどこに響くか

- **界面の `toSpectra` の型が `⟶ KST.Spectra.Sp`**で、Sp の安定性が条件つきなので、Sp の中で極限・cofiber を使う主張は `NativeLoopComparison` を引数に持つことになる。D79 (i) で P⁰ を Sp 値にしたとき、この点は検討されていない（`README.md` §3.1）。
- KST（K 理論）は `Sp` を値域にしていて、同じ条件を抱えている。KST は段階 II では後回し（`stage-ii-focus`）。
- 主定理の閉包は Sp に依存しないので、Sp の弱さは主定理に直接は響かない。E3 の証明（⑤∞）が P⁰ を通して Sp に依存するようになると、そのとき初めて響く。

### 3.3 選択肢（決めない）

- **(A) Sp を直す**：`NativeLoopComparison`（境界つき相対関手 Hom の延長定理）を供給して安定性を無条件にし、さらに有限余極限・presentable・（必要なら）対称モノイダル構造を作る。KST のレーンの未完の仕事と同じ。HA の Sp（Def 1.4.3.1）との比較も、忠実さの意味では別に要る。
- **(B) P⁰ の構成は D(F_p) の中で完結させ、Sp は結果を述べる先だけにする**：D(F_p) の対称モノイダル構造（M3）を作る必要は残るが、Sp の側に要るのは V と π/H 比較（済）と、Lemma 8.4 で使う極限・余極限の保存（M10、ここは Sp の安定性に触れる）。
- **(C) P⁰ を Sp 値ではなく D(F_p) 値の「Frobenius 半線形」な射として述べる**（⑤a §63.3 の案 1）：原典より強い主張になるので、Lurie の構成から持ち上げる定理が別に要る。忠実さからは外れる。

原典に沿うなら (B) が基本で、Sp の弱さは (A) のうち「安定性の無条件化」だけが、M10 のところで要るかを見極める、という順になる。

### 3.4 HA §1.4 の対応表の状態

`research/ha-coverage/review/ch1.csv`：1.4.2.8（Sp(C) の定義）・1.4.2.17（安定）・1.4.3.1（Sp）・1.4.3.6（安定・t 構造）は、KST の `OmegaSpectrum`・`Sp`・`sp_isStable` を partial として対応させている（「Lean が強い：点つき Kan 空間の具体模型」「NativeLoopComparison を仮定」の注記つき）。1.4.4.4（presentable、Σ^∞_+）・1.4.4.5（普遍性）・4.8.2.18–19（smash 積）・4.8.1.23（Sp(C) ≃ C ⊗ Sp）は none。
