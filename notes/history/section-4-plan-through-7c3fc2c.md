> 2026-10-12 に保存した履歴資料。当時の計画・状態・検証数値を保持する。
> 現在の状態は [status.md](../status.md)、作業方針は [PLAN.md](../PLAN.md) を参照。

# §4 の形式化計画

2026-10-11 の整理：抽象化で置き換わった旧比較層・補助証明を削除した。
以下の過去の実施記録には削除前の名前を残す。現行の置換先と保持理由は
[整理記録](../cleanup-candidates-2026-10-11.md) を参照。

## 現在の作業範囲：抽象化と二つの実現に集中する（2026-10-10 方針変更）

ユーザーの指示により、論文全体の形式化は後の課題とし、付録 B・C の共通理論と、
perfect 複体版・ランク無視版への適用を当面の対象とする。この節を実装順の正本とする。
以下の記録にある核心定理や正規化基底の存在構成を「次に進める」という方針は更新された。

既存の抽象 Euler 評価、反復錐、対称比較、二つの実現の主要な消滅・下界は再利用する。
直近に進めた§5の具体的な正値性への接続も保存するが、その先の存在構成は当面進めない。

### 概念的な定義との接続と今回の区切り（2026-10-11）

最後の残作業だった λ-平坦性・λ-CM 性からの入力供給を実装した。

1. `IntersectionMultiplicity/NormalizedTor.lean`：任意の局所環上で、剰余体の正次数 Tor の
   長さ零と λ-平坦性が同値。零次の有限性は不要。有限な剰余体での値を加えると、
   組成列の帰納法で全有限長加群の Tor の長さを計算する。零次 Tor と通常の
   テンソル積を同定し、テンソル積のランク条件も剰余体で判定する。
   既存の `normalizedLength_tor_of_isWeaklyRegular` はこの一般論の適用に移した。
2. `CommutativeAlgebra/RegularSequencePowers.lean`・`RegularSequenceLength.lean`：
   Noether 局所基底の極大イデアル内の弱正則列について、正の冪でも正則であることと、
   商の長さが `v^(列の長さ)` 倍になることを証明。極大イデアル生成元では商の長さは `v^e`。
   重複度の未証明公式は利用していない。
3. `LengthAlgebra/Flat.lean`：`flat_rank_iff_koszul` が座標によらない条件と一乗の
   Koszul 条件の同値を与える。全ての正の冪での商の値・`KoszulAcyclic`・`KoszulFinite`、
   および `koszulEuler = r.toReal` を個別に証明。有限生成イデアルと根基条件の補題も供給する。
4. `LengthAlgebra/CohenMacaulay.lean`：任意のパラメータ系の λ-CM 条件を、
   パラメータの正の冪にも適用して共通入力を得る。有限な単射 `A → D` では、
   パラメータの移送と `restrictToBase` を使い、基底上の λ-平坦性と有限ランクを証明した。
   `D` 全体での λ-CM 性と一つの基底に相対的な λ-平坦性との逆向きの同値は主張しない。
5. `LengthAlgebra/FlatRealization.lean`・`Paper/Section4/FlatRealization.lean`：
   上の共通入力から、二つの実現の共役和比較・範囲外の消滅・極小 Euler 下界へ接続した。
   ランク版も `A → S → C` と一般の `S` 上の自由複体列を扱う。
   下界は既存の対象としての消滅・第零次評価を通る。一般の比較・消滅定理は弱い条件を維持する。
   旧 `normalized_koszul_finite` も共通の `koszul_finite_of_zero_positive` の適用にした。

以上の接続と検証までを今回の抽象化の一区切りとする。仮定は個別の引数で、
専用の仮定束や新しい `sorry` は導入していない。基底の正則列・Koszul 分解と降下は
明示的な入力であり、正則局所環から分解を供給する既存の引用は別に残る。
反復錐の二項係数表示への並べ替え同型と `ι` の独立した入口はユーザーの指示により
完了条件から削除しており、追加実装の予定には含めない。

検証：`lake build` は3484ジョブで成功。新規・変更した35宣言を `#print axioms` で監査し、
全て `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` を含まなかった。
これは今回の接続の監査であり、既存の正則パラメータ・降下などの引用を証明したことは意味しない。
今回の抽象化の完了条件はここまでで満たした。

### 完了した実装段階

1. **P3：二つの長さの商を同定する（完了）。**
   `LengthAlgebra/FiniteQuotientEquivalence.lean` で `finiteQuotientInclusion` の
   完全忠実性と本質的像を証明し、大きな商の有限長さ部分との圏同値を構成した。
   長さの保存、商関手との可換性、perfect ホモロジーの自然同型、
   消滅条件・Euler 数・K₀ 評価の一致まで定理として使える。
2. **P4：perfect 複体の支持の対応を完成させる（完了）。**
   任意の可換環上の有界有限射影複体について、ホモロジーの幾何学的支持と、
   指定したスカラーの冪がホモトピー圏で零作用する条件との同値を証明した。
   Noether 性やホモロジーの有限生成性を仮定せず、実際の `PerfectHomotopy` の
   全対象に対する判定も構成した。有限自由版はその特殊例となる。
3. **P1/P4–P6：Euler 加法性と K₀ 評価の移行（2026-10-11 実装）。**
   長完全列の共通定理を抽出し、`lambdaEuler_cone` と三角圏の加法性の両方を
   その適用にした。旧定理に perfect 性や Koszul 条件は追加していない。
   旧有限自由 K₀ の通常・正規化評価と共通評価の引き戻しとの一致を証明し、
   ランク商・Karoubi 包絡・完備化後の支持圏の K₀ 評価は共通構成で定義した。
   数値の公開定義と、具体的な計算に必要な補題は保持する。
4. **P7/P8：入力境界と対応の照合（2026-10-11）。**
   二つの実現の支持、有限性、Koszul 条件、基底公式、降下、第零次全射の境界を
   下の表に記録した。主な比較・消滅・下界は共通定理を通る。
   有限自由／有限射影 K₀ の比較についても、係数変更との可換性・群作用の
   同変性・局所環での降下入力の移送を証明した。
   数学的な留保と未証明入力は下に明記する。本文・付録もこの構成へ更新した（下記の文書整理の記録）。

§5に必要な環・正規化基底・ガロア閉包の構成、定理2.5の具体的存在証明の続行、
`core_statement`・`main_statement` の完成は今回の完了条件に含めない。
降下を入力にした抽象比較と、その入力を具体的幾何から供給する証明も区別する。
既存の未証明入力を新たに証明する方向へ、作業範囲を自動的に広げない。

新しい `sorry` や仮定の束を導入せず、Lean の変更はモジュール単位で検証し、
実装の区切りで全体 `lake build` と新規・変更定理の公理監査を行う。
方針変更時には計画文書のみを更新した。その後の Lean 実装を以下に記録する。

### 共通加法性と新旧 K₀ 評価の接続（2026-10-11）

- `CategoryTheory/ExactSequenceEuler.lean`：アーベル圏の長完全列について、
  同型不変・短完全列に加法的・零対象で零となる実数値評価の Euler 加法性を証明。
  三つの対象列のうち第二・第三の有界性だけで足り、正値性は使わない。
  `HomologicalEuler.homologicalEuler_triangle` はこの定理の適用にした。
- `LengthAlgebra/ExactSequenceEuler.lean`：冪ねじれ性と長さの有限性を確認した
  加群列を `FiniteLengthTorsion` に入れ、充満忠実な包含による完全性の反映を使って
  共通定理を適用する。任意の加群を扱い、有限生成性・射影性は要求しない。
- `PerfectComplex/NormalizedEuler.lean`：`lambdaEuler_cone` を上の定理へ移行し、
  重複していた像の長さの計算と交代和の相殺を削除。
  `chiOrd_cone`・`chiLam_cone_of_finite` もこの証明を通る。
  旧定理の仮定と数値定義は保持した。有限性の前提を外した場合の
  `toReal`・`finsum` の規約は、新しい有限な Euler 関手の意味とは区別する。
- `LengthAlgebra/EulerCompatibility.lean`：`chiOrdHom` と有限射影圏の共通評価の
  引き戻し、および `chiLamHom_of_finite` と `freeBaseChangeEulerK0` の一致を証明。
  通常版には Noether 性と支持イデアルによる商の Artin 性を使うが、局所性は不要。
  正規化版は新旧両方の評価を定義できる仮定のもとで同じ準同型であると述べる。
- `Asymptotic/RankEulerAdditivity.lean`・`CompletedEulerAdditivity.lean`・
  `CompletedRankEvaluation.lean`：数値評価と共通 `homologicalEuler` の一致、
  シフト列の有界性を独立した補題にした。三つの K₀ 評価の定義を
  `homologicalEulerK0` に統一し、既存の対象上の計算式と
  Karoubi 包絡への制限の等式を維持した。
  `paperRankEulerK0`・`paperBaseChangeEulerK0` はこの共通構成の引き戻しとなる。
- `PerfectComplex/K0Functoriality.lean`：恒等係数変更の自然同型を構成し、
  `freeToPerfectK0_changeRing` で有限自由／有限射影 K₀ 比較と係数変更の可換性を証明。
  パラメータを固定する自己同型に沿う実際の三角関手 `perfectTwist` から
  有限射影 K₀ の群作用を構成した。旧側の逆元による係数制限と新側の係数拡大を
  自然同型で結び、`freeToPerfectK0_smul` で同変性を証明した。
  ここまでは任意の可換環でよく、有限群であることも要求しない。
  係数環が局所環なら逆比較も同変で、`perfectK0_descent_of_free` により
  旧有限自由 K₀ の降下を有限射影版へ移せる。降下自身は明示的な入力のままとする。

### 二つの実現の入力境界（2026-10-11 照合）

表の「入力」は定理の明示的な仮定であり、結論の代用として追加した公理ではない。
一般定理で入力を受け取ることと、論文の具体的な環からそれを供給することを分ける。

| 付録の確認項目 | 入力として指定するもの | 実現側で証明するもの・主な入口 |
| --- | --- | --- |
| perfect：支持 | 有界有限射影複体とホモロジーの幾何学的支持 | スカラーの冪の零作用との同値。`PerfectComplex/Support.lean`・`HomotopyCategory.lean`。任意の可換環で成立 |
| perfect：有限 Euler 評価 | `J.FG`、支持イデアルの根基への包含、全ての正の冪の `KoszulFinite` | 各ホモロジーの冪ねじれ性・有限性、商値のホモロジー関手、シフト・有界性、旧 Euler 数との一致。`LengthAlgebra/PerfectHomology.lean` |
| perfect：二つの商の一致 | 上と同じ有限性条件 | `FiniteQuotientEquivalence`・`PerfectHomologyComparison` が有限商と大きな商の有限部分を同定し、長さ・零対象・Euler・K₀ 評価を一致させる |
| perfect：消滅 | 指定したスカラーの零ホモトピー、項の振幅、環自身の高次 Koszul ホモロジーの長さ零 | 有限射影項のフィルトレーションで (Kosₘ) を確認し、反復錐から消滅。`lambdaHomology_projective_vanishing` は Koszul 有限性を使わない |
| perfect：下界 | Euler の有限性、振幅 `[-e,0]`、零次の全射。具体的な全射には微分の極小性・零次項の基底を指定 | 消滅・第零次同型と全射の長さの単調性。極小性からの全射も `PerfectMinimalLowerBound` で構成し、他の項に自由性は要求しない |
| 共通：基底公式 | Noether 局所基底、`(z)=m`、`IsKoszulResolution z`、係数側の Koszul 有限性 | `KoszulFormula` により係数 `eλ(z;C)` の公式。高次消滅や `eλ=rank` はこの一般公式の仮定にしない |
| 共通：対称な比較 | 二つの Koszul Euler 数の一致、評価元の K₀ の有限群作用、不変類の整数倍の降下 | `perfectEuler_conjSum_eq`・`symmetricPaperEuler_conjSum_eq`。群論の `conjSum_eq` を共有し、係数環への群作用や長さの不変性は要求しない |
| perfect：旧群作用・降下の接続 | 支持パラメータを固定する環の群作用。降下の移送には係数環の局所性と旧 K₀ の降下 | `K0Functoriality` が実際の作用を構成し、K₀ 比較の同変性・係数変更との可換性から降下を移送する。任意の環で比較写像が同型とは主張しない |
| ランク：評価先と局所化 | 正の基準列 `s`、`atTop` に沿う超フィルター、長さ・根基条件・Koszul 有限性 | `SequenceHomologyBounds` が有限性と `O(s)`・`o(s)` を証明。`SequenceHomologyLocalization` が分母の可逆化とホモロジー的関手を構成 |
| ランク：完備化・有界性 | 上の入力と実際のランク商 | `CompletedHomology`・`RankHomologyShiftNatural`・`CompletedRankEvaluation` が冪等完備化への延長、自然なシフト比較、対象ごとの有界性、共通 Euler 評価を与える |
| ランク：全対象での基底公式 | 上記の基底の Koszul 分解 | `supportedRank_isIdempotentComplete_of_koszul` により一様な代表へ帰着し、各段の有限版公式を正規化極限へ移す。`koszulPaperEulerK0_changeRing` はランク K₀ 全体が一つの Koszul 類で生成されるとは仮定しない |
| ランク：消滅 | 商での支持・スカラーの零作用、共通振幅、各段の Koszul 消滅 | `RankVanishing`・`PaperVanishing` が (Kosₘ) と反復錐を接続。元の複体列の一様支持は不要で、Koszul を掛けた列の一様支持を証明して使う |
| ランク：下界 | 上記と微分の極小性、パラメータの冪を含むイデアル | `RankMinimalLowerBound`・`PaperMinimalLowerBound` が第零次全射と正規化極限の単調性から階数の極限による下界を得る |
| §5：有限近似からの正値性 | 有限近似の長さの収束、一様な消去イデアル、係数側の正の商長さなど | `paperEuler_pos_of_finiteApproximation` などが生成元数の正の極限を導き、上記の下界を適用。元の素イデアル商から全データを存在構成することは現在の範囲外 |

付録の `prop:check-perfect-euler`・`prop:check-perfect-comparison`・
`prop:check-perfect-vanishing` と、対応する三つの `prop:check-rank-*` の
仮定確認は上記の経路で追跡できる。有限自由と有限射影の K₀ 同型は局所環上のみ。
任意の環では `freeToPerfectK0` という比較写像を使う。
反復錐の分裂は二項直和を反復する表示を使う。消滅・二項係数の長さ公式・下界は
この再帰表示から証明済みであり、別の並べ替え同型は作業項目に含めない。

未証明入力の境界は以下のとおり。

- 明示した `IsKoszulResolution` と降下を引数に取る共通比較は、これらを証明済みと
  仮定した条件付き定理であり、名前付きの未証明定理を呼ばない。
- 具体的な Lemma 3.5 は `Inputs/Descent.lean` の `theorem_3_1_K0`、
  定理4.7は `Paper/Section4/SupportedDescent.lean` の `supportedRankK0_descent` を呼ぶ。
  後者には補題4.6の dg 表示と一般係数版の降下への接続が含まれ、未証明である。
- 正則局所環から Koszul 分解と通常の階数公式を供給する経路は、
  `Inputs/RegularParameters.lean` の `isWeaklyRegular_of_span_eq_maximalIdeal` に依存する。
  これらの具体的適用の `sorryAx` を、抽象比較や入力確認の証明と混同しない。
- 本文・付録の旧状態表示は、2026-10-11 の文書整理で下記の実装に合わせて更新した。

この時点で残す旧入口 `chiOrdHom`・`chiLamHom_of_finite` は、具体的な数値計算と
従来のより弱い有限性条件を受け付けるためのものである。加法性の独立した証明は
残しておらず、新しい Euler 構成と重なる範囲で K₀ 評価の一致も証明した。
本文は「共通定理、圏と関手の実現、仮定確認、適用」の順に更新し、
上記の未証明入力と、反復錐に用いる再帰表示も付録に記録した。

検証：最終の全体 `lake build` は成功（3478 jobs）。共通層・変更した評価・
主要な適用先の47宣言と、係数変更・群作用の21宣言、合計68宣言を
`#print axioms` で監査した。66宣言は `propext`・`Classical.choice`・`Quot.sound`
のみで、既存の `lemma_3_5` と `Section4.theorem_4_7_K0` だけが上記の引用に由来する
`sorryAx` を含む。新しい `sorry` は追加していない。
群作用との同変性には局所性がなく、降下の移送にだけ係数環の局所性を使うことも
定理の型の表示で確認した。前回の全体ビルドにない新しい警告はなく、
`git diff --check`、対象 Lean ファイルの空白・行長、計画文書のローカルリンクも確認した。

### 本文・付録と実装の対応の更新（2026-10-11）

- `exposition/ja/exposition-ja.tex` の §4・§5 を、共通定理の提示、実際の圏と関手、
  仮定確認、適用の順に整理した。ランク商の局所化・冪等完備化への延長と全対象の
  一様代表を証明済みの構成として述べ、降下の引用と分離した。
- 付録 B の共通ホモロジー代数を最初に置いた。有限な商と大きな商の有限部分の
  同値、任意の可換環の perfect 支持と零ホモトピーの同値、群作用付き K₀ 比較を追記。
  対称比較は降下を明示的に仮定する形とし、幾何的な降下の供給を別段階にした。
- §3・§7 の「パラメータ商 B が正則局所環」という誤った説明を修正。
  Tor の長さ比較は有限生成加群の次数移動、次数の上界は R 上の有限自由分解と
  共通消滅によるものとして書いた。商値 Tor の自然同型まで形式化したとは述べない。
- 付録 A の状態一覧と B の P1–P8 の記述を更新。λ-平坦性・λ-CM の概念的な定義と
  Koszul 条件との同値、明示的な二項係数直和への並べ替えは残る境界として記載。
  命題4.3(c)に対応する `ι(P) = (P^{⊕s_n})` の独立した入口も実装確認できなかったため、
  数学的説明として区別した。この入口は現在の比較・消滅・下界の依存経路には不要。
- 後続の研究メモの付録は、修正済みのパラメータ商の証明を「誤り」とする古い一文のみ
  更新した。論文全体への接続や存在構成へは範囲を広げていない。Lean ファイルの変更なし。

検証：LuaLaTeX/latexmk で PDF を再生成し、50ページ全体を画像で確認。
未定義参照、重複ラベル、欠落文字、overfull box はなし。状態表は長表にして改ページ時も
見出しを繰り返す。内蔵コンパイラは XeTeX のため LuaTeX-ja に対応せず、既存の
LuaLaTeX 手順を使用した。Lean は直前の3478ジョブ・68宣言の監査結果を引用し、
今回の文書変更に対して全体ビルドをやり直したとはしていない。

### 有限長さの商と大きな商の有限部分（2026-10-10）

- `LengthAlgebra/FiniteQuotientEquivalence.lean`：零長さの核・余核をもつ射による
  長さの保存から、商の分数表示の中間対象も有限長さであることを示す。
  これにより `finiteQuotientInclusion` の完全忠実性を証明した。
  `finiteQuotientInclusion_essImage_iff` は本質的像を長さが有限な対象全体と同定する。
- 同ファイルの `FiniteLengthPart` は大きな商の Serre 部分圏であり、
  `finitePartLength` は非負・加法的で、零長さと零対象が同値な実数値の長さである。
  `finiteQuotientEquivalence` は従来の有限長さの商との同値を与え、
  元の商関手と可換し、順・逆の両方向で長さを保つ。
  ここでの「有限」は長さの有限性を指し、加群の有限生成性は追加していない。
- `LengthAlgebra/PerfectHomologyComparison.lean`：既存の Koszul 有限性から
  大きな商の perfect ホモロジーが有限部分に値をもつことを示す。
  `perfectHomologyEquivalenceIso` によって従来の有限商のホモロジーと対応し、
  零対象判定と長さが一致する。対象ごとの有界性も移り、
  `perfectEuler_eq_finitePartEuler` と `perfectEulerK0_eq_finitePartEulerK0` により
  共通理論で構成する Euler 数・K₀ 評価が既存のものと一致する。
- `PerfectLowerBound.lean` の有限商での消滅補題を、大きな商での判定と
  今回の比較を使う証明へ変更した。`LengthAlgebra/Foundations.lean` から公開する。

P3 の圏同値には環の局所性・Noether 性を使わない。perfect ホモロジーへの接続には
従来と同じ `J.FG`、支持イデアルの根基への包含、`KoszulFinite` を明示して使う。
新しい未証明入力や仮定の束は導入していない。TeX は変更していない。

検証：全体 `lake build` 成功（3473 jobs）。新規の名前付き32宣言と、変更した消滅補題・
その適用先の Euler 下界の計34宣言を `#print axioms` で監査し、すべて
`propext`、`Classical.choice`、`Quot.sound` のみだった。
新規2モジュールに `sorry`・`axiom` 宣言なし。対象モジュールのビルドは警告なし。
全体ビルドには従来の引用定理などの警告が残る。`git diff --check` と新規ファイルの
空白・行長検査も通過した。

### perfect 複体の幾何学的支持（2026-10-10）

- `HomologicalAlgebra/NullHomotopy.lean`：一段の成分を消すホモトピーの構成を
  `clear_degree_of_factorization` に抽出した。既存の `clear_degree` は、
  ホモロジーを消すスカラーと射影性から境界への因子分解を作り、この共通補題を使う。
- `HomologicalAlgebra/SupportNullHomotopy.lean`：支持が `V(r)` に入る加群への
  有限生成加群からの射は、ある冪 `r^n` で消えることを証明した。
  有限生成なのは射の像でよく、ホモロジー全体の有限生成性は使わない。
  これを各次数に適用し、射影性によって境界へ持ち上げる一段消去を反復することで、
  `exists_pow_nullHomotopy_of_homology_support` を得た。
- `PerfectComplex/Support.lean`：既存の `isSupported_of_homologySupport`、
  `isSupported_iff_homologySupport`、`isPerfectSupported_of_homologySupport` の
  Noether 仮定を除き、上記の一般的な証明へ移行した。
  逆向きの `IsSupported.homologySupport` には有界性・有限生成性・射影性も不要。
  非射影の複体も対象とする旧来の共通消去冪の補題は、Noether 仮定の下で残す。
- `PerfectComplex/HomotopyCategory.lean`：
  `perfectHomotopyObj_supported_iff_homologySupport` により、具体的な有限射影複体を
  抽象的な支持圏に入れる条件と幾何学的支持を同定した。
  `perfectHomotopy_supported_iff_homologySupport` は代表複体の選択を表面に出さず、
  `PerfectHomotopy` の全対象を実際のホモロジー関手の支持で判定する。

これで、有限射影版の支持圏に入れるための幾何学的な仮定確認が共通の
`scalarSupported` 条件へ直接つながる。局所環・自由性・Noether 性を追加していない。
次は既存証明の移行と二つの実現の入力境界の整理を行う。TeX は変更していない。

検証：全体 `lake build` 成功（3474 jobs）。新規・変更した定理と関連する旧定理の
計12宣言を `#print axioms` で確認し、すべて `propext`、`Classical.choice`、
`Quot.sound` のみだった。主要3定理の型も表示し、Noether 仮定がないことを確認した。
変更した Lean ファイルに `sorry`・`axiom` 宣言なし。
前回の全体ビルドにない新しい警告もなく、`git diff --check`、対象ファイルの
空白・行長検査、計画文書のローカルリンク検査も通過した。

## 2026-10-10：付録 B.9 の抽象論優先計画への移行

抽象化の数学的な主張は `exposition/ja/exposition-ja.tex` の付録 B.9（P1–P8）を基準とする。
現在の実装順と対象範囲は上の「現在の作業範囲」を優先し、以下は移行時点からの実施記録とする。
以下の S1–S5 の計画は、列の圏に固有の構成を参照するために残す。

今回の実装の入口は `CategoryTheory/EulerTheory.lean` と `LengthAlgebra/Foundations.lean`。
両方をプロジェクトのルートから import し、§4 の `Foundations` もルートのビルド対象に加えた。

| 段階 | 今回構成・証明した内容 | 残る接続 |
| --- | --- | --- |
| P1 | 加法的非負長さの単調性、零長さの Serre 部分圏、商の長さと零対象判定、Euler 評価の自然同型・引き戻し・一意性、異なる評価先の共役和比較 | 各実現の旧定義を共通 Euler 定義へ統一する作業は段階的に続ける |
| P2 | 零作用の反復錐の再帰的な対象の分裂、二項係数による長さの式と上に有界な係数列での逆向きの一意性、長さを使わない対象としての消滅、第零次の同型、全射による長さ・Euler の下界 | 完了。分裂は二項直和の再帰表示を使う。具体的な Koszul 列への接続も P4/P6 で実装済み |
| P3 | 冪ねじれ加群と有限長さの部分圏、実数値・拡大実数値の両 Serre 商、有限商から大きな商への完全忠実関手、その有限部分との圏同値と長さ・商関手の対応。perfect ホモロジーの自然同型と Euler・K₀ 評価の一致も証明 | 完了 |
| P4 | 任意の可換環の有界有限射影支持圏と幾何学的ホモロジー支持との同値、実際の商値ホモロジー関手、シフトの自然同型、有界性、共通 Euler 評価と旧交代和の一致、係数変更とその合成の自然同型、旧 K₀ からの比較写像と局所環での逆写像。有限射影項による (Kos_m) の確認、実際の Koszul 列、P2 による消滅と Euler 下界 | 旧加法性証明の整理 |
| P5 | 任意の Koszul Euler 数を係数とする基底公式、二つの長さ付き代数の対称な共役和比較。通常・正規化の両 `lemma_3_5b_*_of_koszul` を共通公式の適用へ変更 | λ-平坦性から有限性・消滅・階数を一括供給する具体的入力の整理は別作業 |
| P6 | 列の長さ・Euler 加法性・公式 (4.2) を共通層へ移行。実際の Koszul 列から対象の消滅・H₀ 同型・Euler 下界を導出。論文側の係数変更後の Hᶜ にも消滅を移送。元の列への一様支持は追加しない。任意の Koszul Euler 数による全対象の基底公式・対称な比較も構成し、両階数倍公式をその特殊例へ移行 | 極小性から具体的な全射を構成し、論文側の Euler 下界まで接続済み。実現の定義と残る互換経路の整理 |
| P7/P8 | Tor 消滅を共通定理へ移行。極小性の全射、有限版・ランク版の具体的 Euler 下界、有限近似の長さから生成元数の正規化下界、その正値性から論文側の Euler 正値性まで接続。極小自由分解・全次数の Betti 階数公式・切り詰めた自由複体列を構成し、境界因子分解から商での支持と零作用を証明。有限近似から正の Euler 評価をもつ対象まで構成。小さい尾部による切り詰めの深さの変更、Tor・Koszul ホモロジーとの比較も実装。通常 Tor の変数交換を証明し、有限近似の極限を深い代表へ移す接続も実装。商の Betti 評価と Tor の正規化極限の一致、極限列の有限支持、有限交代和による Euler 評価、共通剰余体による通常長さの環変更、全自己同型のひねりの通常評価と `c_σ` の同定まで証明。Lemma 5.4 の分解入力を内部構成へ置換し、剰余体極限から増大条件も導出。同じ複体列の支持変更・評価の一致・実際の K₀ 群作用を照合し、第二比較と各共役・通常評価の共通下界へ接続。係数変更後の振幅・極小性を導き、同じ有限近似から第二比較と全共役・通常 Euler 数の正値性を同時に構成。有限局所代数・長さ代数の公式から適用条件を導き、塔の近似列の内部構成から正値性まで接続 | 具体的な環・長さ代数での仮定の確認、core への適用、重複整理、本文の再構成 |

`PerfectComplex/KoszulLengthBounds.lean` の有限自由項による上界は、有限自由加群の直和因子を
各項とする上界から得る形へ変更した。`ProjectiveBounds.lean` は有限射影項の有限性を供給し、
`lemma_3_5a_lam_finite` もこの一般化を利用する。

共役和の群論補題は `GroupTheory/ConjugateSum.lean` へ移動した。旧ファイルは互換 import のみ。
長さによらない台の補題は `PerfectComplex/Support.lean`、通常 Koszul の有限性は
`LengthAlgebra/Ordinary.lean` へ移し、共通層が `Paper` や `Asymptotic` を import しない方向にした。

有限版の新しい Euler 加法性は `homologicalEuler_triangle` による。
旧 `NormalizedEuler` の数値定義と補題は、具体的な長さ上界や既存利用箇所があるためまだ残している。
主な階数倍公式を移したことと、P4–P8 の移行全体の完了は区別する。

新規の構成や定理には `sorry` を追加しない。基底公式は `IsKoszulResolution`、
共役和比較は不変類の降下を明示的に受け取る。既存の定理4.7の未証明入力への依存は別途監査する。

### 最初の移行の検証

- `lake build` 成功（3398 jobs）。共通層、有限射影版、Lemma 3.5、§4 Foundations、
  `IntersectionMultiplicity.ParameterQuotientTorBound` をルート経由で検証した。
- 主要20宣言の `#print axioms` を確認。新規・移行した19宣言は
  `propext`、`Classical.choice`、`Quot.sound` のみ。
- `Section4.theorem_4_7_K0` は既存の引用により引き続き `sorryAx` を含む。
  新しい共通比較と Koszul 基底公式自身はこれに依存しない。
- `git diff --check` と新規 Lean モジュールの空白検査に問題なし。

### 続行分：具体的な Koszul 列と消滅・下界の接続

- `PerfectComplex/KoszulTower.lean`：任意の可換環上の有限射影支持圏に、実際の
  Koszul 複体と各段の完全三角形を構成する。
- `PerfectComplex/KoszulAmplitude.lean`：環自身の高次 Koszul ホモロジーの長さが零なら、
  項の振幅 `[a,b]` が係数つき Koszul ホモロジーの振幅を与える。有限射影項の
  定量上界を使い、長さの有限性・局所性・ネーター性・平坦性は仮定しない。
- `LengthAlgebra/PerfectVanishing.lean`：大きな長さの商への実際のホモロジー関手を構成。
  (Supp) と (Kos_m) を確認し、共通定理から初項の振幅 `[a+e,b]` を得る。
  `PerfectLowerBound.lean` は有限な評価で、Koszul の第零次からの全射を共通 Euler 下界へ渡す。
- `Asymptotic/KoszulTower.lean`：三角関手の像における支持部分圏に実際の錐の列を構成。
  `RankVanishing.lean` は Koszul ホモロジー長の正規化超極限で振幅を確認し、
  対象としての消滅、H₀ の同型、Koszul H₀ からの全射による Euler 下界を得る。
- `Asymptotic/PaperVanishing.lean`：`K_v ⊗ F` をさらに係数変更した複体の振幅から、
  論文の `paperBaseChangeHomology` の消滅を得る。各段の自由振幅と係数環の Koszul 消滅から
  振幅条件を供給する版もある。元の `F` に一様支持を追加していない。
- `completedRankEuler_triangle` と `completedRankBetti_sequenceKoszul`（公式 (4.2) の中核）の
  既存証明を、それぞれ共通 Euler 加法性・反復零錐の二項係数公式の適用に変更。
- `ParamQuot.len_torAlg_eq_zero` の公開仮定は維持し、証明を
  `lambdaHomology_projective_vanishing` の適用へ変更。初項で零なスカラーは零射の錐でも
  零なので、以前の追加の `2^h` 倍の消去指数は不要。`B=R/(x)` の正則性は仮定しない。
  従来の数値的補題は独立に利用できるため残し、上からの評価は新しい振幅補題へ移行した。

- `Paper/Section4/PaperK0Comparison.lean`：
  `koszulPaperEulerK0_changeRing` により、任意の Koszul Euler 数を係数とする基底公式を
  ランク商の全対象で証明した。有限版の共通公式、一様代表、超極限と有限和の交換、
  冪等完備性を使う既存の持ち上げを組み合わせる。
  既存の通常版・正規化版の階数倍公式も、この定理の係数を計算する証明へ移行した。
- `Paper/Section4/SymmetricComparison.lean`：二段階の係数変更の自然同型と上の公式から、
  二つの長さ付き代数の対称な共役和比較を証明。評価先の局所性・有限代数性・群作用、
  高次 Koszul 消滅は不要。Koszul Euler 数の一致と K₀ の不変類の降下を入力にする。

この段階では計画全体は未完了。有限近似の具体的な全射・生成元数の下界への
接続は、次の「極小性と有限近似の接続」で進めた。
大きな商との圏同値・幾何学的支持との同値・重複整理も残る。
本文の全面的な再構成は、二つの実現の残る接続が揃った後に行う。

### 続行分の検証

- 最終の `lake build` 成功（3406 jobs）。有限版・ランク版の消滅と下界、
  Tor 消滅、全対象の任意係数の比較、既存の `NormComparison`・`Theorem4_7` を含む。
- 主要25宣言を `#print axioms` で監査。新規・移行した24宣言は
  `propext`、`Classical.choice`、`Quot.sound` のみ。
- `Section4.theorem_4_7_K0` の既存の `sorryAx` 依存は残る。
  新しい対称な比較・消滅・下界自身と、移行した `ParamQuot.len_torAlg_eq_zero` は依存しない。
- 新規8 Lean モジュールに `sorry`・`axiom` 宣言なし。
  `git diff --check` と新規モジュールの空白検査も通過。
- この続行では exposition 本体・付録の文章は変更していない。

### 極小性と有限近似の接続（2026-10-10 続行）

- `HomologicalAlgebra/HomologyQuotient.lean`：微分を消す零次項の全射から
  実際の第零ホモロジーの全射を構成。行き先を消すスカラーで Koszul 反復をしても
  全射が残ることを長完全列で証明。極小性の座標条件から `(R/I)^b` への全射を得る。
- `PerfectComplex/MinimalLowerBound.lean`：有限直積の長さの公式と全射の単調性から
  `b λ(R/I) ≤ λ H⁰(K(x;P))`。元の複体の支持・Koszul 消滅・平坦性は不要。
- `LengthAlgebra/PerfectMinimalLowerBound.lean`：共通の消滅・Euler 定理と上の全射により、
  有限射影版の `b λ(R/I) ≤ χ(P)` を証明。零次項の自由基底を指定するが、他の項は射影でよい。
- `Asymptotic/RankMinimalLowerBound.lean`：振幅 `[-e,0]` と商での零作用から、
  Euler 評価を実際の Koszul 第零ホモロジーの正規化極限と同定。
  極小性から `λ(R/I) lim_U rank(K⁰)/s ≤ χ(K)` と正値性を得る。
  元の複体列の一様支持は追加しない。
- `Asymptotic/PaperMinimalLowerBound.lean`：行列の係数変更が微分のイデアル条件を保つことを
  証明し、論文側の `paperBaseChangeEulerK0` にも同じ下界を移送。
- `Asymptotic/NormalizedLowerBound.lean`：正規化極限の単調性、有限な ENNReal 極限の実数化、
  長さの収束と生成元数による項ごとの上界から生成元数の正の極限を得る補題。
- `Paper/Section5/ApproximationLowerBound.lean`：既存の
  `length_le_tor_zero_mul` と Lemma 5.4 型の長さの収束から
  `λ(U) ≤ ℓ(B/I) lim_U β₀(M_n)/s_n` および正値性を証明。
- `Paper/Section5/AsymptoticPositivity.lean`：上記と Euler 下界を合成し、
  `paperEuler_pos_of_finiteApproximation` を証明。有限近似の加群、自由複体列、
  微分の極小性、振幅、商での支持、零次階数と `Tor₀(M,k)` の長さの一致、
  係数環の消滅・商の正の長さを個別に引数に取る。`B` の正則性は仮定しない。

この段階で残っていた Lemma 5.5 の極小自由分解・切り詰め・Betti 階数公式は、
次の続行で構成した。商での支持と係数変更後の Euler 同定は引き続き必要。
二つの群比較と最終の `core_of_inputs` へ具体的データを渡す作業も未完了。
本文・付録の TeX はこの続行では変更していない。

検証：公開 import に接続した全体 `lake build` が成功（3414 jobs）。
今回の主要22宣言を `#print axioms` で確認し、すべて
`propext`、`Classical.choice`、`Quot.sound` のみ。
新規8モジュールに `sorry`・`axiom` 宣言なし。`git diff --check` と
新規ファイルの行末空白・行長の検査も通過。
既存の引用入力の未証明部分はこの確認とは別に残る。

### 極小自由分解と切り詰めた有限近似（2026-10-10 続行）

- `CommutativeAlgebra/MinimalGenerators.lean`：剰余体上の基底を持ち上げた有限自由被覆。
  Nakayama による全射性、核の全座標が極大イデアルに入ること、
  零次 Tor の長さと被覆の階数の一致を証明。ここでは Noether 性も不要。
- `HomologicalAlgebra/MinimalFreeResolution.lean`：Noether 局所環上で核の極小被覆を
  繰り返し、全項が有限自由な実際の `ProjectiveResolution` を構成。
  全次数の完全性と微分の極小性を証明。分解の有界性・環の正則性は仮定しない。
- `HomologicalAlgebra/MinimalBetti.lean`：全次数で
  `ℓ Tor_i(M,k) = rank F_i`。第1変数の Tor 長完全列を使う次数のずらしによる。
  零次の被覆と加群の長さが等しいことから必要な同型を得るため、
  一般の Tor の対称性・二重複体による比較は必要ない。
- `HomologicalAlgebra/MinimalTruncation.lean`：項ごとの切り詰めを `[-l,0]` 次に置き、
  有限自由性・残した全項の Betti 階数公式・零次への微分の極小性を保持。
  切り詰めを分解とは主張しない。左端の誤差は残る。
- `Asymptotic/MinimalResolutionFamily.lean`：Betti 数の `O(s)` 評価から、実際の
  `FreeSequence` 上の共通有界複体を構成。各段との鎖同型、全項の階数公式、
  極小性を供給。有限な正規化 Tor 極限から `O(s)`、零極限から `o(s)` を導く。
- `Paper/Section5/MinimalApproximation.lean`：有限近似から上の自由複体列を構成し、
  一様な消去イデアルと正の長さの極限を使って零次階数の正規化超極限の正値性を証明。
  零次階数公式や極小性を別の未証明入力として受け取らない。
  `AsymptoticPositivity` の import を通じて公開入口へ接続。

次の主要作業は、`β_(l+1)(M_n) = o(s_n)` を使って切り詰めの誤差をランク商で消し、
商でのスカラーの零作用と支持を供給すること。その後、ひねり・係数変更と
有限近似の Tor 極限を結び、通常 Euler 評価を `c_σ` と同定して第二比較へ渡す。
`B = R/(x)` の正則性は引き続き仮定しない。本文・付録の TeX は変更していない。

支持の証明で次に実装する経路：加群を消すスカラーの作用は、全極小分解上では
`ProjectiveResolution.liftHomotopyZero` により零ホモトピーをもつ。
切り詰めたホモトピーの等式には左端だけ誤差が残り、その射は
切り捨てた第 `l+1` 自由項を `-l` 次に置いた一項複体を経由する。
その階数は `o(s)` なので商で零となる。この因子分解と列への組み戻しを証明すれば、
元の切り詰め複体列に一様支持を追加せず、商での零作用が得られる。
この段落はこの時点での実装方針。以下の続行で因子分解と商での支持を証明した。

検証：公開 import に接続した全体 `lake build` が成功（3421 jobs）。
新規構成と既存の正値性の接続を含む主要22宣言の `#print axioms` は、全て
`propext`・`Classical.choice`・`Quot.sound` のみ。新規6モジュールに
`sorry`・`axiom` 宣言なし。`git diff --check`、行末空白・行長の検査も通過。
既存の引用入力の未証明部分は引き続き別に残る。

### 切り詰めの境界・商での支持・正の Euler 対象（2026-10-10 続行）

- `HomologicalAlgebra/TruncationBoundary.lean`：任意の加法的な圏の複体について、
  零ホモトピックな射を下端 `a` で切り詰めると、その射はホモトピーを除いて
  `K^(a-1)` を `a` 次に置いた一項複体を経由することを証明。
  制限・延長の線形性も証明し、スカラー作用に適用できる形にした。
- `HomologicalAlgebra/MinimalBoundary.lean`：加群の消去元から射影分解上の
  零ホモトピーを構成。極小分解の切り詰めに上の一般論を適用し、
  境界の唯一の項の階数が `β_(l+1)` であることを証明。
- `Asymptotic/FactorizationSupport.lean`：段ごとの因子分解を自由列に組み戻す。
  経由する複体を零に送る任意の線形加法関手の下で、スカラー作用も零になる。
  論文の順序で商・冪等完備化した `PaperRankQuotient` への適用も証明。
- `Asymptotic/MinimalSupport.lean`：`β_(l+1)(M_n)=o(s_n)` から境界を小さい
  ランクの列として構成し、切り詰めた列の商での零作用・支持を証明。
  加群列の共通消去指数 `N` をそのまま使える。元の切り詰め上での
  零ホモトピーや、`B` の正則性は仮定しない。
- `Paper/Section5/SupportedApproximation.lean`：有限近似から、共通振幅、全項の
  Betti 階数公式、極小性、正の零次階数、商での支持と零作用を同時に構成。
- `Paper/Section5/AsymptoticPositivity.lean`：
  `exists_paperEuler_pos_of_minimalApproximation` によって、構成した列に抽象 Euler
  下界を適用。長さ付き係数環の Koszul 消滅と商の正の長さを与えれば、
  Euler 評価が正の支持つき対象を得る。複体列や支持を未証明入力として受け取らない。

次の主要作業は、ひねり・係数変更と有限近似の Tor 極限を結び、
通常 Euler 評価を `c_σ` と同定して第二比較に渡すこと。
今回の正値性の存在定理は `B → S` に沿う一般の係数変更を扱うもので、
§5 の具体的な環・群・ひねりをすべて供給した最終定理ではない。
二つの比較の具体的適用、`core_of_inputs`、P3/P4 の残る圏同値、P8 の整理は未完了。
本文・付録の TeX は変更していない。

検証：公開 import に接続した全体 `lake build` が成功（3426 jobs）。
境界因子分解、列への組み戻し、支持、構成した対象の正値性を含む主要22宣言の
`#print axioms` はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規5モジュールと拡張した `AsymptoticPositivity` に `sorry`・`axiom` 宣言なし。
`git diff --check`、変更した Lean ファイルの行末空白・行長の検査も通過。
既存の引用入力の未証明部分は別に残る。

### 切り詰めの深さの変更と Tor・Koszul への接続（2026-10-10 続行）

- `HomologicalAlgebra/StupidTruncation.lean`：任意の加法圏で、項ごとの切り詰めの
  包含・射影・次数ごとの分裂を構成。加法関手との両立と、下端より上の
  ホモロジーの同型を証明。係数変更の平坦性は要求しない。
- `CategoryTheory/TruncationTriangle.lean`：切り詰めと尾部を結ぶ完全三角形を構成。
  尾部を零に送る任意の三角関手は、切り詰めの包含を同型に送る。
- `Asymptotic/TruncationComparison.lean`：尾部の各項が `o(s)` なら包含は
  論文のランク商で同型となり、支持つき K₀ 類も変わらない。
- `Asymptotic/MinimalTruncationComparison.lean`：浅い切り詰めの深さを `l` とし、
  `l < j ≤ m` の Betti 数が `o(s)` なら、深さ `m` の切り詰めは同じ商の対象を表す。
  残した項の `O(s)` から深いモデル自体も構成する。
  任意の固定次数 `i` に対し `m = max(l, i+1)` を選べば、同じ対象の代表で
  `H^{-i}(S ⊗ F_n)` を `TorAlg(B → S, i, M_n)` と同定できる。
- `HomologicalAlgebra/KoszulTruncation.lean`：ある次数以上で項ごとに同型な射は、
  Koszul 構成後もその範囲で項ごとに同型。したがって下端より上のホモロジーの
  比較は Koszul 構成後も有効で、列の長さ分だけ余分に深く切る必要はない。
- `HomologicalAlgebra/MinimalTruncationHomology.lean`：極小分解全体との比較、
  代数係数の Tor、通常の `Tor_i(N,M)`（第2変数を分解）、Koszul つき比較を供給。
  切り詰めの下端そのものを Tor と同一視しない。
- `Paper/Section5/ApproximationHomology.lean`：有限近似の剰余体 Tor の有限な極限と
  高次の零極限から `O(s)`・`o(s)` を取り出し、任意の固定次数で Tor を計算する
  支持つきの代表を構成。元の代表との同型は支持部分圏内の同型として返す。
  `AsymptoticPositivity` を通じて公開入口に接続。

通常 Euler 評価を `c_σ` と同定する作業は未完了。次に必要な接続を分ける：

1. 全極小分解の共通消去元による Koszul 分裂と、上の局所的なホモロジー比較を
   既存の商上の二項係数公式 (4.2) に適用し、商の Betti 評価を Tor の極限と同定する。
   代表の各段で Tor を計算できることだけでは、商上の評価の同定にはならない。
2. 有限近似で得た `Tor_i(M_n,E′)` は第2変数の分解による定義であり、今回
   `M_n` の極小分解から計算する `Tor_i(E′,M_n)` との比較が必要。
   一般の Tor の対称性や、変数を交換して計算できることを未証明で流用しない。
   現在の長完全列 API は写像の自然性まで公開していないため、次数のずらしによる
   比較を使う場合も、零次の写像とテンソル積の交換同型との両立を証明する必要がある。
3. ひねり・係数変更・有限交代和を通じて通常 Euler 評価を `c_σ` に同定し、
   第二比較と既存の正の Euler 評価を `core_of_inputs` へ渡す。

`B = R/(x)` の正則性は追加していない。本文・付録の TeX は変更していない。

検証：公開 import に接続した全体 `lake build` が成功（3433 jobs）。
今回の主要24宣言の `#print axioms` はすべて
`propext`・`Classical.choice`・`Quot.sound` のみ。
新規7モジュールに `sorry`・`axiom` 宣言なし。`git diff --check` と
新規 Lean ファイルの行末空白・行長の検査も通過。
既存の `SupportedDescent` 等の未証明入力は別に残る。

### Tor の変数交換と有限近似の極限の移送（2026-10-10 続行）

前節の残作業2（通常 Tor の変数交換）を解消した。

- `HomologicalAlgebra/ResolutionNaturality.lean`：整数添字と自然数添字のホモロジーの
  比較、加法関手と制限の比較について自然性を証明。任意のコチェイン分解による
  導来関手の計算が、分解の射・加法関手の間の自然変換の両方と可換であることを得る。
- `TorLES.lean`：第2変数の長完全列の `α` が導来関手の標準の射に一致することを証明。
  第1変数の長完全列も `α`・`β` の標準の射との一致を返す版へ拡張し、
  従来の公開定理はその完全性を取り出す形にした。第2変数の `β` の同定と
  連結射の自然性は今回の比較に不要であり、引き続き未実装。
- `TorNaturality.lean`：零次左導来関手から元の関手への射の、関手側の自然性を証明。
  `Tor₀(M,N) ≅ M ⊗ N` の両変数での自然性と、変数交換の可換正方形を得る。
- `TorSymmetry.lean`：任意の可換環上の任意の加群について
  `torModuleComm : Tor_i(M,N) ≃ₗ Tor_i(N,M)` を構成。
  一次では、射影的な被覆 `P → M` の核 `K` に対して、両側をそれぞれ
  `Tor₀(K,N) → Tor₀(P,N)` と `Tor₀(N,K) → Tor₀(N,P)` の核として比較する。
  二次以上では両方の長完全列で次数を一つ下げ、次数について帰納する。
  Noether 性・局所性・有限生成性・正則性は不要。高次の同値の自然性や
  交換を二度施したときの恒等性は主張していない。
- 同じファイルで通常の長さの対称性、第1変数の任意のコチェイン分解による計算、
  代数に係数変更した分解の係数制限と `Tor_i(M,T)` の比較を証明した。
  最後の比較は基底環上の線形同値であり、代数側のスカラーとの両立は主張しない。
- `MinimalTruncationHomology`、`MinimalTruncationComparison`：有限近似と同じ変数順の
  `Tor_i(M_n,N)` を、`M_n` の極小分解の切り詰めと任意の自由列モデルで計算する。
  必要な次数に合わせて代表を深くし、支持つきランク商の対象を保つ。
- `Paper/Section5/ApproximationHomology.lean`：
  `exists_supported_representative_with_tor_limit` により、有限近似の
  `ℓ_B(Tor_i(M_n,N))/s_n → ρ` を、同じ支持つき対象の深い代表における
  `ℓ_B(H^{-i}(N ⊗ F_n))/s_n → ρ` へ移した。
  ここで測るのは基底環 `B` 上の通常の長さである。

次の主要作業は、上のホモロジーの極限と、商上に構成した Betti 評価との同定。
全極小分解での Koszul 分裂、切り詰めとの局所的な比較、商の二項係数公式を結ぶ。
続いて、係数変更・ひねり・必要な長さの環変更・有限交代和を処理して
通常 Euler 評価を `c_σ` と同定し、第二比較へ進む。
有限近似のホモロジーの極限を移せたことだけで、商の評価の同定や
第二比較の具体的な適用が完了したとはしない。

検証：公開入口を含む全体 `lake build` が成功（3436 jobs）。
自然性・長完全列・全次数の変数交換・深い代表と極限への接続を含む主要23宣言の
`#print axioms` はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規3モジュールと拡張した4モジュールに `sorry`・`axiom` 宣言なし。
`git diff --check`、変更した証明ファイルの行末空白・行長の検査も通過。
既存の長さ代数・降下等の引用入力への依存は別に残る。
本文・付録の TeX は変更していない。

### 商の Betti 評価と有限近似の極限の同定（2026-10-10 続行）

前節の主要作業だった、全分解のホモロジーの正規化極限と商の Betti 評価の同定を証明した。
新しい仮定の束や未証明入力は追加していない。

1. **共通の係数論**：`CategoryTheory/ConeLengthCancellation.lean` で、
   上に有界な実数列への `(1 + shift)^e` の単射性を証明した。
   下に有界である必要はない。有界性なしでは交代列が核になるため、上限は明示する。
   `CategoryTheory/AlternatingSum.lean` に交代和の添字変換を集約し、
   旧ホモロジー Euler 理論と交点理論の両方から共通の補題を使う形へ整理した。
2. **無限分解での Koszul 公式**：`HomologicalAlgebra/KoszulHomologyLength.lean`。
   零ホモトピックな射の錐の短完全列から、冪ねじれ性と長さの加法性を導く。
   各元の零ホモトピーから二項係数公式を証明し、
   `Asymptotic/KoszulHomologyLimit.lean` で各次数の `O(s)` を使って極限へ移す。
3. **極小分解への適用**：`Asymptotic/MinimalBettiEvaluation.lean`。
   全分解の各ホモロジーの長さが有限で `O(s)` であることを、深い有限自由モデルの
   Koszul ホモロジーの上界と直和因子への引き戻しから証明した。
   比較する次数ごとに深い代表を選び、既存の商の公式 (4.2) と全分解の二項公式を一致させる。
   二項変換を消去して、`paperBaseChangeBetti_eq_minimal_homology_limit` と
   `paperBaseChangeBetti_eq_minimal_tor_limit` を得た。
   元の切り詰めの各段に一様支持は要求しない。
4. **有限近似への接続**：`Paper/Section5/ApproximationBetti.lean`。
   剰余体 Tor の有限な極限と高次の零極限から `O(s)`・`o(s)` を確認する。
   共通の消去冪と係数環の Koszul 有限性の下で、各次数の通常の極限を商の評価と同定。
   極限列の有限支持を導き、Euler 評価をその有限交代和として計算する。
   各段の Euler 数と極限を無条件で交換する主張ではない。
5. **通常長さの環と変数順**：`length_restrictScalars_torAlg_comm` により、
   代数係数 Tor を基底環で測る長さを `Tor_i(M_n,S)` の長さと同定する。
   `B → S → k(S)` が全射のときは、既存の長さ比較から `S` 上の通常長さにも移せる。
   `paperOrdinaryEulerK0_eq_of_common_residueField_limits` が、その Euler 評価の公式。

仮定は Noether 局所環 `B`、剰余体 Betti 数の増大条件、共通の消去冪、
係数環の Koszul ホモロジー長の有限性。`B` の正則性、有限近似の一様な射影次元、
係数変更の平坦性は使っていない。通常の収束値を用いた結論は超フィルターの選択によらない。

次の具体化では、Lemma 5.4 の極限列をひねり・係数変更と照合して `c_σ` に同定し、
実際の環・群・長さ代数で仮定を確認して第二比較へ渡す。
Serre 商の比較の完全忠実性、任意の環での幾何的支持との同値、
降下・長さ代数等の引用入力、本文・付録の再構成は、この接続の証明とは別に残る。

検証：公開入口を含む全体 `lake build` 成功（3442 jobs）。
共通係数論、無限分解の Koszul 公式、正規化極限との比較、通常長さの環変更を含む
主要27宣言の `#print axioms` はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規6モジュールに `sorry`・`axiom` 宣言なし。`git diff --check` と新規ファイルの
行末空白・行長の確認も通過。既存の降下・長さ代数等の引用入力は別に残る。
本文・付録の TeX は変更していない。

### ひねりの通常評価と `c_σ`、有限近似の入力整理（2026-10-10 続行）

- `HomologicalAlgebra/BaseChangeEquivalence.lean` に、二段階の係数変更と
  自己同型に沿う係数制限・逆自己同型に沿う係数拡大の同型を移した。
  一般部品が交点理論のモジュールに依存しない構成にした。
  `length_homology_baseChange_equiv` と `length_torAlg_comp_equiv` は、
  任意の複体・全次数の Tor の通常長さの不変性を証明する。有限性・有界性は不要。
  `KoszulOrdinaryLength.lean` は、ひねり後の Koszul 有限性を元の有限性から導く。
- `Paper/Section5/ApproximationEuler.lean`：極小分解の商の対象について、
  係数写像を任意の自己同型でひねっても通常 Euler 評価は同じ。
  共通剰余体と有限近似の Tor 極限の下で `lambdaChi`、特に
  `paperOrdinaryEulerK0_eq_twistedEuler` で本文の `c_σ` と同定した。
  `σ` を固定したときの、有限係数環側のすべてのひねりに対する主張である。
  長さ付き代数の長さの群不変性は仮定していない。
- `exists_supported_approximation_with_lambdaChi` は同じ有限近似から
  複体列と商での支持を構成し、上記の全ひねりの評価を同時に得る。
  振幅、極小分解の切り詰めとの各段の同型、極小性、零次階数の正の極限、
  商でのスカラーの零作用も返す。後の共通 Euler 下界に同じ対象を渡せる。
- `lemma_5_4` の API を改めた。加群族と剰余体の分解 `G`・`G₀`、その自由性・有限生成性は
  入力から除き、Noether 局所環上の極小自由分解から内部で構成する。
  元の証明で内部に保持していた剰余体係数の全次数の Tor 極限を、同じ `M_n,s_n` の
  結論に追加した。`MinimalFreeResolution.extRes_free`・`extRes_finite` が必要な各項の性質を供給。
  分解全体の有界性やパラメータ商 `B` の正則性は要求しない。
- `ApproximationGrowth.lean`：Lemma 5.4 の剰余体極限に Lemma 5.3 を適用し、
  `dim R = l+h` から `i≤l` の `O(s)` と `i>l` の全次数の `o(s)` を導く。
  この具体化は Lemma 5.3 が用いる既存の正則パラメータの引用に依存する。
- `CategoryTheory/ScalarSupportRadical.lean`：有限パラメータ系のスカラー支持を、
  自己準同型加群の消去イデアルの根基で特徴付けた。根基の包含に沿って支持を移せ、
  同じ根基なら支持部分圏は等しい。線形圏の一般論であり、Noether 性・三角圏構造は不要。
  `Asymptotic/PaperSupportChange.lean` で論文側の支持圏へ適用した。

今回の `c_σ` の同定は、有限近似の極限・共通消去冪・Koszul 有限性などを明示した定理である。
実際の §5 の正規化基底・環・長さ代数からこれらをすべて供給し、第二比較を適用し終えたわけではない。
次に必要なのは、有限近似から得る支持のパラメータ系と `A_E` から来るパラメータ系を照合し、
**支持を変更した際の評価の一致**、および係数写像のひねりと既存の `paperTwist` の
K₀ 作用との対応を確認すること。その後、対称な比較に同じ対象を渡す。
今回の根基補題は支持条件の同一性までであり、評価関手の同一視までは主張しない。

本文・付録の TeX は変更していない。新しい仮定の束や `sorry` は追加していない。

検証：公開入口を含む全体 `lake build` 成功（3448 jobs）。主要21宣言を公理監査し、
ひねり・`c_σ` の同定・同じ対象の構成・根基による支持変更など19宣言は
`propext`・`Classical.choice`・`Quot.sound` の範囲内だった。
`lemma_5_4` と `betti_growth_of_parameter_approximation` の2宣言には、
既存の塔の長さ・正則パラメータの引用に由来する `sorryAx` が残る。
新規6モジュールに `sorry`・`axiom` 宣言なし。`git diff --check`、行末空白・行長の検査も通過。

### 支持変更・実際の群作用・第二比較・共通下界の接続（2026-10-10 続行）

- `Asymptotic/ComplexEvaluationIndependence.lean`：商で二組のパラメータによる支持をもつ
  同じ有界自由複体列の各次数の評価と Euler 評価が一致する。
  それぞれの Koszul 操作で一様支持へ移し、共通のホモロジー長の極限と
  `coneLength_pow_cancel_of_hasFiniteSupport` によって元の評価を比較する。
  元の列の一様支持、二つの生成イデアルの根基の一致は不要。
  対象は具体的な複体列の像であり、任意の冪等直和因子間の関手の自然同型までは主張しない。
- `Asymptotic/PaperComplexBaseChange.lean`：抽象的な係数変更の像と行列を係数変更した
  複体列の像との同型を、論文の支持圏内に構成した。
  係数変更後の Euler 評価を、別の支持を指定した同じ複体列上で計算できる。
- `Asymptotic/OrdinaryTwistEvaluation.lean`：任意の自己同型に沿う係数拡大は
  各次数の通常評価と Euler 評価を保つ。公式 (4.2)、通常ホモロジー長の不変性、
  共通の反復錐の消去から証明し、極小分解や Tor 極限の仮定を必要としない。
  `paperOrdinaryEulerK0_smul` が、既存の `paperTwist` による実際の K₀ 群作用と接続する。
- `Paper/Section5/SecondComparison.lean`：共通の対称比較に上の不変性を適用し、
  通常 Euler 評価の群の位数倍が正規化評価の共役和に一致することを証明した。
  有限近似の基底から係数変更した複体にも適用でき、支持の指定の違いを解消する。
- `Paper/Section5/ApproximationSecondComparison.lean`：同じ有限近似の複体から、
  根基の包含により正則基底側の支持を構成する。Tor 極限と共通剰余体による通常評価の
  同定を接続し、全ての実際のひねりの通常評価が `lambdaChi` であることと、
  `|G| · lambdaChi = Σ_g b_g` を同時に得る。
  近似先の写像を `twistedAlgebraMap` とすると、その `lambdaChi` が本文の `c_σ` である。
- `Asymptotic/PaperTwistLowerBound.lean`：群作用後の評価を、ひねりを合成した
  係数写像の評価と同定した。パラメータの像が固定されるため、Koszul 有限性と消滅は
  元の仮定から供給できる。各共役について、同じ複体の極小性・振幅・零作用から
  `λ(C/Q) · lim_U rank(K_n^0)/s_n` を下界とする。
- `Paper/Section5/SecondComparisonLowerBound.lean`：上の下界を共役ごとに足し、
  第二比較で通常 Euler 評価にも同じ下界を移す。下界の二つの因子が正なら、
  通常評価も全ての共役の正規化評価も正になる。

これにより、前節で残していた「支持を変更した際の評価の一致」と
「係数写像のひねりと実際の K₀ 作用との照合」は、§5 で使う具体的な複体列について接続した。
第二比較自体や通常評価の `c_σ` との一致を、新しい仮定として追加してはいない。

残る具体化は、論文の `A_E`・有限局所代数・長さ代数を実際に選び、
根基の包含、Koszul Euler 数の一致、不変 K₀ 類の降下、商の正の長さ、
係数変更後の振幅・極小性を同じ設定で供給する段階である。
`core_of_inputs` への具体的な `b_{σ,γ}` の供給と `core_statement` は未完了。
比較関手の完全忠実性・幾何学的支持との同値などの別課題も残る。
長さの群不変性、パラメータ商の正則性、元の複体列の一様支持は追加していない。

検証：公開入口を含む全体 `lake build` 成功（3455 jobs）。新しい22宣言を公理監査し、
すべて `propext`・`Classical.choice`・`Quot.sound` の範囲内であることを確認した。
比較のために再確認した `theorem_4_7_K0`・`lemma_5_4` には、既存の引用による `sorryAx` が残る。
新しい第二比較はそれらを呼ばず、Koszul 条件・不変類の降下・近似極限を個別の仮定にしている。
新規7モジュールと更新した共通消去補題に `sorry`・`axiom` 宣言なし。
新規モジュールの警告なし。`git diff --check`、行末空白・行長の確認も通過。
本文・付録の TeX は変更していない。

### 同じ有限近似による第二比較と正値性の同時構成（2026-10-10 続行）

- `Asymptotic/LocalBaseChangeBounds.lean`：行列の係数変更で自由複体列の振幅が保たれ、
  局所準同型なら極小性も保たれることを証明した。群の自己同型は極大イデアルを保つため、
  下界の商 `C/Q` の条件は `ψ(m_T) ⊆ Q` 一つから全共役へ渡せる。
  商での支持から消去指数を選び、全ての正の冪の Koszul 消滅を共通下界に適用する。
- `LengthAlgebra/Ordinary.lean`：Noether 局所環でパラメータの生成イデアルの根基が
  極大イデアルを含めば、全ての正の冪について通常 Koszul 有限性を満たす。
- `LengthAlgebra/QuotientBounds.lean`：パラメータを消す商の冪ねじれ性と長さの上界を証明した。
  第零 Koszul ホモロジーからの全射により、Koszul 有限性からその商の長さの有限性も従う。
  係数環 `C` の Noether 性は不要。
- `Paper/Section5/ApproximationPositivity.lean`：`exists_secondComparison_pos_of_approximation`
  は、有限近似の極小分解を切り詰めて係数変更し、同じ支持つき対象 `X` について
  全ひねりの通常評価が `lambdaChi` に等しいこと、第二比較、全共役の正値性、
  `lambdaChi > 0` を同時に導く。複体・振幅・極小性・正の零次階数・支持・正値性を
  外から与える必要はなくなった。
- `exists_secondComparison_pos_of_primary` は通常有限性と支持変更を準素な支持条件から導く。
  下界の商を `C / m_T C` に選び、その冪ねじれ性と長さの有限性も確認する。
  商について残す数値条件は拡大非負実数としての `0 < λ(C / m_T C)` だけである。

前節で残していた係数変更後の振幅・極小性の確認は、この一般定理の中で完了した。
具体化に残るのは、論文の環と写像を選び、同じ近似列について Tor・長さの極限、局所性、
支持の根基条件、Koszul 消滅・Euler 数の一致、不変 K₀ 類の降下、商の正の長さを供給すること。
`ι` をひねった写像に取れば正値性の結論は `c_σ > 0` になり、実際に構成した対象の
係数変更後の評価が `b_{σ,γ}` の候補になる。`core_statement` への具体的適用全体は未完了。

検証：公開入口を含む全体 `lake build` 成功（3458 jobs）。新規9宣言の公理依存は
全て `propext`・`Classical.choice`・`Quot.sound` のみで、`sorryAx` なし。
対照として確認した `theorem_4_7_K0`・`lemma_5_4` には既存の引用による `sorryAx` が残る。
新規3モジュールと `Ordinary.lean` の追加補題に未証明入力・仮定の束を追加していない。
新規モジュールの警告なし。`git diff --check` と追加コードの行末空白・行長の検査も通過。
本文・付録の TeX は変更していない。

### 長さ代数の公式・正則基底・塔の有限近似との接続（2026-10-10 続行）

- `CommutativeAlgebra/FiniteLocalSupport.lean`：剰余体への全射性から局所性を導き、
  有限局所代数で基底の極大イデアルの像が閉点を定めることを確認した。
  有限余長のイデアルから極大イデアルの生成元と正の共通消去冪を選ぶ。
  基底の極大イデアルの冪で消える有限代数は Artin 環であり、共通剰余体をもつ環から
  その Artin 局所環への写像の核は有限余長であることも証明した。
- `Paper/Section4/LengthAlgebraRealization.lean`：長さ代数の定義域の有限生成性・支持、
  正の冪の Koszul 有限性、Koszul Euler 数の階数公式、通常 Euler 数との一致を供給する。
  比較先の商 `C / m_T C` の正値性は、パラメータ商の階数公式と正の階数から導く。
  この段階は正則パラメータの正則性や降下の引用を使わない。
- `Paper/Section5/LengthAlgebraPositivity.lean`：有限局所代数と共通剰余体、長さ代数の
  高次 Koszul 消滅・商の階数公式から、第二比較と正値性の適用条件を確認した。
  支持のパラメータと消去冪、両写像の局所性、根基条件、Koszul 有限性・Euler 数の一致、
  比較先の商の正値性を個別に入力する必要はなくなった。
  Koszul 分解・通常の階数公式・不変類の降下は個別の仮定とし、証明済みの部分を分離する。
- `RegularLengthAlgebraPositivity.lean`：正則基底と幾何的群作用から、上の三つの仮定を
  既存の正則パラメータと `supportedRankK0_descent` の引用で供給する。
  新しい未証明定理は追加していない。
- `TowerPositivity.lean`：`lambdaChi_pos_of_parameter_tower` が塔のデータから
  `lambdaChi > 0` を導く。Lemma 5.4 を一度適用して同じ近似列と全 Tor 極限を構成し、
  Lemma 5.3 から各極限の有限性・高次消滅を供給する。
  共通消去イデアルには `ker(B → Z)` を選び、その有限余長も上の一般補題で確認する。
  超フィルターも内部で選ぶので、近似列・支持生成元・消去冪・複体・比較等式・Euler 正値性を
  外から入力しない。

塔の定理の変数と本文の対応は次のとおり。

| コードの対象 | 本文の対象 |
| --- | --- |
| `A₀`, `Z` | `A_D`, `D′ / I_σ` |
| `D`, `mu`, `φ` | `C_D`, `λ_D`, `ι_σ` |
| `B x` | `R / (x)` |
| `A`, `T`, `C`, `lam`, `G` | `A_E`, `E′`, `C_E`, `λ_E`, `G_E` |

この対応で結論は `c_σ > 0` になる。正値性の導出に必要な有限近似と第二比較の接続は完了した。
残る具体化は、同じ論文の設定で正規化基底・有限局所代数・パラメータ `x` を選び、
塔の作用 `θ` の両立、二つの長さ代数の公式、近似元の商 `U` の有限な正の長さ、
剰余体・次元・幾何的群作用の条件を供給することである。
`core_statement` からこれらを構成し、第一比較と結ぶ段階は未完了。

検証：公開入口を含む全体 `lake build` 成功（3463 jobs）。新規15宣言を公理監査し、
一般補題と `exists_secondComparison_pos_of_lengthAlgebra` の13宣言は
`propext`・`Classical.choice`・`Quot.sound` のみだった。
`exists_secondComparison_pos_of_regular` と `lambdaChi_pos_of_parameter_tower` には、
既存の正則パラメータ・不変類の降下・塔の長さの引用に由来する `sorryAx` が残る。
新規5モジュールに `sorry`・`axiom` 宣言、仮定の束、警告なし。
`git diff --check` と追加コードの行末空白・100文字の行長の確認も通過。
本文・付録の TeX は変更していない。

### 本文のパラメータ商・全共役の正値性・第一比較との接続（2026-10-10 続行）

上の塔の入口に残っていた具体的な仮定確認を、本文の環を使って進めた。

- `FiniteLocalSupport.residue_surjective_comp_of_surjective`：共通剰余体の条件を
  局所環の全射像へ移す。`IsSystemOfParameters.map_aut`：自己同型でパラメータ系を移す。
  どちらも長さ代数やその群作用を使わない一般補題である。
- `Paper/Section5/ParameterLengthPositivity.lean`：`D′/(ι(x))` を実際に構成し、
  商の局所性・基底上の有限性・極大イデアルの冪による消去・共通剰余体を確認する。
  `Preparation.paramTheta` とその二つの可換性の補題を、同じ商に適用する。
  `λ_D` の定義域の有限生成性・支持・消去冪も確認し、(2.5) の一乗の場合と
  重複度の正値性から `0 < λ_D(C_D/(x)C_D) < ∞` を導く。
  `lambdaChi_pos_of_parameter_lengthAlgebras` はこれらを `TowerPositivity` に渡す。
  比較先の剰余体条件も `R → E′` について一度与えれば `R/(x) → E′` に移せる。
- `TwistedLengthPositivity.lean`：一つのパラメータ系と (2.4)・(2.5) から、
  `twistedEuler_pos_of_lengthAlgebras` が第一比較に現れる全ての `c_σ > 0` を導く。
  各自己同型について、パラメータ系と共通剰余体条件を内部で移す。
  `C_D` への群作用、`λ_D` の群不変性、各 `σ` に別々の塔の仮定は要求しない。
- `Positivity.lean`：`chi_pos_of_firstComparison` と `core_of_twistedEuler_pos` により、
  得られた `c_σ > 0` を直接第一比較へ渡す。従来の二つの比較からの算術も共通部分を使う。
- `CoreLengthPositivity.lean`：`core_of_lengthAlgebras` が、同じ具体的設定で
  全共役の正値性から第一比較までを接続する。比較元の (2.6) は (2.5) と正則基底の
  重複度の階数公式から供給する。第二比較の数値、中間複体、有限近似、商の正値性は
  追加の仮定にしない。

次に残る存在構成は、`core_statement` の仮定から有限拡大と正規化基底・群作用を選び、
`exists_regular_parameters_in` のパラメータを有限拡大へ移し、
`R/(x) → E′` の代数構造と有限性を用意すること。
長さ代数自体は定理2.5から選び、その結論を今の (2.4)・(2.5)・(2.6) の引数へ渡す。
この選択と照合はまだ完了しておらず、`core_statement`・`main_statement` は変更していない。
重複度・塔の長さ・正則パラメータ・降下・第一比較の既存の引用依存も残る。
本文・付録の TeX は変更していない。

検証：公開入口を含む全体 `lake build` 成功（3466 jobs）。新規8宣言のうち、
剰余体の移送・パラメータ系の移送・商の長さの同定・第一比較からの算術の4宣言は
`propext`・`Classical.choice`・`Quot.sound` のみ。
パラメータ商への適用・全共役の正値性・第一比較の具体的適用・二つの接続を合わせた定理の
4宣言には既存の引用に由来する `sorryAx` が残る。
変更した `chi_pos_of_comparisons` も標準公理のみである。
新規3モジュールに `sorry`・`axiom` 宣言、仮定の束、警告なし。
`git diff --check` と新規モジュールの行末空白・100文字の行長の確認も通過。

### パラメータ選択・定理2.5からの長さ代数の構成（2026-10-10 続行）

前項に残っていたパラメータ・商代数の選択と、定理2.5の適用を正値性へ接続した。

- `CommutativeAlgebra/FiniteParameters.lean`：有限局所拡大への準素イデアルの移送、
  単射な有限拡大へのパラメータ系の移送、根基条件から商環内のパラメータ系を得る補題を証明。
  `I ≤ Q` と有限 `R/Q` 代数から、両立する有限 `R/I` 代数構造も存在量化して構成する。
- `Paper/Section5/ParameterChoice.lean`：既存の `exists_regular_parameters_in` で選んだ
  `x_i ∈ Q` を `R/P → D′` へ移し、`R` 上の正則性と `D′` 上のパラメータ系を同時に得る。
  選択の非混合性への引用依存は残り、有限拡大への移送自体は証明した。
- `SelectedParameterPositivity.lean`：`core_of_lengthAlgebras_with_parameter_choice` は
  次元・根基条件から上のパラメータを選び、`R/(x) → E′` の代数構造と有限性を作る。
  `x`、その正則性、`D′` 上のパラメータ条件、商代数構造を外部入力から取り除いた。
- `LengthAlgebra/Nontrivial.lean`：正の長さの加群が存在すれば係数環は非自明。
  定理2.5で得た長さ代数の非自明性を、商の長さの階数公式から導くために使う。
- `NormalizationPositivity.lean`：`core_of_normalization_bases` は定理2.5を二回使って
  `C_D`・`C_E` を選び、(2.4)・(2.5)・(2.6) を正値性の入口へ渡す。
  共通剰余体から標数と完全性を移し、単射性から正の階数・素スペクトルの全射性を導く。
  不変環が正規化基底であるという条件から、両有限群作用の幾何的推移性も導く。
  パラメータ・長さ代数・その公式・比較値・有限近似・複体・正の Euler 数を入力にはしない。
  `AsymptoticPositivity` の公開入口から使える。

残りは `core_statement` の仮定から、正規化基底とそれを固定する有限群作用付き拡大を
両立して構成すること。完備局所整域の有限拡大であり、共通剰余体、生成点での分離性、
不変環条件、定理2.5が要求する冪級数環・Wittベクトル環の具体的な基底表示を確認する必要がある。
任意の拡大を先に選んでから補題2.2で基底を独立に選ぶだけでは、群作用との両立は得られない。
`core_statement`・`main_statement` の証明全体の完了とはしない。
新しい未証明入力は追加せず、本文・付録の TeX も変更していない。

検証：全体 `lake build` 成功（3471 jobs）。新規8宣言のうち、有限拡大・商代数の4補題と
長さからの非自明性は `propext`・`Classical.choice`・`Quot.sound` のみ。
パラメータ選択・その正値性への接続・正規化基底からの正値性の3宣言は、
非混合性・定理2.5・降下などの既存の引用に由来する `sorryAx` に依存する。
新規5モジュールに `sorry`・`axiom` 宣言、仮定の束、警告なし。
`git diff --check` と新規モジュールの行末空白・100文字の行長の確認も通過。

## 従来の §4 固有の実装計画

2026-10-08 作成、2026-10-10 改訂。現在の作業ツリーの実装と [PLAN.md](../PLAN.md) 冒頭の規約に合わせた計画。4.5 は一様な自由持ち上げと既存の有限版 Lemma 3.5b を使い、列の圏の K₀ の明示計算は追加課題とする。

数学的な代替証明は [section-4-devissage.md](../section-4-devissage.md)、プロジェクト全体の入力管理は [PLAN.md](../PLAN.md) に従う。この節は旧計画の記録であり、現在の優先順位は上記の付録 B.9 に従う。

今回の変更は、3.5a の有限性の証明で整備された具体的な道具を出発点にすること。まずその証明をランクによる一様上界へ強める S4a を独立に行い、その後に商の t 構造と冪等完備性 S1 を進める。採用した数学的経路は維持し、着手順と再利用する部品を改める。

仮定をまとめる専用の `structure`・`class` は作らない。旧案の `AsymptoticEvaluation` も作らず、圏・関手・長さを定義し、それぞれの性質を個別の定理として証明する。既存の `NormalizedLength` や Mathlib の圏・t 構造は数学的対象の定義として利用する。引用する未証明結果は名前付きの `sorry` 定理を証明内で直接呼び、公理監査と引用箇所で依存を明示する。

## 到達点と必須範囲

| 到達点 | 完了条件 | 残る仕事 |
| --- | --- | --- |
| M5a：4.5 の代替証明 | 任意の X ∈ P_A^J の一様自由持ち上げを構成し、実際に構成した Euler 評価について Prop. 4.5 の両等式を証明する | Lemma 4.6、一般の係数 H による降下との接続、Theorem 4.7 |
| M5b：論文で使う §4 | Lemma 4.2、Prop. 4.3 と (4.2)、Prop. 4.5、Lemma 4.6、Theorem 4.7 を接続し、§5 が使う評価・ひねり・台の定理を供給する | Theorem 3.1 は引用、正則局所環の標準事実は現在の保留方針に従う。依存先の `sorryAx` を明示する |
| 追加課題 | K₀(P_A^J) ≃ G_s/g_s、その生成元と評価を明示する | sₙ → ∞ の場合の ℓ∞/c₀ との同定など |

「最小範囲」は 4.5 で §4 全体を終えるという意味ではない。M5a を最初の論文上の到達点とし、M5b までを §4 の必須範囲とする。追加課題を終えなくても M5a・M5b を完成できる依存関係にする。

M5b の Theorem 4.7 は、論文と同様に Theorem 3.1 を使う。現在の方針ではその証明と Lemma 3.2・3.3 の K 理論の基礎整備は本トラックで行わず、一般の係数 H に対する必要な帰結を名前付きの引用定理として述べる。引用に依存する完成と、標準公理だけによる完成を区別する。Lemma 4.6 や一様持ち上げ自体を新しい未証明引用に移して M5a・M5b の完了とはしない。

## 現在の実装から再利用するもの

| 部品 | 現状と用途 |
| --- | --- |
| `Paper/Lemma3_5/Ordinary.lean`、`Normalized.lean` | `lemma_3_5b_ord_of_koszul` と `lemma_3_5b_lam_of_koszul` を各 Fₙ に適用する。正則性から Koszul 分解や Euler 階数公式を供給する箇所の引用依存は別に明示する |
| `HomologicalAlgebra/Basic.lean` | `finiteFree_module_induction`、`boundedFiniteFree_induction`、`bottomProjection` とその核の項の同型を実装済み。S4a の定量化では、帰納の各段階で階数を保持する |
| `CommutativeAlgebra/Koszul.lean` | `koszulFunctor_shortExact`、シフトとの同型、`retractKoszulComplexOn` がある。係数つき Koszul 複体のフィルトレーション・直和因子を作り直さない |
| `PerfectComplex/NormalizedLength.lean`、`NormalizedEuler.lean` | `lambdaHomology_cone_le`、`lambdaHomology_koszulComplexOn_ne_top` などを実装済み。通常長さは `NormalizedLength.ordinary` として共通の理論を使える。有限性から O(sₙ) への定量化は未実装 |
| `HomologicalAlgebra/NullHomotopy.lean`、`PerfectComplex/Support.lean` | ホモロジーの消去から零ホモトピーへの橋渡しがある。存在量化された冪をそのまま段ごとに選ばず、共通の次数幅から一様な冪を取り出す接続が必要 |
| `HomologicalAlgebra/KProjectiveLift.lean`、`Resolution.lean`、`Basic.lean`、`ConeResolution.lean` | S5 の制御された Horseshoe 構成の材料。`IsResolutionOf` と `Inputs.regularResolution` だけでは共通の次数幅とランク評価は得られない |
| `GroupTheory/ConjugateSum.lean` の `conjSum_eq` | 任意のアーベル群について証明済み。Theorem 4.7 の最後の共役和の等式に使う |
| `PerfectComplex/K0.lean` | 有限自由複体を生成元とする具体的な K₀。商圏 P_S^J の K₀ を直接与えるものではない。普遍性・関係式の実装方針を再利用する |
| `Inputs/Descent.lean` の `theorem_3_1_K0` | H = A の場合の未証明入力。一般の連結な H が必要な Theorem 4.7 には、そのまま適用できない |

3.5a の `lemma_3_5a_lam_finite` は証明済みで、中間補題も未証明入力に依存しない。一方、列の圏 E_S・D_S・P_S、§4 の評価関手、超極限の専用 API、ランクに比例する一様上界は未実装。「各 n で有限」は O(sₙ) を意味しないので、S4a を独立した成果物にする。

2026-10-10 の確認：`lake build SerrePositivity.Paper.Lemma3_5` 成功。公理監査では、`boundedFiniteFree_induction`、`koszulFunctor_shortExact`、`retractKoszulComplexOn`、Koszul ホモロジーの有限性、`lemma_3_5a_lam_finite`、両 `lemma_3_5b_*_of_koszul`、`conjSum_eq` は標準公理のみ。正則局所環の主張に接続した `lemma_3_5b` は保留中の引用により `sorryAx` に依存する。したがって、低水準の定理の証明と、その仮定を供給する引用を分けて再利用する。

Mathlib の固定版は前回と同じ `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。通常の局所化、Serre 商、t 構造と切り詰め、加法圏の Karoubi 包絡はある。一方、商への t 構造の降下、有界 t 構造からの冪等完備性、Karoubi 包絡への三角構造の延長は、前回確認した未整備の接続として引き続き計画に入れる。リポジトリの有限複体側の整備が、そのまま商圏側の実装完了を意味するわけではない。

## 共通の定義と規約

- s : ℕ → ℕ は各項が正。O(sₙ)、o(sₙ) は `Filter.atTop` における通常の漸近条件とする。主経路には sₙ → ∞ を要求しない。
- 非単項超フィルター U は長さの評価で使う。ランク商 N_S と、正規化長さの超極限が零となる Serre 部分圏を別の定義にする。
- E_S の対象はランク O(sₙ) の有限自由 S 加群の列、射は任意の行列の列。係数やホモトピーに一様な大きさの制限を加えない。
- D_S は共通の有限な次数範囲をもつ複体から作る。各 n ごとに有界であることだけでは対象にしない。既存実装と同じ cochain の ℤ 添字を使い、論文の H_i は H^(−i) と対応させる。
- 台は、その対象が属する圏で z_j^v id = 0 となる共通の v ≥ 1 の存在で定義する。商の前の S_S と商の後の P_S^J を区別する。
- A は正則、T は一般には正則でない。t 構造による持ち上げの強化は A 側だけに適用し、T 側の直和因子は一般の Karoubi 延長で扱う。
- 群作用・ひねりは有限版 3.5 と同じ規約を使う。`K0.lean` の左作用には逆元が入るため、論文の g* と共役和の添字変換の対応を明示する。λ の G 不変性を追加しない。
- 三角圏としての構成と、4.6 で用いる複体・dg の構成の対応を維持する。圏同値だけを作って dg 構造との両立を後で自動とみなさない。

## 段階ごとの作業と完了条件

### S0 目標の型と入力境界

最初に Prop. 4.3、Prop. 4.5、Lemma 4.6、Theorem 4.7、§5 向け評価の主張と依存を固定する。未構成の圏については設計上の署名を記し、既存の定義・証明と区別する。

§4 の長さの仮定は既存の `NormalizedLength` と (4.1) に合わせる。Theorem 2.5 の強い性質や A の完備性を、4.5 のために追加しない。4.6 は非可換な連結 dg 係数を扱うため、その係数に対する Theorem 3.1 の入力が必要であることを型の段階で明示する。

仮定は個別の引数、存在結論は存在量化と明示的な連言で書く。専用の設定構造体や、大きな連言の別名で置き換えない。正則パラメータからの Koszul 分解は現在の引用に接続し、有限長加群の一様自由分解 S5 自体はその Koszul 分解から証明する。一般の正則局所環の大域次元の整備を待たない。

完了条件：各定理に必要なデータと仮定、名前付き引用が一覧になり、結論を未証明の仮定に移す循環がない。

### S1 商の t 構造と冪等完備性

S4a の定量化の後、最初の圏論の実装単位として、列の圏から独立した次の二つの定理を扱う。

1. 有界 t 構造をもつ三角圏 C と、切り詰めに安定な thick 部分圏 W について、W の heart が C の heart の Serre 部分圏となる条件の下で、C/W に有界 t 構造を降ろす。
2. 有界 t 構造をもつ三角圏は冪等完備である。

Mathlib の heart のアーベル性に関する接続も必要に応じて補う。証明に三角的 Karoubi 包絡などの一般論が必要なら、S2 と共用する前提補題として先に整備する。具体的なアーベル圏を heart と同定する設計を利用できる場合は、その形で必要な仮定を明示する。切り詰め安定性だけで商の t 構造を主張しない。

完了条件：二つの定理が未証明の補助定理に依存せずコンパイルされ、公理監査を通る。ここで実装上の大きな障害が判明した場合は、その箇所を記録して設計を見直す。原論文の証明への変更は明示的な方針改訂として扱う。

### S2 ランク商と共通の圏論的基盤

E_S、共通有界な複体のホモトピー圏、その冪等完備化 D_S、rank o(sₙ) の生成元からなる thick 部分圏 N_S、P_S = (D_S/N_S)^♮ を構成する。S = A と S = T で共通の定義を使う。

シフト・錐・直和因子、中心 A の作用、Koszul テンソル、基底変更 A → T、T の自己同型によるひねりを整備する。支持条件の thick 性と、これらの関手がランク条件・台を保つことを証明する。Karoubi 包絡の三角構造とホモロジー的関手の延長は、加法圏の延長 API とは別に確認する。

P_S^J の K₀ は、対象の類を同型と三角形の関係で割る群として必要な範囲で構成する。加法的評価からの準同型、exact functor からの写像、同値・群作用との両立を用意する。この K₀ の基盤は必須であり、追加課題の明示計算とは区別する。

完了条件：商関手・支持部分圏・基底変更・ひねりが定義され、以後の定理が同じ圏と K₀ を使える。

### S3 Lemma 4.2

支持つき対象 X から小さい対象 Y への射を、Koszul テンソルを使って支持つき小対象へ因子化する。これを用い、支持つきの roof による射の表示と零判定から

  S_S/(S_S ∩ N_S) → D_S/N_S

の完全忠実性を証明する。続いて、商の後の支持対象が一様に台をもつ対象の像の直和因子となること、およびその Karoubi 包絡と P_S^J の同値を示す。

完了条件：S = A、T の両方に適用できる Lemma 4.2。固定された射影の鎖写像への持ち上げは仮定しない。

### S4 Proposition 4.3 と公式 4.2

#### S4a 既存の有限性の証明を定量化する

列の圏や商を作る前に、有限自由複体 F の長さを、その各項のランクで評価する補題を作る。3.5a で整備された `koszulFunctor_shortExact`、`bottomProjection` とその核、シフトとの同型を使い、有限性の帰納法にランクの重みを持たせる。現在の `boundedFiniteFree_induction` は性質を伝える帰納原理であり、定量評価そのものを既に返すわけではない。必要なランク等式と下端を除いた和の分解を追加する。

目標は cochain 規約で

  λ H^q(Kv ⊗_A (F ⊗_T C)) ≤ Σ_{i=a}^b rank_T F^i · λ H^(q−i)(Kv ⊗_A C)

という上界。`koszulComplexOn` で表し、一般的な二重複体のスペクトル系列を導入しない。固定した v、a、b に対し、右辺の Koszul ホモロジーの長さは F に依存しない。通常側は C = T、λ = `NormalizedLength.ordinary` に特殊化し、Euler 和だけでなく次数ごとの上界も共通化する。

`retractKoszulComplexOn` と長さの単調性から、パラメータ作用が零ホモトピックな F のホモロジーにも上界を戻す。C の Noether 性や T 上の平坦性を追加しない。値は有限性を示すまでは ℝ≥0∞ で扱い、元の T 自由加群のランクまたは指定した有限基底の個数を用いる。

完了条件：単一複体、共通次数範囲の複体、支持つき複体について定量的な上界が得られる。列に適用した際の O(sₙ) の定数が n に依存しないことまで示す。これは有限性の既存証明を再利用した新しい定理であり、3.5a を証明し直す作業にはしない。

#### S4b 長さの商とホモロジー評価

S2・S3 の後、共通の冪で消され長さ O(sₙ) の加群列のアーベル圏と、正規化長さの超極限が零となる Serre 部分圏を作る。S4a の上界を使い、商上の有限な非負加法長さを得る。C 側の対象に有限生成性を課さない。

次に、Koszul 分裂と thick 性から S_S ∩ N_S のホモロジーが長さの Serre 商で零になることを示す。ホモロジー関手を支持つき Verdier 商に降ろし、S3 を用いて P_T^J 全体へ延長する。直和因子への延長では、冪等元の像が長完全列の完全性を保つことも示す。

完了条件はすべて次を満たすこと：

- H_i^ord、H_i^C と、それらの長さ b_i^ord、b_i^C が任意の X ∈ P_T^J に定義される。
- b_i は有限・非負で、対象ごとに共通の有限範囲の外では零。
- Euler 和が K₀(P_T^J) 上の準同型 χ_ord、χ_C になる。A 側の通常評価 χ_A も得る。
- 商の後で支持される自由複体列 F に対し、論文 (4.2) を証明する。右辺の生のホモロジーは Kv ⊗ Fₙ のものを使う。
- (4.2) は非負な b_i を構成した後の定理とし、多項式の形式的な割り算で b_i を定義しない。

論文の homological 添字では (1+t)^e となる。cochain 添字との変換を一か所で証明し、有限和の交換・シフトの符号を統一する。上界に使う既存の retract と、(4.2) の等式は別である。(4.2) は商で零となるスカラー作用の錐の長完全列から b_i(Cone) = b_i(X) + b_(i−1)(X) を反復して証明する形を優先し、数値等式のためだけに完全な分裂同型を余分に構成しない。

### S5 A 側の一様持ち上げ

固定した Koszul 分解と Horseshoe 構成から、すべての有限長 A 加群 M に対し、次数 [-e,0] の自由分解 P(M) と rank P(M)^i ≤ C·ℓ_A(M) を得る。C は固定した A とパラメータ系だけに依存すればよく、二項係数の厳密なランク公式は不要。

`Inputs.regularResolution` は個々の有限生成加群に有界自由分解を与える引用で、共通の次数幅と長さに線形なランク評価を保証しない。S5 の代用にはしない。Koszul 分解の存在を明示的な仮定にした一様分解の補題を証明し、正則パラメータの正則性に関する保留中の引用は、その適用箇所に限って残す。

`exists_pow_nullHomotopy_of_homology_annihilated` の証明では次数幅から指数を選んでいるが、公開された結論は `∃ n`。列に適用するため、共通の境界 a、b だけで決まる指数を結論にした補題を追加する。各段で任意に選んだ指数が一様だとは仮定しない。

列の圏から各段の導来圏の積への完全忠実性を確認し、次を順に証明する。

1. S_A のホモロジーは共通の J の冪で消され、長さ O(sₙ)。
2. 一様自由分解と有限 Postnikov 三角形により、S_A は切り詰めで閉じ、有界 t 構造をもつ。S_A の対象自体も実際の共通有界自由複体列で表せる。
3. X ∈ S_A に対し、X ∈ N_A と、全次数のホモロジーの長さが通常の o(sₙ) であることが同値。
4. heart 上の通常の o(sₙ) 条件が Serre 条件を満たす。S1 と S3 から S_A/(S_A ∩ N_A) ≃ P_A^J を得る。

完了条件：任意の X ∈ P_A^J に対し、一様に台をもち、共通有界で項のランク O(sₙ) の実際の自由複体列 F と、同型 X ≃ q_A(F) を与える。「直和因子として表せる」だけでは未完了。S_A と heart の有界導来圏の同値は要求しない。

### S6 Proposition 4.5

S5 の F を選び、各 Fₙ に完備性を仮定しない既存の有限版 3.5b を適用する。F とその基底変更の共通有界性、S4 の長さの上界と評価の同定を使い、有限 Euler 和と正規化超極限を交換する。

完了条件：任意の X ∈ P_A^J について

  χ_ord(X ⊗ᴸ_A T) = rχ_A(X) = χ_C(X ⊗ᴸ_A T)

を証明する。ここで M5a 完了。Lemma 4.4 と、原論文の Prop. 4.5 における二つのスペクトル系列の降下は、この経路の必須作業から外す。

### S7 Lemma 4.6 と降下への接続

この段階は S4・S5 とは別の大きな実装課題であり、4.5 の簡略化で省略されない。S2 の圏のモデルを決める時点で、以下の接続を設計する。

1. U_S = (S^{sₙ}) が E_S の加法的生成元であること、行列環の積 B_S = ∏ₙ M_{sₙ}(S) による D_S の表示。
2. A 上の自由列の射加群の A 平坦性、T の有限表示性を使う積とテンソル積の比較。T 側では射加群の T 平坦性を確認し、T 自体の A 平坦性は仮定しない。
3. rank-small 自由列を消す dg 商と、その perfect hull・冪等完備化による P_S の表示。選んだ生成元の自己準同型 dg 代数 H の連結性。
4. P_A ≃ Perf(H)、P_T ≃ Perf(H ⊗ᴸ_A T) と、基底変更・中心作用・G のひねりとの両立。
5. パラメータの冪による零作用と、中心局所化で消える台の同値。これにより Theorem 3.1 の supported K₀ と同定する。

homological な「連結」は cochain 規約では正次数が消えることに対応する。必要な dg 商・生成元による表示を個別の補題に分ける。一般の dg Morita 理論全体を先に整備することは目標にしないが、表示の同値とその両立条件は省略しない。

完了条件：S2 で定義した同じ P_A、P_T に対する Lemma 4.6 と支持・群作用の同定。ここで一般の連結な H に対する Theorem 3.1 の K₀ の帰結を適用し、不変な類 y について

  ∃ n > 0, ∃ x ∈ K₀(P_A^J), n·y = baseChange(x)

を得る。`Inputs/Descent.lean` の H = A 版を一般 H 版として流用しない。必要な H 版を個別の仮定をもつ名前付き引用定理として用意し、証明は `sorry` のまま残すという現在の方針に従う。高次 K 理論や Lemma 3.2・3.3 の再証明を §4 の着手条件にはしない。

### S8 Theorem 4.7 と §5 向けの接続

S4 の二つの準同型、S6 の A から来る類上での一致、S7 の不変類の降下に、既存の `conjSum_eq` を適用する。既存補題は正の整数倍による降下で十分なので、最後の群論のために有理化の API を重複実装しない。

完了条件：すべての X ∈ P_T^J に対する共役和の一致と、§5 が必要とする b_i・非負性・有限性・(4.2)・ひねりの API を同じ評価から供給する。λ の G 不変性や、個々の X で χ_ord(X) = χ_C(X) となることは仮定しない。

S4 の具体的な評価を使い、有限支持・非負性・(4.2)・ひねりとの両立を個別の定理として §5 へ渡す。`AsymptoticEvaluation` や `CoreData`、`Inputs.Core` のような設定用の束は導入しない。現在の `Paper/Section5/Positivity.lean` の `core_of_inputs` は第二比較と正値性を個別の引数で受け取るので、§5 の証明でそれらを構成して渡す。

Theorem 4.7 だけで第二比較や正値性が完成するわけではない。有限近似・切り詰め・支持・係数評価を扱う §5 の接続を別に証明する。「切り詰めた列が商で支持される」という十分条件も、rank-small 誤差と支持条件から示す §5 側の補題として分ける。

§2 の具体的な塔や Theorem 2.5 の構成を待たず、§4 は `NormalizedLength` と (4.1) を個別に仮定して進められる。後で §2 の成果から (4.1) を供給する。塔の作用や上限の性質が必要な有限近似は §5 側に置き、§4 全体の追加仮定にはしない。

## 依存関係と着手順

```text
S0 + 既存の 3.5a の基盤 → S4a ランクによる一様上界
S0 → S1 商の t 構造と冪等完備性
S0 → S2 列の圏とランク商 → S3 Lemma 4.2
S2 + S3 + S4a + 長さ・超極限    → S4b 評価と (4.2)
S1 + S2 + S3 + 一様自由分解    → S5 一様持ち上げ
S4b + S5                      → S6 Prop. 4.5
S2 + dg の構成 + Theorem 3.1 の引用 → S7 Lemma 4.6 と降下
S4b + S6 + S7                 → S8 Theorem 4.7
```

図の S1 は S5 に必要で、S4 には不要。S5 の一様自由分解そのものも S4 に依存しない。S7 は S2 のモデルに依存するため、型と両立条件の設計を S0・S2 で済ませ、証明は独立の段階として進める。

直近は S0 → S4a → S1。既存の有限性の証明を定量化して最初の成果を得てから、依然として主要な未整備部分である二つの圏論定理に取り組む。その後 S2 → S3 を整備し、S4b と S5 を S6 に接続して M5a に到達する。S6 の後は追加の K₀ 計算より S7 → S8 を優先する。

## 配置と検証

予定する配置は、一般的な圏論を `CategoryTheory/`、一般の Horseshoe 構成を `HomologicalAlgebra/`、有限長と Koszul 分解を使う一様自由分解を `CommutativeAlgebra/`、S4a の長さの上界を `PerfectComplex/KoszulLengthBound.lean`、列・商・評価を `Asymptotic/`、論文の主張を `Paper/Section4/` とする。上位の長さ・局所環の理論を `HomologicalAlgebra/` から import しない。ファイルは各段階の実装時に作る。

現在は §2 など別の作業の未コミット変更がある。§4 の先行実装は新規ファイルから既存部品を import して進め、共有ファイルとルートの `SerrePositivity.lean` の変更は接続時にまとめる。特に `Inputs/LengthAlgebra.lean` と既存の `NormalizedLength.lean` は、§2 の作業中に別の設計へ書き換えない。日本語のモジュール・宣言 docstring は `PLAN.md` §18 の規約に従う。

各段階で関連モジュールをビルドし、最終定理の `#print axioms` と名前付き引用の使用箇所を確認する。`#print axioms` の `sorryAx` は引用定理の名前別一覧ではないため、引用箇所も記録する。S4a・S1 の一般補題は未証明入力なしを目標とし、S5・S6・S8 では保留・引用による依存と新規の未証明箇所を区別する。

定義の整合性は次の具体例・特殊化で確認する。

- rank o(sₙ) の自由列とその有限な錐・シフトが P_S で零になる。
- 可変個数の Koszul 列について、既存の有限評価と正規化超極限が一致する。
- Remark 4.1 の DVR の例では、商の対象の評価は零であり、生の H₀ の正規化長さをその評価として採用しない。
- (4.2) は商の後で初めて支持される列にも適用できる。
- 群作用の逆元の規約と、論文の共役和が一致する。

これらは定理の適用範囲を確認するための検証であり、一般定理の証明の代用にはしない。

## 追加課題

M5b の必須作業を優先し、余裕があれば次を行う。

1. 通常の O・o から G_s = { c ∈ ℤ^ℕ : |cₙ| = O(sₙ) }、g_s = { c ∈ ℤ^ℕ : |cₙ| = o(sₙ) } を定義し、K₀(S_A)、K₀(W_A)、K₀(P_A^J) ≃ G_s/g_s を明示する。
2. 個数が変わる Koszul 複体列による生成、Euler 評価 [c] ↦ lim_U cₙ/sₙ を示す。
3. 追加仮定 sₙ → ∞ の下で、G_s/g_s と ℓ∞(ℕ,ℝ)/c₀(ℕ,ℝ) の同定を検討する。

これらは論文のための K₀ の構成・関手性・降下を置き換えるものではなく、その対象をより詳しく記述する追加結果である。
