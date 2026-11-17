# BS-W16 の報告（report-codex-w16.md） — L12a 前半（C444〜C451、停止判断）（§157〜§208、2026-11-14）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 157. L12a の入口：元の合成側の添字と項（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

L11は6d7768d43へ保存した。次は§112.2の固定したL12aの全体（nullaryを含む）へ進む。
まず内側arityがn+1の枝で、既存OverlapPartitionと合成基底語の切断をそのまま直積にする。
外側語の長さはm+1+d、合成語の長さはm+(n+1)+(d+e)。切断区間の数
m+n+(d+e)+1へ等式移送するだけで、色や合成語は変えない。
compositeBasisWord_listとC345の同じ語長の移送の法則で、指定した元のリストとの一致を保持する。

合成側の値は元のcompositionSign倍の元のcutTerm。全次数−(d+e+q)へ同じ等式で移す。
退化した面も添字から除外せず、C347で元の正規化生成元により零になる値として保持する。
これは§112のCompositeBalanceIndexの合成側の正arityの枝を構成するもので、
新しい数学を一覧へ足すものではない。nullary・二段側・対応・符号・実テンソルの比較は未完。
型は次。

```lean
abbrev PositiveCompositeCutIndex {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (_v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1)) (q : ℕ)

def positiveCompositeCutWord {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Surjection.Word (m + (n + 1)) ((m + n + (d + e)) + 1)

lemma word_eq_mp_ofFn {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l) :
    List.ofFn (Eq.mp (congrArg (fun k => Surjection.Word r k) h) v).val =
      List.ofFn v.val

lemma positiveCompositeCutWord_list {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    List.ofFn (positiveCompositeCutWord u v k r).val = Surjection.compositeWord u v k r

def positiveCompositeCutTerm {m n d e q : ℕ} (S : SSet.{0})
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    (power (chains A S) (m + (n + 1))).X (-((d + e + q : ℕ) : ℤ))

lemma positiveCompositeCutTerm_eq_zero {m n d e q : ℕ} (S : SSet.{0})
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌)
    (h : ¬Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    positiveCompositeCutTerm A S u v k c x = 0
```

各証明200行以内。この枝の型検査だけでL12aの全称主張を完了として数えない。
L12a全体の1,400〜2,400行の見込みを保持し、半分に達した時点で実測と残りを報告する。

## 158. L12a の合成側の最初の枝の検証・保存

一覧：済み 12／全体 48（うち追加 4）

PositiveCompositeCuts.lean の対象ビルド成功（2,190 jobs）、
小さい監査成功（1モジュール・24宣言、標準三公理のみ）。
sorry・追加公理0、Lean警告0。監査には添字PositiveCompositeCutIndexのFintypeを
全パラメータで合成するexampleも含め、単に「有限のはず」とは扱わなかった。
C346で残った語長の算術は、元の長さの等式をomegaで明示して閉じた。
語の値・順序・符号は変えない。各証明200行以内。

登録候補：`SerrePositivity.EInfinity.SimplexCuts.PositiveCompositeCuts`。
実測78行。M14は15,207+78=**15,285行**、外枠25,000行の残り9,715行。
L12aの実装済み前段78行であり、対応・二段側・nullary・符号・実テンソルの比較は未完。
一覧の完了数を増やさない。
L12a全体の1,400〜2,400行の見込みにこの78行を含め、後で重複加算しない。
§156.1の全体の22,611〜28,521行の見込みと上端超過リスクを保持する。

ログ：`/tmp/bsw16/m14-positive-composite-cuts-02.log`。
監査入力：`/tmp/bsw16/audit-m14-positive-composite-cuts.lean`、
結果：`/tmp/bsw16/m14-positive-composite-cuts-audit.log`。
ビルド・監査ごとに鍵を取り、終了・返却を確認した。

## 159. 次のL12aの有限対応の原型の点検（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

正の内側arityで、合成語の位置には「元の外側の位置」を付ける。
代入色の位置だけは、分割のstartからの内側位置も付ける。
合成切断の各頂点を（外側位置、元の単体頂点）へ写し、隣り合う同一点をまとめると
元の外側切断になる。その外側切断の代入色の頂点だけを、元の順序で順位付けする。
元の合成切断の代入色部分を（内側位置、この順位）へ写すと、内側切断になる。
重なる分割の隣の部分語は端点の内側位置を共有するため、外側の別の出現へ移る所も
内側切断の縦の一歩になる。

この写像の原型をPythonで点検した。外側の位置数1〜4、非空な全代入位置マスク、
内側長1〜4、入力次元0〜3。分割は元の正の部分長と総和の条件を全列挙し、
切断は全shuffle経路を列挙した。退化項の添字を除いていない。
**416条件・21,939組で、得られた外側/内側切断が正しい経路であり、単射・全射を確認した。**
スクリプト：`/tmp/bsw16/check-composite-cut-projection.py`、
結果：`/tmp/bsw16/check-composite-cut-projection.log`。
これは有限点検であってLeanの全称証明ではない。色マスクは語より一般の位置マスクで
点検したが、色・compositionSign・実テンソルの値を比較したとは扱わない。

対応の次の型案（未実装）は次。L12aの同じ添字の対応の証明の分割であり、
別の数学のまとまりとして追加するものではない。

```lean
abbrev PositiveNestedCutIndex {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (_v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1)) (q : ℕ) :=
  Σ s : Cut (m + d) q, Cut (n + e) (outputDegree s (positiveWord u) k)

-- 正の内側arityの同じ全有限添字を対応させる構成案：
positiveCompositeNestedEquiv {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1)) (q : ℕ) :
  PositiveCompositeCutIndex u v k q ≃ PositiveNestedCutIndex u v k q
```

逆向きでは、外側の各代入色の出現に属する内側切断の横ステップをまとめる。
その最初/最後の内側位置から部分長を読み、共有端点と全横ステップ数により
既存OverlapPartitionの条件を示す。外側の他の色の経路を挟んで合成切断を復元する。
この幾何学的対応だけでcompositionSign・cutSign・指定面・実テンソルの比較が
閉じたとは数えない。nullaryも別に残る。

退化入力については既存`DegenerateInput.lean`の`cutTensor_degenerate`が
項ごとの零を供給することを確認した。したがって二段側の退化した元の面を扱う際、
単に和全体の相殺を仮定しない。この補題を使える形への指定面の比較も残る。

## 160. L12a の同じ切断区間の端点の法則（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

前ターンはL11と合成側の前段を検証・コミットした進捗。作業木はad079c9feから再開した。
二段側から重なる分割を復元する際、内側切断の各縦fiberの横方向の最初/最後を使う。
その隣接fiberの共有端点は、元のCutのlo・hiの同じ法則をexchangeした経路へ適用する。
新しい端点や経路模型を選ばない。

まずm,qが0〜5の全923経路について、最初/最後の端点、隣接区間の共有端点、
lo・hiの単調性を有限点検した（正確な件数は下の実行ログを正本とする）。
スクリプト：`/tmp/bsw16/check-cut-interval-boundaries.py`、
結果：`/tmp/bsw16/check-cut-interval-boundaries.log`。
Leanの全称証明は次のC348〜C352で別に行う。型は次。

```lean
lemma lo_zero {m q : ℕ} (s : Cut m q) : lo s 0 = 0

lemma hi_last {m q : ℕ} (s : Cut m q) : hi s (Fin.last m) = q

lemma hi_eq_lo_succ {m q : ℕ} (s : Cut m q) (i : Fin m) :
    hi s i.castSucc = lo s i.succ

lemma hi_monotone {m q : ℕ} (s : Cut m q) : Monotone (hi s)

lemma lo_monotone {m q : ℕ} (s : Cut m q) : Monotone (lo s)
```

C348・C349は既存lo_eq_of_bound・hi_eq_of_boundと元の経路の端点。
C350は既存horizontal_edge、水平辺の直前の最大点、lo_eq_of_boundで同じ共有頂点を示す。
C351・C352はC350と既存lo_le_hiをFinの隣接単調性へ渡す。
各証明200行以内。固定したL12aの有限対応に使う既存構成の法則・証明分割として数える。

## 161. L12a の二段側の添字と同じ色の順位の区間分解（実装前）

一覧：済み 12／全体 48（うち追加 4）

C350は共有辺の垂直座標の等式の向きをそのまま使うよう直す。
次に、元の一色の頂点の順位を元の外側水平座標のfiberに分ける。
C353は既存orderEmbOfFinによる同じ頂点の全単射で濃度を示す。
C354・C355・C356は、その非空性・区間順序・全順位の被覆の法則である。
新しい頂点列や選択した面を作らない。

有限点検は外側区間数1〜4・arity1〜3の全非退化全射語、入力次元0〜3の全経路。
**2,514例で濃度・非空性・順序・被覆を確認**した。
スクリプト：`/tmp/bsw16/check-color-interval-ranks.py`、
結果：`/tmp/bsw16/check-color-interval-ranks.log`。

二段の添字は§159の型案のまま、外側の切断と、その指定色の全出力次数の内側切断のSigmaとする。
C357は元の語長の等式移送が指定色の出現回数を保つ法則。
構成済みの合成側と二段側の出現の有限添字を合わせるために使う。
型は次。固定したL12aの同じ有限対応の証明の分割として数える。

```lean
def colorIntervalRanks {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (p : Fin (m + 1)) : Finset (Fin (outputDegree s v a + 1))

lemma colorIntervalRanks_card {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    (colorIntervalRanks s v a p).card = (intervalPositions s p).card

lemma colorIntervalRanks_nonempty {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    (colorIntervalRanks s v a p).Nonempty

lemma colorIntervalRanks_ordered {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1)) (hp : p < p')
    (i j : Fin (outputDegree s v a + 1))
    (hi : i ∈ colorIntervalRanks s v a p) (hj : j ∈ colorIntervalRanks s v a p') : i < j

lemma colorIntervalRanks_cover {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s v a + 1)) :
    ∃ p : Fin (m + 1), v.val p = a ∧ j ∈ colorIntervalRanks s v a p

abbrev PositiveNestedCutIndex {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (_v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1)) (q : ℕ)

lemma positiveWord_occurrenceCount {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) :
    Surjection.occurrenceCount (positiveWord u).val k = Surjection.occurrenceCount u.val k
```

各証明200行以内。正の枝の対応そのもの・復元・符号・実テンソル・nullaryは未完。
これらの法則や有限点検だけでL12aを完了へ数えない。

## 162. L12a の同じ色の順位の閉区間（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§161の三本は2,241 jobsの対象ビルドに成功、Lean警告0。
次に同じcolorIntervalRanksのmin'・max'を、その最初・最後の順位として読む。
C358は既存の順序列挙と元の水平座標の単調性により、そのfiberが閉区間であることを示す。
C359・C360は既存の非空性・順序をその二端点へ渡す法則。
§161の2,514例へ閉区間の連続性の条件を加え、同じ全例で確認した。
結果：`/tmp/bsw16/check-color-interval-ranks-convex.log`。
型は次。選び直した順位ではなく元の同じ集合の両端である。

```lean
def colorIntervalFirst {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) : Fin (outputDegree s v a + 1)

def colorIntervalLast {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) : Fin (outputDegree s v a + 1)

lemma colorIntervalRanks_eq_Icc {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    colorIntervalRanks s v a p =
      Finset.Icc (colorIntervalFirst s v a p hp) (colorIntervalLast s v a p hp)

lemma colorIntervalFirst_le_last {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    colorIntervalFirst s v a p hp ≤ colorIntervalLast s v a p hp

lemma colorIntervalLast_lt_first {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (hp : v.val p = a) (hp' : v.val p' = a) (hpp' : p < p') :
    colorIntervalLast s v a p hp < colorIntervalFirst s v a p' hp'
```

各証明200行以内。次にこの両端を内側切断の縦fiberへ渡し、重なる分割の長さを復元する。
有限対応の全体・符号・実テンソル・nullaryはまだ未完。

## 163. L12a の同じ出現順の順位区間の端点（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§162の閉区間の法則まで2,242 jobsの対象ビルドに成功、Lean警告0。
次に既存occurrenceAtで元の色の出現順を使い、同じ順位区間の最初/最後を読む。
C361は既存の昇順リストのgetで元の位置を全列挙する法則。
C362〜C365は既存の所属・区間順序、C366〜C368は同じ被覆と有限順序の法則。
特にC368は隣の二出現の間に別の出現がないことから順位の隙間を排除する。

§161の2,514例へ最初零・最後が全順位の最後・隣接区間の隙間なしを加え、
同じ全例で確認した。結果：`/tmp/bsw16/check-color-occurrence-boundaries.log`。
次の型を既存構成の法則・有限対応の証明分割として実装する。

```lean
lemma occurrenceAt_exists {r l : ℕ} (v : Fin l → Fin r) (a : Fin r)
    (p : Fin l) (hp : v p = a) :
    ∃ j : Fin (Surjection.occurrenceCount v a), Surjection.occurrenceAt v a j = p

def colorOccurrenceFirst {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) : Fin (outputDegree s v a + 1)

def colorOccurrenceLast {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) : Fin (outputDegree s v a + 1)

lemma colorOccurrenceFirst_mem {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) :
    colorOccurrenceFirst s v a j ∈ colorIntervalRanks s v a (Surjection.occurrenceAt v.val a j)

lemma colorOccurrenceLast_mem {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) :
    colorOccurrenceLast s v a j ∈ colorIntervalRanks s v a (Surjection.occurrenceAt v.val a j)

lemma colorOccurrenceFirst_le_last {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) :
    colorOccurrenceFirst s v a j ≤ colorOccurrenceLast s v a j

lemma colorOccurrenceLast_lt_first {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r)
    (j j' : Fin (Surjection.occurrenceCount v.val a)) (hj : j < j') :
    colorOccurrenceLast s v a j < colorOccurrenceFirst s v a j'

lemma colorOccurrenceFirst_zero {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) :
    (colorOccurrenceFirst s v a ⟨0, Surjection.occurrenceCount_pos v a⟩).val = 0

lemma colorOccurrenceLast_top {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a))
    (hj : j.val + 1 = Surjection.occurrenceCount v.val a) :
    (colorOccurrenceLast s v a j).val = outputDegree s v a

lemma colorOccurrence_adjacent {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j j' : Fin (Surjection.occurrenceCount v.val a)) (hj : j.val + 1 = j'.val) :
    (colorOccurrenceLast s v a j).val + 1 = (colorOccurrenceFirst s v a j').val
```

各証明200行以内。新しい出現順・順位・面の選択はしない。
この端点を内側切断へ渡し、既存OverlapPartitionの共有端点と総長を満たす復元へ使う。
L12aの正の枝の全対応・符号・実テンソル・nullaryはまだ未完。

## 164. L12a の二段添字・区間端点の最初の保存

一覧：済み 12／全体 48（うち追加 4）

対象ビルド成功（2,243 jobs）、専用の小さい監査成功（5モジュール・45宣言、標準三公理のみ）。
sorry・追加公理0、Lean警告0。二段添字のFintypeも全パラメータで型検査した。
C361の依存した長さの書き換えは、同じ長さの等式からの不等式の推移で処理した。
最初/最後の順位と隣接する区間の隙間なしは、その元の出現順と被覆だけで証明している。
個々の証明200行以内。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 実測行数 |
| --- | ---: |
| IntervalBoundaryGlue | 73 |
| ColorIntervalRanks | 76 |
| ColorRankIntervals | 66 |
| ColorOccurrenceBoundaries | 154 |
| PositiveNestedCuts | 31 |

`PositiveNestedCuts`からこの五本をすべてimportする。入口と共通監査の登録は調整役が行う。
ログ：`/tmp/bsw16/m14-positive-nested-cuts-04.log`、
監査入力：`/tmp/bsw16/audit-m14-positive-nested-cuts.lean`、
結果：`/tmp/bsw16/m14-positive-nested-cuts-audit.log`。
鍵はビルド・監査ごとに取り、終了・返却を確認した。

今回400行。L12aの前段は78+400=**478行**、M14は15,285+400=**15,685行**。
外枠25,000行の残り9,315行。L12aの1,400〜2,400行の見込みに478行を含め、
あとで独立の新規として重ねて数えない。L12aの対応・復元・符号・実テンソル・nullaryは
まだ未完で、一覧の完了数は増やさない。G10の部品は作らない。

## 165. L12a の二段切断から既存OverlapPartitionへの復元（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§164の五本を0a46b3af2へ保存した。次は§159の逆向きの分割のデータを作る。
内側切断をexchangeし、元の外側出現の最初/最後の順位でlo・hiを評価する。
C369〜C373は既存の端点の単調性・共有端点の法則をそこへ渡すもの。
C374はその部分長の自然数の望遠和。overlapOfIntervalsは、この長さ・総和を
元のOverlapPartitionの欄へ渡すだけで、元の定義・正規化を変えない。

Pythonの正の枝の416条件・21,939組について、射影後の二段切断の各外側出現から
読む内側の最初/最後の位置の差+1が、元の重なる分割の部分長に戻ることを確認した。
結果：`/tmp/bsw16/check-nested-partition-recovery.log`、
スクリプト：`/tmp/bsw16/check-nested-partition-recovery.py`。
Leanではまず、二段切断から読む値が分割の条件を満たすことを証明する。
射影した合成側から元の分割へ戻る全称等式は、まだこの検査だけでは証明されない。
型は次。固定したL12aの同じ分割の復元と有限計算の証明分割として数える。

```lean
def nestedSegmentStart {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a))
    (j : Fin (Surjection.occurrenceCount v.val a)) : ℕ

def nestedSegmentEnd {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a))
    (j : Fin (Surjection.occurrenceCount v.val a)) : ℕ

lemma nestedSegmentStart_le_end {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a)) (j : Fin (Surjection.occurrenceCount v.val a)) :
    nestedSegmentStart s v a t j ≤ nestedSegmentEnd s v a t j

lemma nestedSegmentEnd_le {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a)) (j : Fin (Surjection.occurrenceCount v.val a)) :
    nestedSegmentEnd s v a t j ≤ l

lemma nestedSegmentStart_zero {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a)) (j : Fin (Surjection.occurrenceCount v.val a))
    (hj : j.val = 0) : nestedSegmentStart s v a t j = 0

lemma nestedSegmentEnd_last {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a)) (j : Fin (Surjection.occurrenceCount v.val a))
    (hj : j.val + 1 = Surjection.occurrenceCount v.val a) : nestedSegmentEnd s v a t j = l

lemma nestedSegmentEnd_eq_start {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a))
    (j j' : Fin (Surjection.occurrenceCount v.val a)) (hj : j.val + 1 = j'.val) :
    nestedSegmentEnd s v a t j = nestedSegmentStart s v a t j'

lemma intervalLengths_sum (t L : ℕ) (a b : Fin (t + 1) → ℕ)
    (hab : ∀ j, a j ≤ b j) (hfirst : a 0 = 0) (hlast : b (Fin.last t) + 1 = L)
    (hnext : ∀ i : Fin t, b i.castSucc = a i.succ) :
    (∑ j : Fin (t + 1), (b j - a j + 1)) + 1 = L + (t + 1)

def overlapOfIntervals {t L : ℕ} (ht : 0 < t) (a b : Fin t → ℕ)
    (hab : ∀ j, a j ≤ b j) (hb : ∀ j, b j < L)
    (hfirst : ∀ j, j.val = 0 → a j = 0)
    (hlast : ∀ j, j.val + 1 = t → b j + 1 = L)
    (hnext : ∀ i j, i.val + 1 = j.val → b i = a j) : Surjection.OverlapPartition t L

def positiveNestedPartition {m n d e q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : PositiveNestedCutIndex u v k q) :
    Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)
```

個々の証明200行以内。positiveNestedPartitionは語長・出現数の元の等式で移した
既存OverlapPartitionの値であり、新しい合成や符号を選ぶものではない。
合成切断自体の復元、両向きの一致、符号、実テンソル、nullaryは引き続き未完。

## 166. L12a の復元した部分長の値の法則（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

C374の望遠和と既存OverlapPartitionへの欄の供給は型検査が進んでいる。
C371ではFinの零の自然数値をFin.val_zeroで明示して簡約する。
次に元の出現数の移送で部分長の値が変わらないC375、復元した部分長の指定式C376を示す。
これにより単に「何らかの分割が存在する」とせず、読む部分長そのものを保持する。
型は次。既存の分割の係数移送・同じ構成の評価の法則として数える。

```lean
lemma overlap_eq_mp_val {t t' L : ℕ} (h : t = t') (r : Surjection.OverlapPartition t L)
    (i : Fin t') (j : Fin t) (hij : i.val = j.val) :
    ((Eq.mp (congrArg (fun k => Surjection.OverlapPartition k L) h) r).val i).val =
      (r.val j).val

lemma positiveNestedPartition_length {m n d e q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : PositiveNestedCutIndex u v k q) (i : Fin (Surjection.occurrenceCount u.val k))
    (j : Fin (Surjection.occurrenceCount (positiveWord u).val k)) (hij : i.val = j.val) :
    ((positiveNestedPartition u v k c).val i).val =
      nestedSegmentEnd c.1 (positiveWord u) k c.2 j -
        nestedSegmentStart c.1 (positiveWord u) k c.2 j + 1
```

C375は出現数の等式で置換して同じ番号を合わせるだけ。
C376はpositiveNestedPartitionとoverlapOfIntervalsの元の定義を評価する。
各証明200行以内。射影から元の分割へ戻る全称等式や合成切断の復元はまだ別に残る。

## 167. L12a の同じOverlapPartitionの復元の検証・保存

一覧：済み 12／全体 48（うち追加 4）

対象ビルド成功（2,252 jobs）、小さい監査成功（4モジュール・27宣言、標準三公理のみ）。
sorry・追加公理0、Lean警告0。監査末尾の#checkでpositiveNestedPartitionとその部分長の
全称型も確認した。二段切断の実際の両端の差に一を足した値で、既存の重なる分割を作った。
部分長の正値・上界・共有端点・総和を実際の同じ端点から供給し、
元の出現数への移送でも値が変わらないC375・C376を証明した。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 実測行数 |
| --- | ---: |
| NestedSegmentBounds | 74 |
| OverlapIntervals | 53 |
| RecoveredNestedPartition | 34 |
| RecoveredPartitionValues | 36 |

四本は`RecoveredPartitionValues`からすべてimportされる。
前の五本（§164）と合成側の一本（§158）もL12aの登録候補のまま。
共通入口・共通監査は変更していない。

ログ：`/tmp/bsw16/m14-recovered-partition-values-01.log`。
監査入力：`/tmp/bsw16/audit-m14-recovered-partition-values.lean`、
結果：`/tmp/bsw16/m14-recovered-partition-values-audit.log`。
鍵はビルド・監査ごとに取り、終了・返却を確認した。個々の証明200行以内。

今回197行。L12aの前段は478+197=**675行**、M14は15,685+197=**15,882行**。
外枠25,000行の残り**9,118行**。L12a全体の1,400〜2,400行の目安に675行を含める。
この目安を検証済みの完成予測としては扱わず、半分の1,200行に達した時点で
実測と未実装の対応・符号・実テンソル・nullaryの見込みを出し直す。
正の枝の合成切断の復元と両向きの一致もまだ未完。L12aを完了へ数えない。

## 168. 次のL12a：同じ切断の水平辺の高さによる復元（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§159の射影/復元は元の経路の座標だけで行う。実装では新しい経路の型へ移らず、
Cut m qの元の水平辺の第i位置がi+その高さであることを使って、
同じ有限な水平辺集合を組み立てる方法を次に試す。
高さは元のhi s i.castSuccをFin(q+1)で読める。単調性は検証済みC351。
元の水平辺の昇順列挙は既存orderEmbOfFinであり、その第i番より前の水平辺数はi。
この濃度と元のcoordinate_sumから位置=i+高さを示せる。

有限点検はm,qが0〜5の全923経路。水平辺の高さの族が単調であること、
各水平辺の位置がi+高さ_iであること、全単調な高さの族を過不足なく得ることを確認した。
スクリプト：`/tmp/bsw16/check-cut-heights.py`、
結果：`/tmp/bsw16/check-cut-heights.log`。
これは既存Cutの座標の法則の点検で、Leanの全称証明ではない。

次の型案（未実装）は、同じCutを組み立てるL12aの証明分割として使う。
新しいコチェイン模型・余作用・∞の構成へ置き換えない。

```lean
cutHeights {m q : ℕ} (s : Cut m q) : Fin m →o Fin (q + 1)
cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) : Cut m q
cutHeights_cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) :
  cutHeights (cutOfHeights h) = h
cutOfHeights_cutHeights {m q : ℕ} (s : Cut m q) :
  cutOfHeights (cutHeights s) = s
```

cutOfHeightsは元のShufflePathの有限集合の構成子へ、位置i+h_iの像を渡すだけとする。
その像がm点であることは単調性からの狭義単調な位置写像で示す。
元の集合との一致・座標保存を別に証明し、射影/逆写像の双方の経路の一致へ使う。
この紙の案や有限点検を、L12aの対応・符号・実テンソルの証明済み部分へ数えない。

## 169. L12a の同じ水平辺の高さと元の経路の一致（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

前ターンはc6c95c4caまでの復元を検証・保存した進捗。作業木は清潔な同コミットから再開。
§168の923経路の有限点検に対応する法則を実装する。
C377は既存orderEmbOfFinの第i位置より前の濃度。C378・C380は元の水平/垂直座標、
C379は元のcoordinate_sumからの辺番号=i+高さ、C381は同じ水平辺集合の一意性。

cutOfHeightsは、L12aの逆向きで必要な元のCutを作る実装分割である。
新しい経路模型へ移らず、既存ShufflePathの有限集合の構成子へ同じ辺番号の像を渡す。
C383〜C386で元の昇順列挙と高さを保ち、元の経路へ戻ることを示す。
これらの型は次。既存構成の座標の法則・L12aの有限対応の証明分割として数える。

```lean
lemma card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α] (s : Finset α)
    {n : ℕ} (h : s.card = n) (i : Fin n) :
    (s.filter (fun x => x < s.orderEmbOfFin h i)).card = i.val

abbrev cutHorizontalEdge {m q : ℕ} (s : Cut m q) (i : Fin m) : Fin (m + q)

def cutHeights {m q : ℕ} (s : Cut m q) : Fin m →o Fin (q + 1)

lemma horizontal_before_cutHorizontalEdge {m q : ℕ} (s : Cut m q) (i : Fin m) :
    s.horizontal (cutHorizontalEdge s i).castSucc = i.castSucc

lemma vertical_before_cutHorizontalEdge {m q : ℕ} (s : Cut m q) (i : Fin m) :
    (s.vertical (cutHorizontalEdge s i).castSucc).val = (cutHeights s i).val

lemma cutHorizontalEdge_val {m q : ℕ} (s : Cut m q) (i : Fin m) :
    (cutHorizontalEdge s i).val = i.val + (cutHeights s i).val

lemma cutHeights_injective {m q : ℕ} : Function.Injective (@cutHeights m q)

def heightPosition {m q : ℕ} (h : Fin m →o Fin (q + 1)) (i : Fin m) : Fin (m + q)

lemma heightPosition_strictMono {m q : ℕ} (h : Fin m →o Fin (q + 1)) :
    StrictMono (heightPosition h)

def cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) : Cut m q

lemma cutHorizontalEdge_cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) (i : Fin m) :
    cutHorizontalEdge (cutOfHeights h) i = heightPosition h i

lemma cutHeights_cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) :
    cutHeights (cutOfHeights h) = h

lemma cutOfHeights_cutHeights {m q : ℕ} (s : Cut m q) :
    cutOfHeights (cutHeights s) = s
```

各証明200行以内。これは経路の復元の座標の接続であり、合成/二段切断の全対応、
その符号・実テンソル・nullaryの証明が完成したとは数えない。

## 170. L12a の合成切断からの元の外側切断（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§169の高さと元の経路の両向きの一致まで2,210 jobsの対象ビルドに成功、Lean警告0。
次に、元の代入済み接頭語長を使い、外側の第i水平辺の合成語内での位置を
接頭長(i+1)-1として読む。C387〜C389は既存substitute_prefix_length_mono、
非指定色/指定色の一文字での増分、compositeWord_lengthから得る。
正の内側語では全部分語が非空なので、全境界は正しい有限位置にあり、順序を保つ。
C390・C391はその同じ位置の評価と厳密な順序。

この境界位置で元の合成切断の高さを読み、cutOfHeightsへ渡して元の外側Cutを作る。
C393でその元の境界の高さを保持する。コチェイン・合成・符号の定義は変更しない。
§159の射影の原型に、この境界位置の高さとの一致も加えて点検した。
**416条件・21,939組で一致**。
スクリプト：`/tmp/bsw16/check-composite-outer-heights.py`、
結果：`/tmp/bsw16/check-composite-outer-heights.log`。
型は次。固定したL12aの元の経路の射影を組み立てる証明分割として数える。

```lean
abbrev compositePrefixLength {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) (b : ℕ) : ℕ

lemma compositePrefixLength_monotone {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Monotone (compositePrefixLength u v k r)

lemma compositePrefixLength_step {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin ((m + 1) + d)) :
    compositePrefixLength u v k r p.val + 1 ≤ compositePrefixLength u v k r (p.val + 1)

lemma compositePrefixLength_full {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    compositePrefixLength u v k r ((m + 1) + d) = m + (n + 1) + (d + e)

def compositeOuterEdge {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (m + d)) : Fin (m + n + (d + e))

lemma compositeOuterEdge_strictMono {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    StrictMono (compositeOuterEdge u v k r)

def positiveCompositeOuterCut {m n d e q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : PositiveCompositeCutIndex u v k q) : Cut (m + d) q

lemma positiveCompositeOuterCut_heights {m n d e q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : PositiveCompositeCutIndex u v k q) (i : Fin (m + d)) :
    cutHeights (positiveCompositeOuterCut u v k c) i =
      cutHeights c.2 (compositeOuterEdge u v k c.1 i)
```

各証明200行以内。内側切断の射影・合成切断の逆復元・両向きの一致・符号・
実テンソル・nullaryは未完。有限点検をLeanの全称証明としては数えない。

## 171. L12a の元の分割における内側水平辺の所属（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§170の外側切断と指定境界の高さの一致まで対象ビルドに成功した。
接頭長の型の長い行は改行してから次の束で検証し直す。
次に内側の第p水平辺を含む分割部分を、元の開始位置がp以下の最後の部分として読む。
共有端点そのものは複数の部分語に属しても、その次へ進む同じ水平辺の所属は一意。
元のstart・start_next・last_end・boundary_monoを使う法則であり、分割を作り直さない。

自然数p全体で元の有限候補のmax'を読むが、辺の上界・一意性はp+1<Lを明示して述べる。
実際の内側のFinの辺番号へ適用するとき、この条件はその元の有限上界から供給する。
有限点検は語長1〜5・部分数1〜5の全ての正の重なる部分長について行った。
正確な辺数と読んだ位置数は `/tmp/bsw16/check-segment-edge-owner.log` に記録した。
スクリプト：`/tmp/bsw16/check-segment-edge-owner.py`。
型は次。固定したL12aの同じ有限対応の内部の所属・単調性・一意性の法則として数える。

```lean
def segmentEdgeCandidates {t L : ℕ} (r : Surjection.OverlapPartition t L) (p : ℕ) :
    Finset (Fin t)

lemma segmentEdgeCandidates_nonempty {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) : (segmentEdgeCandidates r p).Nonempty

def segmentEdgeOwner {t L : ℕ} (r : Surjection.OverlapPartition t L) (ht : 0 < t) (p : ℕ) :
    Fin t

lemma segmentEdgeOwner_start_le {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) : r.start (segmentEdgeOwner r ht p) ≤ p

lemma segmentEdgeOwner_end_gt {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (hp : p + 1 < L) :
    p + 1 < r.start (segmentEdgeOwner r ht p) + (r.val (segmentEdgeOwner r ht p)).val

lemma segmentEdgeOwner_monotone {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) : Monotone (segmentEdgeOwner r ht)

lemma segmentEdgeOwner_unique {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (hp : p + 1 < L) (j : Fin t)
    (hleft : r.start j ≤ p) (hright : p + 1 < r.start j + (r.val j).val) :
    segmentEdgeOwner r ht p = j
```

各証明200行以内。この所属だけで内側切断や全対応の完成とは数えない。

## 172. L12a の色別順位と同じ区間の高さ（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

内側射影の高さを作るため、元の一つの区間内の高さを、同じ色の頂点列の順位へ移す。
既存のcolorIntervalRanks_card・colorIntervalRanks_eq_Icc・intervalPositions_cardから、
順位の幅と元の区間の高さの幅が一致する。その同じ幅を使って順位を読む。
L12aの既存の有限列挙の評価・証明分割であり、新しい作用や対応を導入するものではない。
C399〜C402を次の型で追加する（各証明200行以内の見込み）。

```lean
lemma colorIntervalRank_width {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    (colorIntervalLast s v a p hp).val - (colorIntervalFirst s v a p hp).val =
      hi s p - lo s p

def colorHeightRank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (h : ℕ) (hl : lo s p ≤ h) (hr : h ≤ hi s p) : Fin (outputDegree s v a + 1)

lemma colorHeightRank_mem {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (h : ℕ) (hl : lo s p ≤ h) (hr : h ≤ hi s p) :
    colorHeightRank s v a p hp h hl hr ∈ colorIntervalRanks s v a p

lemma colorHeightRank_monotone {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (h h' : ℕ) (hl : lo s p ≤ h) (hr : h ≤ hi s p)
    (hl' : lo s p ≤ h') (hr' : h' ≤ hi s p) (hh : h ≤ h') :
    colorHeightRank s v a p hp h hl hr ≤ colorHeightRank s v a p hp h' hl' hr'

lemma colorHeightRank_endpoints {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    colorHeightRank s v a p hp (lo s p) le_rfl (lo_le_hi s p) =
        colorIntervalFirst s v a p hp ∧
      colorHeightRank s v a p hp (hi s p) (lo_le_hi s p) le_rfl =
        colorIntervalLast s v a p hp
```

有限点検：`/tmp/bsw16/check-color-height-ranks.py`。884組の語と切断、5,410箇所の高さで、
幅の一致と、上の順位が同じ元の水平位置・高さを読むことを確認した。
有限点検は全称証明の代わりには数えない。内側切断・逆復元・符号・nullaryは未完。

## 173. L12a の外側射影と辺の所属：検証・取り込み候補

一覧：済み 12／全体 48（うち追加 4）

§169〜171の6モジュール、387行を検証した。
対象ビルド：`/tmp/bsw16/m14-composite-outer-and-owner-01.log`、2,847 jobs、成功・対象警告0。
小監査：`/tmp/bsw16/audit-m14-composite-outer-and-owner.lean`、
結果 `/tmp/bsw16/m14-composite-outer-and-owner-audit.log`、**6モジュール・61宣言、標準三公理のみ**。
sorry・新規公理は0。既存の公開宣言・界面・共有入口は変更していない。

登録候補（すべて `SerrePositivity.EInfinity.SimplexCuts.` の下）：
`OrderedPrefixCard`、`CutHeights`、`CutOfHeights`、`CompositePrefixLengths`、
`CompositeOuterCut`、`SegmentEdgeOwner`。
元のCutの高さとの相互復元、元の合成語の接頭長、外側切断と指定境界の一致、
内側水平辺の所属の一意性まで。L12a全体の対応・符号・実テンソル・nullaryは未完。

L12a検証済み実測は675+387=**1,062行**、M14は15,882+387=**16,269行**。
外枠25,000行まで**8,731行**。L12aの1,200行の途中報告点はまだ踏んでいない。
§172のColorHeightRanksはこの時点では未検証の下書きで、上の実測・登録候補に含めない。

## 174. L12a の同じ色別頂点写像との厳密な一致（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§172の有限点検は順位が元の水平位置・高さの頂点を指すことも点検している。
次はその全称の照合。有限の狭義単調列では、添字の差以下には値が増えない。
これを元の色別位置列の区間の前半・後半へ適用する。区間全体の順位の幅が高さの幅に
等しいC399と元のcoordinate_sumから、どちらの増分にも隙間がないことが従う。
既存の順序列挙・座標写像の法則だけで、元のverticesと厳密に一致する。
型は次。C403〜C405はL12aの有限列挙の評価・照合の証明分割として数える。
各証明200行以内の見込み。作用・ホモトピー・Totについての新しい主張は足さない。

```lean
lemma finite_strictMono_distance {N : ℕ} (f : Fin N → ℕ) (hf : StrictMono f)
    (i j : Fin N) (hij : i ≤ j) : j.val - i.val ≤ f j - f i

lemma vertices_on_colorIntervalRanks {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    (vertices s v a j).val = lo s p + (j.val - (colorIntervalFirst s v a p hp).val)

lemma vertices_colorHeightRank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (h : ℕ) (hl : lo s p ≤ h) (hr : h ≤ hi s p) :
    (vertices s v a (colorHeightRank s v a p hp h hl hr)).val = h
```

## 175. L12a の内側水平辺の同じ合成語位置（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

C394〜398で所属を決めた同じ内側水平辺を、元の部分語の合成位置へ送る。
位置は元の出現前の接頭長に、元の部分語内の相対位置を足したもの。
型は次。C406〜C408はL12aの同じ有限対応の内部の位置・順序の法則として数える。
各証明200行以内の見込み。新しい作用・ホモトピー・Totの主張は含まない。
有限点検：`/tmp/bsw16/check-composite-inner-edges.py`、416条件・21,939組。
所属部分語内で隣接する元の二位置を読み、合成語での位置が正しいことと狭義順序を確認。

```lean
lemma compositePrefixLength_occurrence_end_le {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (j : Fin (Surjection.occurrenceCount u.val k)) :
    compositePrefixLength u v k r (Surjection.occurrenceAt u.val k j).val + (r.val j).val ≤
      m + (n + 1) + (d + e)

def compositeInnerEdge {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : Fin (n + e)) : Fin (m + n + (d + e))

lemma compositeInnerEdge_val {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : Fin (n + e)) :
    (compositeInnerEdge u v k r a).val =
      compositePrefixLength u v k r
          (Surjection.occurrenceAt u.val k
            (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val)).val +
        (a.val - r.start (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val))

lemma compositeInnerEdge_strictMono {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    StrictMono (compositeInnerEdge u v k r)
```

## 176. L12a の同じ接頭境界と高さの範囲（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

内側射影の高さをC400へ渡すため、C393の射影した切断の左右の端点を読む。
外側位置pに属する合成語内の水平辺は、元の接頭長α(p)からα(p+1)の間にある。
その高さは射影した外側切断のloとhiの間にある。最初/最後は既存lo_zero・hi_last、
途中は既存hi_eq_lo_succとC393の単調性だけを使う。
C409は同じ射影の座標の法則・L12aの証明分割として追加する。各証明200行以内の見込み。
有限点検：`/tmp/bsw16/check-composite-height-bounds.py`、416条件・21,939組。
型は次。合成語や切断の公開定義は変更しない。

```lean
lemma positiveCompositeOuterCut_height_bounds {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (a : Fin (m + n + (d + e)))
    (hl : compositePrefixLength u v k c.1 p.val ≤ a.val)
    (hr : a.val + 1 < compositePrefixLength u v k c.1 (p.val + 1)) :
    lo (positiveCompositeOuterCut u v k c) p ≤ (cutHeights c.2 a).val ∧
      (cutHeights c.2 a).val ≤ hi (positiveCompositeOuterCut u v k c) p
```

## 177. L12a の1,200行の途中報告：実測と残りの出し直し

一覧：済み 12／全体 48（うち追加 4）

§172・174〜176の4本は対象ビルドが成功した。小監査は別の一回の鍵で実行中。
`ColorHeightRanks`82行、`ColorHeightVertices`79行、`CompositeInnerEdges`102行、
`CompositeHeightBounds`53行、合計316行。
ビルド：`/tmp/bsw16/m14-color-height-and-inner-02.log`（内側辺）、
`/tmp/bsw16/m14-color-height-and-bounds-03.log`（残り、2,849 jobs）、対象警告0。
一度目の頂点照合では、差の評価に加えて同じ列挙の値自体の単調性も明示する必要があった。
その数値的な評価を同じ証明内に足し、元の頂点との厳密な一致を閉じた。

ビルド済みのL12a実測は1,062+316=**1,378行**。監査後に検証済みへ数える。
M14は同じ基準で16,269+316=**16,585行**、外枠25,000行まで**8,415行**。
L12aの途中報告点1,200行を踏んだので、残りを次のように出し直す。

| 残るL12aの行 | 見込み |
| --- | ---: |
| 内側切断の高さ・単調性と順方向の写像 | 150〜250 |
| 二段切断から合成切断の逆復元 | 300〜550 |
| 両方向の逆の等式 | 300〜500 |
| 同じcompositionSign・cutSignの照合 | 200〜350 |
| 同じ指定面・実テンソル・零項の照合 | 400〜750 |
| nullaryの元の有限添字と項の接続 | 250〜400 |
| **残り** | **1,600〜2,800** |
| **L12a完成時（1,378行を含む）** | **2,978〜4,178** |

§159のL12a全体1,400〜2,400行の上端より、今の完成上端は+1,778行。
増えたのは、元のCutの座標・色別順位・重なる部分語の位置を、原型のリスト上の対応から
元の有限添字の全称証明へつなぐ分である。この前段を全対応や符号の完成として控除しない。
§156のL12a以外の見込みを据え置いて更新すると、次のとおり。

| 部分 | 残りの下端 | 残りの上端 |
| --- | ---: | ---: |
| L12a | 1,600 | 2,800 |
| L12〜L28（L12aを除く、既存L14前段控除済み） | 2,504 | 4,664 |
| L29〜L37 | 1,200 | 2,000 |
| G10後の指定比較への適用 | 500 | 900 |
| filtered塔 | 300 | 550 |
| 二重模型の実現の比較 | 1,500 | 2,800 |
| **M14完成時（実測込み）** | **24,189** | **30,299** |

外枠25,000行に収まるとは主張しない。上端には**5,299行の超過リスク**がある。
現在は実測16,585行で外枠には届いておらず、固定したL12aの内部の法則だけを進めている。
既存構成の法則・証明分割は型を報告して続行し、新しい数学・範囲外・外枠で止める規則は維持する。
G10・M15・G12は作らない。L12a未完のため一覧は12/48のまま。

## 178. L12a の同じ出現位置と、内側高さの範囲の接続（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

次は元の出現位置をpositiveWordの同じ長さで読むだけの移送を明示し、C409へ渡す。
C410〜C413は既存語長移送・出現位置・接頭長の法則として追加する。
新しい作用や対応は作らない。各証明200行以内の見込み。型は次。

```lean
lemma word_eq_mp_value {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l)
    (i : Fin l') (j : Fin l) (hij : i.val = j.val) :
    (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val i = v.val j

def positiveOccurrencePosition {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (j : Fin (Surjection.occurrenceCount u.val k)) : Fin (m + d + 1)

lemma positiveOccurrencePosition_value {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (j : Fin (Surjection.occurrenceCount u.val k)) :
    (positiveWord u).val (positiveOccurrencePosition u k j) = k

lemma positiveOccurrencePosition_strictMono {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1)) :
    StrictMono (positiveOccurrencePosition u k)

lemma positiveCompositeInnerEdge_height_bounds {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    lo (positiveCompositeOuterCut u v k c)
        (positiveOccurrencePosition u k
          (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val)) ≤
        (cutHeights c.2 (compositeInnerEdge u v k c.1 a)).val ∧
      (cutHeights c.2 (compositeInnerEdge u v k c.1 a)).val ≤
        hi (positiveCompositeOuterCut u v k c)
          (positiveOccurrencePosition u k
            (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val))
```

これらの有限位置・高さは§175〜176の21,939組で点検した同じもの。

## 179. L12a の同じ頂点・辺・高さの範囲：小監査完了

一覧：済み 12／全体 48（うち追加 4）

§177の4本316行の小監査が成功した。
入力 `/tmp/bsw16/audit-m14-color-height-and-inner.lean`、
結果 `/tmp/bsw16/m14-color-height-and-inner-audit.log`、
**4モジュール・38宣言、標準三公理のみ**。sorry・新規公理0、対象警告0。
L12a検証済み実測**1,378行**、M14**16,585行**、外枠まで**8,415行**。
見込みは§177を維持する。既存の公開宣言・界面・共有入口は変更していない。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：
`ColorHeightRanks`、`ColorHeightVertices`、`CompositeInnerEdges`、`CompositeHeightBounds`。
§178の2本はこの時点で未検証の下書き。上の実測・登録候補に含めない。

## 180. L12a の元の内側切断への順方向の接続（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

既に報告した正の枝の対応の順方向を、元の高さと色別順位で組み立てる。
高さが所属区間内にあるC413からcolorHeightRankを読み、同じ所属ならC401、
後の所属ならC355で単調性を得る。元のcutOfHeightsへそのまま渡す。
C414〜C417は固定したL12aの対応の証明分割・同じ座標の法則として追加する。
型は次。各証明200行以内の見込み。全対応・符号・nullaryはまだ未完。

```lean
def positiveCompositeInnerHeights {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    Fin (n + e) →o Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1)

def positiveCompositeInnerCut {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    Cut (n + e) (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k)

lemma positiveCompositeInnerCut_heights {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    cutHeights (positiveCompositeInnerCut u v k c) a = positiveCompositeInnerHeights u v k c a

lemma positiveCompositeInnerCut_vertices {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (cutHeights (positiveCompositeInnerCut u v k c) a) =
      cutHeights c.2 (compositeInnerEdge u v k c.1 a)

def positiveCompositeNestedMap {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) : PositiveCompositeCutIndex u v k q → PositiveNestedCutIndex u v k q

lemma positiveCompositeNestedMap_outer {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    (positiveCompositeNestedMap u v k c).1 = positiveCompositeOuterCut u v k c
```

この順方向の高さは§175の有限点検のepsilonの水平辺の高さそのもの。
点検には退化項を除かない21,939組が含まれる。有限点検を全称証明とは数えない。

## 181. L12a の同じ復元分割の開始位置（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

逆復元に使う既存positiveNestedPartitionについて、部分長だけでなく開始位置も元の端点に
一致することを読む。overlapOfIntervalsの同じ共有端点条件とstart_nextに自然数帰納法を
使う法則であり、新しい分割を選ばない。C418〜C420を同じ構成の法則として追加する。
各証明200行以内の見込み。有限点検は既存§165の21,939組の端点復元と同じもの。
型は次。

```lean
lemma overlapOfIntervals_start {t L : ℕ} (ht : 0 < t) (a b : Fin t → ℕ)
    (hab : ∀ j, a j ≤ b j) (hb : ∀ j, b j < L)
    (hfirst : ∀ j, j.val = 0 → a j = 0)
    (hlast : ∀ j, j.val + 1 = t → b j + 1 = L)
    (hnext : ∀ i j, i.val + 1 = j.val → b i = a j) (j : Fin t) :
    (overlapOfIntervals ht a b hab hb hfirst hlast hnext).start j = a j

lemma overlap_eq_mp_start {t t' L : ℕ} (h : t = t') (r : Surjection.OverlapPartition t L)
    (i : Fin t') (j : Fin t) (hij : i.val = j.val) :
    (Eq.mp (congrArg (fun k => Surjection.OverlapPartition k L) h) r).start i = r.start j

lemma positiveNestedPartition_start {m n d e q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : PositiveNestedCutIndex u v k q) (i : Fin (Surjection.occurrenceCount u.val k))
    (j : Fin (Surjection.occurrenceCount (positiveWord u).val k)) (hij : i.val = j.val) :
    (positiveNestedPartition u v k c).start i = nestedSegmentStart c.1 (positiveWord u) k c.2 j
```

## 182. L12a の元の水平辺と方向を交換した区間（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

逆復元で、内側の水平辺の高さが同じ色別区間に属する条件を、復元分割の始点・終点で読む。
元の水平辺の直前・直後の二頂点は高さが同じで横座標が一だけ増える。
既存exchange_horizontal・exchange_vertical・lo/hiの単調性と端点の評価を使う。
C421〜C422を同じCutの座標・所属の法則として追加する。新しい経路模型は作らない。
各証明200行以内の見込み。型は次。

```lean
lemma cutHeights_exchange_bounds {m q : ℕ} (s : Cut m q) (a : Fin m) (y : Fin (q + 1)) :
    (lo s.exchange y ≤ a.val ↔ y.val ≤ (cutHeights s a).val) ∧
      (a.val < hi s.exchange y ↔ (cutHeights s a).val ≤ y.val)

lemma cutHeights_mem_interval {m q : ℕ} (s : Cut m q) (a : Fin m)
    (first last : Fin (q + 1)) :
    (first ≤ cutHeights s a ∧ cutHeights s a ≤ last) ↔
      lo s.exchange first ≤ a.val ∧ a.val < hi s.exchange last
```

有限点検：`/tmp/bsw16/check-cut-height-exchange.py`、923経路、19,931箇所。
高さ・方向交換の両方の同値を、幅や高さが零の場合も含め確認した。

## 183. L12a の逆復元における同じ順位の所属（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

C376・C420とC422を合わせ、復元分割の内部の辺の高さが、元の同じ色別順位の区間に
属することを読む。C423・C424は同じ端点・頂点の法則。
また同じ語長移送が元の出現位置の列挙を保つことをC425・C426で明示する。
いずれも同じ有限構成の法則・証明分割として追加し、各証明200行以内の見込み。
型は次。finiteの読み方は§165・§182の点検と同じもの。

```lean
lemma positiveNestedPartition_height_interval {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k))
    (j : Fin (Surjection.occurrenceCount (positiveWord u).val k)) (hij : i.val = j.val)
    (a : Fin (n + e)) (hl : (positiveNestedPartition u v k c).start i ≤ a.val)
    (hr : a.val + 1 < (positiveNestedPartition u v k c).start i +
      ((positiveNestedPartition u v k c).val i).val) :
    colorOccurrenceFirst c.1 (positiveWord u) k j ≤ cutHeights c.2 a ∧
      cutHeights c.2 a ≤ colorOccurrenceLast c.1 (positiveWord u) k j

lemma vertices_bounds_on_colorInterval {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1))
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    lo s p ≤ (vertices s v a j).val ∧ (vertices s v a j).val ≤ hi s p

lemma word_eq_mp_occurrenceAt {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l)
    (a : Fin r)
    (i : Fin (Surjection.occurrenceCount
      (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val a))
    (j : Fin (Surjection.occurrenceCount v.val a)) (hij : i.val = j.val) :
    (Surjection.occurrenceAt (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val a i).val =
      (Surjection.occurrenceAt v.val a j).val

lemma positiveOccurrencePosition_eq {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (i : Fin (Surjection.occurrenceCount u.val k))
    (j : Fin (Surjection.occurrenceCount (positiveWord u).val k)) (hij : i.val = j.val) :
    positiveOccurrencePosition u k i = Surjection.occurrenceAt (positiveWord u).val k j
```

## 184. L12a の順方向と同じ復元分割の座標：検証・取り込み候補

一覧：済み 12／全体 48（うち追加 4）

§178・180〜182の7本380行を検証した。
順方向は任意の正arity・全ての合成切断に対する写像として定義され、
同じ色別verticesで読む高さの厳密な一致まで証明した。
復元した同じ分割の開始位置と、方向を交換した元のCutによる高さの所属の同値も証明した。
全対応・逆の等式・符号・実テンソル・nullaryの完成とは数えない。

対象ビルド：`/tmp/bsw16/m14-composite-inner-height-bounds-01.log`（2,852 jobs）、
`/tmp/bsw16/m14-composite-nested-map-02.log`（2,856 jobs）、
`/tmp/bsw16/m14-recovered-partition-starts-01.log`（2,254 jobs）、
`/tmp/bsw16/m14-cut-height-exchange-01.log`（2,215 jobs）、全て成功・対象警告0。
小監査：`/tmp/bsw16/audit-m14-composite-nested-map.lean`、
結果 `/tmp/bsw16/m14-composite-nested-map-audit.log`、
**7モジュール・36宣言、標準三公理のみ**。sorry・新規公理0。
各ビルドと監査で鍵を独立に取り、実行終了後に返した。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：
`PositiveOccurrencePosition`45行、`CompositeInnerHeightBounds`51行、
`CompositeInnerHeights`50行、`CompositeNestedMap`60行、`OverlapIntervalStarts`43行、
`RecoveredPartitionStarts`36行、`CutHeightExchange`95行。
既存の公開宣言・界面・共有入口は変更していない。

L12a検証済み実測1,378+380=**1,758行**、M14は16,585+380=**16,965行**。
外枠25,000行まで**8,035行**。§177の残りの表のうち順方向の接続の実測は206行で、
見込み150〜250行内。174行は同じ逆復元の始点・交換座標の法則。
逆の写像自体や両方向の等式はまだ未完。§177の超過リスクは解消したとは扱わない。
§183の2本はまだ未検証で、上の実測・登録候補に含めない。

## 185. L12a の逆復元に使う元の全水平辺の列挙（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

逆の合成切断の高さは、元の外側境界辺と元の内側内部辺の位置を合わせて指定する。
両者の本数の和は合成語の水平辺数に等しい。元の出現位置pに属する内側辺は、
外側境界iに対してp≤iなら先、i<pなら後にある。C387〜388と元の部分長の評価だけで示せる。
したがって二つの位置写像の和は単射で、同じ有限濃度から全単射となる。
C427〜C429は、§159の固定した同じ有限対応を組み立てる証明分割として追加する。
型は次。各証明200行以内の見込み。新しい作用・定理・別の切断模型は導入しない。

```lean
lemma compositeInnerOuterEdge_order {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : Fin (n + e)) (i : Fin (m + d)) :
    ((Surjection.occurrenceAt u.val k
        (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val)).val ≤ i.val →
      compositeInnerEdge u v k r a < compositeOuterEdge u v k r i) ∧
    (i.val < (Surjection.occurrenceAt u.val k
        (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val)).val →
      compositeOuterEdge u v k r i < compositeInnerEdge u v k r a)

def compositeEdgeSum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Fin (m + d) ⊕ Fin (n + e) → Fin (m + n + (d + e))

lemma compositeEdgeSum_injective {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Function.Injective (compositeEdgeSum u v k r)

lemma compositeEdgeSum_bijective {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Function.Bijective (compositeEdgeSum u v k r)
```

有限点検：`/tmp/bsw16/check-composite-joint-edges.py`、416条件・21,939組。
両種の辺が重複なく全水平辺を埋め、混合した順序が上の不等式どおりであることを点検した。
さらに外側境界の高さと、内側高さを同じ外側verticesで読む値から元の全高さが戻ることも確認。
この最後の復元はまだLeanで証明済みとして数えない。

## 186. L12a の逆方向の同じ内側高さの上下界（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

C423の順位区間の所属をC424の元のverticesの上下界へ渡す。
元の正の語長移送の位置はC426で一致させる。C430は既存lo/hiの隣接端点の法則。
C431は同じ復元分割の内部辺についての指定面の評価の法則。
どちらも固定したL12aの逆復元の証明分割として追加し、各証明200行以内の見込み。
型は次。新しい作用・比較対象は導入しない。

```lean
lemma hi_le_lo_of_lt {m q : ℕ} (s : Cut m q) (i j : Fin (m + 1)) (hij : i < j) :
    hi s i ≤ lo s j

lemma positiveNestedInnerHeight_bounds {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) (a : Fin (n + e)) :
    lo c.1 (positiveOccurrencePosition u k
        (segmentEdgeOwner (positiveNestedPartition u v k c)
          (Surjection.occurrenceCount_pos u k) a.val)) ≤
        (vertices c.1 (positiveWord u) k (cutHeights c.2 a)).val ∧
      (vertices c.1 (positiveWord u) k (cutHeights c.2 a)).val ≤
        hi c.1 (positiveOccurrencePosition u k
          (segmentEdgeOwner (positiveNestedPartition u v k c)
            (Surjection.occurrenceCount_pos u k) a.val))
```

有限点検は§185の21,939組に含まれる同じ外側区間・内側高さの照合。

## 187. L12a の逆の合成切断を同じ全辺の高さから読む（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

C429の全単射の逆で同じ水平辺を読み、外側境界では元の外側高さ、内側辺では
元の内側高さを同じverticesで読む値を使う。同種の辺は既存単調性、異種の辺は
C427とC430〜431で単調性を得る。元のcutOfHeightsから逆の合成切断を作る。
C432〜C434は§159の同じ有限対応の逆方向の証明分割として追加する。
各証明200行以内の見込み。新しい作用・別の模型は作らない。

```lean
def compositeEdgeEquiv {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    (Fin (m + d) ⊕ Fin (n + e)) ≃ Fin (m + n + (d + e))

def positiveNestedEdgeHeight {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    Fin (m + d) ⊕ Fin (n + e) → Fin (q + 1)

lemma positiveNestedEdgeHeight_mono {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q)
    (x y : Fin (m + d) ⊕ Fin (n + e))
    (h : compositeEdgeSum u v k (positiveNestedPartition u v k c) x ≤
      compositeEdgeSum u v k (positiveNestedPartition u v k c) y) :
    positiveNestedEdgeHeight u v k c x ≤ positiveNestedEdgeHeight u v k c y

def positiveNestedCompositeHeights {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    Fin (m + n + (d + e)) →o Fin (q + 1)

lemma positiveNestedCompositeHeights_apply {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q)
    (z : Fin (m + d) ⊕ Fin (n + e)) :
    positiveNestedCompositeHeights u v k c
        (compositeEdgeSum u v k (positiveNestedPartition u v k c) z) =
      positiveNestedEdgeHeight u v k c z

def positiveNestedCompositeMap {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) : PositiveNestedCutIndex u v k q → PositiveCompositeCutIndex u v k q

lemma positiveNestedCompositeMap_heights {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q)
    (z : Fin (m + d) ⊕ Fin (n + e)) :
    cutHeights (positiveNestedCompositeMap u v k c).2
        (compositeEdgeSum u v k (positiveNestedPartition u v k c) z) =
      positiveNestedEdgeHeight u v k c z
```

有限点検は§185。単調性と両方向の逆の等式・符号は、この紙の案で証明済みと数えない。

## 188. L12a の元の外側切断の復元と同じ順位への戻し（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

逆方向で指定した外側境界の高さから、元の外側Cutがそのまま戻ることをC393・C434と
cutHeightsの単射性で読む。また区間内の順位をverticesで読みcolorHeightRankで戻すと
同じ順位になることをC404で読む。C435〜C436は同じ対応の逆の等式の証明分割・法則。
各証明200行以内の見込み。全対応・符号・nullaryはまだ未完。
型は次。有限点検は§185の同じ対応。

```lean
lemma positiveNestedCompositeMap_outerCut {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    positiveCompositeOuterCut u v k (positiveNestedCompositeMap u v k c) = c.1

lemma colorHeightRank_vertices {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    colorHeightRank s v a p hp (vertices s v a j).val
        (vertices_bounds_on_colorInterval s v a p j hj).1
        (vertices_bounds_on_colorInterval s v a p j hj).2 = j
```

## 189. L12a の元の内側順位を同じ区間で戻す接続（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

C423の順位区間の所属をC426で元の出現位置へ移すC437と、その同じ順位をC436で
復元するC438を追加する。既存構成の所属・係数移送の法則と逆の等式の証明分割。
各証明200行以内の見込み。元の高さや頂点写像は選び直さない。
型は次。有限点検は§185の同じ全対応の21,939組。

```lean
lemma positiveNestedInnerRank_mem {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) (a : Fin (n + e)) :
    cutHeights c.2 a ∈ colorIntervalRanks c.1 (positiveWord u) k
      (positiveOccurrencePosition u k
        (segmentEdgeOwner (positiveNestedPartition u v k c)
          (Surjection.occurrenceCount_pos u k) a.val))

lemma positiveNestedInnerRank_recover {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) (a : Fin (n + e)) :
    colorHeightRank c.1 (positiveWord u) k
        (positiveOccurrencePosition u k
          (segmentEdgeOwner (positiveNestedPartition u v k c)
            (Surjection.occurrenceCount_pos u k) a.val))
        (positiveOccurrencePosition_value u k _)
        (vertices c.1 (positiveWord u) k (cutHeights c.2 a)).val
        (positiveNestedInnerHeight_bounds u v k c a).1
        (positiveNestedInnerHeight_bounds u v k c a).2 = cutHeights c.2 a
```

## 190. L12a の同じ二段切断への右逆の等式（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

外側Cutの等式C435が出力次数の等式を与える。C439は、この等しい次数で読んだ
元の二つのCutの高さが同じなら同じCutであることを読む、次数移送だけの法則。
C440で内側切断の高さの自然数値を既存定義から読み、C435・C434・C438を合わせる。
C441の結論はSigma型の元の二段切断そのものの厳密な等式。HEqは等しい出力次数を
持つ同じCutの添字の移送のためだけに使い、ホモトピー圏へ結論を弱めない。
C439〜C441を同じ構成の次数移送・逆の等式の証明分割として追加する。
各証明200行以内の見込み。型は次。

```lean
lemma cutHeights_heq {m q q' : ℕ} (s : Cut m q) (t : Cut m q') (h : q = q')
    (hs : ∀ i, (cutHeights s i).val = (cutHeights t i).val) : HEq s t

lemma positiveCompositeInnerCut_height_val {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    (cutHeights (positiveCompositeInnerCut u v k c) a).val =
      (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
          (positiveOccurrencePosition u k
            (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val))
          (positiveOccurrencePosition_value u k _)).val +
        ((cutHeights c.2 (compositeInnerEdge u v k c.1 a)).val -
          lo (positiveCompositeOuterCut u v k c)
            (positiveOccurrencePosition u k
              (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val)))

lemma positiveCompositeNestedMap_rightInverse {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) :
    Function.RightInverse (positiveNestedCompositeMap u v k (q := q))
      (positiveCompositeNestedMap u v k)
```

有限点検は§185の同じ対応。左逆・符号・実テンソル・nullaryは未完。

## 191. L12a の左逆に使う同じ辺の所属番号の比較（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

元の部分語iと辺の所属番号の比較を、元のstart・終了位置の不等式へ移す。
C442〜C443は既存のmax'とstart_mono・boundary_monoの評価の法則として追加する。
左逆で元の部分語の両端を復元する同じ有限比較の証明分割で、新しい作用は含まない。
各証明200行以内の見込み。型は次。

```lean
lemma le_segmentEdgeOwner_iff {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (i : Fin t) :
    i ≤ segmentEdgeOwner r ht p ↔ r.start i ≤ p

lemma segmentEdgeOwner_le_iff {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (hp : p + 1 < L) (i : Fin t) :
    segmentEdgeOwner r ht p ≤ i ↔ p + 1 < r.start i + (r.val i).val
```

有限点検：`/tmp/bsw16/check-segment-edge-owner-order.py`、799辺、1,552箇所の位置の読み。
有効な全水平辺について全ての部分番号との両同値を確認した。

## 192. L12a の左逆への残る接続（紙の型、未実装）

一覧：済み 12／全体 48（うち追加 4）

右逆の検証待ちの間に、左逆側の残る同じ有限列挙の法則を型に落とした。
C444〜C450はL12aの同じ構成の法則と証明分割。新しい数学の項目は足さない。
以下は紙だけであり、証明済みや行数実測には含めない。

```lean
-- C444：同じ区間の最初の順位との比較。
lemma colorIntervalFirst_le_rank_iff {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (hp : v.val p = a) (hp' : v.val p' = a)
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    colorIntervalFirst s v a p' hp' ≤ j ↔ p' ≤ p

-- C445：同じ区間の最後の順位との比較。
lemma rank_le_colorIntervalLast_iff {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (hp : v.val p = a) (hp' : v.val p' = a)
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    j ≤ colorIntervalLast s v a p' hp' ↔ p ≤ p'

-- C446：順方向の内側高さは同じ所属出現の順位区間内。
lemma positiveCompositeInnerCut_rank_mem {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    cutHeights (positiveCompositeInnerCut u v k c) a ∈
      colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (positiveOccurrencePosition u k
          (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val))

-- C447：同じ順位の上下の比較を元の部分語の両端で読む。
lemma positiveCompositeInnerCut_rank_bounds_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (a : Fin (n + e)) (i : Fin (Surjection.occurrenceCount u.val k)) :
    (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i) ≤
        cutHeights (positiveCompositeInnerCut u v k c) a ↔ c.1.start i ≤ a.val) ∧
    (cutHeights (positiveCompositeInnerCut u v k c) a ≤
        colorIntervalLast (positiveCompositeOuterCut u v k c) (positiveWord u) k
          (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i) ↔
      a.val + 1 < c.1.start i + (c.1.val i).val)

-- C448：有限の全ての辺との同じ比較は、その同じ端点を特定する。
lemma nat_eq_of_fin_le_iff {m : ℕ} (x y : ℕ) (hx : x ≤ m) (hy : y ≤ m)
    (h : ∀ a : Fin m, x ≤ a.val ↔ y ≤ a.val) : x = y

-- C449：同じ交換経路の始点・終点の復元から元の部分長を得る。
lemma positiveCompositeNestedMap_partition {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    positiveNestedPartition u v k (positiveCompositeNestedMap u v k c) = c.1

-- C450：同じ全辺の指定高さによる元の合成切断の復元。
lemma positiveCompositeNestedMap_leftInverse {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) :
    Function.LeftInverse (positiveNestedCompositeMap u v k (q := q))
      (positiveCompositeNestedMap u v k)
```

C444・C445は既存C355の同じ区間間の狭義順序とmin'/max'の法則から、
C446はC400・C415から、C447はC444〜C446とC442・C443から示す。
C448はx<yなら元の有限辺a=x、y<xならa=yを選ぶ有限比較の法則。
C449ではC421にC447を渡し、元の開始位置・終了位置と交換経路の両端の等式を得る。
終了位置の比較a<endはa≥endの否定なので、同じC448を使う。両端は内側の幅以下。
C420・C376とC426で同じ出現番号へ戻し、元のOverlapPartitionの部分長を得る。
C450ではC449を合わせ、C429の全辺の各像でC393・C416・C434の高さの等式を使い、
元のCutの単射な座標C381で閉じる。個別の証明が200行を超えたら行数も報告する。
有限点検は§185の同じ全対応。これで符号・実テンソル・nullaryが閉じたとは扱わない。

## 193. L12a の逆方向・右逆の厳密な等式：検証・取り込み候補

一覧：済み 12／全体 48（うち追加 4）

§183・185〜191の13本624行を検証した。
元の外側境界と内側内部辺の全単射、元の二段切断からの逆の合成切断、
同じ指定高さの保持、元の外側Cutへの復元、二段切断そのものへの右逆の等式まで。
右逆の結論はFunction.RightInverseの元のSigma型の等式であり、ホモトピー圏の等式ではない。
HEqを使うのは等しい出力次数の添字の移送だけ。
左逆・符号・実テンソル・nullaryは未完で、L12aを完了に数えない。

対象ビルド：
`/tmp/bsw16/m14-nested-height-interval-01.log`（2,260 jobs）、
`/tmp/bsw16/m14-composite-edge-enumeration-01.log`（2,807 jobs）、
`/tmp/bsw16/m14-nested-composite-map-01.log`（2,864 jobs）、
`/tmp/bsw16/m14-nested-composite-outer-inverse-01.log`（2,869 jobs）、
`/tmp/bsw16/m14-nested-cut-right-inverse-03.log`（2,877 jobs）、全て成功・対象警告0。
右逆の最初の二回は同じSigmaの射影をrewriteに明示する調整が必要だった。
同じCutと同じ復元分割の射影表記をchangeでそろえ、数学の主張を変更せずに閉じた。

小監査入力 `/tmp/bsw16/audit-m14-nested-cut-right-inverse.lean`、
結果 `/tmp/bsw16/m14-nested-cut-right-inverse-audit.log`、
**13モジュール・43宣言、標準三公理のみ**。sorry・新規公理0、対象警告0。
各ビルド・監査は独立の鍵を取り、実行が終わったら返した。常駐セッションは使っていない。
既存の公開宣言・界面・共有入口・共有監査は変更していない。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 実測行数 |
| --- | ---: |
| NestedPartitionHeightInterval | 46 |
| PositiveOccurrenceComparison | 36 |
| CompositeMixedEdgeOrder | 55 |
| CompositeEdgeEnumeration | 59 |
| NestedInnerHeightBounds | 57 |
| NestedCompositeEdgeHeights | 71 |
| NestedCompositeMap | 63 |
| NestedCompositeOuterCut | 27 |
| ColorHeightRankInverse | 30 |
| NestedInnerRankRecovery | 51 |
| CutHeightTransport | 25 |
| NestedCutRightInverse | 55 |
| SegmentEdgeOwnerOrder | 49 |

L12a検証済み実測1,758+624=**2,382行**、M14は16,965+624=**17,589行**。
外枠25,000行まで**7,411行**。個別の証明200行超はない。
§192は次の左逆の紙の型で、まだ実装・証明済みとして数えない。

## 194. L12a の逆復元の実測差と残り

一覧：済み 12／全体 48（うち追加 4）

§177の各行との接続を重複なく数える。
順方向の高さ・単調性・写像は206行で見込み150〜250行内。
逆復元は§184の始点・交換座標174行に、今回の同じ順位・出現位置・辺の列挙・
高さ・逆写像の387行を合わせた**561行**で、見込み300〜550行の上端を**11行超過**。
今回の残り237行は右逆と左逆への所属比較の前段で、見込み300〜500行の行に属する。
両方向の逆の等式は、右逆を閉じたが左逆が残る。

| L12a の残り | 見込み |
| --- | ---: |
| §192の左逆の接続 | 200〜350 |
| 同じcompositionSign・cutSignの照合 | 200〜350 |
| 同じ指定面・実テンソル・零項の照合 | 400〜750 |
| nullaryの元の有限添字と項の接続 | 250〜400 |
| **残り** | **1,050〜1,850** |
| **L12a完成時（2,382行を含む）** | **3,432〜4,232** |

§177の他の行の見込みを据え置くとM14完成時は**24,643〜30,353行**。
外枠25,000行への上端の超過リスクは**5,353行**であり、収まるとは扱わない。
実測は17,589行で外枠にはまだ届いていない。既存構成の法則・証明分割は型を報告して
続け、新しい数学・まとまりの外・外枠に届くときに止まる規則を維持する。
G10・M15・G12は作らない。B4は595254e10で完了済みのまま。

## 195. §192の左逆の法則C444〜C448の実装開始

一覧：済み 12／全体 48（うち追加 4）

前ターンは4de85cfabで元の右逆を検証・コミットした進捗。枝は変更なしから再開した。
§192の型のまま、同じ区間の順位の上下比較C444・C445、順方向の所属C446、
同じ分割の両端との比較C447、有限比較による端点の特定C448を書いた。
証明済みとして数えるのは対象ビルドと小監査の後。
型は§192のままで、既存の法則・証明分割以外の数学は追加していない。
各証明200行以内。G10・M15・G12・共有入口には触れない。

有限点検を先に実施：`/tmp/bsw16/check-color-rank-bound-comparisons.py`。
884組の元の語と切断・5,410箇所の高さを点検する既存スクリプトに、
同じ色の全区間の最初/最後の順位との両比較を加え、全例で一致を確認した。
C446・C447の分割の所属比較は§191の799辺の点検と同じ読み方。
B4は595254e10で完了済み。前の凍結の記述はB4の明示指示で解除されている。

## 196. C449の元の二端点の復元（証明分割の型）

一覧：済み 12／全体 48（うち追加 4）

C449の証明を、同じ交換経路の両端を読む二つの法則C449a・C449bへ分ける。
新しい構成・定理ではなく、C421・C447・C448をそのまま合わせる証明分割。
各証明200行以内の見込み。型は次。

```lean
lemma positiveCompositeNestedMap_segmentStart {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    lo (positiveCompositeInnerCut u v k c).exchange
        (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
          (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i)) =
      c.1.start i

lemma positiveCompositeNestedMap_segmentEnd {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    hi (positiveCompositeInnerCut u v k c).exchange
        (colorIntervalLast (positiveCompositeOuterCut u v k c) (positiveWord u) k
          (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i)) =
      c.1.start i + (c.1.val i).val - 1
```

比較する両端は元の内側幅以下。全ての有限辺との同じ比較からC448で端点を特定し、
C376・C426に戻して元の部分長を得る。有限点検は§185の元の21,939組の対応。

## 197. C450と既報の正の有限対応の組み立て

一覧：済み 12／全体 48（うち追加 4）

C450は§192の型のまま実装する。C449で同じ分割をそろえ、C429の全水平辺の
元の二種類の各像でC393・C416・C434を使う。元のcutHeightsの単射性で同じCutへ戻す。
その後、§159で既報の次の正の全有限添字のEquivを、両方の逆の等式から組み立てる。
これは固定したL12aの同じ有限対応の組み立てであり、新しい数学の項目ではない。

```lean
def positiveCompositeNestedEquiv {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) :
    PositiveCompositeCutIndex u v k q ≃ PositiveNestedCutIndex u v k q
```

各証明200行以内の見込み。退化した切断も除かない。符号・実テンソル・nullaryの
照合はまだ別に残り、このEquivの構成だけでL12aを完了には数えない。

## 198. C449の同じ位置の順位の移送（既存構成の法則）

一覧：済み 12／全体 48（うち追加 4）

C444〜C448・C449a・C449bは対象ビルドに成功した。
C449の出現位置を直接rewriteすると、その位置の色を示す証明も依存するためmotiveが不正になる。
位置と色の証明をまとめた同じcolorIntervalFirst/Lastの移送をC449c・C449dで明示する。
既存構成の係数移送の法則であり、新しい数学ではない。各証明200行以内。
型は次。

```lean
lemma colorIntervalFirst_congr_position {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (hp : v.val p = a) (hp' : v.val p' = a) (h : p = p') :
    colorIntervalFirst s v a p hp = colorIntervalFirst s v a p' hp'

lemma colorIntervalLast_congr_position {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (hp : v.val p = a) (hp' : v.val p' = a) (h : p = p') :
    colorIntervalLast s v a p hp = colorIntervalLast s v a p' hp'
```

次の符号照合の有限点検も実施した（まだLeanの証明ではない）：
`/tmp/bsw16/check-general-composite-signs.py`。
外側語長1〜4・内側語長1〜3、外側arity最大3・内側arity最大2、単体次数0〜2で、
元の非退化全射語と全ての正の重なる分割を読む12,233組について、合成側の面の非退化性が
二段側の両方の面の非退化性と一致した。残る3,745組では、元のcompositionExponentと
一般cutSignの指数が、二段側の係数交換d*e・内側係数の移動e*prefixDegree・
元の両cutSignの指数の和とmod 2で一致した。退化項は符号検査の対象から除いて別に零を比較する。
元の符号規約を変更するものではない。

## 199. L12a の同じ指定面・符号の比較の型（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

正の全有限添字の同値の後は、元の指定面と元の符号を照合する。
指定面の族は、次数と元のverticesをそのまま組にしたもの。二段側の挿入色では
元の外側verticesと元の内側verticesを合成し、残り色では元の外側verticesを使う。
出力順序は既存IntervalCuts.insertionFamilyを使い、選び直さない。
前方次数は元のoutputDegreeのprefixFamilyのdegreeSumで、係数移動と同じ次数。
型は次。C451〜C453は固定したL12aの指定面・符号・零項の法則の証明分割であり、
新しい数学の項目ではない。型や元の符号規約は変更しない。

```lean
def positiveCompositeFaceFamily {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    Fin (m + (n + 1)) → Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)

def positiveNestedFaceFamily {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    Fin (m + (n + 1)) → Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)

def positiveNestedPrefixDegree {m d q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (s : Cut (m + d) q) : ℕ

def positiveNestedCutCoefficient {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) : ℤ

-- C451：次数と元の指定面の族そのものの厳密な一致。
lemma positiveCompositeFaceFamily_eq_nested {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    positiveCompositeFaceFamily u v k c =
      positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c)

-- C452：元の符号の比較。零となる面の項に符号の等式を強制しない。
lemma positiveCompositeCutCoefficient_eq_nested {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Surjection.compositionSign u v k c.1 * cutSign c.2 (positiveCompositeCutWord u v k c.1).val =
      positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c)

-- C453：元の正規化前の面の退化性も同じ有限対応で照合する。
lemma positiveCompositeCut_nondegenerate_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val ↔
      Nondegenerate (positiveCompositeOuterCut u v k c) (positiveWord u).val ∧
        Nondegenerate (positiveCompositeInnerCut u v k c) (positiveWord v).val
```

有限点検を先に拡張した：`/tmp/bsw16/check-general-composite-faces.py`。
§198の12,233組で、合成側の全色の元の頂点列が、残り色の外側頂点列と、挿入色の
内側頂点列を元の外側頂点列で読んだ列に、順序・重複も含め厳密に一致した。
同じ全例で退化性が一致し、生き残る3,745組で元の符号も一致した。
この点検はLeanの全称証明の代わりに数えない。零arityはこれらの型では含まず、
L12aのnullaryの行として別に残る。

## 200. L12a の正の全有限添字の同値：検証・取り込み候補

一覧：済み 12／全体 48（うち追加 4）

C444〜C450を閉じ、§159のpositiveCompositeNestedEquivを構成した。
任意の正の内外arity、全語次数・単体次数で、元の重なる分割と元の一段切断の全添字と、
元の二段切断の全添字が厳密に対応する。退化した切断も除かず、両方向の逆は元の型の等式。
正の全添字の同値だけで、符号・実テンソル・nullaryまで閉じたとは扱わない。

対象ビルド：`/tmp/bsw16/m14-composite-inner-rank-bounds-01.log`（順位比較2本成功）、
`/tmp/bsw16/m14-composite-nested-equiv-01.log`（端点比較・端点復元成功）、
`/tmp/bsw16/m14-composite-nested-equiv-02.log`（2,884 jobs、全対象成功・対象警告0）。
有限端点の補助では、不要な存在しないtactic importを除き、反射性をNat.le_reflで明示した。
C449の位置と色の証明はC449c・C449dで同じ順位ごと移して閉じた。

小監査入力 `/tmp/bsw16/audit-m14-composite-nested-equiv.lean`、
結果 `/tmp/bsw16/m14-composite-nested-equiv-audit.log`、
**7モジュール・24宣言、標準三公理のみ**。sorry・新規公理0、対象警告0。
個別の証明200行超はない。既存の公開宣言・界面・共有入口・共有監査は変更していない。
各ビルドと監査は一回ずつ鍵を取り、実行が終わったら返した。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 実測行数 |
| --- | ---: |
| ColorRankBoundComparisons | 53 |
| CompositeInnerRankBounds | 54 |
| FiniteEndpointComparison | 30 |
| CompositeSegmentRecovery | 60 |
| CompositePartitionRecovery | 43 |
| ColorRankPositionTransport | 31 |
| CompositeNestedEquiv | 47 |
| **合計** | **318** |

§194の左逆の接続200〜350行に対し実測318行で、見込み内。
L12a検証済み実測2,382+318=**2,700行**、M14は17,589+318=**17,907行**。
外枠25,000行まで**7,093行**。残るL12aの行は符号200〜350行・指定面と実テンソル
400〜750行・nullary250〜400行で合計850〜1,500行、完成時3,550〜4,200行の見込み。
他の行の見込みを据え置くとM14完成時**24,761〜30,321行**。
上端に**5,321行の超過リスク**が残り、収まるとは扱わない。外枠・範囲の停止規則は維持する。
§199の二本は未検証の組み立ての下書きで、上の実測・登録候補に含めない。

## 201. C451の元の経路の座標と区間の所属（証明分割の型）

一覧：済み 12／全体 48（うち追加 4）

指定面の比較に、元の経路の水平位置pと高さcを持つ頂点を読む。
元のcoordinate_sumからその位置番号はp+cであり、区間の最小/最大位置の間にあれば
元のhorizontalの単調性で横座標p、同じcoordinate_sumで縦座標cが特定される。
C451a・C451bは既存座標の所属の法則であり、別の経路や新しい構成は導入しない。
型は次。個々の証明200行以内の見込み。

```lean
def coordinatePosition {m q : ℕ} (p : Fin (m + 1)) (c : Fin (q + 1)) : Fin (m + q + 1)

lemma coordinates_of_interval {m q : ℕ} (s : Cut m q)
    (p : Fin (m + 1)) (c : Fin (q + 1)) (hl : lo s p ≤ c.val) (hr : c.val ≤ hi s p) :
    s.horizontal (coordinatePosition p c) = p ∧ s.vertical (coordinatePosition p c) = c

lemma coordinatePosition_onPath_iff {m q : ℕ} (s : Cut m q)
    (p : Fin (m + 1)) (c : Fin (q + 1)) :
    (s.horizontal (coordinatePosition p c) = p ∧ s.vertical (coordinatePosition p c) = c) ↔
      lo s p ≤ c.val ∧ c.val ≤ hi s p
```

有限点検：`/tmp/bsw16/check-cut-coordinate-interval.py`。
幅・高さ0〜5の923経路、24,683組の座標について、元の経路の頂点の座標と両端の条件が一致した。
これはLeanの全称証明とは別の点検。指定面の全比較C451そのものはまだ未完。

## 202. C451の元の合成語のブロック両端（証明分割の型）

一覧：済み 12／全体 48（うち追加 4）

元の外側位置pに代入された部分語の最初・最後の位置は、既存の接頭長α(p)とα(p+1)-1。
C393で定めた同じ外側切断の両端は、元の合成切断のこの二位置の両端と等しい。
最初/最後の位置では既存lo_zero・hi_lastを使い、途中ではhi_eq_lo_succを使う。
C451c・C451dの同じ座標の法則として次を実装する。個々の証明200行以内の見込み。

```lean
lemma compositePrefixLength_zero {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    compositePrefixLength u v k r 0 = 0

def compositeFirstPosition {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) : Fin (m + n + (d + e) + 1)

def compositeLastPosition {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) : Fin (m + n + (d + e) + 1)

lemma positiveCompositeOuterCut_endpoints {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (p : Fin (m + d + 1)) :
    lo (positiveCompositeOuterCut u v k c) p = lo c.2 (compositeFirstPosition u v k c.1 p) ∧
      hi (positiveCompositeOuterCut u v k c) p = hi c.2 (compositeLastPosition u v k c.1 p)
```

元のブロック位置とその両端は§170・§176の21,939組の点検と同じもの。
新しい経路を作らず、同じ位置番号を既存のCutで読むだけの記法・評価の法則。

## 203. C451の元の色別列挙から指定面への移送（既存構成の法則）

一覧：済み 12／全体 48（うち追加 4）

色別位置集合の順序を保つ同じ列挙の同値が元のverticalを保つとき、元のoutputDegreeと
verticesの組も等しい。この既存構成の係数移送を一つの補題にまとめ、残り色と挿入色の
両方で使う。有限順序列挙はorderIsoOfFinで、同じ有限順序の自己同型は既存StrictMono.eq_id
で一致する。HEqは等しい次数で読むFinの添字の移送だけで、最終結論はSigma型の等式。
C451hの証明分割として次を追加する。各証明200行以内の見込み。新しい模型は導入しない。

```lean
lemma finiteOrderIso_val {N M : ℕ} (e : Fin N ≃o Fin M) (i : Fin N) : (e i).val = i.val

lemma orderHom_heq_of_values {N M Q : ℕ} (f : Fin N →o Fin Q) (g : Fin M →o Fin Q)
    (h : N = M) (hv : ∀ i j, i.val = j.val → f i = g j) : HEq f g

lemma faceData_eq_of_colorOrderIso {m m' q r r' : ℕ} (s : Cut m q) (t : Cut m' q)
    (u : Surjection.Word r (m + 1)) (v : Surjection.Word r' (m' + 1)) (a : Fin r) (b : Fin r')
    (e : ↥(colorPositions s u.val a) ≃o ↥(colorPositions t v.val b))
    (hv : ∀ x, s.vertical x.val = t.vertical (e x).val) :
    (⟨outputDegree s u a, vertices s u a⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) =
      ⟨outputDegree t v b, vertices t v b⟩
```

この補題だけで合成切断の対応する色別位置集合の同値が供給されたとは扱わない。
その元の位置・頂点の照合はC451の残りであり、同じ作用の法則の中で進める。

## 204. C451の残り色の元の位置・頂点（証明分割の型）

一覧：済み 12／全体 48（うち追加 4）

元の指定色以外の位置は、一文字のまま同じ代入語へ残る。既存の
substitute_prefix_length_at_non_slot・compositeBasisWord_outerPositionと、C410の語長移送を使う。
その最初/最後の合成位置が同じになり、C451c・C451dとC451aから元の同じ頂点を読む。
C451e〜C451gの法則・証明分割として次を追加する。各証明200行以内の見込み。
型は次。有限点検は§199の12,233組の同じ残り色の全頂点列の一致。

```lean
lemma compositePrefixLength_at_non_slot {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    compositePrefixLength u v k r (p.val + 1) = compositePrefixLength u v k r p.val + 1

lemma compositeFirstPosition_eq_last_of_non_slot {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    compositeFirstPosition u v k r p = compositeLastPosition u v k r p

lemma positiveCompositeFirstPosition_label {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    (positiveCompositeCutWord u v k r).val (compositeFirstPosition u v k r p) =
      BarrattEccles.remainingPosition m (n + 1) k ⟨(positiveWord u).val p, hp⟩

lemma positiveCompositeRemainingVertex_coordinates {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) (h : Fin (q + 1))
    (hl : lo (positiveCompositeOuterCut u v k c) p ≤ h.val)
    (hr : h.val ≤ hi (positiveCompositeOuterCut u v k c) p) :
    c.2.horizontal (coordinatePosition (compositeFirstPosition u v k c.1 p) h) =
        compositeFirstPosition u v k c.1 p ∧
      c.2.vertical (coordinatePosition (compositeFirstPosition u v k c.1 p) h) = h
```

## 205. C451の残り色の全位置・全頂点への接続（紙の型、未実装）

一覧：済み 12／全体 48（うち追加 4）

次は既存remaining_count_substituteで元の残り色の出現回数を保ち、同じcompositeFirstPosition
の狭義単調性と有限濃度から、残り色の全出現位置の順序同値を得る。
その同じ二端点を保つ順序同値を、区間内の全頂点へ持ち上げる。各頂点はC451aの元の
coordinatePositionで読み、逆は元の位置の順序同値の逆で読む。最後にC451hへ渡す。
既存構成の法則・同じ指定面の比較の証明分割として型を次に記録する。
ここは紙だけであり、証明済み・実測へ含めない。各証明200行以内の見込み。

```lean
lemma occurrences_card_eq_count {r l : ℕ} (v : Fin l → Fin r) (a : Fin r) :
    (Surjection.occurrences v a).card = Surjection.occurrenceCount v a

lemma compositeFirstPosition_strictMono {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    StrictMono (compositeFirstPosition u v k r)

lemma positiveCompositeWord_remaining_count {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : {a : Fin (m + 1) // a ≠ k}) :
    Surjection.occurrenceCount (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k a) =
      Surjection.occurrenceCount (positiveWord u).val a.val

def remainingWordPositionOrderIso {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : {a : Fin (m + 1) // a ≠ k}) :
    ↥(Surjection.occurrences (positiveWord u).val a.val) ≃o
      ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k a))

def colorPathOrderIso {m m' q r r' : ℕ} (s : Cut m q) (t : Cut m' q)
    (u : Surjection.Word r (m + 1)) (v : Surjection.Word r' (m' + 1)) (a : Fin r) (b : Fin r')
    (e : ↥(Surjection.occurrences u.val a) ≃o ↥(Surjection.occurrences v.val b))
    (hl : ∀ p, lo s p.val = lo t (e p).val)
    (hr : ∀ p, hi s p.val = hi t (e p).val) :
    ↥(colorPositions s u.val a) ≃o ↥(colorPositions t v.val b)

lemma colorPathOrderIso_vertical {m m' q r r' : ℕ} (s : Cut m q) (t : Cut m' q)
    (u : Surjection.Word r (m + 1)) (v : Surjection.Word r' (m' + 1)) (a : Fin r) (b : Fin r')
    (e : ↥(Surjection.occurrences u.val a) ≃o ↥(Surjection.occurrences v.val b))
    (hl : ∀ p, lo s p.val = lo t (e p).val)
    (hr : ∀ p, hi s p.val = hi t (e p).val) (x : ↥(colorPositions s u.val a)) :
    t.vertical (colorPathOrderIso s t u v a b e hl hr x).val = s.vertical x.val
```

occurrencesの濃度は元の昇順リストとoccurrencePositions_lengthから読む。
compositeFirstPositionの順序はC388とC387から。有限回数の保存は元の符号や作用を触らない。
区間内の持ち上げの単調性は、横座標が異なれば元の横座標の順序、同じなら元のverticalの
順序とcoordinate_sumを使う。この一般の法則だけで挿入色の全頂点の比較を供給したとは扱わず、
挿入色の部分語・元の順位の照合はC451の残りに保持する。

## 206. L12a の指定面・符号の組み立てと元の座標：検証・取り込み候補

一覧：済み 12／全体 48（うち追加 4）

§199・201〜204の8本401行を検証した。
元の指定面の族、元の前方次数と二つの係数移動を持つ符号を組み立てた。
元の二座標による頂点の所属、合成ブロックの両端、元の残り色の文字と同じ頂点の座標、
同じ順序列挙から元の指定面への係数移送まで。C451全体・C452・C453はまだ未完。

対象ビルド（全て成功・対象警告0）：
`/tmp/bsw16/m14-nested-cut-coefficients-01.log`（2,888 jobs）、
`/tmp/bsw16/m14-interval-vertex-coordinates-01.log`（1,135 jobs）、
`/tmp/bsw16/m14-composite-outer-endpoints-02.log`（2,848 jobs）、
`/tmp/bsw16/m14-face-data-order-transport-01.log`（1,129 jobs）、
`/tmp/bsw16/m14-composite-remaining-vertices-01.log`（2,853 jobs）。
ブロック両端の最初のビルドでは、区間のhiを局所名で隠していたためその局所名を改めた。
数学の主張や既存の公開宣言は変えていない。

小監査入力 `/tmp/bsw16/audit-m14-composite-face-coordinates.lean`、
結果 `/tmp/bsw16/m14-composite-face-coordinates-audit.log`、
**8モジュール・46宣言、標準三公理のみ**。sorry・新規公理0、対象警告0。
個別の証明200行超はない。各ビルドと監査で鍵を独立に取り、実行が終わったら返した。
共有入口・共有監査・drafts・界面は変更していない。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 実測行数 |
| --- | ---: |
| CompositeFaceFamilies | 35 |
| NestedCutCoefficients | 27 |
| IntervalVertexCoordinates | 57 |
| CompositeBlockPositions | 50 |
| CompositeOuterEndpoints | 74 |
| FaceDataOrderTransport | 56 |
| CompositeRemainingPositions | 69 |
| CompositeRemainingVertices | 33 |
| **合計** | **401** |

L12a検証済み実測2,700+401=**3,101行**、M14は17,907+401=**18,308行**。
外枠25,000行まで**6,692行**。L12aは未完のため一覧は12/48のまま。
§205は次の同じ指定面の比較の紙の型で、未実装。有限点検は§198〜199・201のとおりで、
Leanの全称証明へ混ぜていない。

## 207. C451の残りの見込みと外枠との照合

一覧：済み 12／全体 48（うち追加 4）

今回401行のうち27行は符号の組み立て、374行は指定面・実テンソルの比較の前段。
指定面の比較は、元の出現位置を全頂点の順序同値へ持ち上げる法則も必要なため、
§200の指定面と実テンソル400〜750行の見込みでは残りの接続が不足する。
次の残りを分けて数え直す。既存法則の再利用による目安であり、完成済みとして控除しない。

| 指定面・実テンソルの残り | 見込み |
| --- | ---: |
| 残り色の全出現位置・全頂点の順序同値とその面の評価（§205） | 160〜280 |
| 挿入色の同じ部分語・元の順位・全頂点の比較 | 160〜280 |
| 同じ出力次数・指定面から実テンソルと零項への接続 | 130〜240 |
| **残り** | **450〜800** |
| **この行の完成時（374行を含む）** | **824〜1,174** |

他の行の見込みを据え置くと、符号の残り173〜323行、nullary250〜400行で、
L12aの残り**873〜1,523行**、完成時**3,974〜4,624行**。
M14全体の完成見込みは**25,185〜30,745行**で、下端でも外枠を185行上回る。
外枠を緩めたり完了条件を縮めたりはしない。現在の実測は18,308行で、
固定した同じ作用の法則の範囲内で進め、実装の外枠に届くときの停止規則を維持する。
収まるとは主張しない。G10・M15・G12の部品は作らない。

## 208. §207の停止判断の訂正：M14のLeanを外枠で区切る

一覧：済み 12／全体 48（うち追加 4）

前ターンはf19ee4262・1bf98147eで左逆と正の全添字の同値、その後の指定面の座標法則を
検証・コミットした進捗。現在の枝は1bf98147e、作業木に未検証のLeanはない。
本ターンの最初に正本coordination.md §2を読み直した。
規模の規則は「**上限を超えそうなときは報告して止める（止まる前に、それまでの検証済みの分をコミット）**」。
夜の規則も「**上限を超えそうなときは検証済みをコミットして報告を書き、その線の Lean は止めて決めておいた代わりの紙の作業へ**」。
§207の、実測が25,000行未満なのでそのまま実装を続けるという解釈は訂正する。

実測はM14 **18,308行**、L12a **3,101行**、外枠まで6,692行。
しかし§207の完成見込みは **25,185〜30,745行**で、下端でも外枠を185行上回る。
したがって、ここでこの線の追加Leanを止める。既に検証済みを保存してあり、
見込みの外の補題を足したり、同じ型を弱めたり、証明を不自然に圧縮したりはしない。
新しい外枠を自己承認しない。

再開箇所は§205の残り色の全位置・全頂点の順序同値。その後は§199のC451〜C453と
実テンソル・nullary、固定した§112の残り。B4や正の有限対応を再実装しない。
L12a・M14とも未完であり、一覧の完了数は増やさない。
本ターンは、/goalで指定された代わりの仕事「G10後のnative Tot・二重模型・filtered塔の
型つきの一覧を紙で」を下に具体化する。M15・G12の紙の仕事へは戻らない。
Leanファイル・drafts・界面・他レーンのファイル・共有入口・mainには変更しない。

