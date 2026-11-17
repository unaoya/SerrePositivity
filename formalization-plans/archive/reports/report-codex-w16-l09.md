# BS-W16 の報告（report-codex-w16.md） — L09（§113〜§137、2026-11-13〜11-14）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 113. L09aの境界値までの検証と、一覧外の再帰分解での停止（11-13夜）

### 113.1 検証済み・保存する範囲

新しい五本は全てEInfinity/SimplexCuts/。

| モジュール | 行数 | 出力 |
| --- | ---: | --- |
| BoundaryIndex | 33 | 出力面・係数語削除・入力面の三群の有限添字 |
| GeneratorBoundary | 44 | 同じ整数次数の正規化生成元の微分。L09a前提計算1 |
| BoundaryFaces | 35 | 標準面と一因子の次数を下げる指定移送。L09a前提計算2 |
| OutputBoundaryTerms | 63 | 出力の一面を削除した実テンソルとBF・Koszul符号 |
| BoundaryTerms | 71 | 係数語・入力面も含む、同じ次数の三群の境界値 |
| **計** | **246** | |

対象ビルド：m14-boundary-index-01.log、m14-boundary-prerequisites-01.log、
m14-output-boundary-01.log、m14-boundary-terms-01.log（いずれも/tmp/bsw16/）。
BoundaryFacesの未使用変数警告はδの次元を明記して解消し、最終ソースに新しい警告なし。
小さい専用監査audit-m14-boundary-terms.logは **5モジュール・66宣言、標準三公理のみ**で成功。
sorry・追加公理なし。鍵はビルドと監査ごとに取り直し、返却済み。

独立な有限計算として、整数係数のテンソルの微分と、χの文字削除＋入力単体の面を
Pythonで直接比較した。arity1〜3、語次数0〜3、単体次数0〜2の**495例**で一致した。
これはBF符号の点検であり、一般のL09a・L09のLean証明の代用にはしない。

三群の値は型検査済みだが、**boundaryBalance_pairingも微分等式もまだ証明していない**。
May4,128行＋切断の検証済み1,184行で、本経路の基礎実測は **5,312行**。
12,500行の途中報告点・25,000行の外枠で止まったのではない。

### 113.2 一覧外として報告する新しい数学の型

L09aのτを、最後の垂直辺を取り除く再帰で構成する筋を具体化したところ、
次の二つが必要となった。**紙の新規名・型案、未実装・未型検査**。

```lean
-- 追加候補 R01。q+1個目の垂直辺の属する区間pで分類し、末尾を除く。
cutLastVerticalEquiv (m q : ℕ) :
  Cut m (q+1) ≃ Σ p : Fin (m+1), Cut p.val q
```

幾何学的には、各区間の長さの列の最後の正の成分pから一を引き、
pより後の長さ零の区間を除く。逆はその最後に垂直辺を足し、残りの水平辺を戻す。
既存ShufflePath.vertical_edgeは最後の垂直辺の存在と座標を供給するが、
**区間数をp+1へ変えた経路とのこの全単射**は今回調べたAPIには見つからなかった。
ShuffleLastFaceの既存の削除は、経路の最後の辺が垂直という条件の下で固定した水平次数を保つ式で、
この任意の長さ零の末尾を含む分解をそのまま供給するものではない。

この分解だけでなく、色ごとの出力の復元の法則も必要。
以下でverticesListは色のfiberを元の順序で列挙してverticalで写したList。
空のfiberも空リストとして扱い、**ここでは全射性を仮定しない**。

```lean
def verticesList {m q r : ℕ} (s : Cut m q) (v : Fin (m+1) → Fin r) (c : Fin r) :
    List (Fin (q+1)) :=
  ((colorPositions s v c).sort (· ≤ ·)).map (fun i => s.vertical i)

def prefixLabels (v : Fin (m+1) → Fin r) (p : Fin (m+1)) : Fin (p.val+1) → Fin r :=
  fun i => v ⟨i.val, by omega⟩

def terminalMultiplicity (v : Fin (m+1) → Fin r) (p : Fin (m+1)) (c : Fin r) : ℕ :=
  (Finset.univ.filter (fun i => p ≤ i ∧ v i = c)).card

-- 追加候補 R02。欠けた色・末尾の重複も保持する、再帰の値の法則。
verticesList_lastVertical (v : Fin (m+1) → Fin r) (p : Fin (m+1))
    (s : Cut p.val q) (c : Fin r) :
  verticesList ((cutLastVerticalEquiv m q).symm ⟨p,s⟩) v c =
    (verticesList s (prefixLabels v p) c).map Fin.castSucc ++
      List.replicate (terminalMultiplicity v p c) (Fin.last (q+1))
```

例えば語(0,1)の最後の垂直辺が第0区間にある切断では、接頭語は(0)となり色1が欠ける。
それでも元の切断の色1には末尾の頂点が現れる。
既存L01・L02・faceは**全射語で各色が非空**という型なので、
そのまま同じarityの接頭語へ再帰適用はできない。
R02は欠けた色を空のリストとして保持し、末尾で現れる回数を復元する新しい式である。
サフィックスで色が重複すると、List.replicateの重複を正規化で消す必要がある。
存在するかどうかのifで頂点を一つだけ付ける式にはしない。

### 113.3 漏れた理由と停止の扱い

§112ではL09aの**全境界項を対にするτの主張**までを型にしたが、
τを作る再帰のデータと、全射でなくなる接頭部の値の復元を列挙していなかった。
R01・R02は、既存の単位・余単位・自然性・係数移送の式の評価ではなく、
入力の単体次元と区間数を同時に変える新しい組合せ的な分解の主張である。
また単に既存のL09aの証明をelaborationのために同じ式へ分割しただけとは扱わない。

ユーザーの「それ以外の新しい数学の補題が要ったら止まって報告」に従い、
**R01・R02の実装には入らず、ここで停止する**。
L09a前提計算は2/3、照合I01〜I03は0/3のまま。未使用の前提計算枠をこの新しい数学に流用しない。
検証済みの五本と本報告を保存して判断を待つ。
G10・native Totの部品や界面の変更は行っていない。
B3の凍結はmainのみという最新連絡に従い、枝のこの保存は行う。

## 114. R01・R02再開と有限組合せの枠（11-14未明）

BS-W16 §28と最新指示でR01・R02をL09aの部分へ追加し再開する。
mainは凍結中なので取り込まず、mainの指示書§28を読み取りで確認した。
枝の編集・コミットは続行可。対象ビルド・小さい専用監査だけを行う。

### 114.1 実装前の有限計算

/tmp/bsw16/check-terminal-cut.py は、切断を非負の区間長の列として独立に列挙し、
最後の正の区間の長さを一つ下げるR01の逆と、R02の色ごとの頂点列の復元を確認した。
m=0〜4、q=0〜3、色数1〜3の全ての語（非全射も含む）、全ての色で **122,186例**が一致。
うち接頭部の色が空で元の出力が非空の例10,378件、末尾の反復が2以上の例15,366件。
欠けた色を削除したり、末尾を単一の頂点へ潰したりしていない。
この点検はLean証明の代用にはしない。

### 114.2 追加する有限組合せの補題：L09aの枠1/3

最後の垂直辺を補集合の最大元として選び、その前の辺をFinへ詰める構成を使う。
`lowerPart s a` は、sのaより小さい元をFin a.valに圧縮した有限集合。
次を新しい有限組合せの枠 **C01（1/3）** として追加する。

```lean
card_lowerPart_of_max {N : ℕ} (s : Finset (Fin N)) (a : Fin N)
    (ha : a ∈ s) (hm : ∀ i ∈ s, i ≤ a) :
  (lowerPart s a).card + 1 = s.card
```

所属の式と補集合との可換性は、この制限の定義を評価する証明分割。
R01・R02本体は今回承認された二本であり、C01のほかの追加枠へ数えない。
前提計算L09aの2/3、照合の0/3とは別に記録する。

### 114.3 色のfiberのリスト化：有限組合せの枠2/3

R02の定義にある有限集合の昇順列を、経路の頂点の列をfilterする形へ直す。
新しい有限組合せの枠C02（L09aの2/3）は次の型とする。

```lean
sort_filter_univ (N : ℕ) (P : Fin N → Prop) [DecidablePred P] :
  (Finset.univ.filter P).sort (· ≤ ·) =
    (List.finRange N).filter (fun i => decide (P i))
```

接頭部・末尾の水平・垂直座標の評価、リストの連結と写像についての計算は、
R01・R02の同じ構成の証明分割である。新しいBE作用や法則は足していない。

### 114.4 末尾の出現回数：有限組合せの枠3/3

末尾の区間を `terminalSuffixIndex p j = p+j` で列挙する。
新しい有限組合せC03（L09aの3/3）は次の型とする。

```lean
terminalSuffix_card {m r : ℕ} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (c : Fin r) :
  (Finset.univ.filter (fun j : Fin (m - p.val + 1) =>
    v (terminalSuffixIndex p j) = c)).card = terminalMultiplicity v p c
```

R02の末尾の `List.replicate` の回数を元のfiberで数える式である。
一般の新しい有限分解がさらに必要なら、この枠では足さず報告して止まる。

### 114.5 R01・R02の完了と検証

次の8本、計607行を対象ビルドで検証した。

| モジュール（`SerrePositivity.EInfinity.SimplexCuts.` 以下） | 行数 | 内容 |
| --- | ---: | --- |
| LowerPart | 60 | 最大元より前の有限集合、C01 |
| TerminalExtension | 84 | 接頭部から最後の垂直辺と末尾を戻す |
| TerminalData | 107 | 最後の垂直辺、その区間番号、接頭部 |
| TerminalEquiv | 72 | 逆写像の一意性、R01 `cutLastVerticalEquiv` |
| TerminalCoordinates | 84 | 復元した切断の接頭部と末尾の座標 |
| VertexLists | 70 | 欠けた色を含む頂点列、C02 |
| TerminalSuffix | 66 | 末尾の反復数、C03 |
| TerminalTrace | 64 | 頂点列の評価、R02 `verticesList_lastVertical` |

R01の逆は `terminalExtend`。元の経路への復元と復元写像の単射性から同値を作った。
R02の型は§113.2の承認された型そのままであり、`List.replicate` の回数も
`terminalMultiplicity` の定義そのまま。全射性の仮定を足していない。

対象ビルド：`lake build SerrePositivity.EInfinity.SimplexCuts.TerminalTrace` 成功
（`/tmp/bsw16/m14-terminal-trace-03.log`）。新規8本にはLeanの警告なし。
専用監査：`/tmp/bsw16/audit-m14-terminal.lean`、**8モジュール・104宣言・標準三公理のみ**。
`/tmp/bsw16/audit-m14-terminal.log` に成功を確認。新規ソースにsorry・追加公理0。
ビルドと監査はそれぞれ `--wait 3600` の鍵を取り、終了時に返した。
rootビルド・全体監査・入口の登録はしていない。上記8本を次の登録候補とする。

今回の607行を足すと、改訂MayのM14本体は **5,919行**
（完成済みMay 4,128 + SimplexCuts既存1,184 + 今回607）。
半分の12,500行と外枠25,000行には届いていない。
旧coherent経路の10,216行は削除せず、この改訂Mayの内訳と分けて保持している。

## 115. L09aの符号の再帰で要る四本目の有限分解（11-14未明、停止）

R01・R02からL09aの境界項の対応へ戻り、接頭部の符号を比較した。
既存の `cutSign` は `intervalLength` と `positionExponent` で
**元の語の `Surjection.Caesura`** を使う。一方、切断の接頭部の語では
後続の色の出現を失うので、caesuraは保存されない。
例：`v=(0,1,0)`、`p=1`、`i=0`。元の語ではcaesuraだが、接頭語 `(0,1)` では違う。
R02は頂点列を戻す主張であり、元の語での「最後の出現」を接頭語に運ぶ主張ではない。
そのまま `cutSign s (prefixLabels v p)` を元の語の符号として使うことはできない。

### 115.1 追加が必要な主張の型

次の `prefixPosition` は報告内の記法で、未実装。

```lean
def prefixPosition {m : ℕ} (p : Fin (m + 1)) (i : Fin (p.val + 1)) :
    Fin (m + 1) :=
  ⟨i.val, by have hi := i.isLt; have hp := p.isLt; omega⟩

caesura_prefix_iff {m r : ℕ} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (i : Fin (p.val + 1)) :
  Surjection.Caesura v (prefixPosition p i) ↔
    Surjection.Caesura (prefixLabels v p) i ∨
    ∃ j : Fin (m + 1), p < j ∧ v j = prefixLabels v p i
```

これは後続の同色のfiberを接頭部内と末尾へ分ける有限分解であり、
L09aの同じまとまりの追加補題C04として必要になる。
全射性を足して接頭部に欠ける色を排除することはしない。
m=0〜4、色数1〜3、全ての語・接頭部・位置の5,384例でこの分解を確認した。
そのうち1,396例では元の語と接頭部でcaesuraが変わる。
有限点検は証明の代用ではなく、符号にこの区別が要ることの確認である。

### 115.2 既存APIと停止の理由

`Surjection.Caesuras` には定義、色の置換との可換性、全射語の最後の出現のAPIがある。
しかし、非全射も許す接頭語への上記の分解は見つからなかった。
既存のshuffleの混合角の交換・面の一致は利用候補だが、そちらの符号は
`ShufflePath.sign` であり、BFの色ごとのcaesuraを保持した符号の代わりにはならない。

§113では非全射の接頭部の**頂点列**の復元までを追加として挙げたが、
元の語のcaesuraを接頭語と末尾に分解する主張を挙げていなかった。
これはR02の構成の定義評価や相互逆の証明分割ではなく、
符号計算のための別の色のfiberの分解なので、別枠で記録する。
有限組合せの追加はC01・C02・C03で3/3に達した。
前提計算の残り枠を使ってこの第四の有限分解を足すことはしない。
**承認された枠の停止条件に従い、C04を実装する前にここで停止する。**
R01・R02の検証済み8本と本報告をコミットして判断を待つ。
L09aのτ・符号の相殺・微分の等式はまだ証明していない。
BE作用・operadの法則・Tot・界面は変更せず、G10の部品も作っていない。

## 116. C04とL09a再開（11-14未明、BS-W16 §29）

C04を§115.1の型そのままで実装する。§115の5,384例の点検を先行確認として使う。
`PrefixCaesuras.prefixPosition` と `caesura_prefix_iff` を置き、元の語のcaesuraを保持する。
L09a・L09内の有限組合せは数の枠を撤廃する最新指示に従う。
追加の型と有限点検をその都度記録し、行数1,000ごとに停止せず報告する。
BE作用・operad・Tot・界面や別のまとまりの新しい主張の停止規則は維持する。

累計は、L09aの既存境界データ五本246行とR01・R02八本607行の **853行** から数える。
L09aのために新設した有限組合せのファイルも全て含める。
mainは凍結中なので取り込まず、自枝で対象ビルド・小さい専用監査だけを行う。

### 116.1 次の有限計算と型

`/tmp/bsw16/check-terminal-endpoints.py` で、接頭切断の全ての区間長から
復元切断のlo・hiを独立に計算して比較した（m=0〜5、q=0〜4）。
次のC05・C06は、有限順序の区間fiberの最小・最大で定義したlo・hiの特徴づけ。

```lean
lo_eq_of_bound {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) (n : ℕ)
    (j : Fin (m + q + 1)) (hj : s.horizontal j = i) (hv : (s.vertical j).val = n)
    (hb : ∀ k, s.horizontal k = i → n ≤ (s.vertical k).val) : lo s i = n
hi_eq_of_bound {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) (n : ℕ)
    (j : Fin (m + q + 1)) (hj : s.horizontal j = i) (hv : (s.vertical j).val = n)
    (hb : ∀ k, s.horizontal k = i → (s.vertical k).val ≤ n) : hi s i = n
```

所属する頂点での上下界は、この特徴づけの証明分割として置く。

### 116.2 端点の界の型（C07〜C09）

上記の区間長による917例の点検で、それぞれの区間の全頂点が次の界を満たすことも確認した。
`terminalPrefixVertex p k hk` は位置kを同じ値の接頭頂点として読む記法。

```lean
terminal_lo_lower_bound {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + 1)) (k : Fin (m + (q + 1) + 1))
    (hc : (terminalExtend m q p s).horizontal k = prefixPosition p i) :
  lo s i ≤ ((terminalExtend m q p s).vertical k).val
terminal_hi_upper_bound {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + 1)) (hip : i.val < p.val) (k : Fin (m + (q + 1) + 1))
    (hc : (terminalExtend m q p s).horizontal k = prefixPosition p i) :
  ((terminalExtend m q p s).vertical k).val ≤ hi s i
terminal_vertical_of_horizontal_gt {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) (hip : p < i) (k : Fin (m + (q + 1) + 1))
    (hc : (terminalExtend m q p s).horizontal k = i) :
  (terminalExtend m q p s).vertical k = Fin.last (q + 1)
```

C07〜C09は色・区間の有限なfiberと端点の評価であり、BE作用の新しい主張ではない。

### 116.3 端点の復元式の型（C10〜C13）

§116.1の917例で次の等式を確認してからLeanへ入る。

```lean
lo_terminalExtend_prefix {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + 1)) :
  lo (terminalExtend m q p s) (prefixPosition p i) = lo s i
hi_terminalExtend_prefix {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + 1)) (hip : i.val < p.val) :
  hi (terminalExtend m q p s) (prefixPosition p i) = hi s i
hi_terminalExtend_at {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q) :
  hi (terminalExtend m q p s) p = q + 1
endpoints_terminalExtend_suffix {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) (hip : p < i) :
  lo (terminalExtend m q p s) i = q + 1 ∧ hi (terminalExtend m q p s) i = q + 1
```

L09a・L09の累計が1,000行を越えたところで、停止せずチャットでも途中報告した。
この時点ではC04とlo・hiの特徴づけが検証済み、復元区間の界以降を対象ビルド中。
τ・符号の相殺は未証明。C05〜C13は端点の有限計算に限っている。

### 116.4 元の語のcaesuraを保持する符号データ（C14〜C17）

次の式では、接頭部のcaesuraに置き換えず、元の語vのcaesuraを使う。
`prefixIndexOfLE p i h` は値iをFin(p+1)へ読む記法。

```lean
restoredLo p s i := if h : i ≤ p then lo s (prefixIndexOfLE p i h) else q + 1
restoredHi p s i := if h : i < p then hi s (prefixIndexOfLE p i h.le) else q + 1
restoredLength p s v i := restoredHi p s i - restoredLo p s i +
  if Surjection.Caesura v i then 1 else 0
restoredSignExponent p s v :=
  (∑ i, ∑ j, if i < j ∧ v j < v i then
    restoredLength p s v i * restoredLength p s v j else 0) +
  ∑ i, if Surjection.Caesura v i then restoredHi p s i else 0

lo_terminalExtend {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) : lo (terminalExtend m q p s) i = restoredLo p s i
hi_terminalExtend {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) : hi (terminalExtend m q p s) i = restoredHi p s i
intervalLength_terminalExtend {m q r : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (v : Fin (m + 1) → Fin r) (i : Fin (m + 1)) :
  intervalLength (terminalExtend m q p s) v i = restoredLength p s v i
cutSign_terminalExtend {m q r : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (v : Fin (m + 1) → Fin r) :
  cutSign (terminalExtend m q p s) v = (-1 : ℤ) ^ restoredSignExponent p s v
```

C14・C15は917例の端点点検の一括した式。
C16・C17も、以下の符号点検を先行してから実装に入る。
元の語を持つ数値の式であり、新しいBE作用やオペラッドの法則は定義しない。

### 116.5 検証済みの区切り（停止せず続行）

C04と端点・符号データの五本を検証した。`PrefixCaesuras` 42行、`IntervalExtrema` 57行、
`TerminalIntervalBounds` 90行、`TerminalEndpoints` 64行、`TerminalSignData` 77行、計330行。
符号指数の式はm=0〜3、q=0〜3、色数1〜3の全ての語で **8,206例**一致。
対象ビルド `lake build SerrePositivity.EInfinity.SimplexCuts.TerminalSignData` 成功。
専用監査は **5モジュール・47宣言・標準三公理のみ**、sorry・追加公理0。
ログは `/tmp/bsw16/m14-terminal-sign-data-02.log` と
`/tmp/bsw16/audit-m14-terminal-sign.log`。
登録候補はこの五本（名前は全て `SerrePositivity.EInfinity.SimplexCuts.` の下）。

L09a・L09の累計 **1,183行**、改訂MayのM14全体 **6,249行**。
1,000行の途中報告は済み、次は2,000行で報告する。τと境界の相殺は未証明。
最新のBS-W16 §30に従い、M15・G12は⑤dへ移ったので⑤aから進めない。
引継ぎ対象の既存の紙の報告は変更しない。mainへの取り込みも行わない。

## 117. 混合角の削除後の出力列（L09a続行）

`/tmp/bsw16/check-corner-sign.py` で全射・隣接非退化の語と混合角を列挙した。
m=1〜4、q=1〜3、色数1〜3の **9,536例**で、交換後に中間頂点を削除した各色の
出力列が一致し、BF符号とテンソル境界符号の積が反対になることを確認した。
これは符号のLean証明の代用にしない。
C18の列の一致自体は混合角の仮定が要らないので、
`/tmp/bsw16/check-corner-trace.py` で同じ向きの隣接辺も含む全経路を別に点検した。

```lean
def deletedTrace {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) : List (Fin r × Fin (q + 1)) :=
  List.ofFn (fun j => (label s v (k.succAbove j), s.vertical (k.succAbove j)))

deletedTrace_swapSteps {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) :
  deletedTrace (s.swapSteps a b) v b.castSucc = deletedTrace s v b.castSucc
```

既存の `horizontal_swapSteps`・`vertical_swapSteps` を同じ省略頂点の補集合上で使う。
新しいBE作用ではなく、L09aの境界の二項を対応させるための有限列の照合である。

### 117.1 頂点削除を色の面番号へ運ぶ型（C19・C20）

C18は同向きの辺も含む550例で削除後の経路が一致した。
`check-corner-trace.py` の最初の点検では同向きの辺まで対称差で反転して失敗したため、
二つの位置の**交換**による像へ直した。Leanの `swapSteps` もこの交換を使う。

`/tmp/bsw16/check-color-erasure.py` で、長さ0〜6・色数1〜3の全語、
全ての色と範囲外も含む削除位置について、C20の式を点検してからLeanへ入る。
C19の列はその位置を `succAbove` で飛ばす同じ操作。

```lean
eraseIdx_ofFn {β : Type*} {N : ℕ} (f : Fin (N + 1) → β) (k : Fin (N + 1)) :
  (List.ofFn f).eraseIdx k.val = List.ofFn (fun j => f (k.succAbove j))
selectColor_eraseIdx {r : ℕ} {β : Type*} (c : Fin r) (l : List (Fin r × β)) (k : ℕ) :
  selectColor c (l.eraseIdx k) =
    if (l[k]?.map Prod.fst) = some c then
      (selectColor c l).eraseIdx (selectColor c (l.take k)).length
    else selectColor c l
```

削除される色のfiber内の面番号は、元の頂点より前に出た同色の個数である。

### 117.2 出力の面の位置を一つの経路の頂点へまとめる型（C21・C22）

長さ0〜6、色数1〜3の全ての語で、色と色内順位の組を元の位置へ戻す写像が
全位置を一回ずつ覆い、逆の色と先行同色数も一致することを点検した。
Leanでは既存の `Finset.orderIsoOfFin` と `Equiv.sigmaFiberEquiv` を合成する。

```lean
colorPositionEquiv {m q r : ℕ} (s : Cut m q) (u : Surjection.Word r (m + 1)) :
  (Σ a : Fin r, Fin (outputDegree s u a + 1)) ≃ Fin (m + q + 1)
outputBoundaryPositionEquiv {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  OutputBoundaryIndex u q ≃ Σ s : Cut (r + d) q, Fin (r + d + q + 1)
```

前者の正方向は各色の `orderEmbOfFin`、逆の色は `label s u.val k` そのもの。
零となる境界項を添字から先に消さず、零次の色の唯一の面番号も残す。

### 117.3 出力の角交換の対合（C23〜C25）

m=0〜5、q=0〜4の全経路と全指定頂点で、内部の前後の辺の交換が二回で戻ることを
点検してから実装する。同向きの辺では元の経路のまま、両端でも恒等とする。

```lean
def swapAtVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : Cut m q :=
  if h : 0 < k.val ∧ k.val < m + q then
    s.swapSteps (cornerLeftEdge k h) (cornerRightEdge k h) else s
swapAtVertex_involutive {m q : ℕ} (k : Fin (m + q + 1)) :
  Function.Involutive (fun s : Cut m q => swapAtVertex s k)
vertexCornerPerm (m q : ℕ) : Equiv.Perm (Σ _ : Cut m q, Fin (m + q + 1))
outputCornerPerm {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  Equiv.Perm (OutputBoundaryIndex u q)
outputCornerPerm_involutive {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  Function.Involutive (outputCornerPerm u q)
```

これは**全境界項のτではない**。混合角以外に残る固定点の境界項は零とは主張せず、
係数の文字削除・入力の面に対応させる段を別に残す。

### 117.4 実際の色の出力列の削除の型（C26〜C28）

C26〜C28は§117・§117.1の点検済みの列の式を切断へ特殊化する。
先行同色数がその色の範囲内であることも、同じ26,430例の点検で保持した。

```lean
vertexRank s v c k :=
  (selectColor c ((List.ofFn (fun i => (label s v i, s.vertical i))).take k.val)).length
deletedVerticesList s v k c :=
  if label s v k = c then (verticesList s v c).eraseIdx (vertexRank s v c k)
  else verticesList s v c

deletedVerticesList_eq_selectColor {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) (c : Fin r) :
  deletedVerticesList s v k c = selectColor c (deletedTrace s v k)
deletedVerticesList_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (c : Fin r) :
  deletedVerticesList (s.swapSteps a b) v b.castSucc c =
    deletedVerticesList s v b.castSucc c
vertexRank_lt_length {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) :
  vertexRank s v (label s v k) k < (verticesList s v (label s v k)).length
```

### 117.5 昇順fiberの面番号の型（C29・C30）

N=0〜8の全ての部分集合の各昇順位置で、「前の元の数＝順位」を点検してからLeanへ入る。

```lean
card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α] (t : Finset α) {N : ℕ}
    (h : t.card = N) (j : Fin N) :
  (t.filter (fun x => x < t.orderEmbOfFin h j)).card = j.val
colorPositionEquiv_rank {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1)) :
  ((colorPositions s u.val a).filter (fun k => k < colorPositionEquiv s u ⟨a, j⟩)).card = j.val
```

### 117.6 列の順位と面番号の一致の型（C31〜C33）

§117.1の26,430例と§117.2の1,227語の順位点検から、列の先行同色数と
有限集合の順位が一致する式を使う。C31は範囲外のkも含む点検の式の長さである。

```lean
selectColor_take_ofFn_length {r N : ℕ} {β : Type*} (f : Fin N → Fin r × β)
    (c : Fin r) (k : ℕ) :
  (selectColor c ((List.ofFn f).take k)).length =
    (Finset.univ.filter (fun i => i.val < k ∧ (f i).1 = c)).card
vertexRank_eq_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (c : Fin r) (k : Fin (m + q + 1)) :
  vertexRank s v c k = ((colorPositions s v c).filter (fun i => i < k)).card
vertexRank_colorPositionEquiv {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1)) :
  vertexRank s u.val a (colorPositionEquiv s u ⟨a, j⟩) = j.val
```

### 117.7 同じ指定面と頂点列の型（C34〜C36）

正次数0〜4（元の頂点数2〜6）、終域次数0〜3の全ての弱単調写像と全ての削除位置で、
標準面との合成と頂点列の一文字削除が一致することを点検してからLeanへ入る。

```lean
simplexVertexList {n q : ℕ} (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) : List (Fin (q + 1))
simplexVertexList_injective (n q : ℕ) :
  Function.Injective (fun f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌ => simplexVertexList f)
simplexVertexList_delta {n q : ℕ}
    (f : (⦋n + 1⦌ : SimplexCategory) ⟶ ⦋q⦌) (j : Fin (n + 2)) :
  simplexVertexList (SimplexCategory.δ j ≫ f) = (simplexVertexList f).eraseIdx j.val
simplexVertexList_face {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) :
  simplexVertexList (face s u a) = verticesList s u.val a
```

面の一致をホモトピーで済ませず、元の単体圏の射の一致へ戻すための有限計算。

### 117.8 指定した出力面の列（C37〜C40）

C37〜C39は、§117.2の順位と§117.1の削除の点検の同じ式を指定の面番号で読んだもの。
C40は§117.7の標準面の点検を正次数で述べ直す。始域の等式による移送は定義評価。

```lean
vertexRank_symm_colorPositionEquiv {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
  vertexRank s u.val (label s u.val k) k = ((colorPositionEquiv s u).symm k).2.val
label_colorPositionEquiv {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1)) :
  label s u.val (colorPositionEquiv s u ⟨a, j⟩) = a
deletedTrace_at_outputFace {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1))
    (c : Fin r) :
  selectColor c (deletedTrace s u.val (colorPositionEquiv s u ⟨a, j⟩)) =
    if c = a then (verticesList s u.val a).eraseIdx j.val else verticesList s u.val c
simplexVertexList_boundaryFace {n q : ℕ} (hn : 0 < n)
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) (j : Fin (n + 1)) :
  simplexVertexList (boundaryFace n hn j ≫ f) = (simplexVertexList f).eraseIdx j.val
simplexVertexList_cast_source {n n' q : ℕ} (h : n = n')
    (f : (⦋n'⦌ : SimplexCategory) ⟶ ⦋q⦌) :
  simplexVertexList (eqToHom (congrArg SimplexCategory.mk h) ≫ f) = simplexVertexList f
```

### 117.9 混合角と固定点の型（C41〜C43）

m=0〜5、q=0〜4の3,829個の指定頂点付き経路で、非固定点と内部の異向きの二辺が
ちょうど一致することを先に点検した。

```lean
swapSteps_eq_self_iff {m q : ℕ} (s : Cut m q) (a b : Fin (m + q)) :
  s.swapSteps a b = s ↔ (a ∈ s.val ↔ b ∈ s.val)
MixedVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : Prop :=
  ∃ h : 0 < k.val ∧ k.val < m + q,
    cornerLeftEdge k h ∈ s.val ↔ cornerRightEdge k h ∉ s.val
swapAtVertex_ne_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  swapAtVertex s k ≠ s ↔ MixedVertex s k
mixedVertex_swapAtVertex_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  MixedVertex (swapAtVertex s k) k ↔ MixedVertex s k
```

ここでの固定点は「出力の角交換」の固定点であり、全体のτの固定点とは区別する。

## 118. 全境界の有限な対応候補を点検（L09a続行）

`/tmp/bsw16/check-boundary-pairing.py` に、経路の指定頂点の次の対応を独立に書いた。
水平・水平（端点で水平辺の場合も含む）はゼロ長の区間を消して係数の文字削除へ、
垂直・垂直（端点も含む）は垂直辺を一本消して入力面へ、混合角は前後の辺を交換する。
水平次数0の余分な係数添字、入力次数0の入力面添字、総次数0の出力添字は固定する。
逆は、係数位置で水平なゼロ長区間を挿入、入力面の指定レベルで垂直辺を挿入する。

m=0〜5、q=0〜4の **6,070添字**で二回の対応が恒等になることを確認。
さらにm=0〜4、q=0〜3、色数1〜3の全射・隣接非退化の語について、
`cutSign`・`deletionCoefficient`・テンソルの境界のKoszul符号・入力面の負号を保ち、
重複した出力頂点を零とする独立な計算で **38,322項**が反対の値になった。
これからこの候補をLeanで構成する。有限点検だけからτや境界の等式を宣言しない。

### 118.1 分岐の型（C44〜C46）

```lean
inductive BoundaryVertexKind
  | horizontal | vertical | mixed | isolated
boundaryVertexKind {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : BoundaryVertexKind
boundaryVertexKind_eq_mixed_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  boundaryVertexKind s k = .mixed ↔ MixedVertex s k
boundaryVertexKind_eq_isolated_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  boundaryVertexKind s k = .isolated ↔ m = 0 ∧ q = 0
```

C44は前後の辺の所属の判定、C45・C46は上記6,070添字の分岐を点検した条件。

### 118.2 水平境界に対応する一頂点の区間（C47・C48）

m=0〜5、q=0〜5の全ての区間長の列で、一頂点のfiberと零長区間の条件を点検してから
Leanへ入る。区間の非空性と既存の経路の頂点の単射性から証明する。

```lean
intervalPositions_card_eq_one_iff {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
  (intervalPositions s i).card = 1 ↔ lo s i = hi s i
interval_gap_eq_zero_iff {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
  hi s i - lo s i = 0 ↔ (intervalPositions s i).card = 1
```

### 118.3 語に依らない境界添字と種類の分割（C49・C50）

§118の6,070添字の点検の各分岐を、その種類の部分型に分ける。
有限の直和への分割は、各指定頂点を一回だけ保持する。

```lean
abbrev MarkedCut (m q : ℕ) := Σ _ : Cut m q, Fin (m + q + 1)
abbrev BoundaryVertexOfKind (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b}
boundaryVertexPartitionEquiv (m q : ℕ) : MarkedCut m q ≃
  BoundaryVertexOfKind m q .horizontal ⊕ (BoundaryVertexOfKind m q .vertical ⊕
    (BoundaryVertexOfKind m q .mixed ⊕ BoundaryVertexOfKind m q .isolated))
abbrev UniversalBoundaryIndex (m q : ℕ) :=
  MarkedCut m q ⊕ ((Fin (m + 1) × Cut (m - 1) q) ⊕ (Fin (q + 1) × Cut m (q - 1)))
boundaryBalanceIndexEquiv {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  BoundaryBalanceIndex u q ≃ UniversalBoundaryIndex (r + d) q
```

最後の同値は出力面の位置の同値を直和へ運ぶだけで、元の境界項の型を変更しない。

### 118.4 端点・内部の判定の評価（C51〜C53）

§118の全指定頂点の分岐の点検と同じ形で、定義を次の式へ評価する。

```lean
boundaryVertexKind_zero {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
  boundaryVertexKind s 0 =
    if (⟨0, hN⟩ : Fin (m + q)) ∈ s.val then .horizontal else .vertical
boundaryVertexKind_last {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
  boundaryVertexKind s (Fin.last (m + q)) =
    if (⟨m + q - 1, by omega⟩ : Fin (m + q)) ∈ s.val then .horizontal else .vertical
boundaryVertexKind_interior {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (h : 0 < k.val ∧ k.val < m + q) :
  boundaryVertexKind s k =
    if cornerLeftEdge k h ∈ s.val then
      if cornerRightEdge k h ∈ s.val then .horizontal else .mixed
    else if cornerRightEdge k h ∈ s.val then .mixed else .vertical
```

### 118.5 一頂点のfiberと隣接辺（C54〜C56）

有限単調写像（始域次数0〜5、終域次数0〜3）の全ての指定頂点で、
fiberが一頂点であることと両側の厳密な増分の条件を点検してからLeanへ入る。
水平辺の増分自体は、§118の全経路の既存の辺の向きの点検でも確認している。

```lean
mem_iff_horizontal_lt {m q : ℕ} (s : Cut m q) (a : Fin (m + q)) :
  a ∈ s.val ↔ s.horizontal a.castSucc < s.horizontal a.succ
monotone_fiber_singleton_iff {N M : ℕ} (f : Fin (N + 1) →o Fin (M + 1))
    (k : Fin (N + 1)) :
  (∀ j, f j = f k → j = k) ↔
    (∀ a : Fin N, a.succ = k → f a.castSucc < f k) ∧
    (∀ a : Fin N, a.castSucc = k → f k < f a.succ)
HorizontalVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : Prop :=
  (∀ a : Fin (m + q), a.succ = k → a ∈ s.val) ∧
  (∀ a : Fin (m + q), a.castSucc = k → a ∈ s.val)
horizontal_fiber_singleton_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  (∀ j, s.horizontal j = s.horizontal k → j = k) ↔ HorizontalVertex s k
```

総次数零では左右の辺の条件は空となる点を保持し、零次の余分な係数添字の分岐を潰さない。

### 118.6 水平境界の判定と隣接辺の型（C57〜C60）

§118の全指定頂点の分岐の点検と§118.5のfiberの点検を、同じ左右の辺の条件で述べる。

```lean
horizontalVertex_interior_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (h : 0 < k.val ∧ k.val < m + q) :
  HorizontalVertex s k ↔ cornerLeftEdge k h ∈ s.val ∧ cornerRightEdge k h ∈ s.val
horizontalVertex_zero_iff {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
  HorizontalVertex s 0 ↔ (⟨0, hN⟩ : Fin (m + q)) ∈ s.val
horizontalVertex_last_iff {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
  HorizontalVertex s (Fin.last (m + q)) ↔
    (⟨m + q - 1, by omega⟩ : Fin (m + q)) ∈ s.val
boundaryVertexKind_eq_horizontal_iff {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) :
  boundaryVertexKind s k = .horizontal ↔ 0 < m + q ∧ HorizontalVertex s k
```

### 118.7 水平境界と零長区間の型（C61〜C63）

§118の全指定頂点の点検では、水平に分類した頂点の区間は零長であり、水平次数は正。
§118.2のfiberの点検と同じ条件を合わせる。

```lean
horizontalVertex_iff_card_eq_one {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) :
  HorizontalVertex s k ↔ (intervalPositions s (s.horizontal k)).card = 1
boundaryVertexKind_eq_horizontal_gap {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) :
  boundaryVertexKind s k = .horizontal ↔
    0 < m + q ∧ hi s (s.horizontal k) - lo s (s.horizontal k) = 0
horizontal_kind_pos {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (hk : boundaryVertexKind s k = .horizontal) : 0 < m
```

### 118.8 検証済みの区切りと2,000行の途中報告

§117〜§118.7の17モジュール、計 **1,031行**を対象ビルドで検証した。
`CornerTraces`・`VertexErasure`・`BoundaryPositions`・`CornerInvolution`・`DeletedVertices`・
`FiberRanks`・`VertexRanks`・`FaceVertexLists`・`BoundaryVertexLists`・`CornerFixedPoints`・
`BoundaryKinds`・`IntervalSingletons`・`BoundaryPartition`・`BoundaryKindValues`・
`SingletonFiberSteps`・`HorizontalVertexKinds`・`HorizontalSingletons`。
名前の接頭部は全て `SerrePositivity.EInfinity.SimplexCuts.`。次の登録候補一覧はこの17本。

専用監査 `/tmp/bsw16/audit-m14-boundary-fibers.lean` は
**17モジュール・164宣言・標準三公理のみ**。
対象ビルドは `/tmp/bsw16/m14-horizontal-singletons-01.log` などに成功を確認。
新規ソースにsorry・追加公理0、警告も解消。rootや全体監査は回していない。

この時点でL09a・L09の累計 **2,214行**、改訂MayのM14全体 **7,280行**。
2,000行を越えた途中報告は停止せずチャットでも行った。次は3,000行で報告する。
全体のτ、BFの境界の相殺・微分の等式はまだ証明していない。
水平な端点の挿入の同値へ続ける。

### 118.9 水平端点の挿入の同値の型（C64〜C66）

§118の6,070添字の往復の点検のうち、水平な始点・終点を挿入する分岐を使う。
既存の `BarrattEccles.horizontalInsertionEquiv` へ、固定した頂点の条件を付ける。

```lean
fixedMarkedCutEquiv {m q : ℕ} (b : BoundaryVertexKind) (k : Fin (m + q + 1)) :
  {s : Cut m q // boundaryVertexKind s k = b} ≃
    {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ t.2 = k}
horizontalFirstFaceEquiv (m q : ℕ) : Cut m q ≃
  {t : MarkedCut (m + 1) q // boundaryVertexKind t.1 t.2 = .horizontal ∧ t.2 = 0}
horizontalLastFaceEquiv (m q : ℕ) : Cut m q ≃
  {t : MarkedCut (m + 1) q // boundaryVertexKind t.1 t.2 = .horizontal ∧
    t.2 = Fin.last (m + 1 + q)}
```

### 118.10 水平内部面の挿入の同値の型（C67・C68）

§118の6,070添字の往復の点検のうち、内部の水平・水平の分岐を使う。
既存の `horizontalMarkedEdgeEquiv` と `horizontalCornerEquiv` を合成し、
角の中間頂点の値をa+1として指定頂点付き経路へ移す。

```lean
HorizontalInteriorFace (m q : ℕ) :=
  {t : MarkedCut (m + 1) q // boundaryVertexKind t.1 t.2 = .horizontal ∧
    0 < t.2.val ∧ t.2.val < m + 1 + q}
horizontalCornerFaceEquiv (m q : ℕ) :
  BarrattEccles.HorizontalCorner m q ≃ HorizontalInteriorFace m q
horizontalInteriorFaceEquiv (m q : ℕ) :
  Cut m q × Fin m ≃ HorizontalInteriorFace m q
```

### 118.11 水平な三分岐の同値までの検証済み区切り

`HorizontalEndpointFaces` 53行、`HorizontalInteriorFaces` 86行、計139行を対象ビルドで検証した。
水平な始点・終点・内部のそれぞれで、小さい切断から水平辺を挿入する同値が閉じた。
既存のshuffleの角の挿入を利用し、公開宣言の定義は変更していない。

対象ビルド `lake build SerrePositivity.EInfinity.SimplexCuts.HorizontalInteriorFaces` 成功
（`/tmp/bsw16/m14-horizontal-interior-faces-03.log`）。
専用監査 `/tmp/bsw16/audit-m14-horizontal-faces.lean` は
**2モジュール・44宣言・標準三公理のみ**。
新規二本にsorry・追加公理0、Leanの警告なし。次の登録候補はこの二本も含む。
それぞれのビルド・監査だけ鍵を取り、終了時に返した。root・全体監査は回していない。

L09a・L09の累計 **2,353行**、改訂MayのM14全体 **7,419行**。
C04再開後の新規分は、五本330行、十七本1,031行、二本139行、計 **1,500行**。
外枠25,000行と半分の12,500行には届いていない。
有限組合せの追加の数では停止しない最新の規則を維持する。

次に残る有限対応は、水平な三分岐を係数の `Fin (m + 2) × Cut m q` へまとめること、
垂直な始点・終点・内部の対応、および混合角との直和で全体のτを作ること。
その後の符号と正規化した境界項の反対の値のLean証明も未完。
§118の38,322項のPython点検を、それらのLean証明として扱っていない。
G10・Tot・界面・新しいBE作用・operadの法則は作っておらず、M15・G12にも手を付けない。
main凍結を維持し、以上は自枝の検証済み保存の区切りとして記録する。

## 119. 共通の一覧の数え方へ移行して続行（11-14）

最新のcoordination.md §2に従い、既存の構成の法則（単位・余単位・自然性・係数移送・
合成則・貼り合わせ）と証明分割に数の枠を置かない。型を報告に記録し、
200行を超える補題には行数も記す。L09a・L09の有限組合せの事前点検、
1,000行ごとの途中報告、M14全体25,000行の外枠は維持する。
mainは凍結中で、自枝の対象ビルド・小さい専用監査だけを行う。

### 119.1 既存の種類の部分型を三分岐へ貼り合わせる型（C69）

総次数N=1〜12の全90頂点で、始点・内部・終点のちょうど一つに属することを確認。
この有限の位置の判定を、既存の境界種類の部分型に付ける。

```lean
FirstBoundaryFace (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ t.2 = 0}
InteriorBoundaryFace (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ 0 < t.2.val ∧ t.2.val < m + q}
LastBoundaryFace (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ t.2 = Fin.last (m + q)}
boundaryEndpointPartitionEquiv (m q : ℕ) (b : BoundaryVertexKind) (hN : 0 < m + q) :
  BoundaryVertexOfKind m q b ≃ FirstBoundaryFace m q b ⊕
    (InteriorBoundaryFace m q b ⊕ LastBoundaryFace m q b)
```

### 119.2 水平な三分岐の貼り合わせの型（C70・C71）

§118の水平境界の全ての往復の点検と§119.1の位置の分割の点検を使う。
既存の `finSumFinEquiv`、積の直和への分配、三つの挿入同値を合成する。

```lean
singletonSlotProdEquiv (X : Type*) : Fin 1 × X ≃ X
firstInteriorLastIndexEquiv (m : ℕ) : Fin (m + 2) ≃ Fin 1 ⊕ (Fin m ⊕ Fin 1)
coefficientIndexEndpointEquiv (m q : ℕ) :
  Fin (m + 2) × Cut m q ≃ Cut m q ⊕ ((Cut m q × Fin m) ⊕ Cut m q)
horizontalBoundaryFaceEquiv (m q : ℕ) :
  Fin (m + 2) × Cut m q ≃ BoundaryVertexOfKind (m + 1) q .horizontal
```

新しい作用や定理を仮定せず、検証済みの水平な三分岐を同じ有限添字に貼り合わせる。

### 119.3 既存の方向交換と境界種類の照合（C72〜C74）

m=0〜5、q=0〜4の全3,829個の指定頂点付き経路で、水平辺の補集合への交換が
水平・垂直の判定を交換し、混合・単独頂点を保つことを点検してから実装する。
`setBoundaryKind` は既存の `boundaryVertexKind` と同じ有限判定を、全辺数と集合だけで読む記法。

```lean
BoundaryVertexKind.exchange : BoundaryVertexKind → BoundaryVertexKind
BoundaryVertexKind.exchange_involutive : Function.Involutive BoundaryVertexKind.exchange
setBoundaryKind {N : ℕ} (s : Finset (Fin N)) (k : Fin (N + 1)) : BoundaryVertexKind
boundaryVertexKind_eq_setBoundaryKind {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) : boundaryVertexKind s k = setBoundaryKind s.val k
setBoundaryKind_compl {N : ℕ} (s : Finset (Fin N)) (k : Fin (N + 1)) :
  setBoundaryKind sᶜ k = (setBoundaryKind s k).exchange
setBoundaryKind_map_finCongr {N N' : ℕ} (h : N = N') (s : Finset (Fin N))
    (k : Fin (N + 1)) :
  setBoundaryKind (s.map (finCongr h).toEmbedding) (Fin.cast (congrArg (· + 1) h) k) =
    setBoundaryKind s k
boundaryVertexKind_exchange {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
  boundaryVertexKind s.exchange (Fin.cast (by omega : m + q + 1 = q + m + 1) k) =
    (boundaryVertexKind s k).exchange
```

新しい作用は作らず、既存の `shuffleExchangeEquiv` と有限な辺集合の判定を照合する法則。

### 119.4 垂直境界への既存の同値の移送の型（C75〜C78）

§118の垂直分岐の全ての往復と§119.3の方向交換の点検を使う。
水平側の同値と方向交換の同値を合成し、別に垂直側の三分岐を作り直さない。

```lean
markedCutExchangeEquiv (m q : ℕ) : MarkedCut m q ≃ MarkedCut q m
boundaryKindExchangeEquiv (m q : ℕ) (b : BoundaryVertexKind) :
  BoundaryVertexOfKind m q b ≃ BoundaryVertexOfKind q m b.exchange
verticalBoundaryFaceEquiv (m q : ℕ) :
  Fin (q + 2) × Cut m q ≃ BoundaryVertexOfKind m (q + 1) .vertical
vertical_kind_pos {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (hk : boundaryVertexKind s k = .vertical) : 0 < q
```

### 119.5 全境界の同じ添字への書き換え（C79〜C82）

既存の水平・垂直の同値を、正の次数と前者の次数への添字で述べ直す。
混合角の種類の保存と対合の式は、検証済みの角交換の法則の同じ式の書き換え。
点検は§118の全境界の往復と§117.9の混合角の点検に含まれる。

```lean
horizontalBoundaryAllEquiv (m q : ℕ) (hm : 0 < m) :
  Fin (m + 1) × Cut (m - 1) q ≃ BoundaryVertexOfKind m q .horizontal
verticalBoundaryAllEquiv (m q : ℕ) (hq : 0 < q) :
  Fin (q + 1) × Cut m (q - 1) ≃ BoundaryVertexOfKind m q .vertical
mixed_kind_swapAtVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (hk : boundaryVertexKind s k = .mixed) :
  boundaryVertexKind (swapAtVertex s k) k = .mixed
vertexCornerPerm_involutive (m q : ℕ) : Function.Involutive (vertexCornerPerm m q)
```

### 119.6 検証済みの同値を全境界へ貼り合わせる型（C83〜C86）

§118の6,070添字の往復の点検で使った対応を、既存の挿入同値・方向交換・角交換で作る。
水平・垂直の正の次数を満たさない余分な右辺添字と、単独の出力頂点は固定する。

```lean
universalBoundaryPartner (m q : ℕ) : UniversalBoundaryIndex m q → UniversalBoundaryIndex m q
universalBoundaryPartner_involutive (m q : ℕ) : Function.Involutive (universalBoundaryPartner m q)
universalBoundaryPerm (m q : ℕ) : Equiv.Perm (UniversalBoundaryIndex m q)
boundaryBalancePerm {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  Equiv.Perm (BoundaryBalanceIndex u q)
boundaryBalancePerm_involutive {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
  Function.Involutive (boundaryBalancePerm u q)
```

これはL09aのτの**添字上の候補**。符号付き境界項の相殺・固定点の値が零であることは
まだこの宣言に含めず、その証明は残す。候補を前提にL09や作用の法則を宣言しない。

### 119.7 全境界の対合候補の固定点の型（C87・C88）

§118の6,070添字の点検では、対合の固定点は次の零次数の余分な添字だけだった。
この点検は候補の往復だけでなく、固定点の条件も分類したものとして使う。
混合角の非固定性は検証済みの `swapAtVertex_ne_iff` の同じ式。

```lean
mixed_vertexCornerPerm_ne {m q : ℕ} (t : MarkedCut m q)
    (ht : boundaryVertexKind t.1 t.2 = .mixed) : vertexCornerPerm m q t ≠ t
universalBoundaryPartner_fixed_iff (m q : ℕ) (i : UniversalBoundaryIndex m q) :
  universalBoundaryPartner m q i = i ↔
    match i with
    | .inl _ => m = 0 ∧ q = 0
    | .inr (.inl _) => m = 0
    | .inr (.inr _) => q = 0
boundaryBalancePerm_fixed_iff {r d : ℕ} (u : Surjection.BasisWord (r + 1) d)
    (q : ℕ) (i : BoundaryBalanceIndex u q) :
  boundaryBalancePerm u q i = i ↔
    universalBoundaryPartner (r + d) q ((boundaryBalanceIndexEquiv u q) i) =
      (boundaryBalanceIndexEquiv u q) i
```

### 119.8 L09aの固定点の零の部分

C87の固定点の条件は6,070添字で明示的に再確認した。
§118の38,322項の符号付き値の点検では、固定点は全て零だった。
その部分を元の境界項の定義へ戻す。L09aの一覧にある固定点の零の主張の証明分割であり、
別の作用・定理を追加するものではない。

```lean
boundaryBalancePerm_fixed_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ)
    (i : BoundaryBalanceIndex w q) (hi : boundaryBalancePerm w q i = i) (x : S _⦋q⦌) :
  boundaryBalanceTerm A S w q i x = 0
```

出力側はr=d=q=0、係数側はd=0、入力側はq=0に帰着する。
出力側の色の次数は、全頂点数が1である有限濃度評価から零と判定する。

### 119.9 貼り合わせた対合の評価式

以下は検証済みの対合の各分岐の定義評価であり、数の枠を置かない既存構成の法則の補題。
点検は§118の同じ6,070添字の対応の式を使う。

```lean
universalBoundaryPartner_horizontal (m q : ℕ) (hm : 0 < m)
    (t : BoundaryVertexOfKind m q .horizontal) :
  universalBoundaryPartner m q (.inl t.val) =
    .inr (.inl ((horizontalBoundaryAllEquiv m q hm).symm t))
universalBoundaryPartner_vertical (m q : ℕ) (hq : 0 < q)
    (t : BoundaryVertexOfKind m q .vertical) :
  universalBoundaryPartner m q (.inl t.val) =
    .inr (.inr ((verticalBoundaryAllEquiv m q hq).symm t))
universalBoundaryPartner_mixed (m q : ℕ) (t : BoundaryVertexOfKind m q .mixed) :
  universalBoundaryPartner m q (.inl t.val) = .inl (vertexCornerPerm m q t.val)
universalBoundaryPartner_coefficient (m q : ℕ) (hm : 0 < m)
    (c : Fin (m + 1) × Cut (m - 1) q) :
  universalBoundaryPartner m q (.inr (.inl c)) = .inl ((horizontalBoundaryAllEquiv m q hm) c).val
universalBoundaryPartner_input (m q : ℕ) (hq : 0 < q)
    (v : Fin (q + 1) × Cut m (q - 1)) :
  universalBoundaryPartner m q (.inr (.inr v)) = .inl ((verticalBoundaryAllEquiv m q hq) v).val
universalBoundaryPartner_isolated (m q : ℕ) (t : BoundaryVertexOfKind m q .isolated) :
  universalBoundaryPartner m q (.inl t.val) = .inl t.val
```

### 119.10 L09aの三群の等式の貼り合わせ

同じ対合の既存の評価式を使う証明分割。三群の仮定は今後閉じる本来の相殺であり、
未供給の等式を公理や暗黙の前提として最終結果へ入れない。

```lean
universalBoundaryPartner_neg_of_cases {B : Type*} [AddCommGroup B] (m q : ℕ)
    (F : UniversalBoundaryIndex m q → B)
    (hfixed : ∀ i, universalBoundaryPartner m q i = i → F i = 0)
    (hc : ∀ (hm : 0 < m) (c : Fin (m + 1) × Cut (m - 1) q),
      F (.inl ((horizontalBoundaryAllEquiv m q hm) c).val) = -F (.inr (.inl c)))
    (hv : ∀ (hq : 0 < q) (v : Fin (q + 1) × Cut m (q - 1)),
      F (.inl ((verticalBoundaryAllEquiv m q hq) v).val) = -F (.inr (.inr v)))
    (hmix : ∀ t : BoundaryVertexOfKind m q .mixed,
      F (.inl (vertexCornerPerm m q t.val)) = -F (.inl t.val))
    (i : UniversalBoundaryIndex m q) :
  F (universalBoundaryPartner m q i) = -F i
```

実際の境界値については `hfixed` は§119.8で証明済み。
`hc`・`hv`・`hmix` の符号と指定面の照合が残る。全項の相殺をこの補題だけから主張しない。

### 119.11 実際の境界値の同じ添字への移送の型

既存の境界値を、検証済みの添字の同値に沿って読む定義とその評価の法則。
元の複体・境界項・界面の型は変えない。

```lean
universalBoundaryValue (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
  UniversalBoundaryIndex (r + d) q →
    (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
universalBoundaryValue_at_index (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : BoundaryBalanceIndex w q) :
  universalBoundaryValue A S w q x ((boundaryBalanceIndexEquiv w q) i) =
    boundaryBalanceTerm A S w q i x
universalBoundaryValue_partner (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : BoundaryBalanceIndex w q) :
  universalBoundaryValue A S w q x
    (universalBoundaryPartner (r + d) q ((boundaryBalanceIndexEquiv w q) i)) =
      boundaryBalanceTerm A S w q (boundaryBalancePerm w q i) x
universalBoundaryValue_fixed_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : UniversalBoundaryIndex (r + d) q) (hi : universalBoundaryPartner (r + d) q i = i) :
  universalBoundaryValue A S w q x i = 0
```

### 119.12 同方向の削除の指定列の照合（C89・C90）

m=0〜5、q=0〜4の全経路の内部の水平・水平、垂直・垂直の箇所で、
中間頂点の削除の列が、一本の辺を消した小さい経路の指定座標を一つ飛ばす列と一致することを
点検してから実装する。Leanでは既存の `horizontalDeletion_horizontal`・
`horizontalDeletion_vertical`・`verticalDeletion_horizontal`・`verticalDeletion_vertical` を使う。

```lean
horizontal_deletedTrace {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val) :
  deletedTrace s v a.succ = List.ofFn (fun k : Fin (m + q + 1) =>
    (Surjection.erase v (s.horizontal a.succ)
      (((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k),
    ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).vertical k))
vertical_deletedTrace {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + (q + 1))) (hab : b.val = a.val + 1)
    (ha : a ∉ s.val) (hb : b ∉ s.val) :
  deletedTrace s v a.succ = List.ofFn (fun k : Fin (m + q + 1) =>
    (v (((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k),
    (s.vertical a.succ).succAbove
      (((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩).vertical k)))
```

### 119.13 符号次数を出力次数へ結ぶ有限濃度の型（C91・C92）

m=0〜5、q=0〜5の4,752個の区間fiberで、位置の連続性と
「頂点数＝両端の垂直座標の差＋1」を点検してからLeanへ入る。

```lean
intervalPositions_eq_Icc {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
  intervalPositions s i = Finset.Icc
    ((intervalPositions s i).min' (intervalPositions_nonempty s i))
    ((intervalPositions s i).max' (intervalPositions_nonempty s i))
intervalPositions_card {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
  (intervalPositions s i).card = hi s i - lo s i + 1
```

### 119.14 各色のcaesuraの濃度（C93〜C95）

長さ1〜6・色数1〜3の全射語の全ての色で、caesuraが最後の一出現を除いた集合であり、
最後より前の位置であることを点検してからLeanへ入る。
既存の `Surjection.Word.lastOccurrence` の値と最大性を使う。

```lean
caesura_iff_lt_lastOccurrence {n l : ℕ} (u : Surjection.Word n l)
    (c : Fin n) (i : Fin l) (hi : u.val i = c) :
  Surjection.Caesura u.val i ↔ i < u.lastOccurrence c
caesura_filter_occurrences {n l : ℕ} (u : Surjection.Word n l) (c : Fin n) :
  (Surjection.occurrences u.val c).filter (Surjection.Caesura u.val) =
    (Surjection.occurrences u.val c).erase (u.lastOccurrence c)
sum_caesura_occurrences_add_one {n l : ℕ} (u : Surjection.Word n l) (c : Fin n) :
  (∑ i ∈ Surjection.occurrences u.val c, if Surjection.Caesura u.val i then 1 else 0) + 1 =
    (Surjection.occurrences u.val c).card
```

### 119.15 出力次数と区間の符号次数（C96・C97）

m=0〜4、q=0〜4の全切断区間長、色数1〜3の全射語の各色で、
「出力次数＝同じ色の区間の符号次数の和」を点検してからLeanへ入る。
C96は同じ列の色のfiberを水平座標のfiberに分ける濃度式で、全射性は不要。

```lean
colorPositions_card_by_intervals {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (c : Fin r) :
  (colorPositions s v c).card =
    ∑ i ∈ Surjection.occurrences v c, (intervalPositions s i).card
outputDegree_eq_sum_intervalLength {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) :
  outputDegree s v c = ∑ i ∈ Surjection.occurrences v.val c, intervalLength s v.val i
```

出力の境界のKoszul指数と `permutationExponent` を同じ区間の重みで計算するための有限の濃度評価。

### 119.16 既存の逆転数の削除公式と境界符号（C98・C99）

位置数1〜5、色数1〜3の全ての語・非空位置部分集合・その中の削除位置で、
次の整数指数の式を点検してからLeanへ入る。
既存の `IntervalCuts.positionInversionCount_erase` に各位置の寄与の恒等式を足す。

```lean
colorSorting_boundary_term {N r : ℕ} (v : Fin N → Fin r) (a b : Fin N) :
  positionInversionTerm v a b + positionInversionTerm v b a +
    (if v b < v a then 1 else 0) + (if b < a ∧ v b = v a then 1 else 0) =
  (if b < a then 1 else 0) + 2 * positionInversionTerm v a b
positionInversionCount_boundary {N r : ℕ} (v : Fin N → Fin r)
    (s : Finset (Fin N)) (a : Fin N) (ha : a ∈ s) :
  positionInversionCount v s + (s.filter (fun b => v b < v a)).card +
    (s.filter (fun b => b < a ∧ v b = v a)).card =
  positionInversionCount v (s.erase a) + (s.filter (fun b => b < a)).card +
    2 * (∑ b ∈ s, positionInversionTerm v a b)
colorSorting_boundary_sign {N r : ℕ} (v : Fin N → Fin r)
    (s : Finset (Fin N)) (a : Fin N) (ha : a ∈ s) :
  (-1 : ℤ) ^ (positionInversionCount v s + (s.filter (fun b => v b < v a)).card +
    (s.filter (fun b => b < a ∧ v b = v a)).card) =
  (-1 : ℤ) ^ positionInversionCount v (s.erase a) *
    (-1 : ℤ) ^ (s.filter (fun b => b < a)).card
```

これは有限逆転集合の数え上げと既存の係数の冪の法則に限り、作用やoperadの新しい法則ではない。

### 119.17 検証済みの区切りと3,000行の途中報告

次の15本、計 **902行**を対象ビルドと専用監査で検証した。
名前の接頭部は全て `SerrePositivity.EInfinity.SimplexCuts.`。
`BoundaryEndpointPartition`・`HorizontalBoundaryEquiv`・`BoundaryKindExchange`・
`VerticalBoundaryEquiv`・`BoundaryFaceTransfers`・`UniversalBoundaryPartner`・
`BoundaryPartnerFixedPoints`・`BoundaryFixedTerms`・`BoundaryPartnerValues`・
`BoundaryCancellationReduction`・`UniversalBoundaryValues`・`StraightTraceFaces`・
`IntervalCardinalities`・`ColorCaesuraCounts`・`ColorIntervalDegrees`。
次の登録候補一覧はこの15本。

専用監査 `/tmp/bsw16/audit-m14-universal-boundary.lean` は
**15モジュール・157宣言・標準三公理のみ**。
対象ビルドは `m14-boundary-fixed-terms-01.log`・`m14-boundary-counts-01.log`・
`m14-color-interval-degrees-02.log` などに成功を確認。新規15本にsorry・追加公理0、Leanの警告なし。
全てのビルド・監査で `--wait 3600` の整理券を一枚ずつ使い、終了時に返した。
mainへの取り込み・rootビルド・大きな監査は行っていない。

L09a・L09の累計 **3,255行**、改訂MayのM14全体 **8,321行**。
3,000行を越えた途中報告は停止せずチャットでも行った。次は4,000行で報告する。
個々の補題はいずれも200行以下であり、200行を超える補題の追加はない。

全境界の添字の対合候補と、実際の境界項の固定点での零は閉じた。
水平・垂直の指定列の内部の照合、出力次数と区間の重みの同一視も閉じた。
一方、三群の符号付き値の相殺 `hc`・`hv`・`hmix` は未完。
`universalBoundaryPartner_neg_of_cases` はそれらを明示的な前提に取る貼り合わせの補題であり、
最終のL09aやBFの作用の法則を閉じたとは扱わない。§119.16の有限符号計算へ続ける。

### 119.18 展開した色列のcaesuraと区間の重み（C100・C101）

m=0〜4、q=0〜4、色数1〜3の全ての語と切断で、展開した色列の後続の同色が
「同じ区間の後続頂点、または元の語の後続の同色」の条件と一致することを点検した。
各区間のそのような頂点数が `intervalLength` と一致することも点検してからLeanへ入る。
元の語の全射性・隣接非退化性はこの二式には不要。

```lean
caesura_label_iff {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) (j : Fin (m + q + 1)) (hj : s.horizontal j = i) :
  Surjection.Caesura (label s v) j ↔
    j < (intervalPositions s i).max' (intervalPositions_nonempty s i) ∨ Surjection.Caesura v i
interval_active_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) :
  ((intervalPositions s i).filter (Surjection.Caesura (label s v))).card = intervalLength s v i
```

`Surjection.Word` は全射性だけでなく隣接非退化性も含む。展開色列には垂直辺で隣接反復が
あるため、それをWordへ包んで既存のlastOccurrenceのAPIを流用することはしない。
同じ色の後続を持つ位置の有限集合として直接扱う。

### 119.19 展開色列の活動頂点の濃度（C102〜C105）

§119.18の全頂点の点検と、m=0〜4、q=0〜4の全切断・色数1〜3の全射語の各色で、
活動頂点数が出力次数に一致し、全活動頂点数が全出力次数になることを点検してから実装。
`activeVertexPositions` は展開色列のcaesuraを選ぶ同じ有限集合の記法。

```lean
activeVertexPositions {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r) :
  Finset (Fin (m + q + 1))
active_fiber_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) :
  ((activeVertexPositions s v).filter (fun j => s.horizontal j = i)).card = intervalLength s v i
active_color_card_eq_sum {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (c : Fin r) :
  ((activeVertexPositions s v).filter (fun j => label s v j = c)).card =
    ∑ i ∈ Surjection.occurrences v c, intervalLength s v i
active_color_card {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) (c : Fin r) :
  ((activeVertexPositions s v.val).filter (fun j => label s v.val j = c)).card = outputDegree s v c
activeVertexPositions_card {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) :
  (activeVertexPositions s v.val).card = m + q + 1 - r
```

### 119.20 単調なfiberでまとめた逆転数（C106・C107）

位置数・中間の位置数1〜4、色数1〜3の全ての弱単調写像・色付け・位置部分集合で、
逆転数がfiberの濃度の積による重み付き逆転数になることを点検してからLeanへ入る。
途中の写像の全射性や色付けの非退化性は要求しない。

```lean
inversion_condition_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (x y : Fin N) :
  (x < y ∧ v (f y) < v (f x)) ↔ (f x < f y ∧ v (f y) < v (f x))
positionInversionTerm_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (x y : Fin N) :
  positionInversionTerm (v ∘ f) x y = if f x < f y ∧ v (f y) < v (f x) then 1 else 0
positionInversionCount_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (s : Finset (Fin N)) :
  positionInversionCount (v ∘ f) s =
    ∑ i : Fin M, ∑ j : Fin M, if i < j ∧ v j < v i then
      (s.filter (fun x => f x = i)).card * (s.filter (fun y => f y = j)).card else 0
permutationExponent_eq_active_inversions {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) :
  permutationExponent s v = positionInversionCount (label s v) (activeVertexPositions s v)
```

有限和のfiber分割の法則を二回使い、C102の活動頂点の濃度で `intervalLength` に戻す。

### 119.21 実際の出力境界符号を活動頂点で読む型（C108〜C111）

m=0〜4、q=0〜3、色数1〜3の全射・隣接非退化の語と全経路の各頂点で、
先行同色数と小さい色の出力次数が活動頂点の数に一致することを点検。
活動頂点を削除するとき、元のBF境界指数と次のC111の指数の偶奇が一致することを
点検してからLeanへ入る。C110・C111は既存の `outputBoundarySign` を同じ添字で評価する法則。

```lean
vertexRank_eq_active_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) :
  vertexRank s v (label s v k) k =
    ((activeVertexPositions s v).filter (fun j => j < k ∧ label s v j = label s v k)).card
prefixOutputDegree_eq_active_card {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) :
  (∑ b ∈ Finset.univ.filter (fun b : Fin r => b < c), outputDegree s v b) =
    ((activeVertexPositions s v.val).filter (fun j => label s v.val j < c)).card
outputBoundarySignAt {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (k : Fin (m + q + 1)) : ℤ
outputBoundarySignAt_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
  outputBoundarySignAt s v k = cutSign s v.val * (-1 : ℤ) ^
    (((activeVertexPositions s v.val).filter (fun j => label s v.val j < label s v.val k)).card +
    ((activeVertexPositions s v.val).filter (fun j => j < k ∧ label s v.val j = label s v.val k)).card)
outputBoundarySignAt_of_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∈ activeVertexPositions s v.val) :
  outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
    (-1 : ℤ) ^ positionInversionCount (label s v.val) ((activeVertexPositions s v.val).erase k) *
    (-1 : ℤ) ^ ((activeVertexPositions s v.val).filter (fun j => j < k)).card
```

### 119.22 活動頂点の境界符号までの検証済み区切り

次の五本、計 **379行**を検証した。
`ColorSortingBoundarySigns` 57行、`ExpandedCaesuras` 76行、`ActiveVertexCounts` 78行、
`WeightedVertexInversions` 82行、`ActiveBoundarySigns` 86行。
接頭部は全て `SerrePositivity.EInfinity.SimplexCuts.`。次の登録候補一覧はこの五本。

対象ビルド `lake build SerrePositivity.EInfinity.SimplexCuts.ActiveBoundarySigns` 成功
（`/tmp/bsw16/m14-active-boundary-signs-01.log`）。
専用監査 `/tmp/bsw16/audit-m14-active-boundary-signs.lean` は
**5モジュール・52宣言・標準三公理のみ**。新規五本にsorry・追加公理0、Leanの警告なし。
鍵の待ちは一枚の整理券にまとめ、監査が終わって鍵を返した。

事前点検は、色順の境界符号25,710個の指定色付き部分集合、展開caesura347,822頂点、
活動頂点の濃度26,881個の切断と色付け、単調なfiberの重み付き逆転数89,836例、
実際のBF出力符号14,096活動頂点で一致した。
Leanでは、既存の逆転数の削除公式、有限和のfiber分割、同じ面番号の先行同色数を使った。
個々の補題は全て200行以下。既存の公開宣言・界面・BE作用・operadの法則は変更していない。

L09a・L09の累計 **3,634行**、改訂MayのM14全体 **8,700行**。
この再開後は20本・1,281行を検証済みとして保存した。
3,000行の途中報告は済み、次は4,000行で停止せず報告する。
半分の12,500行・外枠25,000行には未到達。

ここまでで全添字の対合、固定点の実際の零、水平・垂直の有限同値、内部の指定面の列、
活動頂点における実際の出力境界符号の共通化が閉じた。
L09a全体の `hc`・`hv`・`hmix` の符号付き値の相殺はまだ未証明。
次は、最後の非活動頂点の符号を直前同色の活動頂点へ運ぶ法則と、対応する残りの逆転集合の照合。
その準備として、位置数1〜6・色数1〜3の全ての色列で、直前同色位置を持つ3,534位置の
先行同色数が一だけ違い、その交代符号が反対になることを有限点検した。
この準備の点検だけを、未実装の照合や最終相殺の証明として扱わない。
mainの凍結を維持し、root・全体監査やM15・G12の作業は行っていない。

## 120. 次の約4,600行で残りの見込みを再評価する（11-14）

調整役の最新指示に従い、L09a・L09が約4,600行になった報告で、
L09a・L09の残りとM14全体の完成の見込みを、外枠25,000行と照合して出し直す。
その見積もりのために停止せず、現在の符号の三群を閉じる作業を続ける。

### 120.1 直前の同色の頂点（C112〜C115）

`/tmp/bsw16/check-previous-vertices.py` で位置数1〜6・色数1〜3の全色列のうち、
直前同色を持つ3,534位置の集合の削除・先行数の差一・直前位置の活動性を確認した。
前後に同色を持たない1,006位置ではその色のfiberが一頂点であることも確認。
以下は既存の `Surjection.previousOccurrences` の最大とその性質の評価。

```lean
previousVertex {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) : Fin N
previousVertex_mem {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) :
  previousVertex v k h ∈ Surjection.previousOccurrences v k
previousVertex_lt {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) : previousVertex v k h < k
previousVertex_value {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) : v (previousVertex v k h) = v k
previousOccurrences_erase_previousVertex {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) :
  (Surjection.previousOccurrences v k).erase (previousVertex v k h) =
    Surjection.previousOccurrences v (previousVertex v k h)
previousOccurrences_card_previousVertex {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) :
  (Surjection.previousOccurrences v (previousVertex v k h)).card + 1 =
    (Surjection.previousOccurrences v k).card
previousVertex_active {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) (h : (Surjection.previousOccurrences (label s v) k).Nonempty) :
  previousVertex (label s v) k h ∈ activeVertexPositions s v
vertexRank_eq_previousOccurrences_card {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) :
  vertexRank s v (label s v k) k = (Surjection.previousOccurrences (label s v) k).card
vertexRank_previousVertex {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) (h : (Surjection.previousOccurrences (label s v) k).Nonempty) :
  vertexRank s v (label s v k) k =
    vertexRank s v (label s v (previousVertex (label s v) k h))
      (previousVertex (label s v) k h) + 1
```

### 120.2 直前同色の面への符号の移送（C116・C117）

元の語が全射・隣接非退化の場合、m=0〜4、q=0〜3、色数1〜3の全経路の
直前同色を持つ位置で、実際のBF境界指数が一つ違って交代符号が反対になることを
点検してから実装。`outputBoundarySignAt` の既存の係数の冪の法則とC115で証明する。

```lean
outputBoundarySignAt_rank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
  outputBoundarySignAt s v k = cutSign s v.val * (-1 : ℤ) ^
    ((∑ c ∈ Finset.univ.filter (fun c : Fin r => c < label s v.val k), outputDegree s v c) +
    vertexRank s v.val (label s v.val k) k)
outputBoundarySignAt_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (h : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  outputBoundarySignAt s v k = -outputBoundarySignAt s v (previousVertex (label s v.val) k h)
outputBoundarySignAt_via_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (h : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  outputBoundarySignAt s v k = -
    ((-1 : ℤ) ^ positionExponent s v.val *
      (-1 : ℤ) ^ positionInversionCount (label s v.val)
        ((activeVertexPositions s v.val).erase (previousVertex (label s v.val) k h)) *
      (-1 : ℤ) ^ ((activeVertexPositions s v.val).filter
        (fun j => j < previousVertex (label s v.val) k h)).card)
```

C117は、k自身が非活動でも直前の同色位置が活動的であるC114と、検証済みのC111の合成。

### 120.3 直前同色を持たない非活動頂点（C118〜C120）

§120.1の1,006個の単独色の位置の点検を使う。前後に同色を持たないなら色のfiberは一頂点、
したがって正の出力次数を持つ非活動頂点には直前同色が必ず存在する。

```lean
colorPositions_singleton_of_inactive_no_previous {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1))
    (hk : k ∉ activeVertexPositions s v)
    (hp : ¬(Surjection.previousOccurrences (label s v) k).Nonempty) :
  colorPositions s v (label s v k) = {k}
outputDegree_zero_of_inactive_no_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∉ activeVertexPositions s v.val)
    (hp : ¬(Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  outputDegree s v (label s v.val k) = 0
previousOccurrences_nonempty_of_inactive_degree_pos {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∉ activeVertexPositions s v.val) (hd : 0 < outputDegree s v (label s v.val k)) :
  (Surjection.previousOccurrences (label s v.val) k).Nonempty
```

### 120.4 既存の一般の単語削除のcaesura公式の再利用（C121〜C124）

位置数1〜6・色数1〜3の全色列・全削除位置で、活動頂点の削除ではその位置だけを、
最後の非活動頂点の削除では直前同色の活動性だけを失うことを点検した。
既存の `IntervalCuts.GeneralDeletionCaesuras.caesura_erase_of_caesura` と
`caesura_erase_final` を使い、同じ集合を像で移す。逆転数の移送は既存の
`positionInversionCount_image` の法則である。

```lean
caesuraPositions {N r : ℕ} (v : Fin N → Fin r) : Finset (Fin N)
caesuraPositions_erase_active_image {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : Surjection.Caesura v k) :
  (caesuraPositions (Surjection.erase v k)).image k.succAbove = (caesuraPositions v).erase k
caesuraPositions_erase_final_image {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : ¬ Surjection.Caesura v k)
    (hp : (Surjection.previousOccurrences v k).Nonempty) :
  (caesuraPositions (Surjection.erase v k)).image k.succAbove =
    (caesuraPositions v).erase (previousVertex v k hp)
inversionCount_erase_active {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : Surjection.Caesura v k) :
  positionInversionCount (Surjection.erase v k) (caesuraPositions (Surjection.erase v k)) =
    positionInversionCount v ((caesuraPositions v).erase k)
inversionCount_erase_final {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : ¬ Surjection.Caesura v k)
    (hp : (Surjection.previousOccurrences v k).Nonempty) :
  positionInversionCount (Surjection.erase v k) (caesuraPositions (Surjection.erase v k)) =
    positionInversionCount v ((caesuraPositions v).erase (previousVertex v k hp))
```

活動集合の移送を新しく仮定せず、既存の任意の色列での削除公式を使う証明分割。

### 120.5 同じ削除色列へ移した実際のBF境界符号（C125〜C127）

m=0〜4、q=0〜3、色数1〜3の全射・隣接非退化の語の全経路の正出力次数の面で、
実際の境界符号が「位置符号・削除色列の逆転符号・展開色列の単語削除係数」の積に
一致することを点検してから実装。既存の `Surjection.deletionCoefficient` の二分岐と、
C111・C117・C123・C124をそのまま同じ削除色列で貼り合わせる。

```lean
erasedColorSign {N r : ℕ} (v : Fin (N + 1) → Fin r) (k : Fin (N + 1)) : ℤ
caesuraRank_label_eq_active_rank {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) :
  Surjection.caesuraRank (label s v) k =
    ((activeVertexPositions s v).filter (fun j => j < k)).card
outputBoundarySignAt_erase_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : Surjection.Caesura (label s v.val) k) :
  outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
    erasedColorSign (label s v.val) k * Surjection.deletionCoefficient (label s v.val) k
outputBoundarySignAt_erase_final {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : ¬ Surjection.Caesura (label s v.val) k)
    (hp : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
    erasedColorSign (label s v.val) k * Surjection.deletionCoefficient (label s v.val) k
outputBoundarySignAt_erase {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < outputDegree s v (label s v.val k)) :
  outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
    erasedColorSign (label s v.val) k * Surjection.deletionCoefficient (label s v.val) k
```

零次数では `outputBoundarySignAt` 自体は±1でも、既存の実際の境界項は零である。
その場合まで誤って符号そのものを削除係数0と同一視する型にはしない。

### 120.6 混合角の座標と区間端点の評価（C128〜C132）

m=0〜5、q=0〜4の全経路の水平辺・垂直辺・水平から垂直への混合角で、
水平辺直前の区間の最後、垂直辺の前後の同色、角交換の一頂点の座標を点検してから実装。
既存の `step_of_mem`・`step_of_notMem`・`horizontal_swapSteps`・`vertical_swapSteps` を合成する。

```lean
interval_max_before_horizontal {m q : ℕ} (s : Cut m q) (a : Fin (m + q))
    (ha : a ∈ s.val) :
  (intervalPositions s (s.horizontal a.castSucc)).max'
    (intervalPositions_nonempty s (s.horizontal a.castSucc)) = a.castSucc
before_horizontal_active_iff {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a : Fin (m + q)) (ha : a ∈ s.val) :
  a.castSucc ∈ activeVertexPositions s v ↔ Surjection.Caesura v (s.horizontal a.castSucc)
before_vertical_active {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a : Fin (m + q)) (ha : a ∉ s.val) : a.castSucc ∈ activeVertexPositions s v
previousVertex_after_vertical {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a : Fin (m + q)) (ha : a ∉ s.val)
    (hp : (Surjection.previousOccurrences (label s v) a.succ).Nonempty) :
  previousVertex (label s v) a.succ hp = a.castSucc
swapSteps_hv_coordinates {m q : ℕ} (s : Cut m q) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  (s.swapSteps a b).horizontal b.castSucc = s.horizontal a.castSucc ∧
    ((s.swapSteps a b).vertical b.castSucc).val = (s.vertical b.castSucc).val + 1
```

### 120.7 削除後の同じ番号の順位と隣接順位（C133〜C135）

位置数1〜6、色数1〜3の全色列について、活動頂点を削除した同じ番号の順位と
隣接二位置の順位の差を点検してから実装する。
C133は既存の `caesura_erase_of_caesura` と同値な接頭集合の濃度、
C135は既存の `prefix_count_succ` の同じcaesura集合での評価。

```lean
caesuraRank_erase_active_at {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : Surjection.Caesura v a) (t : Fin N) (ht : t.val = a.val) :
  Surjection.caesuraRank (Surjection.erase v a) t = Surjection.caesuraRank v a
deletionCoefficient_erase_active_rank {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : Surjection.Caesura v a) (t : Fin N) (ht : t.val = a.val) :
  Surjection.deletionCoefficient v a = (-1 : ℤ) ^ Surjection.caesuraRank (Surjection.erase v a) t
caesuraRank_eq_filter_card {N r : ℕ} (v : Fin N → Fin r) (k : Fin N) :
  Surjection.caesuraRank v k = ((caesuraPositions v).filter (fun j => j < k)).card
caesuraRank_adjacent {N r : ℕ} (v : Fin N → Fin r) (a b : Fin N)
    (hab : b.val = a.val + 1) :
  Surjection.caesuraRank v b =
    Surjection.caesuraRank v a + if Surjection.Caesura v a then 1 else 0
```

### 120.8 混合角による右端と位置指数の増分（C136〜C139）

m=1〜4、q=1〜3の全経路の水平・垂直の角で、右端が直前の区間だけ一つ進むこと、
色数1〜3の全ての語で位置指数がその区間のcaesuraだけ一つ増えることを点検してから実装。
右端の評価C128と、最大位置の非一致、既存の有限和の一位置更新の法則を使う。

```lean
interval_max_ne_before_vertical {m q : ℕ} (s : Cut m q) (b : Fin (m + q))
    (hb : b ∉ s.val) (i : Fin (m + 1)) :
  (intervalPositions s i).max' (intervalPositions_nonempty s i) ≠ b.castSucc
hi_swapSteps_hv_of_ne {m q : ℕ} (s : Cut m q) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val)
    (i : Fin (m + 1)) (hi : i ≠ s.horizontal a.castSucc) :
  SimplexCuts.hi (s.swapSteps a b) i = SimplexCuts.hi s i
hi_swapSteps_hv_at {m q : ℕ} (s : Cut m q) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  hi (s.swapSteps a b) (s.horizontal a.castSucc) = hi s (s.horizontal a.castSucc) + 1
positionExponent_swapSteps_hv {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  positionExponent (s.swapSteps a b) v = positionExponent s v +
    if Surjection.Caesura v (s.horizontal a.castSucc) then 1 else 0
```

### 120.9 同じ削除色列と隣接同色の係数（C140〜C143）

位置数2〜6、色数1〜3の全色列で、隣接同色のどちらを削除しても同じ色列になり、
削除係数は反対になることを点検してから実装する。
C142・C143は、既存の混合角の中間以外の座標保存と§117の削除列の点検を同じ色列で評価した法則。

```lean
erase_adjacent_equal {N r : ℕ} (v : Fin (N + 1) → Fin r) (a b : Fin (N + 1))
    (hab : b.val = a.val + 1) (hv : v a = v b) : Surjection.erase v a = Surjection.erase v b
deletionCoefficient_adjacent_equal {N r : ℕ} (v : Fin N → Fin r) (a b : Fin N)
    (hab : b.val = a.val + 1) (hv : v a = v b) :
  Surjection.deletionCoefficient v b = -Surjection.deletionCoefficient v a
erase_label_swapSteps {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) :
  Surjection.erase (label (s.swapSteps a b) v) b.castSucc = Surjection.erase (label s v) b.castSucc
erasedColorSign_swapSteps {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) :
  erasedColorSign (label (s.swapSteps a b) v) b.castSucc = erasedColorSign (label s v) b.castSucc
```

### 120.10 混合角の削除係数と位置指数を合わせた符号（C144）

m=1〜4、q=1〜3、色数1〜3の全語で28,398例を点検した。
C134・C135・C139〜C142を、同じ削除色列の二つの隣接順位で評価する法則。
新しい作用やホモトピーは作らない。

```lean
signedDeletionCoefficient_swapSteps_hv {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  (-1 : ℤ) ^ positionExponent (s.swapSteps a b) v *
      Surjection.deletionCoefficient (label (s.swapSteps a b) v) b.castSucc =
    -((-1 : ℤ) ^ positionExponent s v *
      Surjection.deletionCoefficient (label s v) b.castSucc)
```

§31の追記を受領。約4,600行の区切りにはL10〜L28の各行について、
`convolutionAlgebra`、`restrictCoalgebra`、χ・TRの既存の法則で再利用できる部分と、
一般単体の切断でなお証明する部分を分け、M14全体の残りを数え直す。

### 120.11 実際の出力境界符号への適用（C145〜C148）

既存の活動頂点の色ごとの濃度と直前同色位置から、両側の出力次数が正であることを確認する。
C147は共通の削除色列の逆転符号をくくってC144を適用し、C148は同じ角交換の自己逆性を使う。
数値符号の有限点検は§120.10に含む。実テンソルの一致はまだ主張しない。

```lean
outputDegree_pos_of_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∈ activeVertexPositions s v.val) : 0 < outputDegree s v (label s v.val k)
outputDegree_pos_of_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hp : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
  0 < outputDegree s v (label s v.val k)
outputBoundarySignAt_swapSteps_hv {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
  outputBoundarySignAt (s.swapSteps a b) v b.castSucc = -outputBoundarySignAt s v b.castSucc
outputBoundarySignAt_swapSteps_vh {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∈ s.val) :
  outputBoundarySignAt (s.swapSteps a b) v b.castSucc = -outputBoundarySignAt s v b.castSucc
```

### 120.12 同じ削除列による実テンソルの更新次数（C149〜C152）

既存のC27のリストの一致の長さを取り、各色の出力次数を更新した族まで一致させる。
これはテンソルの依存した型を合わせるための既存構成の評価で、新しい次数模型は導入しない。
リストの削除と角交換の有限点検は§117と§120.10のものを引き継ぐ。

```lean
verticesList_length {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) :
  (verticesList s v.val c).length = outputDegree s v c + 1
deletedVerticesList_length {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) (c : Fin r) :
  (deletedVerticesList s v.val k c).length =
    outputDegree s v c + 1 - if label s v.val k = c then 1 else 0
deletedVerticesList_length_update {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : 0 < outputDegree s v (label s v.val k)) (c : Fin r) :
  (deletedVerticesList s v.val k c).length =
    Function.update (outputDegree s v) (label s v.val k)
      (outputDegree s v (label s v.val k) - 1) c + 1
deletedOutputDegree_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc)) :
  Function.update (outputDegree (s.swapSteps a b) v)
      (label (s.swapSteps a b) v.val b.castSucc)
      (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) - 1) =
    Function.update (outputDegree s v) (label s v.val b.castSucc)
      (outputDegree s v (label s v.val b.castSucc) - 1)
```

### 120.13 実際の標準面を削除列で読む（既存C40・C154）

既存C40の`simplexVertexList_boundaryFace`とC36を再利用し、C26の指定削除列と同定する。
個別ビルド後の合同監査でC153が既存C40と重複していることが分かり、
重複宣言を除いて`BoundaryVertexLists`のimportへ置き換えた。
式は単体圏の実際の射の頂点列であり、ホモトピー圏へ弱めない。

```lean
simplexVertexList_deletedFace {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < outputDegree s v (label s v.val k))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) :
  simplexVertexList (boundaryFace _ hd j ≫ face s v (label s v.val k)) =
    deletedVerticesList s v.val k (label s v.val k)
```

## 121. 約4,600行の区切り：L09a・L09とM14全体の再見積もり（11-14、§31）

### 121.1 実測と完成範囲

一覧：済み 8／全体 48（うち追加 4）

基準はL01〜L44にL09a・L12a・L43a・L43bを加えた48項目。
済みはL01〜L08。C/R等の既存構成の法則・証明の分割とI01の既存作用の照合は、
共通規則に従い数学の新しい項目として数えない。

§119.22の3,634行から、今回の14モジュール934行を加え、
**L09a・L09の実測4,568行、改訂MayのM14全体9,634行**。
Leanファイルの空行・docstring込みで数え、報告書・監査用ファイルは含めない。
§110の旧coherent経路10,216行は保持するが、今回の改訂Mayの外枠へ重複計上しない。

今回、混合角の交換について、同じ削除色列・その逆転符号・位置指数の差・
単語削除係数を結び、**実際の出力境界符号が反対になることを両向きに証明した**。
削除した色別リストから、実テンソルの更新次数の族も一致した。
指定境界面を削除列で読むC154も検証した。
これらは元の圏・実際の整数係数の等式であり、ホモトピー圏へ弱めていない。

まだL09a全体・L09は閉じていない。とくに、混合角の**実テンソル値**の一致を、
今回の更新次数と指定面から接続するところは残る。
水平・垂直の有限添字の対合は構成済みだが、それぞれの符号と実際の値の照合は残る。

### 121.2 L09a・L09の残り

以下は既存の型一覧L09a・L09の証明の残りで、新しい数学の追加ではない。
実測4,568行からの**追加**を数える。

| 行 | 残りの内容・使える完成分 | 追加見込み |
| --- | --- | ---: |
| 混合角 | C27の削除列、C147・C148の実符号、C152の更新次数、C154の指定面から、依存した次数移送込みの`deletedCutTensor`を一致させる。逆向きと分類の包装も含む | 180〜300 |
| 水平境界と係数微分 | 水平の全添字同値・内点/両端の経路は既存。元の語の削除と展開語の削除の順位・位置指数の比較、無効な削除語と退化面の零、実テンソルの移送が残る | 600〜1,100 |
| 垂直境界と入力面 | 垂直の全添字同値・削除後の座標列は既存。入力面の交代符号と位置指数の差、端点、正規化生成元と実テンソルの移送が残る | 500〜950 |
| L09aの包装・L09 | 構成済みの対合・固定点零・三分岐の合成に実際の値の等式を渡す。有限和の相殺をテンソル微分・語の微分・入力面の和へ戻す | 200〜350 |
| **残り合計** | | **1,480〜2,700** |
| **L09a・L09完成時** | 現在の4,568を加算 | **6,048〜7,268** |

符号の一般的な正規形は今回までに得たので、三分岐ごとに重み付き逆転数を最初から
展開し直す見積もりにはしていない。ただし、実テンソルの依存した型と正規化の零の
処理は未完であり、リストの等式だけで完成と数えない。

### 121.3 L10〜L28：次元によらない既存部分の再利用の確認

ローカルの宣言の引数・結論を読んで、次の境界を確認した。

1. `Surjection.operad`（`Surjection/OperadStructure.lean`）はχの単位・置換・部分合成の
   全法則を持つ。`TableReduction.operadMap`と`operadMap_app`（`TableReduction/OperadMap.lean`）は
   全arityの**実際の**dg operad射と指定TR成分である。χ/TRのoperad則を再証明しない。
2. `Operad.restrictCoalgebraObj`・`restrictCoalgebraMap`・`restrictCoalgebra`
   （`Operad/CoalgebraRestriction.lean`）は任意の複体の余代数に使える。
   一般単体のχ余作用の法則が揃った後、TRによるBE余作用の公理はそのまま引き戻せる。
   ただし、χ自身がoperadであることだけから単体鎖のχ余代数構造は出ない。
3. `Operad.convolutionAlgebra`、`convolutionAction_comp`、`convolutionAction_equivariance`、
   `convolutionAction_unit`は非有界の一般複体・全arityで使える。
   `convolutionPre`・`convolutionPost`・`convolutionPreNat`、
   `convolutionAction_pre`・`convolutionAction_post`も同様。
   正規化コチェインのBE**代数**の公理を切断公式からもう一周証明する必要はない。
   一方、入力となる単体鎖のBE**余代数**と、指定された正規化評価の同定は先に要る。
4. `IntervalCuts.coactionComposition_apply`は`P Q K W X : Complex A`を任意に取り、
   二係数を交換するKoszul符号をそのまま再利用できる。
   `compositeWord_at_non_slot`・`compositeOuterPosition_value`・
   `compositeBasisWord_outerPosition`も単語・OverlapPartitionだけの主張である。
   `GeneralDeletionCaesuras`の削除則、一般の位置逆転数の埋込みの法則は既にL09aで使用している。
5. `IntervalCuts.cochainAction`は`interval A`、
   `cochainAction_comp`・`cochainAction_operad_comp`も`interval A`に固定される。
   `NestedEdgeCut.compositionCoefficient`は`edgeSign`と辺の二段切断、
   `VertexCompositionSigns`は頂点/辺の有限出力族に固定される。
   これらを一般qの定理として直接適用することはできない。
   一般単体のL12aで必要な二段切断の全対応・一般の位置指数の貼り合わせは残る。
   `CutSigns.edgeIntervalLength`もpivot一つの区間用で、一般qの`intervalLength`と同一視しない。

したがって短縮できるのは「χ/TR・convolutionの公理」「任意の複体の係数交換」
「単語代入の接頭部分の評価」であり、一般qの作用則を区間の完成定理だけから出す経路は採らない。
IntervalCutsとの一致I01は指定された同じ作用の照合として残す（下のL28に計上）。

### 121.4 L10〜L28の行ごとの残りの新規見込み

既存宣言は直さず、一般単体に適用する証明・包装・指定比較の行数だけを数える。
L12aの有限対応はL12に重複計上しない。すべて未完成で、以下の数字は実測ではない。

| 行 | 再利用する部分と、新規に残る部分 | 新規見込み |
| --- | --- | ---: |
| L10 | L09と基底/正規化生成元の展開から全整数Leibnizへ。`cochainActionComponent_d`と同じ`TensorProduct.ext`・`tensorLift`の方法。区間のLeibniz定理そのものは流用しない | 130〜230 |
| L11 | 既存の`permutationAction`・Koszulテンソルの置換評価と色別リストを使う。一般qの切断符号の置換と実テンソルの一致は新規 | 250〜450 |
| L12a | 既存OverlapPartition・単語代入の位置/値・`coactionComposition_apply`を使用。一般qの二段切断と一段切断の有限対応、位置符号、退化項零、全色の実テンソルの比較は新規 | 1,400〜2,400 |
| L12 | L12aの同じ添字上の有限和の相殺を`compositeCutSum = nestedCutSum`へ。χの合成係数を再構成しない | 120〜200 |
| L13 | unaryの切断の一意性と同じ生成元。既存`oneIso`を使う | 70〜130 |
| L14 | nullary係数とaugmentationを束ね、L12aの空入力分岐から実余作用へ。区間のnullary完成定理の直接適用はしない | 200〜380 |
| L15 | 既存の生成元自然性L05と線形/テンソル外延性で実複体射の自然性に延長 | 100〜180 |
| L16 | L12の有限和を`tensorCoInsertionAction`の実複体射へ。一般の結合子/交換の評価は既存を使用 | 120〜220 |
| L17 | L11・L13を複体射の等変性/単位へ線形延長。χの対称列を使う | 100〜180 |
| L18 | `restrictCoalgebraObj`・`restrictCoalgebraMap`・`TableReduction.operadMap`でBEへ制限。指定作用の式と射の可換性を包装 | 70〜130 |
| L19 | cosimplicial恒等式の交代和の相殺で正規化部分を保つ。新たなBE法則は不要 | 120〜220 |
| L20 | 同じ包含・微分・写像の制限。既存の交代余面複体の法則を使用 | 100〜180 |
| L21 | Mathlib Dold–Kanの正規化/退化分解・ホモトピーを反対圏で使用。同じ正規化包含が指定homになる接続は新規 | 250〜450 |
| L22 | `convolutionPre`・`convolutionPost`と各自然性、`Algebra.algebraLimitCone`・`algebraLimitIsLimit`で等化子を代数にする。恒等/合成を底のHomで確認 | 140〜260 |
| L23 | convolution等化子の元の恒等単体での評価と逆構成、非単射で零、全単体射の自然性。一般convolutionからは出ない | 450〜850 |
| L24 | 同じ評価の次数係数を保持した微分比較。一般Homの微分は既存だが評価符号の計算は新規 | 180〜340 |
| L25 | L23の評価と既存のpost/pre自然性で全X射に対する自然性を確認 | 80〜160 |
| L26 | L23〜L25を関手同型へ包装し、L20・L21の指定包含/擬同型を接続 | 120〜220 |
| L27 | `convolutionAction_uncurry`・評価自然性と代数の極限射影から指定射影の評価式を得る。BE代数の公理は再証明しない | 80〜160 |
| L28 | L27を実際のTR成分・単体鎖の切断公式で評価し、L26の指定同型で運ぶ。全整数次数とI01の区間との一致を含む | 250〜450 |
| **L10〜L28（L12a込み）合計** | | **4,330〜7,790** |

L21・L23・L24には「既存の同値を選べば終わる」という省略を置かない。
同じ包含・同じ評価・同じ次数係数との照合をこの見込みに含めた。
L12aの上端は区間の有限対応を一般qへ拡張する部分で、実測による不確実性が最も大きい。
一般のoperad則を再利用しても、単体鎖のχ余作用の合成則のこの入力は消えない。

### 121.5 M14全体の完成の見込みと25,000行の外枠

§110の完成見込みをそのまま据え置かず、現在の実測と各未完成行から積み直す。
G10や③-bの橋そのものを作る行数は含めないが、**受け取った指定比較への適用**は含める。

| 部分 | 現時点の実測 / 残りの新規 |
| --- | ---: |
| 完成済みMayと今回までの切断の実装 | **9,634（実測）** |
| L09a・L09の残り | 1,480〜2,700 |
| L10〜L28（L12a・I01込み） | 4,330〜7,790 |
| L29〜L37：同じMay係数・ν・top operationとFrobeniusの照合 | 1,200〜2,000 |
| L38〜L40：G10後の指定native Totと同じFrobenius辺への移送 | 500〜900 |
| L41・L42：filtered塔とA4の利用側 | 300〜550 |
| L43a・L43b・L43・L44：二重模型の実現と同じMay演算の比較 | 1,500〜2,800 |
| **残りの新規合計** | **9,310〜16,740** |
| **M14完成時の見込み** | **18,944〜26,374** |

**上端は25,000行を1,374行上回る。外枠内に必ず閉じるとは報告できない。**
下端は共通符号の正規形・一般convolution・指定Dold–Kan比較の再利用が素直に通る場合、
上端は一般qの二段切断と正規化評価の接続に余裕を取った値である。
現在の実測の余地は15,366行で、残り上端16,740行より1,374行少ない。
これは外枠変更の承認を仮定した見込みではなく、§31の外枠判断のための数値である。

以前の§110の完成上端23,240行との差は3,134行。
L09aの有限添字だけでなく、実際の境界符号・出力次数・指定面までの接続に行数が要り、
一般BFの最初の行の見込みを上方修正したためである。
χ/TR/convolutionの既存の公理を再証明しない短縮を入れても、この増分は全ては吸収できない。

§31の「止まらずに」に従い、この1,000行区切り自体では停止しない。
外枠25,000行を引き上げず、新しい数学の追加もしないまま、型一覧内の混合角の
実テンソルの照合から続ける。今後の実測が残り上端に寄る場合は外枠到達前に明示する。
12,500行の半分報告も別に行う。M15・G12、G10の部品には入らない。

### 121.6 対象ビルド・合同監査と登録候補

今回の14本はすべて対象ビルド成功。合同監査は **14モジュール・104宣言・標準三公理のみ**。
監査ログは `/tmp/bsw16/audit-m14-corner-signs-02.log`。
新規14本のsorry・追加公理0、Leanの警告0、`git diff --check`成功。
合同監査で見つかった既存C40との重複は§120.13のとおり除去し、再監査を通した。
個々の補題は200行以下。共通入口・共通監査は変更していない。mainは凍結中のまま。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：

- `AdjacentColorDeletions`（86行）
- `CaesuraVertexDeletion`（85行）
- `CornerBoundarySigns`（74行）
- `CornerDeletionSigns`（59行）
- `CornerEndpointCoordinates`（82行）
- `CornerIntervalMaxima`（52行）
- `CornerPositionExponent`（64行）
- `DeletedFaceVertexLists`（28行）
- `DeletedOutputDegrees`（65行）
- `ErasedBoundarySigns`（70行）
- `ErasedCaesuraRanks`（81行）
- `InactiveColorDegrees`（51行）
- `PreviousBoundarySigns`（49行）
- `PreviousVertexPositions`（88行）

## 122. 約4,600行の報告後：同じ指定面の厳密な移送（11-14、続行）

一覧：済み 8／全体 48（うち追加 4）

§121は **1fc84640c** に保存済み。停止せず、混合角の既存の型の照合を続ける。
`deletedCutFace`は既存`deletedCutTensor`内の色ごとの指定面を、更新次数を始域にして
書き出したもの。新しい作用・正規化・錐は構成しない。
C155・C156は既存の面の頂点列の評価、C157はC27・C152と頂点列の単射性による
元の単体圏の射の一致である。ホモトピー圏の一致で代用しない。

```lean
simplexVertexList_deletedCutFace {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (c : Fin r) :
  simplexVertexList (deletedCutFace s v a ha j c) =
    if c = a then (verticesList s v.val a).eraseIdx j.val else verticesList s v.val c
simplexVertexList_deletedCutFace_at_vertex {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < outputDegree s v (label s v.val k))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (c : Fin r) :
  simplexVertexList (deletedCutFace s v (label s v.val k) hd j c) =
    deletedVerticesList s v.val k c
deletedCutFace_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc))
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc) (c : Fin r) :
  deletedCutFace (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) hn jn c =
    eqToHom (congrArg SimplexCategory.mk
      (congrFun (deletedOutputDegree_swapSteps s v a b hab ho hn) c)) ≫
      deletedCutFace s v (label s v.val b.castSucc) ho jo c
```

### 122.1 既存生成元と純粋テンソルの次数移送（C158・C159）

同じ等式で型を移す既存構成の法則。等式の帰納法だけで証明し、
新たな作用・ホモトピー・数学の定理は追加しない。

```lean
gen_cast_source (A : Type u) [CommRing A] (S : SSet.{0}) {n n' q : ℕ} (h : n = n')
    (f : (⦋n'⦌ : SimplexCategory) ⟶ ⦋q⦌) (x : S _⦋q⦌) :
  gen A S n (S.map (eqToHom (congrArg SimplexCategory.mk h) ≫ f).op x) =
    (eqToHom (congrArg (fun t : ℤ => (chains A S).X t)
      (congrArg (fun k : ℕ => -(k : ℤ)) h.symm))).hom
      (gen A S n' (S.map f.op x))
tensorValue_congr_degree (A : Type u) [CommRing A] (K : Complex A) (n : ℕ)
    (d e : Fin n → ℕ) (h : d = e)
    (v : ∀ i, K.X (-(d i : ℤ))) (w : ∀ i, K.X (-(e i : ℤ)))
    (hv : ∀ i, (eqToHom (congrArg (fun t : ℤ => K.X t)
      (congrArg (fun k : ℕ => -(k : ℤ)) (congrFun h i)))).hom (v i) = w i) :
  (eqToHom (congrArg (fun t : ℤ => (power K n).X t)
    (congrArg (fun k : ℕ => -(k : ℤ)) (congrArg (degreeSum n) h)))).hom
    (tensorValue K n d v) = tensorValue K n e w
```

### 122.2 指定面と次数移送の検証済み区切り

一覧：済み 8／全体 48（うち追加 4）

§121の報告後も続行して、次の二本 **131行**を追加した。

- `SerrePositivity.EInfinity.SimplexCuts.DeletedCutFaces`（85行）
- `SerrePositivity.EInfinity.SimplexCuts.GeneratorDegreeTransfers`（46行）

対象ビルドは `/tmp/bsw16/m14-deleted-cut-faces-03.log` と
`/tmp/bsw16/m14-deleted-cut-faces-02.log` の各対象で成功。
合同監査 `/tmp/bsw16/audit-m14-deleted-cut-faces.log` は
**2モジュール・10宣言・標準三公理のみ**。sorry・追加公理0、Leanの警告0。
いずれの補題も200行以下、共通入口・共通監査・既存の公開宣言は変更していない。
調整役への登録候補には、この二本も加える。

L09a・L09の実測 **4,699行**、改訂MayのM14全体 **9,765行**。
§121の残り見込みの「混合角」のうち、指定面の厳密な一致と一般の次数移送を進めた。
`deletedCutTensor`内部の各因子をこの指定面の生成元へ実際に書き換え、
全体の次数移送と符号を合わせる接続はまだ残る。L09aの完了には数えない。

## 123. 混合角の実テンソルへ指定面を接続する（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンは進捗あり：`1fc84640c`・`3f38e2eec`で対象ビルド・監査済みの実装と
§121の再見積もりを保存した。作業木はクリーンで再開し、G10や新しい作用には入らない。
以下は既存構成の次数移送・係数移送の法則として型を追加する。

```lean
tensorValue_cast_target_congr (A : Type u) [CommRing A]
    (K : Complex A) (n : ℕ) (d e : Fin n → ℕ)
    (h : d = e) (v : ∀ i, K.X (-(d i : ℤ))) (w : ∀ i, K.X (-(e i : ℤ)))
    (hv : ∀ i, v i = (eqToHom (congrArg (fun t : ℤ => K.X t)
      (congrArg (fun k : ℕ => -(k : ℤ)) (congrFun h i).symm))).hom (w i))
    (z : ℤ) (hd : -(degreeSum n d : ℤ) = z) (he : -(degreeSum n e : ℤ) = z) :
  (eqToHom (congrArg (fun t : ℤ => (power K n).X t) hd)).hom (tensorValue K n d v) =
    (eqToHom (congrArg (fun t : ℤ => (power K n).X t) he)).hom (tensorValue K n e w)
deletedCutTensor_eq_faces (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (x : S _⦋q⦌)
    (h : -(degreeSum r (Function.update (outputDegree s v) a
      (outputDegree s v a - 1)) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
  deletedCutTensor A S s v a ha j x =
    (eqToHom (congrArg (fun t : ℤ => (power (chains A S) r).X t) h)).hom
      (tensorValue (chains A S) r
        (Function.update (outputDegree s v) a (outputDegree s v a - 1))
        (fun c => gen A S _ (S.map (deletedCutFace s v a ha j c).op x)))
```

### 123.1 元の削除テンソルの一致（C162・C163）

C157の指定面、C158の生成元、C160の全体の次数移送を順に適用する、
既存構成の貼り合わせの法則。単体圏の厳密な一致から始め、最後も元の加群の等式で述べる。

```lean
deletedCutTensor_eq_of_faces (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s t : Cut m q) (v : Surjection.Word r (m + 1)) (a b : Fin r)
    (ha : 0 < outputDegree s v a) (hb : 0 < outputDegree t v b)
    (ja : Fin (outputDegree s v a + 1)) (jb : Fin (outputDegree t v b + 1))
    (he : Function.update (outputDegree s v) a (outputDegree s v a - 1) =
      Function.update (outputDegree t v) b (outputDegree t v b - 1))
    (hf : ∀ c, deletedCutFace s v a ha ja c =
      eqToHom (congrArg SimplexCategory.mk (congrFun he c)) ≫ deletedCutFace t v b hb jb c)
    (x : S _⦋q⦌) :
  deletedCutTensor A S s v a ha ja x = deletedCutTensor A S t v b hb jb x
deletedCutTensor_swapSteps (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc))
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc) (x : S _⦋q⦌) :
  deletedCutTensor A S (s.swapSteps a b) v
      (label (s.swapSteps a b) v.val b.castSucc) hn jn x =
    deletedCutTensor A S s v (label s v.val b.castSucc) ho jo x
```

### 123.2 同じ符号付き境界項への適用（C164・C165）

C164は同じ有限同値の逆の面番号を評価する法則、C165は既存の実テンソルの一致と
既存の境界符号反転の貼り合わせ。新しい相殺の対合は作らない。

```lean
outputBoundarySign_eq_at_of_rank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) :
  outputBoundarySign s v (label s v.val k) j = outputBoundarySignAt s v k
outputBoundaryTerm_swapSteps_of_sign (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc))
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc)
    (hs : outputBoundarySignAt (s.swapSteps a b) v b.castSucc =
      -outputBoundarySignAt s v b.castSucc) (x : S _⦋q⦌) :
  outputBoundaryTerm A S (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) jn x =
    -outputBoundaryTerm A S s v (label s v.val b.castSucc) jo x
```

### 123.3 正次数の確認と両向きへの適用（C166・C167）

C166は直前同色位置の既存の法則、C167は水平/垂直の向きでC147・C148とC165を使い分ける
証明の分割。混合角の両側の元の出力境界項を、追加の正次数仮定なしに述べる。

```lean
outputDegree_pos_after_vertical {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin (m + q)) (ha : a ∉ s.val) :
  0 < outputDegree s v (label s v.val a.succ)
outputBoundaryTerm_swapSteps_mixed (A : Type u) [CommRing A] {m q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) (hc : a ∈ s.val ↔ b ∉ s.val)
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc) (x : S _⦋q⦌) :
  outputBoundaryTerm A S (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) jn x =
    -outputBoundaryTerm A S s v (label s v.val b.castSucc) jo x
```

### 123.4 構成済みの対合の混合角の分岐へ戻す（C168・C169）

C168は既存の添字同値に沿う値の定義の評価、C169はC167を既存のMixedVertex分類と
既存の全体の次数移送へ適用する証明の分割。
C161の証明内で使う局所的なcastの法則は
`hcast (M N : ModuleCat A) (hMN : M = N) (y : M) : HEq ((eqToHom hMN).hom y) y`。
等式の帰納法で証明し、HEqは依存した型の処理にだけ使う。出力はすべて元の加群の等式。

```lean
universalBoundaryValue_output (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (s : Cut (r + d) q) (k : Fin (r + d + q + 1))
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
  universalBoundaryValue A S w q x (.inl ⟨s, k⟩) =
    (eqToHom (congrArg (fun t : ℤ => (power (chains A S) (r + 1)).X t) h)).hom
      (outputBoundaryTerm A S s (positiveWord w) (label s (positiveWord w).val k)
        ((colorPositionEquiv s (positiveWord w)).symm k).2 x)
universalBoundaryValue_mixed_neg (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (t : BoundaryVertexOfKind (r + d) q .mixed) :
  universalBoundaryValue A S w q x (.inl (vertexCornerPerm (r + d) q t.val)) =
    -universalBoundaryValue A S w q x (.inl t.val)
```

### 123.5 混合角の分岐の完了・検証・保存

一覧：済み 8／全体 48（うち追加 4）

次の五本、**316行**が対象ビルド・合同監査を通った。
登録候補の接頭部は `SerrePositivity.EInfinity.SimplexCuts.`。

- `DeletedFaceTensors`：75行
- `CornerDeletedTensors`：66行
- `CornerBoundaryTerms`：52行
- `MixedCornerTerms`：61行
- `MixedBoundaryValues`：62行

対象ビルド `/tmp/bsw16/m14-mixed-boundary-values-04.log` は五本すべて成功、Leanの警告0。
専用監査 `/tmp/bsw16/audit-m14-mixed-boundary-values.log` は
**5モジュール・19宣言・標準三公理のみ**。新規五本のsorry・追加公理0、
個々の補題200行以下。既存公開宣言・共通入口・共通監査は変更していない。

独立の有限点検では、m=0〜4・q=0〜3・色数1〜3の全射非退化語と全混合角で
**9,536組**の実際の出力境界符号・削除後の全色の列・正規化での零を確認した。
そのうち**4,080組**は削除面の重複により正規化で零となる。
Leanではこの有限点検を仮定せず、既存の指定面の厳密一致と次数移送の法則から証明した。

`universalBoundaryValue_mixed_neg`は、L09aの三群の貼り合わせ
`universalBoundaryPartner_neg_of_cases`の**hmixを、そのまま仮定なく供給する**。
条件を弱めたり符号の仮定を追加したりしていない。
L09a全体・L09は未完了で、残るのは水平のhc・垂直のhvと有限和から微分への包装。
したがって一覧の完了件数はまだ増やさない。

L09a・L09累計 **5,015行**、改訂MayのM14全体 **10,081行**。
§121の混合角の180〜300行の見込みに対し、§122の131行と今回の316行で実測**447行**、
差は**+147〜+267行**。指定面の一致だけでは元の`deletedCutTensor`内の依存した型の
二段の移送を解消できず、因子ごとの生成元と全体の終域次数までを明示的に接続したため。
新しい数学の追加ではなく同じ構成の照合だが、この行数も外枠に含める。
混合角の残りは0行として、ほかの見込みを据え置いたM14完成見込みは
**19,211〜26,521行**。上端は外枠25,000行を1,521行上回るリスクが残る。
外枠の変更は仮定せず、水平の分岐へ続行する。

## 124. 水平・垂直の符号に共通する接頭順位（11-14、続行）

一覧：済み 8／全体 48（うち追加 4）

混合角の完了は **46bd6230f** に保存済み。
次は水平の分岐の符号を照合するため、展開した語の順位を元の語と垂直座標で読む。
m=0〜4・q=0〜3・色数1〜3の全ての語（全射性・非退化性を要求しない）で
**142,272頂点**の順位を点検してから実装した。
これはL09a内の接頭部分の有限の数え上げ。型は次のとおり。

```lean
caesuraRank_label {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) :
  Surjection.caesuraRank (label s v) k =
    (s.vertical k).val + Surjection.caesuraRank v (s.horizontal k)
```

証明は経路の頂点の帰納法で、水平辺では元の語のcaesuraだけが、垂直辺では一つが増える。
既存のC129・C130、`step_of_mem`・`step_of_notMem`と隣接順位C135を使う。
この法則を水平の単語削除係数と垂直の入力面の交代符号の双方へ使い、
重み付き逆転数の二重和の展開を各分岐で繰り返さない。

### 124.1 同じ削除集合の重み付き和（C171・C172）

既存C121・C122の集合の一致に有限和を適用する法則。
位置数1〜6・色数1〜3の全色列の活動/最後の位置について、
重みH(i)=iおよびH(i)=(i+1)²で**11,344例**を点検してから実装する。

```lean
caesura_sum_erase_active {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : Surjection.Caesura v a) (H : Fin (N + 1) → ℕ) :
  (∑ i ∈ caesuraPositions v, H i) =
    (∑ i ∈ caesuraPositions (Surjection.erase v a), H (a.succAbove i)) + H a
caesura_sum_erase_final {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : ¬Surjection.Caesura v a)
    (hp : (Surjection.previousOccurrences v a).Nonempty) (H : Fin (N + 1) → ℕ) :
  (∑ i ∈ caesuraPositions v, H i) =
    (∑ i ∈ caesuraPositions (Surjection.erase v a), H (a.succAbove i)) +
      H (previousVertex v a hp)
```

### 124.2 削除後に残る区間の右端（C173）

一般の座標対応について既存C06の達成上界の法則を適用する、L09a内の有限fiberの評価。
水平な二辺の内部の削除と両端の削除で、p=1〜5・q=0〜4の全経路の
残る区間の右端を**5,700例**点検してから実装する。
C173はその座標の対応を引数とする共通法則。水平の具体的な対応への適用は次に行う。

```lean
hi_eq_of_coordinate_cover {m n q : ℕ} (s : Cut m q) (t : Cut n q)
    (ρ : Fin (n + q + 1) → Fin (m + q + 1)) (φ : Fin (n + 1) → Fin (m + 1))
    (hφ : Function.Injective φ)
    (hh : ∀ j, s.horizontal (ρ j) = φ (t.horizontal j))
    (hv : ∀ j, s.vertical (ρ j) = t.vertical j) (i : Fin (n + 1))
    (hcover : ∀ j, s.horizontal j = φ i → ∃ k, ρ k = j) :
  hi t i = hi s (φ i)
```

### 124.3 水平の座標公式と位置指数への適用（C174〜C176）

§124.1・§124.2の有限点検の組合せに対応する法則。
C174は既存の`horizontalDeletion_horizontal`・`horizontalDeletion_vertical`をC173へ渡す。
C175・C176は同じ右端の重みについてC171・C172を評価する。
局所的な法則`positionExponent_eq_caesura_sum`は位置指数の定義を有限集合の和へ戻すだけ。

```lean
hi_horizontalDeletion {m q : ℕ} (s : Cut (m + 1) q)
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (i : Fin (m + 1)) :
  hi ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) i =
    hi s ((s.horizontal a.succ).succAbove i)
positionExponent_eq_caesura_sum {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) :
  positionExponent s v = ∑ i ∈ caesuraPositions v, hi s i
positionExponent_erase_active {m q r : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (v : Fin (m + 2) → Fin r) (a : Fin (m + 2)) (ha : Surjection.Caesura v a)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  positionExponent s v = positionExponent t (Surjection.erase v a) + hi s a
positionExponent_erase_final {m q r : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (v : Fin (m + 2) → Fin r) (a : Fin (m + 2)) (ha : ¬Surjection.Caesura v a)
    (hp : (Surjection.previousOccurrences v a).Nonempty)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  positionExponent s v = positionExponent t (Surjection.erase v a) +
    hi s (previousVertex v a hp)
```

### 124.4 活動区間の係数削除の符号（C177）

元の語の活動区間を消す場合、C170の垂直座標とC175の右端が等しく、
同じ(-1)の冪が二回現れて消える。m=1〜4・q=0〜3・色数1〜3の全色列の
内部/両端の水平削除で、活動位置を消す**27,644例**を点検してから実装する。
これはL09a内の既存の符号規則の照合で、界面・作用・operad則は変更しない。

```lean
signedDeletionCoefficient_horizontal_active {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Fin (m + 2) → Fin r)
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1)) (ha : Surjection.Caesura v a)
    (hk : s.horizontal k = a) (hy : (s.vertical k).val = hi s a)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  (-1 : ℤ) ^ positionExponent s v * Surjection.deletionCoefficient (label s v) k =
    Surjection.deletionCoefficient v a * (-1 : ℤ) ^ positionExponent t (Surjection.erase v a)
```

C177の局所的な整数積の法則の型は
`cancel (P R : ℤ) (n : ℕ) : (P * (-1 : ℤ)^n) * ((-1 : ℤ)^n * R) = R * P`。
`(-1)^n * (-1)^n = 1`と可換結合法則だけを使う。
最後の非活動区間の分岐と、実テンソル/無効な削除語の零の照合はまだ残る。

### 124.5 最後の位置の前にある同色頂点（C178）

m=1〜4・q=0〜3・色数1〜3の全ての色列について、一頂点の水平区間で元の語に
直前同色位置がある**27,644例**を点検してから実装する。
元の語と展開語の既存の`previousOccurrences`の最大を、同じ水平fiberの最大で照合する
有限の数え上げ。新しいBE作用や削除の構成は作らない。

```lean
previousVertex_label_horizontal_singleton {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin (m + 1)) (k : Fin (m + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hp : (Surjection.previousOccurrences v a).Nonempty)
    (he : (Surjection.previousOccurrences (label s v) k).Nonempty) :
  previousVertex (label s v) k he =
    (intervalPositions s (previousVertex v a hp)).max'
      (intervalPositions_nonempty s (previousVertex v a hp))
```

### 124.6 最後の非活動区間の係数削除の符号（C179）

m=1〜4・q=0〜3・色数1〜3の全ての色列の内部/両端の水平削除について、
元の語の最後の非活動位置で直前同色位置がある**18,374例**を点検してから実装する。
C178で直前同色区間の最後を指定し、C170・C176と既存の最後の削除係数の法則を適用する。
同じ右端の冪の二乗を消す局所法則`cancel`の型はC177と同じ。

```lean
signedDeletionCoefficient_horizontal_final {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Fin (m + 2) → Fin r)
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1)) (ha : ¬Surjection.Caesura v a)
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hp : (Surjection.previousOccurrences v a).Nonempty)
    (he : (Surjection.previousOccurrences (label s v) k).Nonempty)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  (-1 : ℤ) ^ positionExponent s v * Surjection.deletionCoefficient (label s v) k =
    Surjection.deletionCoefficient v a *
      (-1 : ℤ) ^ positionExponent t (Surjection.erase v a)
```

### 124.7 接頭順位と水平削除係数の検証済み区切り

一覧：済み 8／全体 48（うち追加 4）

次の七本 **366行**を対象ビルド・監査済みとして保存する。
登録候補の接頭部は `SerrePositivity.EInfinity.SimplexCuts.`。

- `ExpandedCaesuraRanks`：46行
- `CaesuraDeletionSums`：42行
- `DeletedIntervalMaxima`：38行
- `HorizontalDeletionExponents`：79行
- `HorizontalActiveDeletionSigns`：38行
- `HorizontalPreviousVertices`：62行
- `HorizontalFinalDeletionSigns`：61行

対象ビルドは`m14-expanded-caesura-ranks-02.log`、`m14-caesura-deletion-sums-01.log`、
`m14-deleted-interval-maxima-01.log`、`m14-horizontal-deletion-exponents-01.log`、
`m14-horizontal-active-deletion-signs-02.log`、`m14-horizontal-previous-vertices-01.log`、
`m14-horizontal-final-deletion-signs-03.log`（いずれも`/tmp/bsw16/`）で成功。
新規七本のLean警告0、sorry・追加公理0、`git diff --check`成功。
個々の補題は200行以下。
専用監査 `/tmp/bsw16/audit-m14-horizontal-deletion-signs.log` は
**7モジュール・23宣言・標準三公理のみ**。
鍵スクリプトの他レーンの既存ビルド検出通知は出たが、監査のLeanの警告/エラーはない。
鍵を持つ常駐プロセスは作っていない。

C170は全ての色関数で成立し、Wordの非退化性を余分に仮定していない。
C174は内部の水平削除の右端の具体的な対応、C175・C176は同じ右端を受け取る一般の位置指数の法則。
C177・C179により、活動区間・最後の非活動区間の両方で、位置指数と単語削除係数が
元の語の削除係数へ戻るところまで検証した。

**水平のhcはまだ未完了**。共通の削除色列の逆転符号を小さい切断の符号へ移すこと、
始端・終端への具体的な座標対応、実テンソルの一致、削除語が無効な場合の零が残る。
C179の元の語と展開語の先行同色の非空性は、適用時に正の出力次数から供給する必要がある。
その適用を仮定したままhcを証明したとは報告しない。垂直のhvも未完了。

L09a・L09累計 **5,381行**、改訂MayのM14全体 **10,447行**。
次の1,000行の区切りは約5,600行。12,500行の半分報告・25,000行の外枠には未到達。
次は、同じ色列の次数移送で削除後の逆転符号を比較し、活動/最後の二つの係数公式を
実際の水平境界符号へ適用する。共通入口・共通監査・界面の変更は行わない。

## 125. 水平の実際の符号へ接続する（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンは進捗あり：`46bd6230f`で混合角の実境界値の相殺、`5f9f9d382`で
水平の二種類の削除係数の照合を対象ビルド・監査後に保存した。クリーンな作業木で再開。
以下は同じ有限順序の次数移送・既存符号の照合・L09a内の有限な先行位置の分類。
C181の事前点検は§124.5の27,644例、C182は§124.4・§124.6の両分岐を使う。

```lean
caesuraInversionCount_congr_length {N M r : ℕ} (h : N = M)
    (v : Fin N → Fin r) (w : Fin M → Fin r) (he : ∀ i, v i = w (Fin.cast h i)) :
  positionInversionCount v (caesuraPositions v) = positionInversionCount w (caesuraPositions w)
erasedColorSign_eq_permutationSign {m q n q' r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) (t : Cut n q')
    (w : Fin (n + 1) → Fin r) (h : m + q = n + q' + 1)
    (he : ∀ i, Surjection.erase (label s v) k i = label t w (Fin.cast h i)) :
  erasedColorSign (label s v) k = (-1 : ℤ) ^ permutationExponent t w
previousOccurrences_of_horizontal_singleton {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin (m + 1)) (k : Fin (m + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (he : (Surjection.previousOccurrences (label s v) k).Nonempty) :
  (Surjection.previousOccurrences v a).Nonempty
signedDeletionCoefficient_horizontal {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Surjection.Word r (m + 2))
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hd : 0 < outputDegree s v (label s v.val k))
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
  (-1 : ℤ) ^ positionExponent s v.val * Surjection.deletionCoefficient (label s v.val) k =
    Surjection.deletionCoefficient v.val a *
      (-1 : ℤ) ^ positionExponent t (Surjection.erase v.val a)
```

### 125.1 同じ小さい切断の実符号へ戻す（C183・C184）

C180・C182を、元のC127の出力符号の式へ適用する既存構成の符号照合。
内部の具体的な対応には、既存の水平削除座標公式とC174を使う。
有効な削除語の実テンソル・無効な語の零はまだ主張しない。
局所的な整数積の法則は`rearrange (P E D : ℤ) : P * E * D = E * (P * D)`。

```lean
outputBoundarySignAt_horizontal_of_coordinates {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hd : 0 < outputDegree s v (label s v.val k))
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) (hw : w.val = Surjection.erase v.val a)
    (he : ∀ i, Surjection.erase (label s v.val) k i =
      label t w.val (Fin.cast (by omega : m + 1 + q = m + q + 1) i)) :
  outputBoundarySignAt s v k = Surjection.deletionCoefficient v.val a * cutSign t w.val
outputBoundarySignAt_horizontalDeletion {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (a b : Fin (m + 1 + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ)) :
  outputBoundarySignAt s v a.succ =
    Surjection.deletionCoefficient v.val (s.horizontal a.succ) *
      cutSign ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w.val
```

### 125.2 小さい切断の更新次数と指定面（C185・C186）

既存の削除列の一致の長さと、単体圏の頂点列の単射性を使う既存構成の照合。
混合角で使ったC152・C157を、区間数の異なる小さい切断との比較にも使える形で述べる。
削除列の具体的な一致自体を新しい仮定として残してhcを証明したことにはしない。

```lean
deletedOutputDegree_eq_of_vertexLists {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c) :
  Function.update (outputDegree s v) (label s v.val k)
    (outputDegree s v (label s v.val k) - 1) = outputDegree t w
deletedCutFace_eq_of_vertexLists {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (c : Fin r) :
  deletedCutFace s v (label s v.val k) hd j c =
    eqToHom (congrArg SimplexCategory.mk
      (congrFun (deletedOutputDegree_eq_of_vertexLists s t v w k hd hl) c)) ≫ face t w c
```

### 125.3 約5,600行の区切り・B4前の検証済み保存

一覧：済み 8／全体 48（うち追加 4）

今回の四本 **214行**は対象ビルド成功、専用監査
`/tmp/bsw16/audit-m14-horizontal-boundary-signs.log` も
**4モジュール・14宣言・標準三公理のみ**で成功。Leanの警告0、sorry・追加公理0。
登録候補の接頭部は `SerrePositivity.EInfinity.SimplexCuts.`。

- `ErasedColorSignComparisons`：37行
- `HorizontalDeletionCoefficients`：56行
- `HorizontalBoundarySigns`：74行
- `HorizontalDeletedFaces`：47行

対象ビルドの最終ログは`m14-horizontal-deletion-coefficients-01.log`の後者の対象、
`m14-horizontal-boundary-signs-01.log`、`m14-horizontal-deleted-faces-01.log`（`/tmp/bsw16/`）。
L09a・L09実測 **5,595行**、改訂MayのM14全体 **10,661行**。
約5,600行の1,000行区切りとして報告する。個々の補題は200行以下。

内部の水平境界の**元の実符号**が、元の語の削除係数と小さい切断のcutSignに一致した。
削除列が同じ場合の更新次数と指定面の厳密一致も閉じた。
水平hcの実テンソルへの接続、両端、無効な削除語の零、垂直hvはまだ残る。
§121・§123.5の全体見込みと外枠超過のリスクは、B4を理由に縮小した扱いにはしない。

## 126. B4の追従を先に行う（11-14昼）

一覧：済み 8／全体 48（うち追加 4）

調整役のB4指示を受領しM14の新しい実装より優先する。
mainの`citation-attributes.md` §14と`bulk-w1-b3/B4-README.md`を読んだ。
現在の四本の対象ビルドと監査を完了して先に保存し、main取り込み前のソースから採取する。
基準はc5c4436c0、本体のみ・drafts除外。
昼の採取は`--class impl --wait 3600`で組ごとに取り、280秒の実行上限で分ける。
索引と原ソースを保持し、保留0と差分確認の後にmainを取り込む。
取り込み後のソースには古い索引を適用しない。

### 126.1 B4採取中の記録（main取り込み前）

一覧：済み 8／全体 48（うち追加 4）

M14の検証済み四本は **94c593fe0** に保存済み。
基準c5c4436c0から自枝のコミットが触った本体Leanを再集計し、draftsを除外した対象は
**106本**。既存のB4一覧95本をすべて含み、その後の11本を加えた。
main上には、この106本の同名ファイルはまだないことも確認した。

採取前のソースコミット・全106本のSHA256・改名表のSHA256は
`bulk-w1-b4/bs-impl-before.json`に保存した。
原ソースの完全なコピー、分割した採取のJSON、ログは
`/tmp/bsw16/b4-20261114/`に保持している。
初期の6本の組の鍵内実行時間が約72秒だったため、進行中の組の完了と鍵返却を確認して
12本の組へまとめ直した。採取済み24本は原ソース一致を再検証して引き継ぎ、
未採取分のみを続行している。各組は`--class impl --wait 3600`、実行上限280秒。
整理券を重複して発行していない。

この記録時点の採取完了は **36／106本**。採取ジョブは稼働しており、次の組は鍵待ち。
完了済み36本の26,311件の参照を定義元つき改名表へ照合した範囲では、
移動する宣言への直接参照は0。これは**部分的な事前照合**であり、
全件のrewrite・`review.json`の保留0の確認に代えるものではない。
通常importのmodule-mapへの直接該当と、106本自身のファイル配置の移動の該当はともに0。
非修飾名の最終的な確認には全件の採取と正式rewriteを使う。

取り込み後の対象ビルドの範囲は、106本の自モジュール内のimportグラフから求めた。
次の8本の上位importerをすべてビルドすると、自分の106本を推移的にすべて覆う。
追加の依存が少ない順と被覆数は`bulk-w1-b4/bs-impl-build-scope.json`、
詳細な依存グラフは`/tmp/bsw16/b4-20261114/build-coverage-plan.json`に保存した。
これは計画であり、まだmain取り込み後のビルド成功を主張しない。

- `SerrePositivity.EInfinity.SimplexCuts.GeneratorBoundary`
- `SerrePositivity.EInfinity.SimplexCuts.TopTerm`
- `SerrePositivity.EInfinity.SimplexCuts.StraightTraceFaces`
- `SerrePositivity.EInfinity.SimplexCuts.TerminalSignData`
- `SerrePositivity.EInfinity.SimplexCuts.Normalization`
- `SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletedFaces`
- `SerrePositivity.EInfinity.SimplexCuts.HorizontalBoundarySigns`
- `SerrePositivity.EInfinity.SimplexCuts.MixedBoundaryValues`

106本それぞれに宣言があることと標準三公理のみであることを検査する専用監査も用意した。
採取中のLeanソースは変更せず、M14の次のLean実装には戻っていない。
全件の採取→rewrite・保留/差分確認→main取り込み→対象ビルド/専用監査の順を保つ。

### 126.2 B4の完了：採取・プレビュー・main取り込み・検証

一覧：済み 8／全体 48（うち追加 4）

**B4は完了**。基準以降に自枝で追加・変更した、存在する本体Leanは**106本**で、
対象JSONとの一致と、drafts以外の採取漏れ0を確認した。
原ソースは **94c593fe0** のLeanに対応し、その後の文書コミットでLeanは変更していない。
全106本をmain取り込み前の環境で採取し、索引と原ソースの完全なバイト一致を保って
正式`bulk_namespace.py rewrite`を実行した（終了0）。

- 採取：106／106本、10組、各実行上限280秒。鍵は組ごとに返却。
- プレビュー：`review.json`は空、**保留0件**。
- 差分確認：106本すべてを比較し、**書き換え0ファイル・削除0行・追加0行**。
- 通常import・ファイル配置のmodule-map該当も0。importの追加の変更は不要。
- main取り込み：**923a15dd6**、main側の親は **efa846fe8**（16d6b4547以降）。競合なし。
- 取り込み後：106本が事前に生成したプレビューと一致し、import被覆グラフも不変。
  古い索引を取り込み後のソースへ適用し直していない。

原ソース・索引・分割ログ・プレビューは`/tmp/bsw16/b4-20261114/`に保持。
初期の組をまとめ直す際は、当該採取プロセスの終了と鍵返却を確認し、
旧監視ドライバだけを計画的に終了した。検証済み24本をバイト一致で再検証し、
未採取分のみを新しい監視ドライバへ引き継いだ。
この切替の記録は`batch-transition.json`。旧監視ドライバの終了137を、
採取の失敗や未完の索引の成功扱いにはしていない。
全106本を受け取る正式rewriteでも索引と原ソースの検査を通した。

対象ビルドは、全106本を覆う8対象を、依存の追加が少ない順に3組で実行した。
各組は独立した`with_build_lock.sh --class impl --wait 3600`で鍵を取り、終了後返却した。

| 組 | 対象（接頭部`SerrePositivity.EInfinity.SimplexCuts.`） | 結果 |
| --- | --- | --- |
| 1 | GeneratorBoundary・TopTerm・StraightTraceFaces・TerminalSignData・Normalization | 成功、2,376 jobs |
| 2 | HorizontalDeletedFaces・HorizontalBoundarySigns | 成功、2,257 jobs |
| 3 | MixedBoundaryValues | 成功、2,289 jobs |

続けて別の一回の鍵で、106本をそれぞれ明示した専用監査を実行。
**106モジュール・967宣言・標準三公理のみ**で成功した。
各モジュールの宣言が0でないことも検査しており、狭い一対象だけの監査を106本の証拠にしていない。
新規106本のsorry・追加公理0、Leanの警告0。`git diff --check`成功。
rootビルド・共通入口・共通監査への登録は調整役の持ち分のまま。

永続的な検収資料は`bulk-w1-b4/`の次のファイル。

- `bs-impl-before.json`：全106ファイルの一覧、原ソースと改名表のSHA256、元のソースコミット。
- `bs-impl-rewrite.json`：保留0・106本一致・ソース差分0の結果。
- `bs-impl-build-scope.json`：8対象による106本の被覆と実際のビルド結果。
- `bs-impl-audit-source.lean.txt`：実行した専用監査の原文（本体のLeanではない検証資料）。
- `bs-impl-audit-result.txt`：監査の成功出力。
- `bs-impl-result.json`：merge親・各ログのハッシュ・967宣言の監査結果をまとめた記録。

**登録候補は`bs-impl-before.json`の全106モジュール**。全て
`SerrePositivity.EInfinity.SimplexCuts.*`で、B4による場所・名前の変更はない。
入口のimportは上の8対象で106本を覆う。監査の宣言元を選ぶ際は全106本を対象にできる。

B4で自レーンのLeanの差分は0なので、L09a・L09 **5,595行**、M14 **10,661行**の計数は不変。
B4の検収報告後、承認待ちを挟まず/goalの水平hcの実テンソルの接続へ戻る。

## 127. B4完了後：小さい切断の実テンソルへ戻す（11-14）

一覧：済み 8／全体 48（うち追加 4）

B4完了は **595254e10** に保存した。取り込み済みmainの環境で/goalへ戻る。
以下はC185・C186の同じ削除列の一致を、元の`cutTensor`と`cutTensorAt`へ接続する
既存構成の次数移送・貼り合わせの法則。新しい作用・錐・ホモトピーは作らない。
C188・C189の`h`は型を合わせる次数の等式で、C187と既存の全出力次数の式から導ける。
具体的な水平の削除列の一致は、別に既存C89から供給する。未供給のままhcを閉じたとは扱わない。

```lean
degreeSum_deleted_small_cut {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c) :
  degreeSum r (outputDegree t w) + 1 = m + q + 1 - r
deletedCutTensor_eq_small_cutTensor (A : Type u) [CommRing A] {m n q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -(degreeSum r (outputDegree t w) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
  deletedCutTensor A S s v (label s v.val k) hd j x =
    (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom (cutTensor A S t w x)
deletedCutTensor_eq_small_cutTensorAt (A : Type u) [CommRing A] {m n q r : ℕ}
    (S : SSet.{0}) (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -((n + q + 1 - r : ℕ) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
  deletedCutTensor A S s v (label s v.val k) hd j x =
    (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom (cutTensorAt A S t w x)
```

C189の局所法則は`step {M N P : ModuleCat A} (hMN : M = N) (hNP : N = P) (y : M) :
(eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y`。
等式の帰納法だけを使う。

### 127.1 検証

対象ビルド成功（2,189 jobs）。別の一回の鍵で専用監査も成功、1モジュール・3宣言・標準三公理のみ。
新規82行、L09a・L09 5,677行、M14 10,743行。sorry・追加公理0。
登録候補：`SerrePositivity.EInfinity.SimplexCuts.DeletedSmallCutTensors`。
一覧：済み 8／全体 48（うち追加 4）。

## 128. 内部の水平面の元の実テンソル（11-14）

一覧：済み 8／全体 48（うち追加 4）

C190–C192は既存C89・C184・C189の係数移送と貼り合わせの法則。
新しい組合せ分解はなく、有限点検済みのC89の削除列をそのまま各色へ写す。
次数等式`h`を明示して共通次数の指定移送を固定し、ホモトピー圏へは移らない。
型は次のとおり。いずれも200行以内。

```lean
lemma deletedVerticesList_horizontalDeletion {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (a b : Fin (m + 1 + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Fin (m + 1) → Fin r) (hw : w = Surjection.erase v (s.horizontal a.succ))
    (c : Fin r) :
    deletedVerticesList s v a.succ c =
      verticesList ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w c

lemma deletedCutTensor_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌)
    (h : -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v (label s v.val a.succ) hd j x =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensorAt A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)

lemma signedDeletedCutTensor_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌)
    (h : -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1) :
    outputBoundarySignAt s v a.succ • deletedCutTensor A S s v (label s v.val a.succ) hd j x =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)
```

### 128.1 元の境界項への貼り合わせ

一覧：済み 8／全体 48（うち追加 4）

C193–C194も既存構成の次数移送・貼り合わせの法則。C193は既存`Surjection.Word.arity_le_length`と整数計算だけ。
C194はC192とC164を合わせ、正の出力次数`hd`を明示した内部面について元の境界項を照合する。
水平の端点・無効な削除語・零出力次数の扱いはなお残り、全hcの完了とは扱わない。

```lean
lemma horizontalDeletion_degree_eq {m q r : ℕ} (w : Surjection.Word r (m + 1)) :
    -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1

lemma outputBoundaryTerm_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val a.succ) j x =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)
```

### 128.2 正次数の前提の供給

一覧：済み 8／全体 48（うち追加 4）

C195はC150の削除リストの長さとC149の既存の長さの式から従う算術の法則。
C196はC190・C194・C195の貼り合わせで、出力の正次数を外部の仮定として残さない。
無効な削除語と端点はなお別の残作業。いずれも200行以内。

```lean
lemma outputDegree_pos_of_deleted_vertexLists {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c) :
    0 < outputDegree s v (label s v.val k)

lemma outputBoundaryTerm_horizontalDeletion_valid {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val a.succ) j x =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)
```

### 128.3 検証と取り込み候補

一覧：済み 8／全体 48（うち追加 4）

次の3モジュール、計166行を対象ビルドと小さい監査で検証した。
接頭部は`SerrePositivity.EInfinity.SimplexCuts.`。共通入口・共通監査には触っていない。

- `HorizontalDeletedTensors`：69行（C190–C192）。
- `HorizontalBoundaryTerms`：48行（C193–C194）。
- `HorizontalValidTerms`：49行（C195–C196）。

最終対象ビルドは`/tmp/bsw16/m14-horizontal-valid-terms-02.log`、
**2,271 jobs成功・警告0**。最初の型検査でC194の次数等式の引数の省略が解決されず、
既に証明済みのC193を明示して修正した。次のビルドで出た`if_pos`の非推奨警告は
`ite_eq_left`へ直し、最終ビルドで解消を確認した。
監査は別の一回の鍵で`/tmp/bsw16/audit-m14-horizontal-valid-terms.lean`を実行し、
**3モジュール・10宣言・標準三公理のみ**で成功（`m14-horizontal-valid-terms-audit.log`）。
先の一モジュール監査では内部に生成された補助も含め4宣言を確認し、
最後は上の3モジュールすべてを明示して改めて監査した。
各ビルド・監査で整理券は一枚、鍵は実行中だけで、終了と返却を確認した。
sorry・追加公理0、`git diff --check`成功。

§127の82行と合わせ、B4後の追加は248行。L09a・L09累計 **5,843行**、
改訂MayのM14全体 **10,909行**。次のL09a・L09の1,000行区切りは約6,600行、
M14半分の12,500行と外枠25,000行には未到達。

有効な削除語を持つ内部水平面について、正次数の仮定を供給した上で元の境界項を
小さい切断の指定項へ接続した。等式は元の加群のもので、ホモトピー圏へ弱めていない。
残りは水平の両端・無効な削除語の零・全添字の貼り合わせ、垂直hvと全相殺。
L09a・L09全体を閉じたとは扱わず、§121・§123.5の規模リスクも据え置く。

B4取り込み点は595254e10の106本のまま。B4後の新規4モジュールは§127・§128に
別途登録候補を記したので、B4の106本の監査に含まれるとは扱わない。

## 129. 水平な両端の指定座標を共通の比較へ移す（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンはB4と内部面の実境界項を検証・コミットした進捗。B4後の作業木から続行。
ここでは既存の`ShuffleFirstFace`・`ShuffleLastFace`の水平削除の座標公式を使う。
新たな作用や定理を導入せず、既存C173の右端の特徴付けと削除列の定義への貼り合わせを行う。
両端の座標・hi・削除列は、先にPythonでm,q=0〜3、3色の任意の語について
**20,862例**を確認した（`/tmp/bsw16/check-horizontal-endpoint-transport.py`）。

### 129.1 指定座標からの移送法則（C197・C198）

C197は既存C174の証明を、既に供給された水平・垂直座標に依存する形で使う。
局所型は`hne : j ≠ k`と、Fin.cast二回が元の`l`へ戻る等式`hc`。
C198は同じ二座標を削除列の定義へ写すだけ。両方200行以内。

```lean
lemma hi_eq_of_horizontal_deleted_coordinates {m q : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hh : ∀ j : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) =
        a.succAbove (t.horizontal j))
    (hv : ∀ j : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) = t.vertical j)
    (i : Fin (m + 1)) : hi t i = hi s (a.succAbove i)

lemma deletedTrace_eq_of_horizontal_coordinates {m q r : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (v : Fin (m + 2) → Fin r) (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2))
    (hh : ∀ j : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) =
        a.succAbove (t.horizontal j))
    (hv : ∀ j : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) = t.vertical j) :
    deletedTrace s v k = List.ofFn (fun j : Fin (m + q + 1) =>
      (Surjection.erase v a (t.horizontal j), t.vertical j))
```

### 129.2 同じ境界項の貼り合わせと両端（C199–C201）

一覧：済み 8／全体 48（うち追加 4）

C199はC183の符号・C189の実テンソル・C195の正次数へ、C197・C198の指定座標を供給する法則。
C200・C201は既存の始端・終端の座標公式を代入する。同じ二つの構成の照合で、
作用の新しい法則やホモトピーを作らない。個々の補題は200行以内。
局所の`hl`は全色の削除列の等式、`hd`は正次数、`hs`はC183の符号等式。
`hc`は二回のFin.castの消去、`hk`は末尾の辺の終点がFin.lastである等式、
`he`は末尾の辺の標準添字と指定`a`の等式、`hH`は既存の水平端点の判定である。

```lean
lemma outputBoundaryTerm_horizontal_of_coordinates {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (t : Cut m q)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hsingle : ∀ l, s.horizontal l = a → l = k)
    (hw : w.val = Surjection.erase v.val a)
    (hh : ∀ l : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        a.succAbove (t.horizontal l))
    (hv : ∀ l : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) = t.vertical l)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x =
      Surjection.deletionCoefficient v.val a •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom (cutTerm A S t w x)

lemma outputBoundaryTerm_horizontal_first {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (h₀ : (0 : Fin (m + 1 + q)) ∈ s.val)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val 0)
    (j : Fin (outputDegree s v (label s v.val 0) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val 0) 0) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val 0) j x =
      Surjection.deletionCoefficient v.val 0 •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q 0).symm ⟨s, h₀⟩) w x)

lemma outputBoundaryTerm_horizontal_last {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (a : Fin (m + 1 + q)) (ha : a ∈ s.val)
    (hlast : a.val + 1 = m + 1 + q)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (Fin.last (m + 1)))
    (j : Fin (outputDegree s v (label s v.val (Fin.last (m + 1 + q))) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val (Fin.last (m + 1 + q)))
      (Fin.last (m + 1 + q))) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val (Fin.last (m + 1 + q))) j x =
      Surjection.deletionCoefficient v.val (Fin.last (m + 1)) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x)
```

### 129.3 削除しない因子の正規化による消滅（C202–C204）

一覧：済み 8／全体 48（うち追加 4）

既存構成の法則の証明分割。C202は既存`faces_mono_iff`の順方向を一色だけに制限し、
同じfiberの順序同型の逆で二頂点を読む。C203は既存`gen_map_of_not_mono`と
`tensorValue_eq_zero`を、`deletedCutTensor`の削除しない因子に適用。C204は符号を戻す。
新しい非退化性の定理や作用を仮定せず、既存の消滅をそのまま使用する。各補題200行以内。
局所型は色のfiberへの所属`hci`・`hcj`、同じ順序同型の逆の評価`hei`・`hej`、
元の面の値の等式`hval`と単射性からの添字の等式`heq`（既存`faces_mono_iff`と同型の分割）。

```lean
lemma face_not_mono_of_repeated_color {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) (i j : Fin (m + q + 1))
    (hi : label s v.val i = c) (hj : label s v.val j = c)
    (hne : i ≠ j) (hv : s.vertical i = s.vertical j) : ¬Mono (face s v c)

lemma deletedCutTensor_eq_zero_of_other_face {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (c : Fin r) (hc : c ≠ a)
    (hm : ¬Mono (face s v c)) (x : S _⦋q⦌) :
    deletedCutTensor A S s v a ha j x = 0

lemma outputBoundaryTerm_eq_zero_of_other_face {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s v a + 1))
    (c : Fin r) (hc : c ≠ a) (hm : ¬Mono (face s v c)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v a j x = 0
```

### 129.4 非全射な削除語の零（C205・C206）

一覧：済み 8／全体 48（うち追加 4）

L09a内の有限なfiberの計算。先にPythonでm=1〜4、q=0〜3、arity=1〜3の全非退化全射語を
点検し、非全射な削除の次数零 **2,616例**、退化な削除の別の色の重複 **2,440例**で一致を確認した
（`/tmp/bsw16/check-horizontal-invalid-deletions.py`）。
まず前者を既存`Surjection.erase_surjective_iff`とC56の水平fiberの特徴付けへ戻す。
C205の局所型`hu : ∀ i, v.val i = v.val (s.horizontal k) → i = s.horizontal k`、
`hc : colorPositions s v.val (label s v.val k) = {k}`。C206は次数零の定義への貼り合わせ。
各補題200行以内。後者の退化な削除への適用はまだ閉じたとは数えない。

```lean
lemma outputDegree_zero_horizontal_of_not_surjective {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) (hk : HorizontalVertex s k)
    (hns : ¬Function.Surjective (Surjection.erase v.val (s.horizontal k))) :
    outputDegree s v (label s v.val k) = 0

lemma outputBoundaryTerm_horizontal_not_surjective {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) (hk : HorizontalVertex s k)
    (hns : ¬Function.Surjective (Surjection.erase v.val (s.horizontal k)))
    (j : Fin (outputDegree s v (label s v.val k) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x = 0
```

### 129.5 退化した削除の元の二位置（C207）

一覧：済み 8／全体 48（うち追加 4）

上の2,440例の点検で使った有限な位置の計算をLeanにする。
非退化な語で新しく隣接同色が生じるのは、消した位置をちょうど挟むときだけ。
既存`Surjection.succAbove_val_eq`の二分岐と元の語の隣接非退化性を使う。
局所型は削除後の隣接同色対`hij`・`he`、元での隣接の否定`hskip`、
`hleft : i.val + 1 = a.val ∧ j.val = a.val`。200行以内。

```lean
lemma erased_word_degenerate_neighbors {m r : ℕ} (v : Surjection.Word r (m + 2))
    (a : Fin (m + 2)) (h : ¬Surjection.Nondegenerate (Surjection.erase v.val a)) :
    ∃ i j : Fin (m + 2), i.val + 1 = a.val ∧ a.val + 1 = j.val ∧ v.val i = v.val j
```

### 129.6 残る同色の二頂点と、無効な削除全体の零（C208–C210）

一覧：済み 8／全体 48（うち追加 4）

C208は上の2,440例で先に点検した有限な水平隣接辺の計算。
C207から元の区間の両隣`i,j`を取り、水平座標の端点の公式により`0 < k.val < m+1+q`。
その前後の辺`l,e`を読む既存`step_of_mem`で、削除しない別の色の同じ頂点を二つ得る。
C202へ適用するだけで、BEの新しい作用・operad法則を導入しない。
C209は既存の正規化の消滅C204への貼り合わせ、C210は非全射と退化の二場合の貼り合わせ。
個々の補題200行以内。局所型は内部性`hk0`・`hkN`、辺の終始点`hl : l.succ=k`・
`he : e.castSucc=k`、水平座標の一致`hi : s.horizontal l.castSucc=i`・
`hj : s.horizontal e.succ=j`、異なる二頂点`hne : l.castSucc ≠ e.succ`。

```lean
lemma other_face_not_mono_horizontal_degenerate {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (k : Fin (m + 1 + q + 1)) (hk : HorizontalVertex s k)
    (hdeg : ¬Surjection.Nondegenerate (Surjection.erase v.val (s.horizontal k))) :
    ∃ c : Fin r, c ≠ label s v.val k ∧ ¬Mono (face s v c)

lemma outputBoundaryTerm_horizontal_degenerate {m q r : ℕ} (S : SSet.{0}) (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (k : Fin (m + 1 + q + 1)) (hk : HorizontalVertex s k)
    (hdeg : ¬Surjection.Nondegenerate (Surjection.erase v.val (s.horizontal k)))
    (j : Fin (outputDegree s v (label s v.val k) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x = 0

lemma outputBoundaryTerm_horizontal_invalid {m q r : ℕ} (S : SSet.{0}) (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (k : Fin (m + 1 + q + 1)) (hk : HorizontalVertex s k)
    (hinvalid : ¬(Function.Surjective (Surjection.erase v.val (s.horizontal k)) ∧
      Surjection.Nondegenerate (Surjection.erase v.val (s.horizontal k))))
    (j : Fin (outputDegree s v (label s v.val k) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x = 0
```

### 129.7 検証・実測と次の接続

一覧：済み 8／全体 48（うち追加 4）

今回の新規6モジュールは、対象ビルドと専用の小さい監査で検証した。
登録候補の接頭部は`SerrePositivity.EInfinity.SimplexCuts.`。

| モジュール | 実測 | 内容 |
| --- | ---: | --- |
| `HorizontalDeletionCoordinates` | 61行 | 指定座標から右端・削除列への移送 |
| `HorizontalEndpointTerms` | 127行 | 同じ実境界項の比較と水平な両端 |
| `OtherFaceZeroTerms` | 66行 | 削除しない色の非単射な面による正規化の消滅 |
| `NonSurjectiveZeroTerms` | 53行 | 非全射な削除で次数零・元の境界項零 |
| `DegenerateDeletionNeighbors` | 35行 | 退化した削除の元の両隣の二位置 |
| `DegenerateHorizontalTerms` | 96行 | 別の色の重複から退化な削除・無効な削除の境界項零 |
| **合計** | **438行** | |

最終対象ビルドは`/tmp/bsw16/m14-horizontal-invalid-terms-03.log`、
**2,288 jobs成功・Lean警告0**。
初期の型検査では、端点判定の明示import、letの展開、存在命題の表示、
Fin.zero・Fin.lastの値を算術へ明示する処理を修正した。
余分な`rfl`・非推奨名・100字を超える行も直した。
主張の型を弱めたり、非単射性やテンソルの消滅を未証明の前提に足したりしていない。

別の一回の鍵で`/tmp/bsw16/audit-m14-horizontal-endpoint-invalid.lean`を実行し、
**6モジュール・59宣言・標準三公理のみ**で成功した
（`/tmp/bsw16/m14-horizontal-endpoint-invalid-audit.log`）。
全6モジュールを明示し、各モジュールの宣言数が0でないことも検査した。
新規本体のsorry・追加公理0、`git diff --check`成功。
共通入口・共通監査の登録、rootビルドは調整役の持ち分として実行していない。
各実行は`--class impl --wait 3600`、整理券は一枚、
ビルドまたは監査の終了後に鍵を返却し、待ち時間・編集・報告中には鍵を持っていない。

L09a・L09累計 **6,281行**、改訂MayのM14全体 **11,347行**。
次の1,000行区切りは約6,600行、M14の半分報告は12,500行、外枠は25,000行のまま。
§121・§123.5の完成見込みと上端超過のリスクを、今回の局所的な完了で縮小した扱いにはしない。

これで有効な水平削除の内部・始端・終端の元の実境界項、および非全射・隣接退化による
無効な水平削除の元の境界項零がそろった。すべて元の加群の等式である。
次は既存`horizontalBoundaryFaceEquiv`／`horizontalBoundaryAllEquiv`の
指定された語の位置・小さい切断との照合を行い、実際の全水平添字のhcへ接続する。
垂直hv、全相殺とL09a・L09全体は未完。G10や他レーンのファイルには触っていない。

## 130. 全水平添字の同値との厳密な照合（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンは§129の6モジュールを検証・コミットした進捗。作業木がクリーンであることを確認して続行。
B4は完了済み。新しい数学や別の同値を作らず、既存C70・C71が選ぶ文字位置と切断を読む。
先にm=0〜5、q=0〜4の全切断・係数位置について、三分割の逆、対応する水平座標、
指定削除で元の切断が復元されることをPythonで **2,771例** 点検した
（`/tmp/bsw16/check-horizontal-index-transport.py`）。

### 130.1 三つの枝での指定添字の評価（C211–C216）

既存の構成の合成・逆の法則と有限の添字の計算。各補題200行以内。
内部の文字位置は`i.castSucc.succ`、両端は0と`Fin.last (m+1)`で、元の添字を保持する。

```lean
lemma coefficientIndexEndpointEquiv_symm_first (m q : ℕ) (t : Cut m q) :
    (coefficientIndexEndpointEquiv m q).symm (.inl t) = (0, t)

lemma coefficientIndexEndpointEquiv_symm_interior (m q : ℕ) (t : Cut m q) (i : Fin m) :
    (coefficientIndexEndpointEquiv m q).symm (.inr (.inl (t, i))) = (i.castSucc.succ, t)

lemma coefficientIndexEndpointEquiv_symm_last (m q : ℕ) (t : Cut m q) :
    (coefficientIndexEndpointEquiv m q).symm (.inr (.inr t)) = (Fin.last (m + 1), t)

lemma horizontalBoundaryFaceEquiv_first (m q : ℕ) (t : Cut m q) :
    (horizontalBoundaryFaceEquiv m q (0, t)).val = (horizontalFirstFaceEquiv m q t).val

lemma horizontalBoundaryFaceEquiv_interior (m q : ℕ) (t : Cut m q) (i : Fin m) :
    (horizontalBoundaryFaceEquiv m q (i.castSucc.succ, t)).val =
      (horizontalInteriorFaceEquiv m q (t, i)).val

lemma horizontalBoundaryFaceEquiv_last (m q : ℕ) (t : Cut m q) :
    (horizontalBoundaryFaceEquiv m q (Fin.last (m + 1), t)).val =
      (horizontalLastFaceEquiv m q t).val
```

### 130.2 元の文字位置の保存（C217・C218）

一覧：済み 8／全体 48（うち追加 4）

点検済みの有限な座標の計算と、既存の同値の法則。
C217は`horizontalCornerEquiv_horizontal`と`horizontalMarkedEdgeEquiv_horizontal`の合成。
C218は同じ既存の三分割の逆で三場合に分け、C214–C217と水平座標の端点の式を使う。
個々の補題200行以内。

```lean
lemma horizontalInteriorFaceEquiv_horizontal (m q : ℕ) (t : Cut m q) (i : Fin m) :
    (horizontalInteriorFaceEquiv m q (t, i)).val.1.horizontal
      (horizontalInteriorFaceEquiv m q (t, i)).val.2 = i.castSucc.succ

lemma horizontalBoundaryFaceEquiv_horizontal (m q : ℕ) (c : Fin (m + 2) × Cut m q) :
    (horizontalBoundaryFaceEquiv m q c).val.1.horizontal
      (horizontalBoundaryFaceEquiv m q c).val.2 = c.1
```

### 130.3 指定された全水平添字での実項の照合（C219・C220）

一覧：済み 8／全体 48（うち追加 4）

C219は既存の構成の貼り合わせの法則。C211–C216で同じ三分割に分け、
C200・C196・C201を適用し、指定挿入の`Equiv.symm_apply_apply`で元の小さい切断へ戻す。
C220はC218の文字位置の一致とC210の無効削除の消滅の貼り合わせ。
どちらも元の加群の等式で、実際の小さい切断`c.2`と削除位置`c.1`を保持する。
各補題200行以内。C219の局所型は挿入辺の所属`ha`・`hb`、
`hh : (e t).val.horizontal a.succ = i.castSucc.succ`と
`hw' : w.val = Surjection.erase v.val ((e t).val.horizontal a.succ)`。

```lean
lemma outputBoundaryTerm_horizontalBoundaryFaceEquiv_valid {m q r : ℕ} (S : SSet.{0})
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1)) :
    ∀ (c : Fin (m + 2) × Cut m q) (_hw : w.val = Surjection.erase v.val c.1)
      (j : Fin (outputDegree (horizontalBoundaryFaceEquiv m q c).val.1 v
        (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
          (horizontalBoundaryFaceEquiv m q c).val.2) + 1))
      (_hj : j.val = vertexRank (horizontalBoundaryFaceEquiv m q c).val.1 v.val
        (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
          (horizontalBoundaryFaceEquiv m q c).val.2) (horizontalBoundaryFaceEquiv m q c).val.2)
      (x : S _⦋q⦌),
    outputBoundaryTerm A S (horizontalBoundaryFaceEquiv m q c).val.1 v
        (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
          (horizontalBoundaryFaceEquiv m q c).val.2) j x =
      Surjection.deletionCoefficient v.val c.1 •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom (cutTerm A S c.2 w x)

lemma outputBoundaryTerm_horizontalBoundaryFaceEquiv_invalid {m q r : ℕ} (S : SSet.{0})
    (v : Surjection.Word r (m + 2)) (c : Fin (m + 2) × Cut m q)
    (hinvalid : ¬(Function.Surjective (Surjection.erase v.val c.1) ∧
      Surjection.Nondegenerate (Surjection.erase v.val c.1)))
    (j : Fin (outputDegree (horizontalBoundaryFaceEquiv m q c).val.1 v
      (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
        (horizontalBoundaryFaceEquiv m q c).val.2) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S (horizontalBoundaryFaceEquiv m q c).val.1 v
      (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
        (horizontalBoundaryFaceEquiv m q c).val.2) j x = 0
```

### 130.4 元の係数境界値との次数移送（C221–C224）

一覧：済み 8／全体 48（うち追加 4）

既存構成の係数移送・貼り合わせの法則。C221・C222は同じ実境界項を読む定義の照合。
C223はC219・C220を元の全境界値の共通次数へ運び、定義の負号と相殺する。
C224の係数次数零の場合は、削除語の長さがarityより小さいため全射が存在しないことを
既存`Fintype.card_le_of_surjective`から読み、C220へ戻す。新しい非退化性の仮定は足さない。
C223の局所型`ho`・`hc`は書かれている二つの整数次数の等式、
`step {M N P : ModuleCat A} (hMN : M = N) (hNP : N = P) (y : M) :
(eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y`は
§127の同じ移送の合成則。C224の`hns`は削除語の全射性・非退化性の連言の否定。
各補題200行以内。未検証の段階ではhcの完了とは数えない。

```lean
lemma coefficientBoundaryTerm_succ_eq {r d q : ℕ} (S : SSet.{0})
    (u : Surjection.BasisWord (r + 1) (d + 1)) (c : Fin (r + d + 2) × Cut (r + d) q)
    (x : S _⦋q⦌)
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1) :
    coefficientBoundaryTerm A S r (d + 1) q u c x =
      if hw : Function.Surjective (Surjection.erase (positiveWord u).val c.1) ∧
          Surjection.Nondegenerate (Surjection.erase (positiveWord u).val c.1) then
        -Surjection.deletionCoefficient (positiveWord u).val c.1 •
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (cutTerm A S c.2 ⟨Surjection.erase (positiveWord u).val c.1, hw⟩ x)
      else 0

lemma universalBoundaryValue_coefficient (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (r + d + 1) × Cut (r + d - 1) q) :
    universalBoundaryValue A S u q x (.inr (.inl c)) = coefficientBoundaryTerm A S r d q u c x

lemma universalBoundaryValue_horizontal_succ (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) (d + 1)) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (r + d + 2) × Cut (r + d) q) :
    universalBoundaryValue A S u q x (.inl (horizontalBoundaryFaceEquiv (r + d) q c).val) =
      -universalBoundaryValue A S u q x (.inr (.inl c))

lemma universalBoundaryValue_horizontal_neg (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) (hm : 0 < r + d)
    (c : Fin (r + d + 1) × Cut (r + d - 1) q) :
    universalBoundaryValue A S u q x (.inl ((horizontalBoundaryAllEquiv (r + d) q hm) c).val) =
      -universalBoundaryValue A S u q x (.inr (.inl c))
```

### 130.5 依存する面番号を保つ証明分割

一覧：済み 8／全体 48（うち追加 4）

C219の最初の型検査では、面番号`j`に依存する型の中を部分的にsimpして、
元の同値の値が残った。証明の分割として、次の同じ述語`P`を局所的に置き、
指定頂点を丸ごと書き換えてから面番号を導入する。主張の型・比較する射・前提は変更しない。

```lean
  let P (z : MarkedCut (m + 1) q) (a : Fin (m + 2)) (t : Cut m q) : Prop :=
    ∀ (_hw : w.val = Surjection.erase v.val a)
      (j : Fin (outputDegree z.1 v (label z.1 v.val z.2) + 1))
      (_hj : j.val = vertexRank z.1 v.val (label z.1 v.val z.2) z.2) (x : S _⦋q⦌),
      outputBoundaryTerm A S z.1 v (label z.1 v.val z.2) j x =
        Surjection.deletionCoefficient v.val a •
          (eqToHom (congrArg (fun n : ℤ => (power (chains A S) r).X n)
            (horizontalDeletion_degree_eq (q := q) w))).hom (cutTerm A S t w x)
```

C219の同じ指定切断への戻りは、局所型
`hsmall : e.symm ⟨(e t).val, (e t).property⟩ = t`（内部では所属証明`ha`）を
既存`e.symm_apply_apply t`から明示し、元の等式で書き換える。新しい照合の仮定ではない。

待ち時間には垂直分岐の有限計算も先に点検した。
`/tmp/bsw16/check-vertical-position-signs.py`、**14,942例**で、
C170の接頭順位、位置指数の差が削除区間以後のcaesura数になること、
同色の直前の面の削除係数と実境界符号の一致を確認した。
垂直の新しいLeanはまだ書かず、水平hcの検証を先にする。この点検を垂直hvの証明済み扱いにはしない。

C223・C224の全出力値への移送では、C168で読む`⟨z.val.1,z.val.2⟩`と
元の指定頂点`z.val`を既存`Sigma.eta`で明示的に照合する。
局所型`hout`はC168の等式の左辺をその同じ指定頂点へ戻したもので、
新しい射・仮定・自然性の選択を加えない。

C223では、同じ実境界項の等式`ht`を、指定された共通次数への線形射に
`congrArg`で写した`ht'`として使う。型はC219またはC220の両辺に
`(eqToHom (congrArg (fun n : ℤ => (power (chains A S) (r+1)).X n) ho)).hom`
を適用した等式そのもので、`map_zsmul`・`map_zero`と上の`step`だけを使う。
依存した引数内へのrwの照合に頼らず、既存の係数移送の法則を明示する分割である。

C223の詳細型の比較では、`r+(d+1)`と`(r+d)+1`が式内部に異なる形で残っていた。
`Nat.add_assoc`で同じ正規形へそろえ、上の移送の合成則を適用する。
一時的なppオプションは除去した。型クラス引数を明示した診断ログは
`/tmp/bsw16/m14-horizontal-boundary-values-diag.log`に保持する。

### 130.6 色と面番号の依存した組を保つ（C225）

一覧：済み 8／全体 48（うち追加 4）

より具体的な型検査で、逆同値の`.2`の型が`.1`に依存し、`.1=label`を
semireducibleな定義の展開だけで読むと、通常のimplicit透明性では型が合わないことを確認した。
加法の括弧をそろえるだけでは解消しなかった。C225は元の値を同じ依存した組のまま読む定義の法則。
既存公開宣言は変えず、新しい名前で足す。C223・C224では
`hp : (colorPositionEquiv z.val.1 v).symm z.val.2 = ⟨a,j⟩`で一度だけ分解し、
既存C22から`ha : a = label z.val.1 v.val z.val.2`を得て色を置き換える。
その後の`j`は正しい色のFinとして通常の透明性でも型が合う。
`hj : j.val = vertexRank z.val.1 v.val (label z.val.1 v.val z.val.2) z.val.2`は既存C28の順位の式から得る。
新しい構成や主張の弱化はなく、同じ出力値の評価の分割。C225は200行以内。

```lean
lemma universalBoundaryValue_output_paired (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (s : Cut (r + d) q) (k : Fin (r + d + q + 1))
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
    universalBoundaryValue A S w q x (.inl ⟨s, k⟩) =
      (eqToHom (congrArg (fun n : ℤ => (power (chains A S) (r + 1)).X n) h)).hom
        (outputBoundaryTerm A S s (positiveWord w)
          ((colorPositionEquiv s (positiveWord w)).symm k).1
          ((colorPositionEquiv s (positiveWord w)).symm k).2 x)
```

### 130.7 待ち時間の垂直の次の型案（紙のみ）

一覧：済み 8／全体 48（うち追加 4）

水平hcの検証待ちの間に、同じL09aの垂直の有限計算を整理した。
以下のC226–C229は**紙の型案で、Lean未実装・未検証**。
新しい数学のまとまりではなく、既存の垂直削除の座標・右端・位置指数の法則。
C229の位置差は非退化性・全射性を仮定しない任意の3色の関数についても
先に **76,407例** 点検した（`/tmp/bsw16/check-vertical-arbitrary-position.py`）。
これは既存C170の接頭順位と、削除後に残る区間の右端を使う経路を確認する点検であり、
Leanでの証明を代用しない。

```lean
-- C226：指定された垂直削除で、削除しない右端を垂直の順序単射で比較する。
hi_eq_of_vertical_deleted_coordinates {m q : ℕ} (s : Cut m (q + 1)) (t : Cut m q)
    (k : Fin (m + (q + 1) + 1))
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j))
    (i : Fin (m + 1))
    (hmax : (intervalPositions s i).max' (intervalPositions_nonempty s i) ≠ k) :
  hi s i = ((s.vertical k).succAbove ⟨hi t i, by have := hi_le_q t i; omega⟩).val

-- C227：垂直の削除頂点は、活動区間の右端ではない。
hi_vertex_ne_vertical_of_caesura {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical)
    (i : Fin (m + 1)) (hi : Surjection.Caesura v i) :
  (intervalPositions s i).max' (intervalPositions_nonempty s i) ≠ k

-- C228：入力の削除頂点以後にある右端は、その区間以後のものに限る。
vertical_vertex_le_hi_iff {m q : ℕ} (s : Cut m (q + 1))
    (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical) (i : Fin (m + 1)) :
  (s.vertical k).val ≤ hi s i ↔ s.horizontal k ≤ i

-- C229：同じ語の位置指数の差は、削除区間以後のcaesuraの個数。
positionExponent_vertical_deleted_coordinates {m q r : ℕ}
    (s : Cut m (q + 1)) (t : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) :
  positionExponent s v = positionExponent t v +
    ((caesuraPositions v).filter (fun i => s.horizontal k ≤ i)).card
```

C226は既存C173・C06と同じ右端の上下界の特徴付けを、
垂直座標の狭義単調な`Fin.succAbove`へ移す。C227は内部・始端の次の垂直辺と、
終端では元の最後の区間がcaesuraにならないことを使う有限な計算。
C228は既存の座標の単調性と直前の垂直辺、C229はこれらと`Fin.succAbove`の値の式を
既存`positionExponent_eq_caesura_sum`へ戻す。
全caesura数は既存`Surjection.Word.card_caesuras`／`Surjection.card_caesuras_basisWord`を使い、
同じ濃度の式を再証明しない。C170の接頭順位と合せて入力面の交代符号へ戻す。

### 130.8 待ち時間のC226のLean下書き

一覧：済み 8／全体 48（うち追加 4）

水平hcの検証順は維持し、待ち時間に紙のC226のみLeanの下書きを置いた。
C227–C229はまだ紙のまま。C226は検証前にはコミットしない。
右端の達成と上界の既存C06を使い、削除前の右端の逆像`j`と削除後の右端`jt`を比較する。
局所型`hji : t.horizontal j = i`、`hsmall : t.vertical j ≤ ⟨hi t i,⋯⟩`、
`hmon`は既存`Fin.strictMono_succAbove`による同じ上界の移送。

実装前の有限点検は`/tmp/bsw16/check-vertical-interval-maxima.py`、
**12,341例**で右端の移送、入力頂点以上の右端と区間番号の閾値の一致、
削除頂点自体が右端なら最後の頂点・最後の区間になることを確認した。
この点検はC226–C228の有限計算の確認であり、Leanの検証結果ではない。

C227・C228に使う隣接辺の証明分割も作業木へ下書きした（未検証、検証前にはコミットしない）。
既存C51–C53の始端・内部・終端の式を指定した辺へ戻すだけで、
垂直のための新しい構造や判定の定義は作らない。各補題200行以内。
有限点検は上の垂直頂点の全候補12,341例と、既存の全境界の対合6,070添字の点検で
用いた同じ前後の辺の条件。局所型`he0`・`helast`は指定終始点の0・Fin.lastとの等式、
`heq`・`hl`・`hr`は指定辺と既存の端点/角の辺番号との等式。

```lean
lemma vertical_kind_outgoing_not_mem {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) (hk : boundaryVertexKind s k = .vertical)
    (e : Fin (m + q)) (he : e.castSucc = k) : e ∉ s.val

lemma vertical_kind_incoming_not_mem {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) (hk : boundaryVertexKind s k = .vertical)
    (e : Fin (m + q)) (he : e.succ = k) : e ∉ s.val
```

C227も同じ検証待ちの間に下書きした。型は§130.7のまま、未検証。
既存の右端の達成から`hhi : s.horizontal k = i`。次の頂点がある場合は、
上の`vertical_kind_outgoing_not_mem`と既存`step_of_notMem`で同じ区間の次の頂点が得られ、
右端の最大性`hb : e.succ ≤ max' (intervalPositions s i) ⋯`に反する。
終端なら水平座標の端点の式から`i=Fin.last m`で、caesuraの定義に反する。
新しい構成を加えない有限の右端の計算。個々の補題200行以内。

C228も同じ待ち時間に、§130.7の型のまま下書きした（未検証）。
右端の頂点`j`の水平座標は`i`。`i < s.horizontal k`なら単調性で`j<k`となり、
直前の垂直辺の厳密な増分により`hi s i < (s.vertical k).val`。
逆に区間番号が指定区間以後なら、右端が`k`より前にあると同じ区間に`k`を含める
最大性に反する。局所型`hjk : j < k`、`hjle : j ≤ e.castSucc`、
`hm : (s.vertical j).val ≤ (s.vertical e.castSucc).val`、
`hkmem : k ∈ intervalPositions s i`。既存の順序と最大性だけの有限計算で、200行以内。

C229の位置指数の式も、§130.7の型のまま下書きした（未検証）。
局所型は
`hterm : ∀ i ∈ caesuraPositions v, hi s i = hi t i + if s.horizontal k ≤ i then 1 else 0`。
C226・C227の右端の式と既存`Surjection.succAbove_val_eq`、C228の閾値を合わせ、
既存`positionExponent_eq_caesura_sum`・`Finset.sum_add_distrib`・`Finset.sum_filter`へ戻す。
任意の語の位置指数の76,407例の点検は実装前に済ませてある。
200行以内で、同じ有限の分解と加法の法則。検証・監査前にはコミットしない。

### 130.9 依存した組の等式を全体の値へ写す法則

一覧：済み 8／全体 48（うち追加 4）

C225の評価は通ったが、組の等式の部分的なrwは通常の透明性で型を見失うため、
組全体を引数に取る同じ値の関数へ`congrArg`で写す法則を明示する。
新しい構成や仮定ではなく、同じ実境界値への等式の合成。200行以内。
垂直側ではC226・前後の辺の補題がビルド成功。C227・C228に必要な既存
`ShuffleStepMembership`のimportを明示し、同じ主張を再検証する。

```lean
lemma universalBoundaryValue_output_of_pair (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (s : Cut (r + d) q) (k : Fin (r + d + q + 1))
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1)
    (ij : Σ a : Fin (r + 1), Fin (outputDegree s (positiveWord w) a + 1))
    (hp : (colorPositionEquiv s (positiveWord w)).symm k = ij) :
    universalBoundaryValue A S w q x (.inl ⟨s, k⟩) =
      (eqToHom (congrArg (fun n : ℤ => (power (chains A S) (r + 1)).X n) h)).hom
        (outputBoundaryTerm A S s (positiveWord w) ij.1 ij.2 x)
```

C226〜C228と隣接辺の補題は対象ビルドを通った。C229では`rw [Nat.add_zero]`が
暗黙の次元引数を抽象して型を崩すため、同じ算術の等式を`simpa only`で使う形に直す。
水平C223では、依存した組の評価を通した後、同じ移送の合成の照合が残るため、
新しいこのファイルの補助的なbackward/透明性オプションを外し、通常の設定で検証する。
主張・比較する射・公理の仮定は変更しない。

通常の透明性に戻したC223では移送の合成が通り、C229も対象ビルド成功。
最後のC223の値の照合で、追加していた`Nat.add_assoc`と局所名の展開を外し、
既に指定されている同じ次数・点・語のまま、負号と零だけを簡約して等式を使う。
垂直のC226–C229はここまで検証済みだが、専用監査前にはコミットしない。

C223の最後の値の型の診断では、局所名を除いた式の内部表現でも
`r+(d+1)`と`(r+d)+1`の差が残ることを確認した。一般の結合則の展開ではなく、
定義と同じ向きの既存`Nat.add_succ`だけで両方をそろえる。
一時的な`run_tac`の内部表現出力は除去し、本体には残さない。
診断の生データは`/tmp/bsw16/horizontal-actual-expr.txt`・
`horizontal-expected-expr.txt`に保持する。

### 130.10 水平hcのビルド成功

一覧：済み 8／全体 48（うち追加 4）

`universalBoundaryValue_horizontal_neg`が、係数次数零も含めて対象ビルドを通った。
最後の同じ値の照合は`convert ht' using 1`で合同を明示すると閉じ、
補助的に付けていた`rfl`は未使用なので除去した。
同じ元の加群での等式で、ホモトピー圏への弱化や未供給の数学的仮定はない。
同じ`universalBoundaryPartner_neg_of_cases`のhcをそのまま供給する。
垂直のC226〜C229もビルド済みだが、垂直hvの全体やL09a・L09の完了とは数えない。
この後は警告を除いた対象ビルドと全10モジュールの専用監査を行う。

### 130.11 検証・登録候補と約6,600行の区切りの確定

一覧：済み 8／全体 48（うち追加 4）

以下の10本、計 **663行** を対象ビルドと専用監査で検証した。
接頭部は`SerrePositivity.EInfinity.SimplexCuts.`。

| 登録候補 | 実測 |
| --- | ---: |
| `EndpointCoefficientIndices` | 67行 |
| `HorizontalFaceCoordinates` | 44行 |
| `HorizontalFaceTerms` | 108行 |
| `HorizontalBoundaryValues` | 131行 |
| `OutputBoundaryPairedValues` | 46行 |
| `VerticalDeletedMaxima` | 46行 |
| `VerticalVertexEdges` | 67行 |
| `VerticalActiveMaxima` | 47行 |
| `VerticalIntervalThresholds` | 53行 |
| `VerticalDeletionExponents` | 54行 |

最終対象ビルドは`/tmp/bsw16/m14-horizontal-vertical-final.log`、
`HorizontalBoundaryValues`・`VerticalDeletionExponents`の二対象で **2,320 jobs成功・警告0**。
両対象のimportで新規10本を覆う。
専用監査は別の一回の鍵で`/tmp/bsw16/audit-m14-horizontal-vertical-progress.lean`を実行し、
**10モジュール・54宣言・標準三公理のみ**で成功
（`/tmp/bsw16/m14-horizontal-vertical-audit.log`）。
全10モジュールを明示し、それぞれの宣言数が0でないことも確認した。
新規本体のsorry・追加公理0。`run_tac`や一時的なppの診断は本体に残っていない。
`git diff --check`成功。既存公開宣言・共通入口・共通監査・draftsは変更していない。
共通入口・共通監査への登録は調整役の担当のまま。

ビルド・監査はそれぞれ独立した一回の`--class impl --wait 3600`で実行。
整理券は常に一枚、待ち時間と編集・報告の間に鍵は持たず、各実行の終了と返却を確認した。

実際に閉じたもの：

- `universalBoundaryValue_horizontal_neg`：元の全水平添字のhcを、係数次数零も含め仮定なく供給。
  元の同じ加群・指定射での等式で、ホモトピー圏へ弱めていない。
- `positionExponent_vertical_deleted_coordinates`：C226〜C229の有限な幾何を合わせ、
  任意の語の位置指数の差を同じ語の末尾側のcaesura数へ戻す。
  実際の垂直の指定座標は既存C90と端点の公式から次に供給する。

L09a・L09の約6,600行の区切りは、§130の途中で下書き込みの実測を止まらず報告した。
その検証待ちの間に垂直の267行を進め、今回の検証済みの最終累計は
**L09a・L09 6,944行、改訂MayのM14全体12,010行**。
次は垂直の実際の削除係数と入力面の符号、指定面・生成元・実テンソル、全垂直添字のhv、
L09aの対合への包装とL09の微分の和への戻し。
L09a全体・L09はまだ閉じていないため、一覧の完了件数を増やさない。
M14の半分12,500行までは490行で、その時点でも止まらず途中報告する。
L09a・L09の次の1,000行区切りは約7,600行。

### 130.12 実測による残りと外枠の照合

一覧：済み 8／全体 48（うち追加 4）

§121の水平の600〜1,100行に対し、混合角の完了後の5,015行から
水平hcを閉じるまでの実測は **1,662行**（垂直に再利用する共通の順位・次数移送も含む）。
差は **+562〜+1,062行**。依存した面番号と指定された全添字の同値、
共通次数への実際の移送までの照合を含めた増分で、数学の主張の弱化はしていない。
垂直の267行はこの1,662行に重複計上しない。

垂直の残りの見込みは、位置指数が閉じた実測から次のように置く。

| 残りの部分 | 追加の見込み |
| --- | ---: |
| 元の削除係数・全caesura数を合わせた実符号 | 80〜150行 |
| 入力の面を合成した指定面・正規化生成元・実テンソル | 150〜280行 |
| 方向交換で指定された全垂直添字の座標と小さい切断への照合 | 90〜170行 |
| 元の入力境界値への包装とhv | 80〜150行 |
| **垂直の残り** | **400〜750行** |
| L09aの全対合・L09の微分の和への包装 | 200〜350行 |
| **L09a・L09の残り** | **600〜1,100行** |

垂直全体は今回までの267行を含め667〜1,017行の見込みで、
§121の500〜950行の上端より67行高い。指定射を省いた短縮は見込んでいない。
L09a・L09完成時の見込みは **7,544〜8,044行**。
L10以後の既存部分の再利用は§121.3・§121.4のまま、未実装部分を勝手に控除しない。

| M14の部分 | 実測／残り |
| --- | ---: |
| 完成済みMayと現在までの切断 | **12,010行（実測）** |
| L09a・L09の残り | 600〜1,100行 |
| L10〜L28（L12a込み） | 4,330〜7,790行 |
| L29〜L37の係数・ν・top operation | 1,200〜2,000行 |
| L38〜L40のG10後の指定比較への適用 | 500〜900行 |
| L41・L42のfiltered塔とA4の利用側 | 300〜550行 |
| L43a・L43b・L43・L44の二重模型の比較 | 1,500〜2,800行 |
| **残りの合計** | **8,430〜15,140行** |
| **M14完成時の見込み** | **20,440〜27,150行** |

上端は外枠25,000行より **2,150行高い**。外枠を変更した扱いにはせず、
同じ型一覧の中で続ける。旧coherent経路10,216行は保持し、改訂Mayに二重計上しない。
G10・③-bの橋そのもの、M15・G12のLeanは作っていない。

## 131. 垂直の実際の削除係数を入力符号へ接続する（11-14）

一覧：済み 8／全体 48（うち追加 4）

前ターンは水平hcと垂直C226〜C229を検証・コミットした進捗。
枝a1dabccd9とクリーンな作業木を確認して続行。M14実測12,010行、
12,500行の半分報告まで490行である。B4は完了済み。

### 131.1 同色の直前の位置と、両端を含む垂直頂点（C230〜C233）

同じL09aの有限計算と既存の削除係数の法則。実装前に
`/tmp/bsw16/check-adjacent-deletion-coefficients.py`で任意の語の隣接同色対を
**6,678例** 点検した。垂直頂点の係数の14,942例の点検も§130で先に済ませてある。
C230は直前の出現集合の最大が隣接位置になることと既存C135を使う。
C231は既存の垂直辺の判定、C232は既存C170の接頭順位、C233は既存の正次数の法則へ戻す。
新しい作用や構成は作らない。各補題200行以内。
局所型`hprev : previousVertex v b hp = a`、`hf`は既存の最終出現の削除係数の等式、
`hr`は既存C135の隣接順位の式。C231の`he`は指定辺の始端または終端の一致、
C232の`hcolor`は同じ垂直辺の両端の色の一致。

```lean
lemma deletionCoefficient_eq_rank_of_adjacent {N r : ℕ} (v : Fin N → Fin r)
    (a b : Fin N) (hab : b.val = a.val + 1) (hcolor : v a = v b) :
    Surjection.deletionCoefficient v b = (-1 : ℤ) ^ Surjection.caesuraRank v b

lemma vertical_vertex_active_or_incoming {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical) :
    Surjection.Caesura (label s v) k ∨
      ∃ e : Fin (m + (q + 1)), e.succ = k ∧ e ∉ s.val

lemma deletionCoefficient_vertical {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical) :
    Surjection.deletionCoefficient (label s v) k =
      (-1 : ℤ) ^ ((s.vertical k).val + Surjection.caesuraRank v (s.horizontal k))

lemma outputDegree_pos_vertical {m q r : ℕ} (s : Cut m (q + 1))
    (v : Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical) :
    0 < outputDegree s v (label s v.val k)
```

### 131.2 元の語の次数と入力面番号への実符号の比較（C234〜C236）

一覧：済み 8／全体 48（うち追加 4）

既存構成の符号の法則の貼り合わせ。C234は既存`Word.card_caesuras`と有限集合の
接頭/末尾の分割を使い、濃度の新しい定理は作らない。C235はC229とC234の
自然数の加法の等式。実装前に`/tmp/bsw16/check-vertical-exponent-balance.py`で
**14,942例** の指数の整数としての完全な等式を点検した。
C236は既存C127・C180とC232を合わせ、C235で同じ入力面の符号へ戻す。
座標`hh`・`hv`は、既存C90と端点/全添字の式から後で供給する。未供給のままhv全体の完了とは扱わない。
個々の補題200行以内。局所型`hcard : (caesuraPositions v.val).card = m+1-r`、
`hp`はC229の位置指数の式、`hc`はC234の区切り数の式、
`hperm`はC180による同じ削除色列の逆転符号の一致。

```lean
lemma caesuraRank_add_tail_card {m r : ℕ} (v : Surjection.Word r (m + 1))
    (a : Fin (m + 1)) :
    Surjection.caesuraRank v.val a +
      ((caesuraPositions v.val).filter (fun i => a ≤ i)).card = m + 1 - r

lemma positionExponent_plus_vertical_rank {m q r : ℕ} (s : Cut m (q + 1)) (t : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) :
    positionExponent s v.val +
        ((s.vertical k).val + Surjection.caesuraRank v.val (s.horizontal k)) =
      (m + 1 - r + (s.vertical k).val) + positionExponent t v.val

lemma outputBoundarySignAt_vertical_of_coordinates {m q r : ℕ} (s : Cut m (q + 1)) (t : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) :
    outputBoundarySignAt s v k =
      (-1 : ℤ) ^ (m + 1 - r + (s.vertical k).val) * cutSign t v.val
```

### 131.3 入力の単体射を合成した指定面（C237〜C239）

一覧：済み 8／全体 48（うち追加 4）

C230〜C236の対象ビルドが成功。次は既存C185・C186と同じ次数・指定面の照合を、
入力射`g`の像の色列へ使う。既存の公開宣言は変更せず、新しい名前で足す。
C237は既存の単体射の合成とList.mapの法則、C238は既存C150・C151とList.length_map、
C239は既存C156・C40と同じ頂点列の単射性を使う。新しい構成やホモトピーは作らない。
実装前に`/tmp/bsw16/check-vertical-mapped-vertices.py`で
実際の垂直削除の各色の列と入力面による像の列を **76,407例** 点検した。
個々の補題200行以内。局所型`hsrc`はC238の次数の族の等式を一色で評価したもの。

```lean
lemma simplexVertexList_postcomp {n q q' : ℕ}
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) (g : (⦋q⦌ : SimplexCategory) ⟶ ⦋q'⦌) :
    simplexVertexList (f ≫ g) = (simplexVertexList f).map g.toOrderHom

lemma deletedOutputDegree_eq_of_mapped_vertexLists {m n q q' r : ℕ}
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom) :
    Function.update (outputDegree s v) (label s v.val k)
      (outputDegree s v (label s v.val k) - 1) = outputDegree t w

lemma deletedCutFace_eq_of_mapped_vertexLists {m n q q' r : ℕ}
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (c : Fin r) :
    deletedCutFace s v (label s v.val k) hd j c =
      eqToHom (congrArg SimplexCategory.mk
        (congrFun (deletedOutputDegree_eq_of_mapped_vertexLists s t v w k hd g hl) c)) ≫
          (face t w c ≫ g)
```

### 131.4 入力射を合成した実テンソル（C240・C241）

一覧：済み 8／全体 48（うち追加 4）

C237〜C239の対象ビルド成功。C240・C241は既存C188・C189の同じ次数移送に、
C239の指定面と既存の関手の合成則を代入する法則。新しい構成は足さない。
個々の補題は200行以内。以下は実装する宣言の型（証明は省略）。

```lean
lemma deletedCutTensor_eq_mapped_cutTensor {m n q q' r : ℕ} (S : SSet.{0})
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -(degreeSum r (outputDegree t w) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v (label s v.val k) hd j x =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensor A S t w (S.map g.op x))

lemma deletedCutTensor_eq_mapped_cutTensorAt {m n q q' r : ℕ} (S : SSet.{0})
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -((n + q' + 1 - r : ℕ) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v (label s v.val k) hd j x =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensorAt A S t w (S.map g.op x))

```

### 131.5 同じ入力面による各色の列の像（C242・C243）

一覧：済み 8／全体 48（うち追加 4）

C240・C241のビルド成功。既存C90の座標と`selectColor_map`の法則を各色へ適用する。
§131.3の76,407例の点検に含まれる。既存構成の係数移送であり、個々の補題200行以内。

```lean
lemma deletedVerticesList_vertical_of_coordinates {m q r : ℕ}
    (s : Cut m (q + 1)) (t : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + (q + 1) + 1))
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) (c : Fin r) :
    deletedVerticesList s v k c =
      (verticesList t v c).map (s.vertical k).succAbove

lemma deletedVerticesList_vertical_interior {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + (q + 1)))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∉ s.val) (c : Fin r) :
    deletedVerticesList s v a.succ c =
      (verticesList ((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩) v c).map
        (s.vertical a.succ).succAbove

```

### 131.6 検証・実測・次の接続

一覧：済み 8／全体 48（うち追加 4）

新規5本・339行。各モジュールの対象ビルドは成功し、Leanの警告0。
小さい独立監査は **5モジュール・24宣言・標準三公理のみ** で成功。
新規5本にsorry・追加公理0。既存の公開宣言・界面・共通入口・共通監査は変更していない。
`git diff --check`成功。鍵は各対象ビルド・各監査の間だけ取り、終了後返却。

| 登録候補（すべて `SerrePositivity.EInfinity.SimplexCuts.` 以下） | 行数 | 対象ビルド |
| --- | ---: | --- |
| VerticalDeletionCoefficients | 92 | 成功、2,234 jobs |
| VerticalBoundarySigns | 64 | 成功、2,274 jobs |
| MappedDeletedFaces | 58 | 成功、2,185 jobs |
| MappedDeletedTensors | 76 | 成功、2,189 jobs |
| VerticalMappedVertices | 49 | 成功、2,039 jobs |

ログは `/tmp/bsw16/m14-vertical-deletion-coefficients-01.log`、
`m14-vertical-boundary-signs-01.log`、`m14-mapped-deleted-faces-02.log`、
`m14-mapped-deleted-tensors-01.log`、`m14-vertical-mapped-vertices-01.log`。
監査ソースは `/tmp/bsw16/audit-m14-vertical-mapped.lean`、
結果は `/tmp/bsw16/m14-vertical-mapped-audit.log`。
C237の初回ビルドは単体射の合成の定義展開の一行が不足して失敗した。
`rfl`で補い、2回目の対象ビルド成功を検収結果とする。

L09a・L09累計は **7,283行**（6,944+339）、M14全体は **12,349行**。
12,500行の途中報告まで151行、L09a・L09の次の約7,600行の区切りまで317行。
§130.12の完成見込み20,440〜27,150行の上側は依然として外枠25,000行を超える。
この見込みを上限の承認とは扱わず、次の途中報告で残りを出し直す。

今回閉じたのは垂直の実符号と、入力射の像の色列から元の圏での実テンソルへ戻す法則。
C242・C243は実際の内部削除に適用済み。一方、端点と全垂直添字への適用、
実境界項の符号付き等式、`universalBoundaryValue_vertical_neg` の組み立ては残る。
L09a全体を完了とは数えない。次は端点を含む同じ座標の供給と、C236・C241の接続。
B4は595254e10で完了済みのまま。/goalは継続中。

## 132. 垂直端点の列と同じ入力面の実境界項（11-14）

一覧：済み 8／全体 48（うち追加 4）

§131は593c7df71で検証・保存済み。C244・C245は既存の始端・終端の座標式を
C242へ代入する法則。先の76,407例の点検には端点も含まれる。
C246は語の全射性からの次数の計算。C247はC236・C241・C242の貼り合わせであり、
同じ入力面に対する元の圏の厳密な等式を示す。既存の公開宣言の型は変えない。
すべて個々の補題200行以内。以下の型を記録してから検証する。

```lean
lemma deletedVerticesList_vertical_first {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (h₀ : (0 : Fin (m + (q + 1))) ∉ s.val) (c : Fin r) :
    deletedVerticesList s v 0 c =
      (verticesList ((BarrattEccles.verticalInsertionEquiv m q 0).symm ⟨s, h₀⟩) v c).map
        (0 : Fin (q + 2)).succAbove

lemma deletedVerticesList_vertical_last {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a : Fin (m + (q + 1))) (ha : a ∉ s.val)
    (hlast : a.val + 1 = m + (q + 1)) (c : Fin r) :
    deletedVerticesList s v (Fin.last (m + (q + 1))) c =
      (verticesList ((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩) v c).map
        (Fin.last (q + 1)).succAbove

lemma verticalDeletion_degree_eq {m q r : ℕ} (v : Surjection.Word r (m + 1)) :
    -((m + q + 1 - r : ℕ) : ℤ) = -((m + (q + 1) + 1 - r : ℕ) : ℤ) + 1

lemma outputBoundaryTerm_vertical_of_coordinates {m q r : ℕ} (S : SSet.{0})
    (s : Cut m (q + 1)) (t : Cut m q) (v : Surjection.Word r (m + 1))
    (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q + 1⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x =
      (-1 : ℤ) ^ (m + 1 - r + (s.vertical k).val) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (verticalDeletion_degree_eq (q := q) v))).hom
            (cutTerm A S t v (S.δ (s.vertical k) x))

```

### 132.1 全添字への座標の貼り合わせ（C248）

一覧：済み 8／全体 48（うち追加 4）

既存の三分割と水平挿入の座標式を同じ指定切断へ適用する構成の法則。
新しい有限同値は作らない。C248を方向交換して、既存の垂直同値の同じ指定切断を読む。
個々の補題200行以内。以下の型を記録する。

```lean
lemma horizontalBoundaryFaceEquiv_deleted_coordinates (m q : ℕ)
    (c : Fin (m + 2) × Cut m q) (l : Fin (m + q + 1)) :
    let z := (horizontalBoundaryFaceEquiv m q c).val
    z.1.horizontal (z.2.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        c.1.succAbove (c.2.horizontal l) ∧
      z.1.vertical (z.2.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        c.2.vertical l
```

### 132.2 同じ全垂直添字への方向交換（C249・C250）

一覧：済み 8／全体 48（うち追加 4）

C218・C248と既存の`exchange_horizontal`・`exchange_vertical`だけを使う構成の法則。
小さい切断や入力面を別の同値で選び直さない。`hcast`は同じ自然数値のFinの移送と
`succAbove`の可換性、`ht`はC248、`hv`・`hh`は小さい切断の交換公式の適用。
個々の補題200行以内。型は次のとおり。

```lean
lemma verticalBoundaryFaceEquiv_vertical (m q : ℕ) (c : Fin (q + 2) × Cut m q) :
    (verticalBoundaryFaceEquiv m q c).val.1.vertical
      (verticalBoundaryFaceEquiv m q c).val.2 = c.1

lemma verticalBoundaryFaceEquiv_deleted_coordinates (m q : ℕ)
    (c : Fin (q + 2) × Cut m q) (j : Fin (m + q + 1)) :
    let z := (verticalBoundaryFaceEquiv m q c).val
    z.1.horizontal (z.2.succAbove j) = c.2.horizontal j ∧
      z.1.vertical (z.2.succAbove j) = c.1.succAbove (c.2.vertical j)

```

### 132.3 指定された全入力面の実境界項（C251）

一覧：済み 8／全体 48（うち追加 4）

C247へC249・C250を代入する構成の法則。入力面の番号を元の同値の番号で置換し、
型の仮定を追加せず同じ指定項の厳密な一致を得る。個々の補題200行以内。

```lean
lemma outputBoundaryTerm_verticalBoundaryFaceEquiv {m q r : ℕ} (S : SSet.{0})
    (v : Surjection.Word r (m + 1)) (c : Fin (q + 2) × Cut m q)
    (j : Fin (outputDegree (verticalBoundaryFaceEquiv m q c).val.1 v
      (label (verticalBoundaryFaceEquiv m q c).val.1 v.val
        (verticalBoundaryFaceEquiv m q c).val.2) + 1))
    (hj : j.val = vertexRank (verticalBoundaryFaceEquiv m q c).val.1 v.val
      (label (verticalBoundaryFaceEquiv m q c).val.1 v.val
        (verticalBoundaryFaceEquiv m q c).val.2) (verticalBoundaryFaceEquiv m q c).val.2)
    (x : S _⦋q + 1⦌) :
    outputBoundaryTerm A S (verticalBoundaryFaceEquiv m q c).val.1 v
      (label (verticalBoundaryFaceEquiv m q c).val.1 v.val
        (verticalBoundaryFaceEquiv m q c).val.2) j x =
      (-1 : ℤ) ^ (m + 1 - r + c.1.val) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (verticalDeletion_degree_eq (q := q) v))).hom
            (cutTerm A S c.2 v (S.δ c.1 x))
```

### 132.4 全垂直分岐とL09aの貼り合わせ（C252〜C255、L09a）

一覧：済み 8／全体 48（うち追加 4）

C249〜C251の対象ビルド成功、警告0。以下は既存の全境界値・依存した色と面の組・
元の対合の貼り合わせ。C253はC223と同じ次数移送の合成を入力境界の分岐に適用する。
新しい数学の補題ではなく、L09aの未供給のhvと既存の三分岐への接続そのもの。
L09aは§112の型のまま。検証するまでは完了数を増やさない。個々の補題200行以内。

```lean
lemma universalBoundaryValue_input (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (q + 1) × Cut (r + d) (q - 1)) :
    universalBoundaryValue A S w q x (.inr (.inr c)) = simplexBoundaryTerm A S w q c x

lemma universalBoundaryValue_vertical_succ (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q + 1⦌)
    (c : Fin (q + 2) × Cut (r + d) q) :
    universalBoundaryValue A S w (q + 1) x
        (.inl (verticalBoundaryFaceEquiv (r + d) q c).val) =
      -universalBoundaryValue A S w (q + 1) x (.inr (.inr c))

lemma universalBoundaryValue_vertical_neg (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) (hq : 0 < q)
    (c : Fin (q + 1) × Cut (r + d) (q - 1)) :
    universalBoundaryValue A S w q x
        (.inl ((verticalBoundaryAllEquiv (r + d) q hq) c).val) =
      -universalBoundaryValue A S w q x (.inr (.inr c))

lemma boundaryBalancePerm_neg (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : BoundaryBalanceIndex w q) :
    boundaryBalanceTerm A S w q (boundaryBalancePerm w q i) x =
      -boundaryBalanceTerm A S w q i x

theorem boundaryBalance_pairing {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) :
    ∃ τ : Equiv.Perm (BoundaryBalanceIndex w q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        boundaryBalanceTerm A S w q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        boundaryBalanceTerm A S w q (τ i) x = -boundaryBalanceTerm A S w q i x)

```

### 132.5 同じ有限和の相殺（C256）

一覧：済み 8／全体 48（うち追加 4）

C252〜C254の対象ビルド成功。L09aの包装は混合角モジュールのimportを補って再検証する。
C256は既存`Finset.sum_ninvolution`へ同じ対合を渡す法則であり、固定点零を使うため
2が可逆という仮定も加えない。L09の複体の微分の式への照合は別に残る。
個々の補題200行以内。

```lean
lemma sum_boundaryBalanceTerm_eq_zero (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    ∑ i : BoundaryBalanceIndex w q, boundaryBalanceTerm A S w q i x = 0
```

### 132.6 L09aの完了・取り込み点・検証

一覧：済み 9／全体 48（うち追加 4）

**L09a `boundaryBalance_pairing` は§112の型のまま完成**。同じ有限対合の対合性、
固定点での実境界値の零、非固定点の両側の負号による一致を、任意の係数環・単体的集合・
単体に対して元の加群で示した。三分岐のどれも仮定として残していない。
ホモトピー圏への移行や2の可逆性は使わない。C256で同じ全境界項の和が零まで検証済み。
**L09 `cutSum_boundary` の複体の微分の式への照合は未完**なので、完了数を増やすのはL09aの一件だけ。

新規8モジュール・457行、既存公開宣言・界面・drafts・共通入口・共通監査に変更なし。
対象ビルドと専用監査が成功。監査は **8モジュール・32宣言・標準三公理のみ**。
全8本にsorry・追加公理0、最終ソースのLean警告0、`git diff --check`成功。
鍵は各ビルド・監査ごとに取り、終了を確認して返却。一枚だけ並び、待機中の別レーンの
鍵を使うことも、常駐のビルドセッションを置くこともしていない。

登録候補（接頭部はすべて `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 | 検証内容 |
| --- | ---: | --- |
| VerticalEndpointVertices | 46 | 始端・終端の削除色列。最初の2対象ビルドでこの対象自体の生成成功、専用監査でも読込成功 |
| VerticalInputTerms | 54 | 座標を指定した実境界項。最終対象ビルド成功、2,278 jobs |
| AllHorizontalDeletionCoordinates | 93 | 全水平添字の両削除座標。下のVerticalFaceTermsの成功ビルドに含む |
| VerticalFaceCoordinates | 61 | 全垂直添字の両削除座標・入力面番号。下の成功ビルドに含む |
| VerticalFaceTerms | 45 | 指定した同じ入力面の実境界項。最終対象ビルド成功、2,303 jobs |
| VerticalBoundaryValues | 78 | 全境界値のhv。下の成功ビルドに含む |
| BoundaryPairingValues | 47 | 三分岐の貼り合わせ・L09a。下の成功ビルドに含む |
| BoundarySumCancellation | 33 | 同じ全有限和の相殺。最終対象ビルド成功、2,334 jobs |

ログ：`/tmp/bsw16/m14-vertical-input-terms-01.log`（端点の対象自体は成功、別対象失敗）、
`m14-vertical-input-terms-02.log`、`m14-all-face-coordinates-03.log`（水平の対象自体は成功、別対象失敗）、
`m14-vertical-face-terms-02.log`、`m14-boundary-sum-cancellation-01.log`。
専用監査は `/tmp/bsw16/audit-m14-boundary-pairing.lean` と
`/tmp/bsw16/m14-boundary-pairing-audit.log`。
失敗した組全体を成功とは扱わず、該当対象の生成成功と後続の成功ビルド・監査で区別している。
途中の修正は、同値の局所略記の展開、同じFin値の移送、入力面の略記の展開、
混合角のimport不足だけ。新しい数学の前提や追加の構成は導入していない。

### 132.7 約12,500行・約7,600行の途中報告（止まらず継続）

一覧：済み 9／全体 48（うち追加 4）

§131の検証済み12,349行に今回457行を加え、**M14全体12,806行**。
L09a・L09は7,283+457=**7,740行**。旧coherent経路の保管済み10,216行、
報告・監査・Pythonの点検はこれに含めない。未検証の本体下書きは現在ない。
半分の12,500行と、L09a・L09の次の約7,600行の区切りを越えたため、ここで出し直す。
外枠25,000行は変更せず、残り実装可能な枠は **12,194行**。

§130.12の垂直の残り400〜750行に対し、§131の339行と今回の実境界値までの377行、
合計716行を使った。差は **−34〜+316行**（今回の包装・有限和の80行は別計上）。
内部だけでなく全添字へ接続するため、
既存の水平三分割の削除座標を明示し、それを方向交換する2本154行が増えた。
この座標の供給を証明済みと見なして見込みから消したり、同じ式の仮定を残してhv完了とはしなかった。
L09aの包装は今回のBoundaryPairingValuesの47行、有限和の相殺は33行で閉じた。

L09aの残りは0。L09の残りは、零次数も含む次の既存構成の法則と貼り合わせ。

| 残り | 現在の不足 | 新規見込み |
| --- | --- | ---: |
| 出力の微分の和 | 右括弧の同じ純粋テンソルの微分則とgen_dを、指定削除面の全和へ戻す。現在の有限和零をこれだけで微分の式とは呼べない | 250〜450 |
| 係数・入力の和 | 非全射・退化語を零にした係数の微分の実基底の式、および入力の交代面和と同じ指定移送を照合 | 100〜180 |
| L09包装 | 三つの和をC256に代入し、零次数の分岐と共通次数の移送をまとめる | 50〜120 |
| **L09残り** | **L09aをやり直す部分は含まない** | **400〜750** |

前の「包装・L09」200〜350行は、純粋テンソルの一般の微分則を既存の同じ型で直接使えるかの
確認が不足していた。IntervalCutsの区間版の境界定理を一般次元の代用にはしない。
同じ右括弧テンソルの再帰と既存のテンソル微分則を使う法則として型を記録して進める。
L09a・L09の完成時は **8,140〜8,490行** の見込み。

L10〜L28の次元によらないconvolution・χ/TR・符号の再利用の筋と行ごとの見込みは
§121.3・§121.4から変更なし。そこを今回の実測なしに控除しない。

| M14全体の残り | 下端 | 上端 |
| --- | ---: | ---: |
| L09 | 400 | 750 |
| L10〜L28（L12a込み） | 4,330 | 7,790 |
| L29〜L37 | 1,200 | 2,000 |
| G10後のnative Totへの適用 | 500 | 900 |
| filtered塔 | 300 | 550 |
| 二重模型の実現の比較 | 1,500 | 2,800 |
| **新規残り** | **8,230** | **14,790** |
| **実測12,806行を含む完成見込み** | **21,036** | **27,596** |

上側は外枠を **2,596行** 超えるリスクが残る。外枠を上げたとは扱わない。
下端は収まり、現在の実測は外枠に届いていないため、指示どおり止まらずL09へ進む。
次のL09a・L09の1,000行区切りは約8,600行。G10の部品、M15・G12は作らない。

## 133. L09への接続：同じテンソルの微分則の型（実装前）

一覧：済み 9／全体 48（うち追加 4）

§132は56fc86f0bで保存した。L09aの対合・固定点零・全有限和零は検証済み。
次のC257・C258は、既存の右括弧純粋テンソル・生成元・有限和の微分の法則を
同じ出力境界項へ書き直すもの。新しい演算や別の鎖模型は作らない。
C257は`tensorValue`の因子数に沿う再帰、既存`ιTensorObj`の二因子の微分則、
既存`gen_d`を使う。因子の次数零は正次数への延長の零で分ける。
`NegativeTensor.degreeMap_D₁`・`degreeMap_D₂`の零次数と符号の処理も参照できるが、
IntervalCutsの区間上の境界定理を一般単体での証明の代用にはしない。
C258はC257と`map_sum`、共通次数への`eqToHom`の自然性の貼り合わせ。
いずれも§112のL09に必要な既存構成の法則の証明分割で、別の一覧IDを増やさない。

```lean
lemma cutTerm_d_eq_sum_outputBoundaryTerm (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (power (chains A S) r).d (-((m + q + 1 - r : ℕ) : ℤ))
        (-((m + q + 1 - r : ℕ) : ℤ) + 1) (cutTerm A S s v x) =
      ∑ a : Fin r, ∑ j : Fin (outputDegree s v a + 1),
        outputBoundaryTerm A S s v a j x

lemma cutSum_d_eq_sum_outputBoundaryTerm (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q : ℕ} (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌)
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) =
      ∑ s : Cut (r + d) q, ∑ a : Fin (r + 1),
        ∑ j : Fin (outputDegree s (positiveWord w) a + 1),
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (outputBoundaryTerm A S s (positiveWord w) a j x)
```

C258の`h`は算術で常に供給できる等式であり、未供給の数学的仮定としてL09へ残さない。
C257・C258はここでは型の記録だけで、実装・検証・完成行数にはまだ数えない。

### 133.1 既存の因子微分の再帰的評価（C259）

一覧：済み 9／全体 48（うち追加 4）

既存の任意の二複体の`IntervalCuts.tensorPair_d_apply`を、同じtensorValueの右括弧で
繰り返す。`tensorValueDifferentialFactor`は、その微分の各因子の成分を評価する略記で、
新しい作用・微分・複体を構成しない。零番目は先頭の既存微分、後続は先頭のKoszul符号を
掛けた同じ包含。これは§133のC257の出力微分の法則を証明する再帰の証明分割。
個々の補題200行以内。型は次のとおり。

```lean
def tensorValueDifferentialFactor (K : Complex A) : (n : ℕ) → (d : Fin n → ℕ) →
    (∀ i, K.X (-(d i : ℤ))) → Fin n → (power K n).X (-(degreeSum n d : ℤ) + 1)

lemma tensorValue_d_sum (K : Complex A) (n : ℕ) (d : Fin n → ℕ)
    (v : ∀ i, K.X (-(d i : ℤ))) :
    (power K n).d (-(degreeSum n d : ℤ)) (-(degreeSum n d : ℤ) + 1)
        (tensorValue K n d v) = ∑ i : Fin n, tensorValueDifferentialFactor K n d v i
```

### 133.2 同じ生成元の零次数と指定標準面（C260〜C262）

一覧：済み 9／全体 48（うち追加 4）

C259の対象ビルド成功。以下は既存の微分・零延長・gen_d・境界面の次数移送の法則。
C260は両等式の除去、C261は既存`NegativeTensor.isZero_positive`、C262は既存gen_dを
同じ終域の等式射で移す。C262のhはhqから算術で供給する。どの零次数も捨てない。
個々の補題200行以内。以下の型を実装前に記録する。

```lean
lemma complex_d_cast_source_target (K : Complex A) {i i' j j' : ℤ}
    (hi : i = i') (hj : j = j') (x : K.X i) :
    K.d i' j' ((eqToHom (congrArg K.X hi)).hom x) =
      (eqToHom (congrArg K.X hj)).hom (K.d i j x)

lemma gen_d_zero (S : SSet.{0}) (x : S _⦋0⦌) :
    (chains A S).d 0 1 (gen A S 0 x) = 0

lemma gen_d_boundaryFace (S : SSet.{0}) (q : ℕ) (hq : 0 < q) (x : S _⦋q⦌)
    (h : -((q - 1 : ℕ) : ℤ) = -(q : ℤ) + 1) :
    (chains A S).d (-(q : ℤ)) (-(q : ℤ) + 1) (gen A S q x) =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ j.val •
        (eqToHom (congrArg (fun t : ℤ => (chains A S).X t) h)).hom
          (gen A S (q - 1) (S.map (boundaryFace q hq j).op x))

```

### 133.3 包含の次数移送と微分零の成分（C263・C264）

一覧：済み 9／全体 48（うち追加 4）

C263は既存の斉次テンソル包含で三つの次数の等式を除去する法則。C264は同じ因子微分の
再帰を辿り、微分零・テンソル零・包含の零保存を使う。C261の零次数因子をC257へ戻す際に使う。
新しい比較射や準同型は作らない。個々の補題200行以内。

```lean
lemma tensorPair_cast_indices (P Q : Complex A) {i j k i' j' k' : ℤ}
    (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j') (hk : k = k')
    (x : P.X i) (y : Q.X j) :
    (eqToHom (congrArg (fun t : ℤ => (P ⊗ Q).X t) hk)).hom
        (ιTensorObj P Q i j k h (x ⊗ₜ[A] y)) =
      ιTensorObj P Q i' j' k' h'
        ((eqToHom (congrArg P.X hi)).hom x ⊗ₜ[A]
          (eqToHom (congrArg Q.X hj)).hom y)

lemma tensorValueDifferentialFactor_eq_zero_of_closed (K : Complex A) (n : ℕ)
    (d : Fin n → ℕ) (v : ∀ i, K.X (-(d i : ℤ))) (i : Fin n)
    (h : K.d (-(d i : ℤ)) (-(d i : ℤ) + 1) (v i) = 0) :
    tensorValueDifferentialFactor K n d v i = 0

```

### 133.4 入力境界の和を同じcutSumへ戻す（C265〜C267）

一覧：済み 9／全体 48（うち追加 4）

同じ入力境界項の定義、有限積の和の添字替え、cutSumの指定次数移送の合成、
既存の整数冪・スカラー作用の法則を使う。新しい切断の同値や数学の主張は加えない。
hは常に算術で供給し、界面やL09の仮定へ残さない。個々の補題200行以内。

```lean
lemma simplexBoundaryTerm_sum_cut (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (i : Fin (q + 2)) (x : S _⦋q + 1⦌)
    (h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1) :
    ∑ s : Cut (r + d) q, simplexBoundaryTerm A S w (q + 1) (i, s) x =
      -((-1 : ℤ) ^ (d + i.val)) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
          (cutSum A S w (S.δ i x))

lemma sum_simplexBoundaryTerm_succ_by_face (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q + 1⦌)
    (h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1) :
    ∑ c : SimplexBoundaryIndex r d (q + 1), simplexBoundaryTerm A S w (q + 1) c x =
      ∑ i : Fin (q + 2), -((-1 : ℤ) ^ (d + i.val)) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
          (cutSum A S w (S.δ i x))

lemma sum_simplexBoundaryTerm_succ (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q + 1⦌)
    (h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1) :
    ∑ c : SimplexBoundaryIndex r d (q + 1), simplexBoundaryTerm A S w (q + 1) c x =
      -((-1 : ℤ) ^ d) •
        ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (cutSum A S w (S.δ i x))

```

### 133.5 同じ純粋テンソルの一因子の線形性（C268・C269）

一覧：済み 9／全体 48（うち追加 4）

既存のテンソル積の一因子の加法性・整数倍と包含の線形性を同じ右括弧で適用する法則。
生成元の微分の面和をC257の同じ更新次数のテンソルへ運ぶ際に使う。
変更しない他の因子の等式を仮定に明示するが、C257の型へ数学的仮定は加えない。
新しいテンソル模型や線形写像を構成しない。個々の補題200行以内。

```lean
lemma tensorValue_sum_factor {J : Type*} [Fintype J] (K : Complex A) (n : ℕ)
    (d : Fin n → ℕ) (v : ∀ i, K.X (-(d i : ℤ)))
    (w : J → ∀ i, K.X (-(d i : ℤ))) (a : Fin n)
    (hv : v a = ∑ j, w j a) (hw : ∀ j b, b ≠ a → w j b = v b) :
    tensorValue K n d v = ∑ j, tensorValue K n d (w j)

lemma tensorValue_zsmul_factor (K : Complex A) (n : ℕ) (d : Fin n → ℕ)
    (v w : ∀ i, K.X (-(d i : ℤ))) (a : Fin n) (z : ℤ)
    (hv : v a = z • w a) (hw : ∀ b, b ≠ a → w b = v b) :
    tensorValue K n d v = z • tensorValue K n d w

```

### 133.6 同じ更新次数への因子微分の移送（C270〜C272、型）

一覧：済み 9／全体 48（うち追加 4）

C270・C271は同じ次数の等式と因子の異種等式を除去するだけの既存構成の照合。
ホモトピー圏は使わず、型が同じになれば元の加群の等式へ戻す。
C272は同じテンソル微分の一因子の成分を、一つだけ次数を下げた同じ純粋テンソルへ
戻すKoszulの法則。先頭・後続に分けた同じ右括弧の帰納でC263・C270・C271を使う。
その後C268・C269で同じ生成元の面和を展開し、既存C161で指定削除テンソルへ接続する。
以下はC270・C271の実装前の型と、C272の残りの証明分割の型。
C272は未実装で、一覧の完了数・検証済み行数へは含めない。

```lean
lemma tensorValue_heq_degree (K : Complex A) (n : ℕ) (d e : Fin n → ℕ)
    (hd : d = e) (v : ∀ i, K.X (-(d i : ℤ))) (w : ∀ i, K.X (-(e i : ℤ)))
    (hv : ∀ i, HEq (v i) (w i)) : HEq (tensorValue K n d v) (tensorValue K n e w)

lemma tensorPair_heq_indices (P Q : Complex A) {i j k i' j' k' : ℤ}
    (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j') (hk : k = k')
    (x : P.X i) (y : Q.X j) (x' : P.X i') (y' : Q.X j')
    (hx : HEq x x') (hy : HEq y y') :
    HEq (ιTensorObj P Q i j k h (x ⊗ₜ[A] y))
      (ιTensorObj P Q i' j' k' h' (x' ⊗ₜ[A] y'))

lemma tensorValueDifferentialFactor_eq_updated_tensor (K : Complex A) (n : ℕ)
    (d e : Fin n → ℕ) (v : ∀ i, K.X (-(d i : ℤ)))
    (w : ∀ i, K.X (-(e i : ℤ))) (a : Fin n)
    (hd : ∀ b, d b = e b + if b = a then 1 else 0)
    (hv : HEq (K.d (-(d a : ℤ)) (-(d a : ℤ) + 1) (v a)) (w a))
    (hw : ∀ b, b ≠ a → HEq (v b) (w b))
    (h : -(degreeSum n e : ℤ) = -(degreeSum n d : ℤ) + 1) :
    tensorValueDifferentialFactor K n d v a =
      (-1 : ℤ) ^ (∑ b ∈ Finset.univ.filter (fun b : Fin n => b < a), d b) •
        (eqToHom (congrArg (fun z : ℤ => (power K n).X z) h)).hom
          (tensorValue K n e w)
```

hd・hv・hwは一因子の同じ微分の値を照合するための引数であり、C257の仮定に残さない。
既存の純粋テンソルと微分の法則で、新しい作用や比較射は作らない。
C270・C271は個々の補題200行以内。C272の実装が200行を超えれば実測も報告する。

### 133.7 C272の実装に使う局所の法則

一覧：済み 9／全体 48（うち追加 4）

§133.6の型のままC272の下書きを書く。`hcast`は
`{M N : ModuleCat A} → (hMN : M = N) → (y : M) → HEq ((eqToHom hMN).hom y) y`、
等式の除去だけ。先頭の`he`は残る次数の族の等式、`htail`はC270、
後続の`htail`は全次数の既存等式から先頭次数を引いた同じ算術の等式。
`hp`は既存の`Fin.sum_univ_succ`で接頭の有限和を分ける法則。
符号の同定には既存`Int.negOnePow_neg`・`Int.coe_negOnePow_natCast`を使う。
新しい数学や比較射は加えない。下書きは検証までコミットしない。

### 133.8 指定削除面の同じ生成元への照合（C273〜C276）

一覧：済み 9／全体 48（うち追加 4）

既存C158・deletedCutFaceの指定始域の等式移送を、同じ生成元の異種等式で読む。
変更しない色の指定面は面番号に依存しないので、C268の他の因子の一致を供給できる。
選んだ色は同じ標準面と元の面の合成。新しい面や比較射は作らない。
個々の補題200行以内。以下の型を検証前に記録する。

```lean
lemma gen_cast_source_heq (S : SSet.{0}) {n n' q : ℕ} (h : n = n')
    (f : (⦋n'⦌ : SimplexCategory) ⟶ ⦋q⦌) (x : S _⦋q⦌) :
    HEq (gen A S n (S.map (eqToHom (congrArg SimplexCategory.mk h) ≫ f).op x))
      (gen A S n' (S.map f.op x))

lemma deletedCutFace_other_eq {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (ha : 0 < outputDegree s v a)
    (j j' : Fin (outputDegree s v a + 1)) (b : Fin r) (hb : b ≠ a) :
    deletedCutFace s v a ha j b = deletedCutFace s v a ha j' b

lemma deletedCutFace_gen_other_heq (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (a : Fin r)
    (ha : 0 < outputDegree s v a) (j : Fin (outputDegree s v a + 1))
    (b : Fin r) (hb : b ≠ a) (x : S _⦋q⦌) :
    HEq (gen A S (outputDegree s v b) (S.map (face s v b).op x))
      (gen A S (Function.update (outputDegree s v) a (outputDegree s v a - 1) b)
        (S.map (deletedCutFace s v a ha j b).op x))

lemma deletedCutFace_gen_self_heq (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (a : Fin r)
    (ha : 0 < outputDegree s v a) (j : Fin (outputDegree s v a + 1)) (x : S _⦋q⦌) :
    HEq (gen A S (outputDegree s v a - 1)
        (S.map (boundaryFace _ ha j ≫ face s v a).op x))
      (gen A S (Function.update (outputDegree s v) a (outputDegree s v a - 1) a)
        (S.map (deletedCutFace s v a ha j a).op x))

```

### 133.9 微分の交代面和を同じ指定削除面へ戻す（C277〜C279）

一覧：済み 9／全体 48（うち追加 4）

既存の加群の等式移送、有限和、整数倍、関手の合成の法則。C279はC262の標準面和を
C276で同じ指定削除面へ移すだけで、新しい微分や比較は作らない。
局所`e`は既存の一因子の更新次数、`f`は標準面の生成元、`g`は指定削除面の同じ生成元、
`he`はFunction.update_self、`hshift`はhaからの整数次数の等式。
`hu`はC262を共通終域で書いた等式、`hcast`は§133.7と同じ加群の等式の除去。
個々の補題200行以内。以下の型を検証前に記録する。

```lean
lemma sum_zsmul_heq {J : Type*} [Fintype J] {M N : ModuleCat A} (h : M = N)
    (c : J → ℤ) (x : J → M) (y : J → N) (hv : ∀ j, HEq (x j) (y j)) :
    HEq (∑ j, c j • x j) (∑ j, c j • y j)

lemma gen_map_comp (S : SSet.{0}) {n m q : ℕ}
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋m⦌) (g : (⦋m⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (x : S _⦋q⦌) :
    gen A S n (S.map (f ≫ g).op x) = gen A S n (S.map f.op (S.map g.op x))

lemma gen_d_heq_sum_deletedCutFace (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (a : Fin r)
    (ha : 0 < outputDegree s v a) (x : S _⦋q⦌) :
    HEq ((chains A S).d (-(outputDegree s v a : ℤ)) (-(outputDegree s v a : ℤ) + 1)
        (gen A S (outputDegree s v a) (S.map (face s v a).op x)))
      (∑ j : Fin (outputDegree s v a + 1), (-1 : ℤ) ^ j.val •
        gen A S (Function.update (outputDegree s v) a (outputDegree s v a - 1) a)
          (S.map (deletedCutFace s v a ha j a).op x))

```

### 133.10 正次数の実因子微分への貼り合わせ（C280、実装前の型）

一覧：済み 9／全体 48（うち追加 4）

C272・C279を同じ更新次数に適用し、C268・C269で一因子の面和と整数倍を展開して、
既存C161の同じdeletedCutTensorへ戻す。新しい作用・面・添字の選択は作らない。
hは既存outputDegree_sumから常に供給できる算術の等式で、C257へ仮定として残さない。
局所dは既存出力次数、eはその一因子の更新、Gは既存指定削除面の生成元の族、
wは指定因子だけを交代面和にした同じ族、W jはその一面の整数倍だけを入れた同じ族。
hd・htは同じ更新次数の等式、hw・hvはC275・C279、hs・hzはC268・C269、hgはC161、
stepは既存の加群の等式移送の合成。個々の補題200行以内。検証までは完了扱いしない。

```lean
lemma cast_tensorValueDifferentialFactor_eq_sum_deletedCutTensor (S : SSet.{0})
    {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (ha : 0 < outputDegree s v a) (x : S _⦋q⦌)
    (h : -(degreeSum r (outputDegree s v) : ℤ) + 1 = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
    (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (tensorValueDifferentialFactor (chains A S) r (outputDegree s v)
          (fun b => gen A S (outputDegree s v b) (S.map (face s v b).op x)) a) =
      ∑ j : Fin (outputDegree s v a + 1),
        (-1 : ℤ) ^ ((∑ b ∈ Finset.univ.filter (fun b : Fin r => b < a), outputDegree s v b) + j.val) •
          deletedCutTensor A S s v a ha j x
```

### 133.11 C257の零次数を含む接続（C281、C257下書き）

一覧：済み 9／全体 48（うち追加 4）

C257の型は§133のまま。正次数の因子はC280、零次数はC261・C264を使い、
既存の同じcutSignとoutputBoundarySignを保持する。
局所hgは`(p : ℕ) → (hp : p = 0) → (y : S _⦋p⦌) →
(chains A S).d (-(p : ℤ)) (-(p : ℤ)+1) (gen A S p y) = 0`で、pの置換後C261。
h0・h1は既存outputDegree_sumの整数次数の等式、hcはC260による同じ微分の移送。
新しい構成や微分の選択は作らない。個々の補題200行以内。下書きは検証までコミットしない。

```lean
lemma tensorValueDifferentialFactor_cut_zero (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (a : Fin r)
    (ha : outputDegree s v a = 0) (x : S _⦋q⦌) :
    tensorValueDifferentialFactor (chains A S) r (outputDegree s v)
      (fun b => gen A S (outputDegree s v b) (S.map (face s v b).op x)) a = 0
```

### 133.12 C258と全境界和の貼り合わせ（C258・C282・C283下書き）

一覧：済み 9／全体 48（うち追加 4）

C258は§133の型のまま、C257・C260と有限和の線形性を適用する。
C282は既存のΣ添字の有限和を展開し、C283は既存C256の三つの和を加群で整理する。
新しい数学や操作は作らない。q=0・d=0も型から除かない。
C283は同じ実境界項の二つの和までであり、係数の元の線形削除微分との照合が残るため、
これだけでL09完成とは数えない。個々の補題200行以内。以下を検証前に記録する。

```lean
lemma cutSum_d_eq_sum_outputBoundaryTerm (S : SSet.{0})
    {r d q : ℕ} (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌)
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) =
      ∑ s : Cut (r + d) q, ∑ a : Fin (r + 1),
        ∑ j : Fin (outputDegree s (positiveWord w) a + 1),
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (outputBoundaryTerm A S s (positiveWord w) a j x)

lemma sum_boundaryBalanceTerm_output_eq_d_cutSum (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (∑ i : OutputBoundaryIndex w q, boundaryBalanceTerm A S w q (.inl i) x) =
      (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x)

lemma cutSum_d_eq_neg_boundarySums (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) =
      -((∑ c : CoefficientBoundaryIndex r d q, coefficientBoundaryTerm A S r d q w c x) +
        ∑ i : SimplexBoundaryIndex r d q, simplexBoundaryTerm A S w q i x)

```

## 134. 同じ切断和の微分への接続の検証・約8,600行の区切り（11-14）

一覧：済み 9／全体 48（うち追加 4）

### 134.1 今回閉じた範囲と残り

§133のC257・C258は、記録した型のまま検証を通した。
任意の係数環・単体的集合・切断・非退化全射語・入力単体について、零次数の因子も含めて
**同じcutTermの微分が全指定出力境界値の和**となり、さらに
**同じcutSumの微分が移送した全出力境界和**となる。
C283でL09aの全境界和の相殺を適用し、元の係数境界と入力境界の二つの和へ戻した。
正の入力次数ではC267により入力境界の和が同じcutSumの交代面和になる。
異種等式は次数の等式移送の照合にだけ用い、C257・C258・C283は元の加群での厳密な等式。

**L09は未完**。残る係数境界の和と元の線形削除微分の照合、およびq=0・d=0を含む
最終の線形境界式の包装を閉じる必要がある。C283だけをL09完成とは数えない。
C257・C258に、未供給の数学的仮定を追加していない。
C258のhは常に算術で供給できる共通次数の等式で、最終のL09の仮定へ残さない。

### 134.2 検証・登録候補・取り込み点

新規12モジュール・**819行**。対象ビルドと専用の小さい監査が成功。
監査は **12モジュール・82宣言・標準三公理のみ**。
新規12本のsorry・追加公理0、最終ソースのLean警告0。
既存の公開宣言・界面・drafts・共通入口・共通監査は変更していない。
鍵は各ビルド・監査の間だけ取り、終了を確認して返却。一枚だけ並び、待機中に別の鍵を取らなかった。

登録候補（接頭部はすべて `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 | 検証済みの内容 |
| --- | ---: | --- |
| HomogeneousTensorDifferential | 58 | 同じ純粋テンソルの微分の因子和、C259 |
| GeneratorDifferentialValues | 63 | 同じ生成元の零次数・標準面和・微分の次数移送、C260〜C262 |
| HomogeneousTensorDifferentialTransports | 54 | 同じ包含の次数移送・微分零の因子の成分、C263・C264 |
| InputBoundarySums | 62 | 同じcutSumの入力面の交代和、C265〜C267 |
| HomogeneousFactorLinearity | 72 | 一因子の有限和・整数倍、C268・C269 |
| HomogeneousTensorHEq | 44 | 同じ次数と因子の値の照合、C270・C271 |
| UpdatedTensorDifferential | 93 | 同じ更新次数のテンソルへのKoszul符号付き移送、C272 |
| DeletedGeneratorValues | 60 | 同じ指定削除面の生成元の照合、C273〜C276 |
| DeletedGeneratorDifferential | 77 | 同じ微分の交代面和から指定削除面への移送、C277〜C279 |
| PositiveOutputFactor | 95 | 正次数因子の微分から実削除テンソルへの接続、C280 |
| CutTermDifferential | 74 | 零次数因子・各切断項の全出力境界、C281・C257 |
| OutputBoundarySums | 67 | 同じcutSumの微分と全実境界和、C258・C282・C283 |

最終の `OutputBoundarySums` の対象ビルドは **成功、2,369 jobs**。
この依存閉包は上のInputBoundarySumsを除く11本を含む。
InputBoundarySumsは先の組で自対象の生成が成功しており、現ソースを専用監査でも読み込んだ。
その先の組全体は別対象の未検証の添字の下書きで失敗したため、組全体を成功とは扱わない。
最終の監査は上の12本すべての宣言元を明示し、各モジュールの監査宣言数が0でないことも検査した。

- 対象ビルド：`/tmp/bsw16/m14-output-boundary-sums-03.log`。
- InputBoundarySumsの生成成功：`/tmp/bsw16/m14-input-sums-and-factor-laws-01.log`。
- 監査ソース：`/tmp/bsw16/audit-m14-tensor-boundary-laws.lean`。
- 監査結果：`/tmp/bsw16/m14-tensor-boundary-laws-audit.log`。

途中のビルドでは、有限添字の既存API・局所の次数の略記の展開・同じ標準面の合成の展開・
加群での有限和の分配・証明が閉じた後の余分な手順を修正した。
一因子の更新次数の同定には既存degreeSum_deleteを、同じ局所の族の型を明示して適用した。
新しい作用・鎖模型・微分・比較射を導入したり、既存の公開宣言を変えて対処していない。
個々の証明は200行以内。未検証の本体下書きは現在ない。

### 134.3 実測と残りの見込み

検証済みの基準§132に819行を加え、**L09a・L09は8,559行**、**M14全体は13,625行**。
約8,600行の41行手前だが、検証済みの束の区切りとしてここで途中報告する。
旧coherent経路の保管済み10,216行・報告・監査・Pythonの点検は数えない。
外枠25,000行は変更せず、現在の残り枠は **11,375行**。

§132.7ではL09の残りを400〜750行としたが、今回819行を使い、係数微分との照合は残った。
一般の二因子の微分公式だけでは、同じ更新次数の全因子の値・一因子の線形性・
零次数・生成元の標準面和・全切断和の次数移送までは供給されず、それぞれを
同じ実テンソルの型で明示する必要があった。この法則の供給を以前は過小評価していた。

残りは次のとおり。L09aの対合や今回閉じた出力側の微分を作り直す部分は含まない。

| 残り | 用いる既存の宣言と接続 | 新規見込み |
| --- | --- | ---: |
| 係数微分の実基底での値 | Surjection.differential_basis・differentialOnWord・generatorとrawComponent_value。非全射・退化な削除は元と同じく零 | 100〜180 |
| 指定係数添字・語長の照合 | 同じFinの等式移送・positiveWord・erase・deletionCoefficientの構成の法則を使い、既存coefficientBoundaryTermの同じ添字と照合 | 100〜170 |
| L09の包装 | C283、上の係数の式、C267の入力の面和、零次数の分岐を同じ線形境界式へまとめる | 100〜150 |
| **L09残り** | **追加の数学的仮定を残さない** | **300〜500** |

§132.7から見た新規総量の出し直しは819+(300〜500)=**1,119〜1,319行**。
旧上端750行を少なくとも369行超える。L09a・L09の完成時は **8,859〜9,059行** の見込み。
次はこの係数微分の同じ実生成元の型を記録してから進める。L09の完了時に実測を報告する。

L10〜L28の次元によらないconvolution・χ/TR・符号の再利用の筋と各行の見込みは
§121.3・§121.4のまま。今回の一因子の線形性・次数移送も再利用できるが、
未実装部分から実測なしに控除しない。

| M14全体の残り | 下端 | 上端 |
| --- | ---: | ---: |
| L09 | 300 | 500 |
| L10〜L28（L12a込み） | 4,330 | 7,790 |
| L29〜L37 | 1,200 | 2,000 |
| G10後のnative Totへの適用 | 500 | 900 |
| filtered塔 | 300 | 550 |
| 二重模型の実現の比較 | 1,500 | 2,800 |
| **新規残り** | **8,130** | **14,540** |
| **実測13,625行を含む完成見込み** | **21,755** | **28,165** |

上側は外枠を **3,165行** 超えるリスクが残る。外枠の追加承認とは扱わない。
現在の実測は外枠に届いておらず、指示どおり止まらずL09の残りへ進む。
G10の部品、M15・G12は作らない。

## 135. L09の残る係数微分の同じ実生成元の型（実装前）

一覧：済み 9／全体 48（うち追加 4）

§134はee5887388で検証・保存済み。次は既存の元の線形削除微分を使い、
非全射・退化な削除を同じく零とした係数境界の和へ接続する。
`Surjection.differential_basis`・`differentialOnWord`・`generator`の実際の定義を確認した。
まず自然な語長のままC284・C285を示し、C286〜C290の等式移送の法則を使って
`positiveWord`が使う同じ添字と語へ戻す。これらは既存構成の基底上の法則・照合で、
新しい数学・作用・微分を作らない。L09の型は弱めない。

```lean
-- C284：元の生成元か零の評価を、同じcutSumか零として読む。
lemma rawComponent_generator (A : Type u) [CommRing A] (S : SSet.{0}) {r d q : ℕ}
    (v : Fin ((r + 1) + d) → Fin (r + 1)) (x : S _⦋q⦌) :
    rawComponent A S r d q (Surjection.generator A v) (ModuleCat.freeMk (ULift.up x)) =
      if hv : Function.Surjective v ∧ Surjection.Nondegenerate v then
        cutSum A S (⟨v, hv⟩ : Surjection.BasisWord (r + 1) d) x
      else 0

-- C285：同じ実基底の元の線形削除微分をrawComponentで評価する。
lemma rawComponent_differential_basis (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q : ℕ} (w : Surjection.BasisWord (r + 1) (d + 1)) (x : S _⦋q⦌) :
    rawComponent A S r d q
        (Surjection.differential A (r + 1) d
          (Surjection.basis A (r + 1) (d + 1) (ULift.up w)))
        (ModuleCat.freeMk (ULift.up x)) =
      ∑ i : Fin ((r + 1) + (d + 1)), Surjection.deletionCoefficient w.val i •
        rawComponent A S r d q (Surjection.generator A (Surjection.erase w.val i))
          (ModuleCat.freeMk (ULift.up x))

-- C286：同じ語長の等式移送を、値の有限添字の移送で読む。
lemma word_cast_val {r ℓ ℓ' : ℕ} (h : ℓ = ℓ') (v : Surjection.Word r ℓ) :
    (Eq.mp (congrArg (Surjection.Word r) h) v).val =
      fun i : Fin ℓ' => v.val (Fin.cast h.symm i)

-- C287：既存削除係数は、同じ語長と指定位置の等式移送を保つ。
lemma deletionCoefficient_cast_length {r ℓ ℓ' : ℕ} (h : ℓ = ℓ')
    (v : Fin ℓ → Fin r) (a : Fin ℓ) :
    Surjection.deletionCoefficient (fun i : Fin ℓ' => v (Fin.cast h.symm i)) (Fin.cast h a) =
      Surjection.deletionCoefficient v a

-- C288：既存の文字削除は、同じ語長と指定位置の等式移送を保つ。
lemma erase_cast_length {r ℓ ℓ' : ℕ} (h : ℓ = ℓ')
    (v : Fin (ℓ + 1) → Fin r) (a : Fin (ℓ + 1)) :
    Surjection.erase
        (fun i : Fin (ℓ' + 1) => v (Fin.cast (congrArg (fun n : ℕ => n + 1) h.symm) i))
        (Fin.cast (congrArg (fun n : ℕ => n + 1) h) a) =
      fun i : Fin ℓ' => Surjection.erase v a (Fin.cast h.symm i)

-- C289：同じ語長の等式移送は、元と同じ有効な語の判定を保つ。
lemma word_valid_cast_length {r ℓ ℓ' : ℕ} (h : ℓ = ℓ') (v : Fin ℓ → Fin r) :
    (Function.Surjective v ∧ Surjection.Nondegenerate v) ↔
      (Function.Surjective (fun i : Fin ℓ' => v (Fin.cast h.symm i)) ∧
        Surjection.Nondegenerate (fun i : Fin ℓ' => v (Fin.cast h.symm i)))

-- C290：同じ語を元の係数加群の自然な語長へ移してから評価する。
lemma rawComponent_generator_cast_length (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q ℓ : ℕ} (h : ℓ = (r + 1) + d) (v : Fin ℓ → Fin (r + 1)) (x : S _⦋q⦌) :
    rawComponent A S r d q
        (Surjection.generator A (fun i : Fin ((r + 1) + d) => v (Fin.cast h.symm i)))
        (ModuleCat.freeMk (ULift.up x)) =
      if hv : Function.Surjective v ∧ Surjection.Nondegenerate v then
        cutSum A S (Eq.mp (congrArg (Surjection.Word (r + 1)) h) ⟨v, hv⟩) x
      else 0
```

C284は元のgeneratorの二分岐とrawComponent_value、C285は元のdifferential_basisと
線形性、C286〜C289はhの等式の除去、C290はhを除去してC284を適用する。
Finの添字替えは既存finCongrの和の保存を使い、追加の有限な対応は構成しない。
その後、coefficientBoundaryTerm_succ_eqの同じ負号・同じ切断の有限和・同じ次数移送を
上の元の線形微分へ照合する。上の型は現時点では紙のみで、実装・検証済み行数へは数えない。

## 136. 係数境界の同じ添字への接続（11-14、型を先に記録）

一覧：済み 9／全体 48（うち追加 4）

C284・C285の対象生成は成功。C286〜C290と次の4法則は、既存のpositiveWordの
等式移送を評価するだけで、新しい有限対応や削除係数を作らない。
C296は元の語長への移送とpositiveWordの移送の合成を、同じ語の厳密な等式で戻す。
C291〜C293・C296は個々の補題200行以内。C294・C295は後の接続に使う番号として空ける。

```lean
lemma positiveWord_cast_val {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) :
    (positiveWord w).val = fun i : Fin (r + d + 1) =>
      w.val (Fin.cast (by omega : r + d + 1 = (r + 1) + d) i)

lemma erase_positiveWord {r d : ℕ} (w : Surjection.BasisWord (r + 1) (d + 1))
    (a : Fin ((r + 1) + (d + 1))) :
    Surjection.erase (positiveWord w).val
        (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a) =
      fun i : Fin (r + d + 1) => Surjection.erase w.val a
        (Fin.cast (by omega : r + d + 1 = (r + 1) + d) i)

lemma deletionCoefficient_positiveWord {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) (d + 1)) (a : Fin ((r + 1) + (d + 1))) :
    Surjection.deletionCoefficient (positiveWord w).val
        (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a) =
      Surjection.deletionCoefficient w.val a

lemma positiveWord_of_cast {r d : ℕ} (w : Surjection.Word (r + 1) (r + d + 1)) :
    positiveWord (Eq.mp (congrArg (Surjection.Word (r + 1))
      (by omega : r + d + 1 = (r + 1) + d)) w) = w

```

### 136.1 同じ指定係数位置の有限和（C294・C295、型）

一覧：済み 9／全体 48（うち追加 4）

C294はC290へ同じ削除語を代入し、C292で元の線形削除の生成元へ戻す法則。
C295は既存C221の同じ切断項を足し、C296で同じ語のcutSumを復元する法則。
局所hlは同じ語長の等式、heはC292とFinの移送の合成、hsはC221、stepは加群の
等式移送の合成。非全射・退化な削除を零とする判定と符号を変えない。
個々の補題200行以内。以下を検証前に記録する。

```lean
lemma rawComponent_generator_erase_positiveWord (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) (d + 1))
    (a : Fin ((r + 1) + (d + 1))) (x : S _⦋q⦌) :
    rawComponent A S r d q (Surjection.generator A (Surjection.erase w.val a))
        (ModuleCat.freeMk (ULift.up x)) =
      if hv : Function.Surjective (Surjection.erase (positiveWord w).val
          (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a)) ∧
          Surjection.Nondegenerate (Surjection.erase (positiveWord w).val
            (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a)) then
        cutSum A S (Eq.mp (congrArg (Surjection.Word (r + 1))
          (by omega : r + d + 1 = (r + 1) + d))
          ⟨Surjection.erase (positiveWord w).val
            (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a), hv⟩) x
      else 0

lemma coefficientBoundaryTerm_sum_cut (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) (d + 1)) (a : Fin (r + d + 2)) (x : S _⦋q⦌)
    (h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1) :
    (∑ s : Cut (r + d) q, coefficientBoundaryTerm A S r (d + 1) q w (a, s) x) =
      if hv : Function.Surjective (Surjection.erase (positiveWord w).val a) ∧
          Surjection.Nondegenerate (Surjection.erase (positiveWord w).val a) then
        -Surjection.deletionCoefficient (positiveWord w).val a •
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (cutSum A S (Eq.mp (congrArg (Surjection.Word (r + 1))
              (by omega : r + d + 1 = (r + 1) + d))
              ⟨Surjection.erase (positiveWord w).val a, hv⟩) x)
      else 0

```

### 136.2 元の線形微分への全和の接続（C297〜C299、型）

一覧：済み 9／全体 48（うち追加 4）

C297は既存finCongrによる同じ添字の和の保存、C285・C293・C294・C295と有限和の
線形性を適用する。零判定は元と同じ。新しい対応は構成しない。
局所heは既存の同じ全語長の等式、hrはそのfinCongrによる和の保存。
C298・C299は元の境界の次数零の分岐を保持した零の全和。個々の補題200行以内。
以下を検証前に記録する。

```lean
lemma sum_coefficientBoundaryTerm_succ (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) (d + 1)) (x : S _⦋q⦌)
    (h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1) :
    (∑ c : CoefficientBoundaryIndex r (d + 1) q,
      coefficientBoundaryTerm A S r (d + 1) q w c x) =
      -((eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
        (rawComponent A S r d q
          (Surjection.differential A (r + 1) d
            (Surjection.basis A (r + 1) (d + 1) (ULift.up w)))
          (ModuleCat.freeMk (ULift.up x))))

lemma sum_coefficientBoundaryTerm_zero (S : SSet.{0}) {r q : ℕ}
    (w : Surjection.BasisWord (r + 1) 0) (x : S _⦋q⦌) :
    (∑ c : CoefficientBoundaryIndex r 0 q, coefficientBoundaryTerm A S r 0 q w c x) = 0

lemma sum_simplexBoundaryTerm_zero (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋0⦌) :
    (∑ c : SimplexBoundaryIndex r d 0, simplexBoundaryTerm A S w 0 c x) = 0

```

### 136.3 元の二つの微分の線形像とL09の包装（C300〜C302、L09の型）

一覧：済み 9／全体 48（うち追加 4）

§108・§112のL09の右辺`cutSumLinear(boundaryCoefficient)`と
`cutSumLinearSimplex(boundarySimplex)`を、既存rawComponent・normalizedComponentへ
元のSurjection.differential・正規化鎖のdを適用した値として明示する記法を置く。
以下の二つはその既存の線形像の略記であり、別の切断作用・微分・鎖模型を構成しない。
とくに全境界和から逆向きに右辺を定義せず、元の二つの微分の像を直接使う。
C300はC297・C298、C301は既存AlexanderWhitney.generator_dとL08の生成元評価、
C302はC267・C299、L09は既存C283とこの二つの同じ線形像を合わせる。
q=0・d=0を除かず、追加仮定はない。個々の補題200行以内。以下を検証前に記録する。

```lean
def cutSumCoefficientBoundary (A : Type u) [CommRing A] (S : SSet.{0}) (r : ℕ) :
    (d q : ℕ) → Surjection.BasisWord (r + 1) d → S _⦋q⦌ →
      (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)

def cutSumSimplexBoundary (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) :
    (q : ℕ) → S _⦋q⦌ → (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)

lemma sum_coefficientBoundaryTerm_eq (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (∑ c : CoefficientBoundaryIndex r d q, coefficientBoundaryTerm A S r d q w c x) =
      -cutSumCoefficientBoundary A S r d q w x

lemma cutSumSimplexBoundary_succ_eq_sum (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q + 1⦌)
    (h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1) :
    cutSumSimplexBoundary A S w (q + 1) x =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
          (cutSum A S w (S.δ i x))

lemma sum_simplexBoundaryTerm_eq (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (∑ c : SimplexBoundaryIndex r d q, simplexBoundaryTerm A S w q c x) =
      -((-1 : ℤ) ^ d) • cutSumSimplexBoundary A S w q x

theorem cutSum_boundary (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) =
      cutSumCoefficientBoundary A S r d q w x +
        (-1 : ℤ) ^ d • cutSumSimplexBoundary A S w q x

```

検証まではL09の完了数へ足さない。C297・C300のhは算術で常に供給し、L09の仮定に残さない。

### 136.4 検証待ちの間の次段L10の既存API点検（紙のみ）

一覧：済み 9／全体 48（うち追加 4）

L10のLeanにはまだ進まず、§121の再利用の筋を本体で確認した。
`IntervalCuts.surjection_d_neg_apply`は区間の入力を含まない次元によらない宣言で、
次の型のまま使える。コピーしてχの微分の比較を作り直す必要はない。

```lean
IntervalCuts.surjection_d_neg_apply (A : Type u) [CommRing A] (n d : ℕ)
    (x : (Surjection.complex A n).X (-((d + 1 : ℕ) : ℤ))) :
    (Surjection.complexXIso A n d).hom
      ((Surjection.complex A n).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ)) x) =
      Surjection.differential A n d ((Surjection.complexXIso A n (d + 1)).hom x)
```

入力の任意の負自然数次数では既存`SimplexCuts.chains_d_neg`を使い、
正次数零は`NegativeTensor.isZero_positive`、χの正次数零は
`Surjection.complex_isZero_positive`を使う。
一般Sの負次数は全て現れうるため、`IntervalCuts.interval_eq_zero_of_other`の
区間に固有の零性は適用対象ではない。
`IntervalCuts.cochainActionComponent_d`の`TensorProduct.ext`・`tensorLift`の組み立ては
§121のとおり再利用できる。

§108.3ではarity零はL14で別に処理する規約であることも確認した。
そのときには一般Sの既存`AlexanderWhitney.cochainCounit`と
`Surjection.zeroAugmentation`（空語を含む）を再利用する。
今回の点検は紙のみで、L10〜L28の未実装行数を控除せず、完了数へ足さない。

## 137. L09の完了・検証・実測（11-14）

一覧：済み 10／全体 48（うち追加 4）

### 137.1 完了した主張

**L09 `cutSum_boundary` は完了**。§108・§112の同じ切断和について、
任意の可換環A・単体的集合S・正のarity r+1・全語次数d・全入力次数qで、
元の二つの微分のLeibniz則を、元の加群の厳密な等式として示した。
q=0・d=0を除いていない。追加の数学的仮定はない。
右辺は元の線形削除微分 `Surjection.differential` と元の正規化鎖微分
`AlexanderWhitney.chains.d` を、既存のrawComponent・normalizedComponentで評価した値。
全境界和の相殺から右辺を逆に定義することはしていない。

```lean
cutSum_boundary (A : Type u) [CommRing A] (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) =
      cutSumCoefficientBoundary A S r d q w x +
        (-1 : ℤ) ^ d • cutSumSimplexBoundary A S w q x
```

専用監査の実行内の `#check @...cutSum_boundary` でも、実際の型が
A・CommRing A・S・r・d・q・w・xだけを引数に持つことを確認した。
arity零は固定した§108.3の規約どおりL14で別に扱い、ここでは元のL09のr+1の型を維持した。
L10やM14全体が完了したとは数えない。

### 137.2 取り込み点・登録候補・検証

新規 **7モジュール・432行**。最終対象ビルドは **成功、2,525 jobs**、
専用の小さい監査は **7モジュール・70宣言・標準三公理のみ**。
新規7本のsorry・追加公理0、Lean警告0、`git diff --check`成功。
未検証の本体下書きは現在ない。
既存の公開宣言・界面・drafts・共通入口・共通監査は変更していない。
鍵は各対象ビルド・各監査の間だけ取り、終了を確認して返却した。
整理券待ちは一枚にまとめ、最大約26分の待機中も別の鍵を取らなかった。

登録候補（接頭部はすべて `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 | 検証済みの内容 |
| --- | ---: | --- |
| CoefficientDifferentialValues | 52 | 元の生成元・線形削除微分の実基底での値、C284・C285 |
| CoefficientLengthTransports | 66 | 同じ語・文字削除・削除係数・有効性・実生成元の語長移送、C286〜C290 |
| CoefficientWordComparisons | 58 | 同じpositiveWordと元の係数語、C291〜C293・C296 |
| CoefficientBoundarySums | 83 | 同じ指定係数位置の生成元と切断の全和、C294・C295 |
| CoefficientDifferentialSums | 64 | 全係数境界和と元の線形微分、二つの次数零の分岐、C297〜C299 |
| CutSumBoundaryInputs | 78 | 元の二つの微分の既存線形像の記法と同じ境界和の照合、C300〜C302 |
| CutSumBoundary | 31 | L09、全次数の同じ切断和のLeibniz則 |

入口は `CutSumBoundary` の一対象がこの7本をすべて依存に含む。
監査では7本の宣言元をそれぞれ明示し、各モジュールの監査宣言数が0でないことも検査した。

- 最終対象ビルド：`/tmp/bsw16/m14-cut-sum-boundary-03.log`。
- 監査ソース：`/tmp/bsw16/audit-m14-coefficient-boundary.lean`。
- 監査結果と定理の実際の型：`/tmp/bsw16/m14-coefficient-boundary-audit.log`。

途中の検証では、語長の算術の等式を明示し、定義上同じ型をタクティクが拾わない箇所を
等式の直接の接続と反射性で照合した。元の語長での有限和は既存finCongrで添字替えした。
未使用の簡約・既に閉じた後の手順の警告を除いた。
新しい数学の仮定、別の切断作用、別の微分、別の比較射を足して対処していない。
個々の補題は200行以内。

### 137.3 実測と見込みの差

§134から432行を加え、**L09a・L09の最終実測は8,991行**、
**M14全体は14,057行**。旧coherent経路の保管済み10,216行、報告・監査・有限点検は除外。
L09a完成時§132の7,740行から見たL09への接続は **1,251行**。
§132の旧上端750行に対して501行増えたが、§134で最後に出し直した残り300〜500行には
今回の432行が収まった。§134のL09a・L09の完成見込み8,859〜9,059行の範囲内。

L09a・L09の残りは0。次は固定した一覧のL10へ進む。
次元によらない既存のχの微分・生成元の外延性・全整数の次数の組み立てを再利用し、
区間の入力に固有の零性や区間の境界定理を一般Sへ適用しない。

| M14全体の残り | 下端 | 上端 |
| --- | ---: | ---: |
| L10〜L28（L12a込み） | 4,330 | 7,790 |
| L29〜L37 | 1,200 | 2,000 |
| G10後のnative Totへの適用 | 500 | 900 |
| filtered塔 | 300 | 550 |
| 二重模型の実現の比較 | 1,500 | 2,800 |
| **新規残り** | **7,830** | **14,040** |
| **実測14,057行を含む完成見込み** | **21,887** | **28,097** |

外枠25,000行は変更しない。現在の残り枠は **10,943行**。
上側が外枠を **3,097行** 超えるリスクは残る。未実装部分から実測なしに控除しない。
現在の実測は外枠に届いていないため、指示どおり止まらずL10へ進む。
G10の部品、M15・G12は作らない。B4は595254e10で完了済みのまま。

