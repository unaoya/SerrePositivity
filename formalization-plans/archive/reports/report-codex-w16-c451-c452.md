# BS-W16 の報告（report-codex-w16.md） — §32 承認後の再開：C451・C452（§220〜§291、2026-11-14〜11-15）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 220. §32承認による再開（11-14夜）

一覧：済み 12／全体 48（うち追加 4）

ユーザー承認のmain 81a3a3b31（W16 §32）をmath/bs-implへfast-forwardで取り込んだ。
§208・§219の外枠による停止条件は、この明示の承認で解消された。
外枠は**31,000行**へ変更、約**25,000行**で止まらず途中報告。
型つき一覧48本と数え方・G10の部品を作らない規則は維持する。
開始時実測18,308行、L12a3,101行、未検証のLeanはなし。

§205の残り色の全位置・全頂点の順序同値から実装を再開する。
完備化後のP⁰については§32の三案(a)(b)(c)を別に紙で比較し、仮定で隠さない。
(c)が必要と判明したときはD79の判断に関わるため止まって報告する。
G10・M15・G12・drafts・界面・他レーンのファイルには触れない。

§205の最初の有限比較を実装前に点検した。
`/tmp/bsw16/check-remaining-word-positions.py`：12,233組の元の合成切断の点検へ、
全ブロックの最初の位置の狭義順序と、残り色の全出現位置・濃度の一致を加え、全例で一致。
これはLeanの全称証明とは別の点検。型は§205のままで、同じ既存構成の法則・証明分割。

## 221. C451の既存区間移送の証明分割（§205の続き）

一覧：済み 12／全体 48（うち追加 4）

`colorPathOrderIso`を、同じ指定二座標の写像・その座標の法則・狭義単調性へ分割する。
新しい作用や定理の追加ではなく、§205の同じ既存構成の法則。各証明200行以内。
以下の共通変数のもとでの補助の型を記録する。

```lean
variable {m m' q r r' : ℕ} (s : Cut m q) (t : Cut m' q)
  (u : Surjection.Word r (m + 1)) (v : Surjection.Word r' (m' + 1))
  (a : Fin r) (b : Fin r')
  (e : ↥(Surjection.occurrences u.val a) ≃o ↥(Surjection.occurrences v.val b))
  (hl : ∀ p, lo s p.val = lo t (e p).val)
  (hr : ∀ p, hi s p.val = hi t (e p).val)

def colorPathMap (x : ↥(colorPositions s u.val a)) : ↥(colorPositions t v.val b)

lemma colorPathMap_coordinates (x : ↥(colorPositions s u.val a)) :
  t.horizontal (colorPathMap s t u v a b e hl hr x).val =
    (e ⟨s.horizontal x.val, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp x.property).2⟩⟩).val ∧
  t.vertical (colorPathMap s t u v a b e hl hr x).val = s.vertical x.val

lemma colorPathMap_strictMono : StrictMono (colorPathMap s t u v a b e hl hr)
```

これをC451hへ渡す残り色の同じ指定面の比較の型は次。
元のSigmaの等式であり、ホモトピー圏へ弱めない。退化した切断にも適用する。

```lean
lemma positiveComposite_remaining_face {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (a : {a : Fin (m + 1) // a ≠ k}) :
    (⟨outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) a.val,
       vertices (positiveCompositeOuterCut u v k c) (positiveWord u) a.val⟩ :
        Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) =
      ⟨outputDegree c.2 (positiveCompositeCutWord u v k c.1)
          (BarrattEccles.remainingPosition m (n + 1) k a),
       vertices c.2 (positiveCompositeCutWord u v k c.1)
          (BarrattEccles.remainingPosition m (n + 1) k a)⟩
```

元の同じブロックの最初＝最後（non-slot）、同じ両端、§205の出現位置の順序同値、
上の全頂点の順序同値、`faceData_eq_of_colorOrderIso`を順に使う。
挿入色・符号・L12a全体が閉じたとは扱わない。

## 222. §205の残り色の比較：検証済み・取り込み点

一覧：済み 12／全体 48（うち追加 4）

新しい5本306行を検証した。全出現位置の順序同値を、同じ区間の両端を使って全頂点へ
持ち上げ、元のSigma型の中で残り色の指定面を厳密に照合した。非退化性は仮定しない。
新しい公理・sorryなし。既存の公開宣言・界面・drafts・共有入口は変えていない。

対象ビルド：`m14-remaining-word-positions-01.log`（2,859 jobs）、
`m14-remaining-color-faces-01.log`（2,863 jobs）、ともに成功・対象警告0。
`ColorPathTransport`の最初の二回は簡約とsubtypeの所属証明の明示で修正し、最後のビルドで検証した。
小さい監査：`/tmp/bsw16/audit-m14-remaining-color-faces.log`、
**5モジュール・27宣言、標準三公理のみ**。鍵はビルド・監査ごとに取得し、終了時に返した。

調整役が登録すべきモジュール（共通接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

- OccurrenceCardinalities（25行）
- CompositeFirstPositionOrder（31行）
- RemainingWordPositions（65行）
- ColorPathTransport（140行）
- RemainingColorFaces（45行）

M14実測**18,614行**、L12a実測**3,407行**。一覧の完了は12/48のまま。
§207の残り色の160〜280行に対し実測306行（上端から26行増）。
他の行を据え置いた完成見込みは**25,331〜30,771行**で、31,000行の外枠内だが余裕は小さい。
挿入色・符号・nullary・後段を完成済みとして控除していない。

## 223. 完備化後のP⁰：§32の三案の比較（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

### 223.1 比較する対象を固定する

`K`はrawなFrobenius塔の余極限をmod pしてκへ制限した台、
`Y`は**実際の**`directPerfectionValue`をmod pしてκへ制限した台とする。
`Y ≅ LΛ_d K`という単位・Frobeniusを保つ比較自体も供給義務として数える。
以下のprincipal completionの計算を、その比較を証明せずにYへ適用しない。
記法はcochain次数、Π_n = H^{-n}。Frobeniusは係数の半線形性も保持する。

BS著者版Definition 8.2は完備化後を定義し、Lemma 8.4はlevelwise FrobeniusとP⁰を
使っている。rawな対象へのL42・L44だけでこの完備化の比較も終わったとは読まない。
原典の主張への反例を述べているのではなく、現在の模型での証明義務の切り分けである。
出典：[BS著者版 §8](https://www.math.uni-bonn.de/people/scholze/prisms.pdf)。

### 223.2 (a) 各項を完備化した二重模型

**各項を完備化するだけでは足りない。** 完備反射Lは完備対象の圏で余極限を保つが、
その圏の包含がambientな単体的実現を保つことは別である。
L44で使うのはambientなdirect-sum totalであり、完備圏の余極限への変更ではない。

台の複体だけでも障害が見える。R=κ[[d]]とし、正規化した外側の単体次数sの複体を
cochain次数sにRを一つ置いたものにする（微分と正規化単体微分は零）。
各単体次数の非正規化項はこれらの有限直和なのでd完備だが、実現の次数0は
⊕_{s≥0} Rとなる。これはd完備ではない：完備化に存在するΣ_s d^s e_sが直和に入らない。
従って項ごとの完備性だけから、ambientな同じ実現が完備になるとはいえない。
この例は二重模型での自由な交換に対する点検であり、実際のA4の模型が交換不能だと
証明する例ではない。

可能性を残す経路は、元の模型にd進フィルトレーションを保持し、完備totalを作り、
元の有限p入力の作用・明示primitiveを連続に延長して、**同じ指定Frobenius**を比較するもの。
ただし次をまだ証明していない。

1. 完備totalが実際の`directPerfectionValue/p`を表すこと。
2. BF/Mayの指定作用とprimitiveが、必要なフィルトレーションを保ち、完備totalへ延長すること。
3. 元のnative実現と同じFrobeniusの辺への比較。

これは各項を置換するだけの照合ではなく、連続な作用の延長と完備totalの比較という
数学的な仕事を要する。現在の48本へ証明済みの法則として紛れ込ませない。
各項を完備化しただけのMで§217.1のeを供給できる、とはまだ結論しない。

### 223.3 (b) 単位の全射性・同型性と、別方向からの検出

**coconnective性だけでは単位はΠ_0上で全射にならない。**
κ[t]→κ[[t]]は離散な環の導来t完備化の単位であり、1/(1-t)は像に入らない。
tは非零因子なので、この例では導来と通常の完備化の差もない。
従って§216.3のEpiをcoconnective性から供給してはならない。
一般のΠ_nについても、完備化単位の同型性を追加仮定としてA4へ持ち込まない。

単位とは反対向きの、商の塔への射による検出は別の候補になる。
K_r = K ⊗^L (A --d^r→ A)とすると、逆極限の核にはlim¹ H^{i-1}(K_r)がある。
この項を無視して「各商で一致すれば一致」とはしない。
principal completionのTate項とlim¹項は
[Stacks Example 15.95.5・Lemma 15.95.6](https://stacks.math.columbia.edu/tag/0BKF)
で確認した。naiveな商A/d^rで置き換える際のbaseの冪ねじれ条件も別である。

ここからの**自分の推論としての候補**は次。
rawなKに対してL42・MayからH^i(K)=0 (i<0)、H^0(K)のFrobeniusが同型と
証明できれば、H^0(K)はreducedであり、そのd冪ねじれはdで殺される。
実際d^r a=0なら(da)^r=0なのでda=0。
従ってそのTate moduleは零、またK_rのH^{-1}の系はpro-zeroとなる。
これにより次の二つを導ける見込みがある。

- LΛ_d Kはcoconnective。これはA4(a)に必要なΠ_n=0 (n>0)を直接与える候補。
- H^0(LΛ_d K)→lim_r H^0(K_r)は単射。従って、**同じ指定FrobeniusとP⁰が各K_rで
  一致すると証明した後なら**、Π_0での一致を検出できる。

ただしH^0(LΛ_d K)を通常のH^0(K)の完備化と同一視しない。
T_d(H^1(K))が残り得るためであり、その消滅を仮定として足さない。
この候補は単位のEpiを置き換えるもので、既存のL44からの即時の帰結ではない。
特に**各K_rで同じFrobeniusを比較する義務が残る**。
rawな辺をd^rのKoszul商へ運ぶ際、d↦d^pとKoszul生成元の写り方も保持しなければならない。
rawなH^0上で一致することだけでは、商のTor由来の元の一致は示していない。

本体で確認した再利用候補は`complexCompletionReductionIso`、
`complexCompletionUnit_koszul_quasiIso`（任意の複体の元の単位のKoszul比較）、
`derivedComplexCompletionFunctor_homology_isModuleComplete`（実際のホモロジーの完備性）。
`completionUnit_tensor_module_powerTorsion_isIso`はMinusの版であり、
coconnectiveな任意のKへそのまま適用する一般版ではない。
これらはP⁰と商での指定Frobeniusの一致や、Yとのnativeな比較を供給する宣言ではない。

### 223.4 (c) coherentな議論が必要になる場合の境界

現時点では**(c)が不可避とは結論していない**。
(a)の連続な鎖計算や(b)の商・Π_0の検出をまだ排除できず、APIが見つからないことを
coherentなP⁰が数学的に必要という理由にはしない。
一方、現状のho(CAlg)上のP⁰の自然性だけで完備化を越えた、とも結論しない。

もし(b)の商での照合ができず、完備化の極限そのものにP⁰を運ぶことが必要になるなら、
最小限でも**同じ完備化塔に沿う高次に整合した演算と指定錐の比較**が要る。
ho上の自然性は射のホモトピー類の等式だけなので、その高次整合性を供給しない。
単に各段で代表射を選び、native極限の射へ昇格させることはしない。

一般のcoherent Sp値P⁰へ戻る場合、§110.2(b)の残り13,300〜24,500行は、
既存V・π/H・鎖模型10,216行を既に除いた見込みである。
Mayの18,614行をさらに機械的に控除することはできない。
特定の完備化塔だけのcoherentな比較ならこれより短い可能性はあるが、
塔の演算・同じ指定錐・πとの比較の構成を決めておらず、現在は信頼できる行数を出せない。
この経路が必要と判明した時点で、§32に従いLeanを止め、D79への判断を報告する。
今回、その経路のLean・界面変更・新しい仮定の追加はしていない。

### 223.5 当面の結論と残る検収点

(a)は「各項を完備化すればよい」という短縮では閉じない。
(b)の単位による消去も、coconnective性だけでは閉じない。
ただし(b)の**逆向きの射によるΠ_0の検出**は、A4に必要な次数を分けて扱う候補として残る。
Π_n (n>0)はrawのcoconnective性とH^0のreduced性を使った完備化の計算、
Π_0はKoszul商での同じFrobeniusの照合という、別の証明義務になる。
すべての整数次数での「完備化単位はEpi」を仮定して隠す案は採らない。

この紙の比較は、完備化後のP⁰の照合を完了した報告ではない。
未供給の比較や新しい完備化定理を48本へ自己承認で追加せず、L12aの既存の証明を進める。
(c)が必要と分かったという停止報告でもない。

## 224. C451hの挿入色への係数移送（既存の法則の証明分割）

一覧：済み 12／全体 48（うち追加 4）

次に挿入色の頂点を、外側の指定面ρを通して元の単体へ読む。
§203の同じ順序列挙の法則をρ付きに述べ直す。新しい作用や同値の構成ではない。
全頂点の順序同値そのものはまだ仮定であり、供給済みとしない。
証明は200行以内、元の次数のSigmaの等式を保つ。

```lean
lemma faceData_comp_eq_of_colorOrderIso {m m' q q' r r' : ℕ}
    (s : Cut m q) (t : Cut m' q')
    (u : Surjection.Word r (m + 1)) (v : Surjection.Word r' (m' + 1))
    (a : Fin r) (b : Fin r') (ρ : Fin (q' + 1) →o Fin (q + 1))
    (e : ↥(colorPositions s u.val a) ≃o ↥(colorPositions t v.val b))
    (hv : ∀ x, s.vertical x.val = ρ (t.vertical (e x).val)) :
    (⟨outputDegree s u a, vertices s u a⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) =
      ⟨outputDegree t v b, ρ.comp (vertices t v b)⟩
```

有限点検は§220の12,233組で既に同じ内側面・外側面の合成を全ての色で比較済み。
この一般の移送の法則だけで、挿入色の順序同値やC451全体が完成したとは扱わない。


## 225. C451の元の挿入部分語の位置（既存の語長移送）

一覧：済み 12／全体 48（うち追加 4）

`IntervalCuts.compositeSegmentPosition`とその`_value`が既に一般の重なる分割である。
新しい位置の選択をせず、その同じ値をpositiveCompositeCutWordの語長で読む。
C451の同じ指定面の照合の法則として型を記録する。各証明200行以内。

```lean
def positiveCompositeSegmentPosition {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    Fin (m + n + (d + e) + 1)

lemma positiveCompositeSegmentPosition_val {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    (positiveCompositeSegmentPosition u v k r i z).val =
      compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + z.val

lemma positiveCompositeSegmentPosition_label {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    (positiveCompositeCutWord u v k r).val (positiveCompositeSegmentPosition u v k r i z) =
      BarrattEccles.insertedPosition m (n + 1) k
        (v.val ⟨r.start i + z.val, by
          have h := r.start_add_length_le i; have hz := z.isLt; omega⟩)
```

実装前の有限点検：`/tmp/bsw16/check-composite-segment-positions.py`。
12,233組・非退化3,745組で、部分語の全相対位置について、元の外側位置・内側位置・
挿入ラベルが同じことを確認した。元の脚・色の順序・符号は変えない。
この位置の法則を示しただけでは、内側Cutの全頂点の順序同値はまだ供給していない。

## 226. 挿入色の比較の前段：検証済み・取り込み点

一覧：済み 12／全体 48（うち追加 4）

§224・225の2本96行を検証した。既存の全頂点の順序列挙を外側の指定面との合成へ
適用する法則と、既存の挿入部分語の全位置・同じ挿入ラベルの語長移送まで。
挿入色の全頂点の順序同値・指定面の比較そのものは未完で、仮定を追加して閉じていない。

対象ビルド：`/tmp/bsw16/m14-composite-segment-positions-01.log`、
2,849 jobs、成功・対象Lean警告0。
小さい監査：`/tmp/bsw16/audit-m14-inserted-face-transports.log`、
**2モジュール・10宣言、標準三公理のみ**。
対象ビルドと監査は別々に鍵を取得し、終了時に返した。
`git diff --check`成功。新しいsorry・公理なし。

調整役への追加の登録対象：

- `SerrePositivity.EInfinity.SimplexCuts.FaceDataCompositionTransport`（42行）
- `SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentPositions`（54行）

今回§222と合わせて**7本402行**、対象の小監査は合わせて**37宣言**。
M14実測**18,710行**、L12a実測**3,503行**。
一覧は12/48（追加4）のまま。次は同じ元の挿入部分語の位置と内側Cutの順位を接続し、
挿入色の全頂点の順序同値をC451hへ渡す。B4はやり直さず、mainや他レーンのファイルは触っていない。

旧§219の停止理由は§32によって解消され、実際の証明作業は再開済み。
ただし本ターンの`get_goal`が返したUI上のstatusは依然`blocked`だった。
利用可能な`update_goal`の引数はcomplete/blocked/pausedのみで再開操作はなく、
`create_goal`で未完の目標を置き換えることも契約上できないため、statusをactiveへ更新できていない。
完了や別のblockedを設定することでこの差を隠さない。これは数学的な再停止判断ではない。


## 227. C451の挿入部分語の元の全頂点と外側順位（法則の型）

一覧：済み 12／全体 48（うち追加 4）

元の部分語内の位置を挟む最初・最後の合成位置を使い、同じ合成Cutの頂点の高さを
元の外側区間の高さとして読み、その区間の既存colorHeightRankへ渡す。
新しい経路や順位を選ばず、既存の指定二座標・順位の合成の法則として分割する。
各証明200行以内。ここでは内側Cutに属することはまだ主張しない。

```lean
variable {m n d e q : ℕ}
  (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
  (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
  (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)

lemma positiveCompositeSegmentPosition_bounds :
  compositeFirstPosition u v k c.1 (positiveOccurrencePosition u k i) ≤
      positiveCompositeSegmentPosition u v k c.1 i z ∧
    positiveCompositeSegmentPosition u v k c.1 i z ≤
      compositeLastPosition u v k c.1 (positiveOccurrencePosition u k i)

lemma positiveCompositeSegment_outer_bounds
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
  lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) ≤
      (c.2.vertical x).val ∧
    (c.2.vertical x).val ≤
      hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i)

def positiveCompositeSegmentVertexRank
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
  Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1)

lemma positiveCompositeSegmentVertexRank_vertices
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
  vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k
    (positiveCompositeSegmentVertexRank u v k c i z x hx) = c.2.vertical x
```

有限点検：`/tmp/bsw16/check-composite-segment-ranks.py`、12,233組・非退化3,745組。
全ての挿入色の元の経路頂点について、元の外側区間への所属と、
最初の色別順位＋高さの差で読む同じ順位・同じ頂点を確認した。
型つき一覧の新しい項目は増やさない。


## 228. C451の挿入頂点の内側順位への所属（法則の型）

一覧：済み 12／全体 48（うち追加 4）

元の外側の一つの色別区間の上でverticesが順序を反映することを、既存の
`vertices_on_colorIntervalRanks`の同じ高さの差の式から読む。
挿入部分語の内側番号はstart＋相対位置という同じ番号の移送だけ。
その順位が内側Cutの同じ区間内に入ることを、元の内側辺の高さと比較する。
左の辺の所属番号はi以下、右の辺の所属番号はi以上。同じ所属なら高さを比較し、
異なる所属なら`colorIntervalRanks_ordered`を使う。各証明200行以内の見込み。

```lean
lemma vertices_le_iff_on_colorInterval {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (i j : Fin (outputDegree s v a + 1))
    (hi : i ∈ colorIntervalRanks s v a p) (hj : j ∈ colorIntervalRanks s v a p) :
  vertices s v a i ≤ vertices s v a j ↔ i ≤ j

variable {m n d e q : ℕ}
  (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
  (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
  (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)

def positiveCompositeSegmentInnerPosition : Fin (n + e + 1)

lemma positiveCompositeSegmentVertexRank_mem
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
  positiveCompositeSegmentVertexRank u v k c i z x hx ∈
    colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i)

lemma positiveCompositeSegmentRank_inner_bounds
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
  lo (positiveCompositeInnerCut u v k c) (positiveCompositeSegmentInnerPosition u v k c i z) ≤
      (positiveCompositeSegmentVertexRank u v k c i z x hx).val ∧
    (positiveCompositeSegmentVertexRank u v k c i z x hx).val ≤
      hi (positiveCompositeInnerCut u v k c) (positiveCompositeSegmentInnerPosition u v k c i z)
```

この所属を示した後、元の`coordinates_of_interval`で同じ二座標の内側頂点を読む。
新しい作用の定理や別の経路を作るのではなく、C451の指定頂点の照合の証明分割である。
有限点検は§227と同じ元の切断の12,233組を使う。


## 229. C451の同じ内側経路の頂点と二段の面（法則の型）

一覧：済み 12／全体 48（うち追加 4）

§228の同じ区間への所属を、既存の`coordinates_of_interval`へ渡す。
同じ内側番号と外側順位の二座標で元の頂点を読み、指定面と挿入ラベルを照合する。
全頂点の同値や逆写像はまだ主張しない。同じ指定座標の合成の法則で、各証明200行以内。
有限点検は§227の12,233組の同じ内側経路・元の外側順位を使う。

```lean
def positiveCompositeSegmentInnerVertex {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    Fin (n + e + outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1)

lemma positiveCompositeSegmentInnerVertex_coordinates {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    (positiveCompositeInnerCut u v k c).horizontal
        (positiveCompositeSegmentInnerVertex u v k c i z x hx) =
        positiveCompositeSegmentInnerPosition u v k c i z ∧
      (positiveCompositeInnerCut u v k c).vertical
        (positiveCompositeSegmentInnerVertex u v k c i z x hx) =
        positiveCompositeSegmentVertexRank u v k c i z x hx

lemma positiveCompositeSegmentInnerVertex_vertices {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k
      ((positiveCompositeInnerCut u v k c).vertical
        (positiveCompositeSegmentInnerVertex u v k c i z x hx)) = c.2.vertical x

lemma positiveCompositeSegmentInnerVertex_label {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    label c.2 (positiveCompositeCutWord u v k c.1).val x =
      BarrattEccles.insertedPosition m (n + 1) k
        (label (positiveCompositeInnerCut u v k c) (positiveWord v).val
          (positiveCompositeSegmentInnerVertex u v k c i z x hx))
```


## 230. C451の挿入ラベルの全位置を元の部分語へ戻す（法則の型）

一覧：済み 12／全体 48（うち追加 4）

既存の`exists_segmentPosition_of_inserted_pivot`は辺の非退化性を仮定するので、
今回の全切断にはその仮定を足して使わない。
元の接頭長の増大を使い、一般の位置を挟む最後の外側番号を有限集合のmaxで読む。
同じ語の位置の分解の法則であって、新しい作用や合成の定理を追加するものではない。
各証明200行以内の見込み。

```lean
lemma positiveCompositePosition_block {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (h : Fin (m + n + (d + e) + 1)) :
    ∃ p : Fin (m + d + 1), compositePrefixLength u v k r p.val ≤ h.val ∧
      h.val < compositePrefixLength u v k r (p.val + 1)

lemma positiveCompositePosition_remaining_or_segment {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (h : Fin (m + n + (d + e) + 1)) :
    (∃ (p : Fin (m + d + 1)) (_hp : (positiveWord u).val p ≠ k),
      h = compositeFirstPosition u v k r p) ∨
      ∃ (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val),
        h = positiveCompositeSegmentPosition u v k r i z

lemma positiveCompositePosition_of_inserted_label {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (h : Fin (m + n + (d + e) + 1)) (b : Fin (n + 1))
    (hb : (positiveCompositeCutWord u v k r).val h = BarrattEccles.insertedPosition m (n + 1) k b) :
    ∃ (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val),
      h = positiveCompositeSegmentPosition u v k r i z
```

有限点検：`/tmp/bsw16/check-composite-position-blocks.py`、12,233組・非退化3,745組。
全合成位置について、接頭長で挟む元の外側番号が一意に元のoriginと一致し、
挿入部分語の相対位置と内側位置も一致することを先に確認した。
``remaining_or_segment``は退化した切断を捨てずに使う。


## 231. C451の全挿入色の頂点の順方向（法則の型）

一覧：済み 12／全体 48（うち追加 4）

§230の元の部分語分解を§229へ渡すことで、非退化性を仮定せず、全挿入色の頂点を
同じ内側Cutの同じ色へ送る。分解の選択を使うが、元の合成語と元の二段Cutは変えない。
同じ指定面の照合の順方向の証明分割として型を記録する。各証明200行以内。

```lean
def insertedColorPathMap {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)) →
      ↥(colorPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val b)

lemma insertedColorPathMap_vertices {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b))) :
    vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k
      ((positiveCompositeInnerCut u v k c).vertical (insertedColorPathMap u v k c b x).val) =
        c.2.vertical x.val
```

ここでは全単射性・順序同値・C451全体を主張していない。
次に同じ内側順位・位置からの逆復元と順序を照合し、§224の指定面の合成の法則へ渡す。


## 232. C451の全挿入頂点の順方向の単射性（法則の型）

一覧：済み 12／全体 48（うち追加 4）

同じ内側頂点の縦座標から元の外側色別順位を特定する。
同じ順位が入る外側区間はfiberの定義から一意で、同じ横座標から部分語の相対位置も
一致する。最後に同じ元のCutの二座標の単射性を使う。既存構成の同じ指定座標の法則。
各証明200行以内で、同じ入力を弱めたり非退化性を仮定したりしない。

```lean
lemma positiveCompositeSegmentInnerVertex_source_injective {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z)
    (j : Fin (Surjection.occurrenceCount u.val k)) (w : Fin (c.1.val j).val)
    (y : Fin (m + n + (d + e) + q + 1))
    (hy : c.2.horizontal y = positiveCompositeSegmentPosition u v k c.1 j w)
    (h : positiveCompositeSegmentInnerVertex u v k c i z x hx =
      positiveCompositeSegmentInnerVertex u v k c j w y hy) : x = y

lemma insertedColorPathMap_injective {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    Function.Injective (insertedColorPathMap u v k c b)
```

有限点検：`/tmp/bsw16/check-inserted-vertex-map.py`、12,233組・非退化3,745組。
全挿入頂点の内側二座標が重複せず、二座標の和が元の内側経路の列挙番号に一致することを
先に確認した。単射性を示しただけで全射性・順序同値は結論しない。


## 233. C451の逆方向：元の内側位置の所属（法則の型）

一覧：済み 12／全体 48（うち追加 4）

逆方向で、元の内側頂点の縦順位に属する外側区間を選ぶと、その部分語が元の内側横位置を
含むことを、既存C447の両端の比較で読む。新しい分割やCutは構成しない。
位置が開始より前なら右辺の高さと最初の順位に矛盾、終了以後なら左辺の高さと最後の順位に
矛盾する。既存構成の同じ所属の法則で、200行以内の見込み。

```lean
lemma positiveCompositeInnerPosition_segment_covered {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (a : Fin (n + e + 1))
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1))
    (hm : rank ∈ colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i))
    (hl : lo (positiveCompositeInnerCut u v k c) a ≤ rank.val)
    (hr : rank.val ≤ hi (positiveCompositeInnerCut u v k c) a) :
    c.1.start i ≤ a.val ∧ a.val < c.1.start i + (c.1.val i).val
```

有限点検は§232の全内側経路の元の二座標の比較と同じ12,233組で行った。
これだけで逆写像や全射性を完成したとは扱わない。

## 234. C451の全挿入頂点の順方向・単射性：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

前ターンは§220〜226の7本402行を対象ビルド・小監査の後にコミットした進捗。
本ターンはそこから再開し、次の7本**523行**を対象ビルド・小監査で検証した。
新しい作用・界面・仮定の追加なし。既存の公開宣言を変更せず、sorry・新しい公理なし。

| 登録対象（共通接頭辞 SerrePositivity.EInfinity.SimplexCuts.） | 行数 |
| --- | ---: |
| CompositeSegmentVertexRanks | 83 |
| ColorIntervalVertexOrder | 35 |
| CompositeSegmentInnerRanks | 124 |
| CompositeSegmentInnerVertices | 77 |
| CompositePositionDecomposition | 91 |
| CompositeSegmentInnerVertexInjective | 55 |
| InsertedColorPathMap | 58 |
| **合計** | **523** |

検証の射程は、元の挿入部分語内の全頂点の同じ外側順位、その順位の内側Cutへの所属、
同じ二座標・指定面・挿入ラベル、全合成位置の残り/部分語の分解、
全挿入色の頂点の写像とその単射性まで。非退化性は仮定しない。
`insertedColorPathMap`の全射性・狭義単調性・順序同値・C451全体・符号・nullaryは未完。
§233は逆方向の型と/tmpの未検証の下書きだけであり、実測・完成宣言に加えていない。

対象ビルドは最後に`/tmp/bsw16/m14-inserted-color-path-map-01.log`（2,873 jobs）で成功。
途中の頂点座標も`m14-composite-inserted-geometry-01.log`で通過している。
修正は、単調性への引数の明示、元の有限添字と語長の明示、
既存`occurrenceAt_exists`の名前空間の訂正、100字の改行。
新しい数学の補題で埋めたものではない。
最後の対象Lean警告0。
小監査は`/tmp/bsw16/audit-m14-inserted-color-path-map.log`、
**7モジュール・53宣言、標準三公理のみ**。
鍵は各対象ビルド・監査で一回ずつ取り、実行終了時に返した。待ちの整理券は常に一枚。

M14実測**19,233行**、L12a実測**4,026行**、一覧は12/48（追加4）のまま。
§207の挿入色の160〜280行の見込みに対し、§224〜232で既に619行を使い、全射・順序が残る。
増えたのは同じ合成語の全位置の分解、元のCutの高さから色別順位への移送、
内側Cutへの所属を元の辺から示す分。これを既存の位置のラベルの照合だけでは代用しない。
残りを削ったり、元の指定面の一致をホモトピー圏へ弱めたりはしない。
31,000行内に収まると確定したわけではなく、残りの見込みのリスクを保持する。
約25,000行での中間報告という§32の指定も維持する。

次のLeanは§233の元の内側位置の所属の検証、その同じ内側順位から元の合成頂点への逆復元、
全射性と順序、§224の指定面の合成の法則への接続。
完備化後のP⁰の三案の紙は§223に保存済みで、(c)が不可避との結論はまだ出していない。
G10・M15・G12・drafts・界面・共有入口・mainは変更していない。
ユーザーが/goalをactiveへ変更したことを受け、旧blocked表示の差は解消した。
この取り込み点は承認待ちの停止点ではなく、同じL12aを続ける途中報告である。


## 235. C451の同じ合成区間への逆方向（法則の型）

一覧：済み 12／全体 48（うち追加 4）

前ターンは656d22333の検証・監査済み7本523行という進捗。
作業木が空で同じ枝にいることを確かめ、§233の元の内側位置の所属から再開した。
次は同じ内側順位が、元の合成語の区間の両端の間の高さになることを示す。
部分語の最初/最後では元の外側区間の両端、内部では元の内側辺の所属と高さを使う。
同じCut・指定verticesの合成の法則であり、別の経路・作用・仮定は作らない。
200行以内の見込み。

```lean
lemma positiveCompositeSegment_inverse_interval {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1))
    (hm : rank ∈ colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i))
    (hl : lo (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z) ≤ rank.val)
    (hr : rank.val ≤ hi (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z)) :
    lo c.2 (positiveCompositeSegmentPosition u v k c.1 i z) ≤
        (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k rank).val ∧
      (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k rank).val ≤
        hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z)
```

有限点検：`/tmp/bsw16/check-inserted-vertex-inverse.py`、12,233組・非退化3,745組。
全内側頂点について、同じ外側順位の出現・相対位置・元の高さから戻した二座標が、
元の合成経路上のただ一つの頂点を表すことを先に確認した。
この区間の所属の逆向きだけで、全色の順序同値やL12aの完了は主張しない。


## 236. C451の部分語分解の一意性と指定した分解での評価（法則の型）

一覧：済み 12／全体 48（うち追加 4）

順方向の写像に使った分解の選択を、逆復元で得る同じ分解へ合わせる。
異なる部分語は既存`compositeSegmentPosition_lt`で交わらず、
同じ部分語では元の接頭長を消去する。元の構成の係数・位置の移送の法則。
各証明200行以内の見込み。

```lean
lemma positiveCompositeSegmentPosition_sigma_injective {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Function.Injective (fun s : Σ i, Fin (r.val i).val =>
      positiveCompositeSegmentPosition u v k r s.1 s.2)

lemma positiveCompositeSegmentInnerVertex_eq_of_same_source {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z)
    (j : Fin (Surjection.occurrenceCount u.val k)) (w : Fin (c.1.val j).val)
    (hy : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 j w) :
    positiveCompositeSegmentInnerVertex u v k c i z x hx =
      positiveCompositeSegmentInnerVertex u v k c j w x hy

lemma insertedColorPathMap_val_of_segment {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (hx : c.2.horizontal x.val = positiveCompositeSegmentPosition u v k c.1 i z) :
    (insertedColorPathMap u v k c b x).val =
      positiveCompositeSegmentInnerVertex u v k c i z x.val hx
```

有限点検：`/tmp/bsw16/check-composite-segment-position-injective.py`、12,233組・非退化3,745組。
元の全部分語の全相対位置の像が互いに異なることを追加して点検した。
写像を別の選択へ置き換えず、同じ合成位置の一意性で元の指定頂点を照合する。


## 237. C451の元の逆頂点・順位の復元と全射性（法則の型）

一覧：済み 12／全体 48（うち追加 4）

§235の元の区間への逆向きの所属を、同じ`coordinatePosition`へ渡す。
元のverticesの高さから同じ色別順位へ戻る計算は既存の差の公式を使う。
内側頂点の縦順位は既存の色別区間の被覆に属し、その部分語に横位置が属することは§233。
そこから作った元の合成頂点を同じ写像で送り、元の二座標の単射性で内側頂点へ戻す。
同じ既存のCut・指定面の逆の照合であり、各証明200行以内の見込み。

```lean
def positiveCompositeSegmentInverseVertex {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1)) :
    Fin (m + n + (d + e) + q + 1)

lemma positiveCompositeSegmentInverseVertex_coordinates {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1))
    (hm : rank ∈ colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i))
    (hl : lo (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z) ≤ rank.val)
    (hr : rank.val ≤ hi (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z)) :
    c.2.horizontal (positiveCompositeSegmentInverseVertex u v k c i z rank) =
        positiveCompositeSegmentPosition u v k c.1 i z ∧
      c.2.vertical (positiveCompositeSegmentInverseVertex u v k c i z rank) =
        vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k rank

lemma positiveCompositeSegmentInverseVertex_rank {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1))
    (hm : rank ∈ colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i))
    (hl : lo (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z) ≤ rank.val)
    (hr : rank.val ≤ hi (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z)) :
    positiveCompositeSegmentVertexRank u v k c i z
        (positiveCompositeSegmentInverseVertex u v k c i z rank)
        (positiveCompositeSegmentInverseVertex_coordinates u v k c i z rank hm hl hr).1 = rank

lemma insertedColorPathMap_surjective {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    Function.Surjective (insertedColorPathMap u v k c b)
```

有限点検は§235の全内側頂点の逆復元（12,233組、非退化3,745組）。
全射性の後も順序保存と指定面の全族・符号・nullaryは残る。
ここは型の報告で、未検証の下書きは/tmpへ置き、実測に含めない。


## 238. C451の挿入色の順序と指定面への接続（法則の型）

一覧：済み 12／全体 48（うち追加 4）

同じ部分語内では、元のcoordinate_sumと同じ順位の差の式により、写像は位置番号の
平行移動となる。異なる部分語では、元の分割の境界と色別区間の狭義順序を使う。
§237の全射性と合わせ、同じ全頂点の順序同値を§224の面の合成の法則へ渡す。
既存の指定面・位置の合成の法則と同じC451の証明分割であり、各証明200行以内の見込み。

```lean
lemma positiveCompositeSegmentInnerVertex_strict_order {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z)
    (j : Fin (Surjection.occurrenceCount u.val k)) (w : Fin (c.1.val j).val)
    (y : Fin (m + n + (d + e) + q + 1))
    (hy : c.2.horizontal y = positiveCompositeSegmentPosition u v k c.1 j w) (hxy : x < y) :
    positiveCompositeSegmentInnerVertex u v k c i z x hx <
      positiveCompositeSegmentInnerVertex u v k c j w y hy

lemma insertedColorPathMap_strictMono {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    StrictMono (insertedColorPathMap u v k c b)

def insertedColorPathOrderIso {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)) ≃o
      ↥(colorPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val b)

lemma insertedColorPathOrderIso_vertices {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b))) :
    vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k
      ((positiveCompositeInnerCut u v k c).vertical (insertedColorPathOrderIso u v k c b x).val) =
        c.2.vertical x.val

lemma positiveComposite_inserted_face {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    (⟨outputDegree c.2 (positiveCompositeCutWord u v k c.1)
        (BarrattEccles.insertedPosition m (n + 1) k b),
      vertices c.2 (positiveCompositeCutWord u v k c.1)
        (BarrattEccles.insertedPosition m (n + 1) k b)⟩ :
        Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) =
      ⟨outputDegree (positiveCompositeInnerCut u v k c) (positiveWord v) b,
        (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k).comp
          (vertices (positiveCompositeInnerCut u v k c) (positiveWord v) b)⟩
```

有限点検は§232の元の全内側経路の列挙番号（12,233組、非退化3,745組）と、
§199の全色の同じ面の合成の点検。順序を捨てた全単射や対象ごとの任意の同値で代用しない。
ここは型と/tmpの下書きであり、検証後にのみ実測へ加える。


## 239. C451の全指定面の族への包装（既報の型の接続）

一覧：済み 12／全体 48（うち追加 4）

§199の同じC451の型を変更せず、残り色と挿入色の厳密なSigmaの等式を
元の`operadInsertionEquiv`の二つの成分で接続する。
元の`insertionFamily`の出力順序・次数・指定面を保ち、任意の同型や順序なしの族で代用しない。

```lean
lemma positiveCompositeFaceFamily_eq_nested {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    positiveCompositeFaceFamily u v k c =
      positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c)
```

有限点検は§199の元の全色の指定面の族の比較（12,233組・非退化3,745組）のまま。
この包装が通った後も、C452の符号・C453の退化性、実テンソル・nullaryは未完。
この型の報告をC451の証明完了の代わりにはしない。


## 240. C453の元の指定面の単射性による二つの方向（法則の型）

一覧：済み 12／全体 48（うち追加 4）

C453の既報の同値の証明分割。C451のSigmaの等式で面の単射性を移し、
二段の非退化性から合成の非退化性、合成の非退化性から内側の非退化性を読む。
既存の`faces_mono_iff`と`vertices_strictMono`を再利用する。各証明200行以内の見込み。

```lean
lemma positiveCompositeCut_nondegenerate_of_nested {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (hOuter : Nondegenerate (positiveCompositeOuterCut u v k c) (positiveWord u).val)
    (hInner : Nondegenerate (positiveCompositeInnerCut u v k c) (positiveWord v).val) :
    Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val

lemma positiveCompositeCut_inner_nondegenerate {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Nondegenerate (positiveCompositeInnerCut u v k c) (positiveWord v).val
```

有限点検は§199の全12,233組の退化性の比較を再利用する。
この二方向だけでC453全体を完成とはしない。合成から外側の指定色kの単射性へ戻す部分では、
元の隣接する部分語の共有端点の同じラベル・高さを照合する必要が残る。
新しい非退化性の仮定を入れたり、この色を検査から外したりはしない。


## 241. C453の外側指定色の共有端点（法則の型）

一覧：済み 12／全体 48（うち追加 4）

元の隣接部分語の共有端点は、異なる合成位置に同じ挿入ラベルとして現れる。
元の合成Cutの区間の最後/最初の経路頂点を取り、元の非退化性から高さを厳密に比較する。
外側の指定色を検査から除かずに戻すC453の法則の証明分割。各証明200行以内。

```lean
lemma positiveCompositeSegment_boundary_pair {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i j : Fin (Surjection.occurrenceCount u.val k)) (hij : j.val = i.val + 1) :
    compositeLastPosition u v k r (positiveOccurrencePosition u k i) <
        compositeFirstPosition u v k r (positiveOccurrencePosition u k j) ∧
      (positiveCompositeCutWord u v k r).val
          (compositeLastPosition u v k r (positiveOccurrencePosition u k i)) =
        (positiveCompositeCutWord u v k r).val
          (compositeFirstPosition u v k r (positiveOccurrencePosition u k j))

lemma positiveComposite_outer_slot_boundary_strict {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val)
    (i j : Fin (Surjection.occurrenceCount u.val k)) (hij : j.val = i.val + 1) :
    hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) <
      lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k j)
```

有限点検：`/tmp/bsw16/check-outer-slot-boundary-strict.py`。
全12,233組を読み、生き残る3,745組の隣接する外側指定色の全出現の間で、
元の外側右端＜次の左端を先に確認した。
ここも/tmpの未検証の下書きであり、実測へ加えていない。


## 242. C453の全指定色と元の非退化性の同値への接続（法則の型）

一覧：済み 12／全体 48（うち追加 4）

共有端点の隣接する出現の厳密な高さの比較を、元のloの単調性で全出現へ延ばす。
異なる同色区間が高さで厳密に離れれば、元の面の単射性が従うことを二座標で確認する。
残り色はC451の面の等式、指定色kはこの区間の検査で外側へ戻す。
§199のC453の同値の型を変更しない証明分割であり、各証明200行以内の見込み。

```lean
lemma vertices_injective_of_strict_intervals {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r)
    (h : ∀ p p', v.val p = a → v.val p' = a → p < p' → hi s p < lo s p') :
    Function.Injective (vertices s v a)

lemma positiveComposite_outer_slot_intervals_strict {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val)
    (i j : Fin (Surjection.occurrenceCount u.val k)) (hij : i < j) :
    hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) <
      lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k j)

lemma positiveCompositeCut_outer_nondegenerate {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Nondegenerate (positiveCompositeOuterCut u v k c) (positiveWord u).val

lemma positiveCompositeCut_nondegenerate_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val ↔
      Nondegenerate (positiveCompositeOuterCut u v k c) (positiveWord u).val ∧
        Nondegenerate (positiveCompositeInnerCut u v k c) (positiveWord v).val
```

有限点検は§199の全非退化性の同値と§241の共有端点の比較。
この型の報告だけでC453の完成とせず、対象ビルド・小監査を経てから認定する。


## 243. C452の元の符号の指数の比較（既報の型の証明分割、紙のみ）

一覧：済み 12／全体 48（うち追加 4）

C451・C453の後のC452は、元のcompositionExponent・cutSignの二指数を変更せず、
全整数係数の(-1)の累乗の比較へ戻す。次は§199のC452と同じ主張のmod 2での法則の型。
後から符号を定義し直すものでも、消えない項を捨てるものでもない。

```lean
lemma positiveCompositeCut_exponent_modeq {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Nat.ModEq 2
      (Surjection.compositionExponent u v k c.1 +
        (permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val +
          positionExponent c.2 (positiveCompositeCutWord u v k c.1).val))
      ((d * e + e * positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c)) +
        (permutationExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
          positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val) +
        (permutationExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
          positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val))
```

このmod 2の比較を供給した後は、既存`neg_one_pow_eq_pow_mod_two`と`pow_add`で
§199の同じ整数係数の等式へ戻せる。肝心の指数の比較を追加仮定として界面やL12aへ足さない。
これはまだ紙の型で、有限点検は§198〜199の同じ3,745個の非退化な合成切断の符号比較。
型の正しさ・Leanの証明・監査の代わりには扱わない。

## 244. C451・C453の完成：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§233・235〜242の13本**849行**を検証した。
C451（元の全出力次数と指定面の族の厳密な一致）とC453（元の合成Cutと同じ二段Cutの
非退化性の同値）が、§199の型のまま閉じた。
この二つはL12aの証明分割であり、一覧のIDを新しく増やしたりL12a全体を完成にしたりはしない。
C452・実テンソル・nullaryは残る。

挿入色の全頂点の写像は、同じ元の内側順位からの逆復元で全射性を示した。
同じ部分語内では元のcoordinate_sumによる平行移動、異なる部分語では元の境界と
色別区間の順序により、狭義順序を保つことを示した。
残り色と挿入色のSigmaの等式を、元の`operadInsertionEquiv`で全族へ接続した。
外側の指定色kも、隣接部分語の共有端点の同じラベルと元の非退化性で検査しており、
検査から除いたり、追加の非退化性の仮定を置いたりしていない。

対象ビルド：

- `m14-inner-vertex-segment-coverage-01.log`（2,868 jobs）：元の内側位置の所属。
- `m14-inserted-color-path-surjective-01.log`（2,890 jobs）：同じ逆頂点・順位・全射性。
- `m14-composite-nondegenerate-components-01.log`（2,921 jobs）：C451とC453の二方向。
- `m14-composite-nondegenerate-comparison-03.log`（2,924 jobs）：最終C453、100字の改行修正後。

全て成功。最終の対象Lean警告0。
途中の修正は、Sigmaに適用した位置写像の簡約の明示、指定面の包装での既存定義の展開、
共有端点の自然数の等式を依存型のrewriteを使わずに読むこと、docstring/行の改行。
元の型・定義・指定射を変更して通したものではない。

小監査：`/tmp/bsw16/audit-m14-composite-faces-nondegenerate.log`、
**13モジュール・65宣言、標準三公理のみ**。
新しいsorry・公理なし。鍵は対象ビルド・監査ごとに一回取得して返した。
待ちの整理券は常に一枚、編集・紙・報告の間は鍵を持っていない。
`git diff --check`と、追加したソースを含むstaged diffの確認を行う。

調整役への登録対象（共通接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| InnerVertexSegmentCoverage | 64 |
| CompositeSegmentInverseInterval | 108 |
| CompositeSegmentPositionInjective | 62 |
| InsertedColorPathMapEvaluation | 29 |
| CompositeSegmentInverseVertices | 76 |
| InsertedColorPathMapSurjective | 67 |
| CompositeSegmentInnerOrder | 87 |
| InsertedColorFaces | 52 |
| CompositeFaceComparison | 37 |
| CompositeNondegenerateComponents | 59 |
| CompositeSlotBoundary | 87 |
| VerticesStrictIntervals | 41 |
| CompositeNondegenerateComparison | 80 |
| **合計** | **849** |

M14実測は**20,082行**、L12a実測は**4,875行**。
このうち今回C451の逆・順序・全族への接続が582行、C453が267行。
§207のL12a完成時3,974〜4,624行の見込みは、既に実測が上端を251行超えており、
完成の見込みとしては使わない。

## 245. C451・C453後の残りと外枠の照合

一覧：済み 12／全体 48（うち追加 4）

元の全位置・順位・高さの比較が見込みより増えたことを、完了したC451・C453へ反映する。
C453の完成を、符号や実テンソルの完成として控除しない。
他の未供給の行の旧見込みを据え置いた、保守的な比較は次のとおり。

| L12aの残り | 旧見込みを据え置いた残り |
| --- | ---: |
| C452：元のcompositionExponentと二つのcutSignの照合（§243） | 173〜323 |
| 同じ指定面から元の実テンソル・係数移送への接続 | 130〜240 |
| nullary：元の有限添字と項の接続 | 250〜400 |
| **残り** | **553〜963** |
| **L12a完成時（実測4,875行を含む）** | **5,428〜5,838** |

§177以降のL12a以外の残り6,004〜10,914行も据え置くと、
M14完成時の比較は**26,639〜31,959行**。
外枠は§32の**31,000行のまま**で、上端には**959行の超過リスク**がある。
増枠や範囲の削除は自己承認せず、収まるとの主張もしない。
約25,000行で止まらず途中報告する指定は維持し、実測と残りを分けて報告する。
§223で未確定の完備化後の比較を、新しく無料で供給された前提として扱ってもいない。
供給が必要と分かった仕事は全体の見込みに算入し直し、(c)が必要と判明したら§32で止める。

次は同じ既報のC452の整数符号・指数の比較。
`vectorTensorAt_congr`と`IntervalCuts.coactionComposition_apply`の実際の型も読み、
実テンソルへの接続で元の次数・二つの係数移動・指定面を保つことを再確認した。
この二つのAPIだけで符号の指数の照合を供給したとは扱わない。
G10・M15・G12・drafts・界面・共有入口・mainは変更していない。
これは同じL12aの途中の取り込み点であり、goalはactiveのまま継続する。


## 246. C452の残り色の区切りと区間重み（法則の型）

一覧：済み 12／全体 48（うち追加 4）

前ターンは35d3d044bでC451・C453を検証・監査・保存した進捗。
作業木が空で同じ枝にいることを確認し、元のC452へ進む。
§243の指数の比較のうち、残り色のCaesuraとintervalLengthを、
既に証明した全出現位置の順序同値と元のCutの両端で読む。
既存の符号の定義は変えず、法則の証明分割として次の型を記録する。
各証明200行以内の見込み。

```lean
lemma caesura_iff_of_occurrenceOrderIso {r r' l l' : ℕ}
    (v : Fin l → Fin r) (w : Fin l' → Fin r') (a : Fin r) (b : Fin r')
    (e : ↥(Surjection.occurrences v a) ≃o ↥(Surjection.occurrences w b))
    (p : ↥(Surjection.occurrences v a)) :
    Surjection.Caesura w (e p).val ↔ Surjection.Caesura v p.val

lemma positiveComposite_remaining_caesura_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (compositeFirstPosition u v k r p) ↔ Surjection.Caesura (positiveWord u).val p

lemma positiveComposite_remaining_intervalLength {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (compositeFirstPosition u v k c.1 p) =
      intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p
```

有限点検：`/tmp/bsw16/check-remaining-caesura-weights.py`。
元の12,233組（非退化3,745組を含む）に、全残り色の全位置の元の区切りと、
各元の合成CutのintervalLengthが同じ外側のintervalLengthと一致することを追加して点検した。
非退化な場合だけの弱い主張にはしていない。
C452全体、挿入色の区切り、positionExponentやpermutationExponentの和の比較はまだ未完。


## 247. C452の挿入部分語の順序と共有端点の区切り（法則の型）

一覧：済み 12／全体 48（うち追加 4）

元の合成位置を部分語番号と相対位置の辞書式順序で読み、
内側語の位置が真に進む場合と、元の共有端点として重なる場合を分ける。
共有端点が次の部分語にも現れる場合は、既存C453の同じラベルの二位置をそのまま使う。
新しい符号や分割を構成するのではなく、C452の元の区切りの法則の証明分割である。
各証明200行以内の見込み。

```lean
lemma positiveCompositeSegmentPosition_lt_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i j : Fin (Surjection.occurrenceCount u.val k))
    (z : Fin (r.val i).val) (w : Fin (r.val j).val) :
    positiveCompositeSegmentPosition u v k r i z < positiveCompositeSegmentPosition u v k r j w ↔
      i < j ∨ (i = j ∧ z.val < w.val)

lemma positiveCompositeSegment_future_inner_order {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i j : Fin (Surjection.occurrenceCount u.val k))
    (z : Fin (r.val i).val) (w : Fin (r.val j).val)
    (h : positiveCompositeSegmentPosition u v k r i z <
      positiveCompositeSegmentPosition u v k r j w) :
    r.start i + z.val < r.start j + w.val ∨
      (r.start i + z.val = r.start j + w.val ∧
        z.val + 1 = (r.val i).val ∧ i.val + 1 < Surjection.occurrenceCount u.val k)

def segmentInnerWordPosition {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (i : Fin t) (z : Fin (r.val i).val) : Fin L

lemma positiveCompositeSegment_boundary_caesura {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val)
    (hz : z.val + 1 = (r.val i).val) (hi : i.val + 1 < Surjection.occurrenceCount u.val k) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
      (positiveCompositeSegmentPosition u v k r i z)
```

有限点検：`/tmp/bsw16/check-inserted-caesura-order.py`。
全12,233組の元の全挿入部分語の全位置対について、合成位置の順序と内側位置の順序、
共有端点の条件を先に照合した。元の挿入色のCaesuraの候補式も全例で点検したが、
一般のiffのLeanの証明はまだ別に要る。


## 248. C452の挿入色の区切りの元の全条件（法則の型）

一覧：済み 12／全体 48（うち追加 4）

元の内側語に後の同色位置がある場合、その位置の直前の辺の所属部分語を使い、
同じラベルの後の合成位置を得る。
逆に後の合成位置は§230で同じ挿入部分語の位置へ分解し、§247の内側位置の順序で
真に後の内側位置か共有端点の重複かを特定する。
既存のCaesuraの定義と元の位置・分割の法則の証明分割であり、各証明200行以内。

```lean
lemma positiveCompositeSegment_caesura_of_inner {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val)
    (h : Surjection.Caesura v.val (segmentInnerWordPosition r i z)) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
      (positiveCompositeSegmentPosition u v k r i z)

lemma positiveComposite_inserted_caesura_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) ↔
      Surjection.Caesura v.val (segmentInnerWordPosition r i z) ∨
        (z.val + 1 = (r.val i).val ∧ i.val + 1 < Surjection.occurrenceCount u.val k)
```

有限点検は§247の`check-inserted-caesura-order.py`（全12,233組、非退化3,745組）。
共有端点で元の内側語に区切りがない場合も合成語に区切りが増えることを、候補式に含めた。
この元のiffを、区切りを定義し直したり非退化な場合だけの比較にしたりはしない。


## 249. C452の元の末尾・内部の重みと整数係数への移送（法則の型）

一覧：済み 12／全体 48（うち追加 4）

元の最後の部分語の末尾には後の位置がないので、区切りがない。
これで§248の二条件を、部分語の末尾と内部に分けた同じ0/1重みの式へ移す。
また、§243のmod 2の指数の比較が供給された場合にだけ、同じ元の整数係数へ戻す法則を分割する。
指数の比較の仮定を露出させた係数移送であり、未証明の§243やC452全体を完成扱いしない。
各証明200行以内の見込み。

```lean
lemma not_caesura_last_segment_end {t L N : ℕ} (v : Fin L → Fin N)
    (r : Surjection.OverlapPartition t L) (i : Fin t) (z : Fin (r.val i).val)
    (hz : z.val + 1 = (r.val i).val) (hi : i.val + 1 = t) :
    ¬ Surjection.Caesura v (segmentInnerWordPosition r i z)

lemma positiveComposite_inserted_end_caesura_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val)
    (hz : z.val + 1 = (r.val i).val) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) ↔
      i.val + 1 < Surjection.occurrenceCount u.val k

lemma positiveComposite_inserted_caesura_split_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) ↔
      if z.val + 1 = (r.val i).val then i.val + 1 < Surjection.occurrenceCount u.val k
      else Surjection.Caesura v.val (segmentInnerWordPosition r i z)

lemma positiveComposite_inserted_caesura_indicator {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    (if Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) then 1 else 0 : ℕ) =
      if z.val + 1 = (r.val i).val then
        (if i.val + 1 < Surjection.occurrenceCount u.val k then 1 else 0)
      else (if Surjection.Caesura v.val (segmentInnerWordPosition r i z) then 1 else 0)

lemma positiveComposite_inserted_intervalLength_formula {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val) :
    intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (positiveCompositeSegmentPosition u v k c.1 i z) =
      (hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z) -
        lo c.2 (positiveCompositeSegmentPosition u v k c.1 i z)) +
      (if z.val + 1 = (c.1.val i).val then
        (if i.val + 1 < Surjection.occurrenceCount u.val k then 1 else 0)
      else (if Surjection.Caesura v.val (segmentInnerWordPosition c.1 i z) then 1 else 0))

lemma positiveCompositeCutCoefficient_eq_nested_of_modeq {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nat.ModEq 2
      (Surjection.compositionExponent u v k c.1 +
        (permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val +
          positionExponent c.2 (positiveCompositeCutWord u v k c.1).val))
      ((d * e + e * positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c)) +
        (permutationExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
          positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val) +
        (permutationExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
          positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val))) :
    Surjection.compositionSign u v k c.1 * cutSign c.2 (positiveCompositeCutWord u v k c.1).val =
      positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c)
```

末尾・内部の式の有限点検：`/tmp/bsw16/check-inserted-caesura-boundary.py`（全12,233組）。
最後の部分語の末尾を含め、元のCaesuraの式と一致することを先に確認した。
整数係数の移送は既存の`neg_one_pow_eq_pow_mod_two`と`pow_add`だけを使う。
新しい界面の欄や、A4/L12aへ追加する仮定ではない。


## 250. C452の既存の活動頂点の移送（法則の型）

一覧：済み 12／全体 48（うち追加 4）

既存`permutationExponent_eq_active_inversions`は、元のintervalLengthの重み付き逆転指数を
展開した活動頂点の逆転数へ移す。ここで新しく活動頂点を定義せず、
§246の全出現位置の順序同値によるCaesuraの法則を、展開した元の色列へ適用する。
C451で構成した同じ挿入色の順序同値が、元の活動頂点を保つことを読む。
既存構成の同じ順序・色別fiberの移送の法則で、各証明200行以内。

```lean
lemma colorOrderIso_active_iff {m m' q q' r r' : ℕ} (s : Cut m q) (t : Cut m' q')
    (v : Fin (m + 1) → Fin r) (w : Fin (m' + 1) → Fin r') (a : Fin r) (b : Fin r')
    (e : ↥(colorPositions s v a) ≃o ↥(colorPositions t w b))
    (x : ↥(colorPositions s v a)) :
    (e x).val ∈ activeVertexPositions t w ↔ x.val ∈ activeVertexPositions s v

lemma insertedColorPathOrderIso_active_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b))) :
    (insertedColorPathOrderIso u v k c b x).val ∈
        activeVertexPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val ↔
      x.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val
```

有限点検：`/tmp/bsw16/check-inserted-active-vertices.py`、全12,233組。
展開色列のCaesuraを元の経路番号で直接計算し、同じ挿入色の内側経路番号の
展開Caesuraと一致することを先に確認した。
この活動頂点の保存だけで二つの逆転指数の全和やC452の完成を主張しない。


## 251. C452の元の順位・他色の活動頂点・区切り順位の橋（法則の型）

一覧：済み 12／全体 48（うち追加 4）

既存C170 `caesuraRank_label`とC108の面番号の活動頂点数の式を再利用する。
同じ元の色別位置までの活動頂点を、その色と他色へ分けて数えるだけの法則。
新しい活動頂点の定義や新しい作用は作らない。200行以内の見込み。

```lean
lemma colorRank_add_other_active_prefix {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1))
    (j : Fin (outputDegree s v a + 1)) (hm : j ∈ colorIntervalRanks s v a p) :
    j.val + ((activeVertexPositions s v.val).filter (fun z =>
      z < colorPositionEquiv s v ⟨a, j⟩ ∧ label s v.val z ≠ a)).card =
      (vertices s v a j).val + Surjection.caesuraRank v.val p
```

有限点検：`/tmp/bsw16/check-color-rank-active-prefix.py`（全12,233組）。
同じ元の外側経路の全頂点で、色別順位＋先行他色の活動頂点数＝高さ＋元の語の区切り順位を
直接計算して先に確認した。位置指数と逆転指数の比較へ渡すための法則であり、
この橋だけでC452全体のmod 2の等式を完成したとは扱わない。


## 252. C452の同じ外側区間内の先行他色の集合（法則の型）

一覧：済み 12／全体 48（うち追加 4）

§251の他色の先行活動頂点は、元の同じ水平区間内では高さを変えても変わらない。
二つの位置の間の全頂点の水平座標は元の単調性から同じであり、そのラベルはaなので、
他色の位置が二つの位置を跨ぐことはない。元のfiberの法則の証明分割で200行以内。

```lean
lemma other_active_prefix_eq_on_interval {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin r) (p : Fin (m + 1)) (hp : v p = a)
    (x y : Fin (m + q + 1)) (hx : s.horizontal x = p) (hy : s.horizontal y = p) :
    (activeVertexPositions s v).filter (fun z => z < x ∧ label s v z ≠ a) =
      (activeVertexPositions s v).filter (fun z => z < y ∧ label s v z ≠ a)
```

有限点検：`/tmp/bsw16/check-other-active-prefix-constant.py`（全12,233組）。
同じ元の外側区間の全頂点で、他色の先行活動頂点の番号の集合そのものが一致することを
先に確認した。濃度だけの一致へ弱めない。


## 253. C452の二つの指数の全和への分解（法則の型と紙の接続）

一覧：済み 12／全体 48（うち追加 4）

§251の順位の橋と元の成分次数の総和を使い、符号の比較を元の二つの指数へ分け直す。
まず既存`sum_segmentDegree`と`lineRank_last`で閉じる補和の法則は次。
零arityの内側語も含む元の合成指数を変更しない法則で、200行以内の見込み。

```lean
lemma compositionExponent_add_prefixRanks {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) (n + e)) :
    Surjection.compositionExponent u v k r +
        ∑ i, Surjection.segmentDegree v.val r i *
          Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i) = d * e
```

残る二つの全和の型は次の候補として具体化する。以下は紙だけで、
既存の有限集合の濃度の記法をB_iとして置くものであり、新しい演算や界面の欄を作らない。
`positiveCompositeOtherActivePrefix`の位置は既存の色別の最初の順位である。

```lean
def positiveCompositeOtherActivePrefix {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) : ℕ :=
  let δ := positiveCompositeOuterCut u v k c
  let j := colorIntervalFirst δ (positiveWord u) k (positiveOccurrencePosition u k i)
    (positiveOccurrencePosition_value u k i)
  ((activeVertexPositions δ (positiveWord u).val).filter (fun z =>
    z < colorPositionEquiv δ (positiveWord u) ⟨k, j⟩ ∧ label δ (positiveWord u).val z ≠ k)).card

lemma positiveComposite_positionExponent_balance {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
  positionExponent c.2 (positiveCompositeCutWord u v k c.1).val +
    (∑ i, Surjection.segmentDegree v.val c.1 i *
      Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i)) =
  positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
    positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
    (∑ i, Surjection.segmentDegree v.val c.1 i * positiveCompositeOtherActivePrefix u v k c i)

lemma positiveComposite_permutationExponent_modeq {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
  Nat.ModEq 2 (permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val)
    (permutationExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
      permutationExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
      (∑ i, Surjection.segmentDegree v.val c.1 i *
        (positiveCompositeOtherActivePrefix u v k c i +
          positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c))))
```

位置指数では、合成語の共有端点の項が元の外側の区切りの項へ戻り、
内側の区切りの各位置では§251の順位の橋を使う。
逆転指数では既存`permutationExponent_eq_active_inversions`を使い、
挿入色同士、残り色同士、異なる種類の対へ元の有限和を分ける。
§250は挿入色の活動頂点の移送に、§246は残り色の区間重みに使える。
この説明を、未供給の有限和の比較の証明済み扱いにはしない。

有限点検：`/tmp/bsw16/check-composition-exponent-decomposition.py`。
全12,233組で補和・位置指数の等式・逆転指数のmod 2・全符号のmod 2を比較し、
失敗は全て0。非退化3,745組だけに絞らず点検したが、上の主張の型では元のC452の
非退化性の仮定を保持した。有限点検はLeanの全称証明ではない。
二つの全和の法則と補和から、同じB_iの和をmod 2で二回消し、成分次数の総和eを使えば
§243の元の指数の比較へ接続する。ここは残るLeanの仕事である。

## 254. C452の異なる挿入色の順序の照合（次の法則の型、紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§253の逆転指数の比較では、C451の色ごとの順序同値を異なる色の対でも比較する必要がある。
新しい全色の経路や別の指定同値を作る前に、既存の同じ内側頂点の
`positiveCompositeSegmentInnerVertex_strict_order`と
`positiveCompositeSegmentInnerVertex_eq_of_same_source`を使って、次の法則を示せる。
真に逆の順序ならstrict_orderに矛盾し、元の位置が等しければeq_of_same_sourceで像も等しい。
既存の同じ順序・指定頂点の反映の法則で、各証明200行以内の見込み。

```lean
lemma positiveCompositeSegmentInnerVertex_lt_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z)
    (j : Fin (Surjection.occurrenceCount u.val k)) (w : Fin (c.1.val j).val)
    (y : Fin (m + n + (d + e) + q + 1))
    (hy : c.2.horizontal y = positiveCompositeSegmentPosition u v k c.1 j w) :
    positiveCompositeSegmentInnerVertex u v k c i z x hx <
      positiveCompositeSegmentInnerVertex u v k c j w y hy ↔ x < y

lemma insertedColorPathOrderIso_cross_lt_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b b' : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)))
    (y : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b'))) :
    (insertedColorPathOrderIso u v k c b x).val <
      (insertedColorPathOrderIso u v k c b' y).val ↔ x.val < y.val
```

有限点検：`/tmp/bsw16/check-inserted-cross-order.py`、全12,233組。
異なる色も含む元の全挿入頂点対について、元の経路番号の順序が内側番号の順序と
同値であることを点検した。ここはまだ紙で、同じ型のLeanの証明は次の工程。
§250の活動頂点の保存と合わせ、挿入色同士の逆転の対を元の色別同値で数えるために使う。
新しい全体の経路同値の構成を必須とはしない。

## 255. 完備化後のP⁰の紙の続き：Koszul商の模型による検出候補

一覧：済み 12／全体 48（うち追加 4）

§223の(b)の候補を、普通の商A/d^rが完全であるという仮定を入れずに具体化する。
以下は紙の候補であり、nativeな同じ指定辺までの比較を証明済みとした報告ではない。
L12aとは独立の紙の作業で、界面・drafts・新しい完備化のLeanは変更していない。

### 255.1 (a)について追加で確認した点

導来完備化は有限Koszulとのテンソルの逆極限で表せる。
また固定した複体とのRHomとして表すこともできる。
出典：[Stacks Lemma 15.93.10・15.93.18](https://stacks.math.columbia.edu/tag/091N)。
この記述から、**台の導来圏では**完備化と極限の可換性を使う候補がある。
これは反射が左随伴であることだけからの主張ではなく、RHom/有限Koszulの表示からの推論。
ただし外側の単体的実現との可換性にはならず、§223.2のambientな実現の障害は残る。
完備圏の余極限へ置き換えてL44を適用済みとはしない。

### 255.2 (b)の商の模型：正則性を仮定しない候補

記法は§223のK・Y・d・κ=F_pのまま。
各r>0に対し、κ[t]→A/pをt↦d^r、κ[t]→κをt↦0とする。
rawなCAlg対象から

`Q_r := X_raw ⊗^L_{κ[t]} κ`

という**導来**pushoutを作れば、台はK//d^rという二項Koszul商になる候補である。
κ[t]上のκは有限の二項自由解像度を持つので、dがA/pの非零因子であることは要らない。
通常のA/d^rとのテンソルへ勝手に置き換えない。

原料の二重模型が各項で通常のκ[t]代数なら、相対的な二-sided barの各項は通常のκ代数で、
その面・退化・増大は積と単位から作れる。各項のFrobeniusはt↦t^pの同じ平方と両立する。
このbarで導来商を表し、L44の同じsimplicial-cosimplicial模型へ渡すのが具体的な候補。
有限Koszulの台とのテンソルはdualizableな係数とのテンソルなので、台のTotの比較を
任意の非完全な通常の商とのテンソルの比較へ一般化する必要もない。
これらは構成の筋であって、同じnativeなCAlg対象と辺の同定まで得たという主張ではない。

実際に型を再読した本体の宣言は
`BarrattEccles.barrattEcclesBaseChange_forget`（CAlgExtensionForgetKFlat.lean）。
これは任意のfに対する**関手全体の**台の係数拡大との比較で、追加のK平坦性の仮定はない。
一方、`BarrattEccles.strictBarFunctor`・`strictBarUnderlyingExtraDegeneracy`は
自由・忘却随伴のbarであり、上の相対的なテンソルのbarそのものの完成宣言ではない。
名前だけを理由に、そのbarと同じ模型が供給済みとはしない。

### 255.3 この候補に必要な比較を露出させる

必要な仕事は次である。

1. Q_rを上の相対barの同じ二重模型で表すこと。台が元のK//d^rである比較を保持する。
2. t↦t^pによる同じFrobeniusの辺が、相対barの項ごとのa↦a^pと一致すること。
   これは指定されたFrobeniusの辺の構成であり、P⁰をcoherentな自然変換へ強める要求ではない。
3. barの実現、有限Koszulの台とのTotの交換、同じnativeな指定錐への比較。
   `baseChange_forget`だけでこの全部が自動で出るとはしない。G10/3b-4の未供給の橋は作らない。
4. 実際の完備化後のYとmod pのprincipal completionの比較。
   perfectPrismRingは零環の枝とW(R♭)の枝を持つ固定した本体の係数であり、
   必要なpのKoszul/mod p比較を、この実際の係数について供給する。
   pやdの正則性を追加仮定としてA4へ入れて隠さない。
5. §223.3のpro-zero・lim¹の計算と、YからQ_rへのΠ_0の射が共同で単射であること。

(1)〜(4)が供給されれば、各Q_rでL44によりP⁰と同じFrobeniusを比較し、
(5)とho(CAlg)上の自然性でYのΠ_0で比較する、という候補が具体化する。
Π_n (n>0)の消滅は、rawのcoconnective性とH^0のreduced性を用いる§223.3の完備化の計算で
別に扱う。全Π_nの上で完備化単位が全射だという仮定は使わない。

この候補は、§223で不足として残した「各Koszul商での同じFrobeniusの照合」への筋である。
native比較や新しい相対barの構成が48本の既存の受け渡しに含まれるかはまだ照合が要る。
新しい構成を自己承認で一覧へ足して実装することはしない。
それでも、通常の商の正則性を仮定するかcoherentなP⁰へ戻るかの二択だとはまだ言えない。
(c)が不可避という判定は現段階では出しておらず、その判定になれば§32どおり止めて報告する。

### 255.4 barとTotの比較で省いてはいけない工程

κ[t]上のκが完全であることは、**導来テンソル関手**とTotの可換性の理由であり、
二-sided barの各項とTotが項ごとに可換であるという理由ではない。
barの各項に現れるκ[t]のテンソル冪は、κ上では無限階数になり得る。
従って、二つの実現方向を対角へまとめてL44の模型へ渡す途中の比較は自動ではない。

具体的に残る候補は、相対barの加群解像度とκ[t]上の二項自由Koszul解像度の比較を保ち、
同じcosimplicialな係数に自然な鎖比較・ホモトピーを通して、
実現とTotを組み合わせた実際の台を有限Koszul模型へ照合すること。
その比較が元のnativeなbarの増大の像を表すことと、同じFrobeniusの辺も追う必要がある。
これは未検証の必要工程であり、既存`strictBarFunctor`や`baseChange_forget`の名前だけで
供給されたとは扱わない。(b)の候補を完成した証明へ昇格させず、(1)〜(3)の不足へ明示して残す。

## 256. C452の区切り・活動頂点・指数の補和：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§246〜253の12本**625行**を検証・監査した。
残り色の元の区切り・区間長、挿入色の元の区切りの全条件と末尾/内部の判定、
その0/1重みとintervalLengthの式、同じ活動頂点の移送、
色別順位と先行他色数の和の式、同じ区間内の先行他色の集合の不変性、
元のcompositionExponentと接頭区切りの重み付き和の補和までを証明した。

`positiveCompositeCutCoefficient_eq_nested_of_modeq`は、元の指数の比較が与えられた場合の
整数係数への移送だけを証明した。肝心の§243のmod 2の比較はまだ供給しておらず、
元のC452の無条件の完成には数えない。§253の二つの全和の型と§254は紙のまま。
C451・C453は前ターンで閉じたが、L12a全体は未完で一覧12/48（追加4）のまま。

対象ビルド（全て成功）：

- `m14-remaining-caesura-weights-01.log`（2,861 jobs）。
- `m14-segment-caesura-order-01.log`（2,874 jobs）。
- `m14-inserted-caesura-02.log`（2,878 jobs）。
- `m14-caesura-boundary-and-modeq-01.log`（2,909 jobs、整数係数移送）。
- `m14-caesura-weights-and-active-transport-01.log`（2,901 jobs、区切りの非推奨名修正後）。
- `m14-color-rank-active-prefix-02.log`（2,214 jobs、未使用simp引数修正後）。
- `m14-composition-exponent-complement-01.log`（1,572 jobs）。

途中では元の有限位置の記法`segmentInnerWordPosition`の展開を明示し、
非推奨のif_pos/if_negを現行名ite_eq_left/ite_eq_rightへ直した。
最終ソースの対象Lean警告0。既存の公開宣言・符号規約・型は変更していない。

小監査は2回に分け、新しく検証した分だけを対象にした。

- `audit-m14-caesura-sign-transport.log`：11モジュール・52宣言。
- `audit-m14-composition-exponent-complement.log`：1モジュール・2宣言。

合計**12モジュール・54宣言、標準三公理のみ**。
新しいsorry・公理なし。鍵はビルド・監査の間だけ一回ずつ取得し、終了時に返した。
待ちの整理券は一枚。大きい監査・rootビルド・mainの作業木での作業はしていない。

調整役への登録対象（共通接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| OccurrenceCaesuraTransport | 39 |
| RemainingCaesuraWeights | 43 |
| SegmentPositionOrder | 70 |
| SegmentWordPositions | 20 |
| SegmentBoundaryCaesura | 42 |
| SegmentCaesuraFromInner | 57 |
| InsertedCaesura | 44 |
| InsertedCaesuraBoundaryWeights | 98 |
| CompositeSignModEqTransport | 48 |
| ColorOrderActiveTransport | 37 |
| ColorRankActivePrefix | 85 |
| CompositionExponentComplement | 42 |
| **合計** | **625** |

M14実測は**20,707行**、L12a実測は**5,500行**。
旧§245のC452の残り173〜323行に対し、今回既に625行を使い、全和の比較が残る。
従って旧26,639〜31,959行を新しい完成見込みとして使わない。
他行の旧上端を据え置き、C452の旧上端323を今回625へ置き換える機械的な比較だけでも
**32,261行＋C452の未供給の全和の分**となる。
これは工程見込みの比較で、確定行数や数学的な下界ではないが、上端の超過リスクは増えている。
外枠**31,000行は変更しない**し、収まるとも主張しない。
実測と残りを分け、§32の約25,000行の中間報告で全和の実装分を含めて出し直す。
完備化後のP⁰の候補の不足（§255）も、無料で供給済みの前提や別枠の完成分へ置かない。

次は§254の異なる挿入色の順序の比較、既存の活動頂点の逆転数の有限和、
§253の位置指数・逆転指数の二つの全和の比較を同じ元の構成の法則として進める。
実テンソル・nullaryと、その後のL13以降を完成済みとして控除していない。
G10・M15・G12・drafts・界面・共有入口は変更していない。
これは同じL12aの途中の取り込み点であり、goalはactiveのまま継続する。

## 257. C452の挿入色同士の逆転対の移送（法則の型）

一覧：済み 12／全体 48（うち追加 4）

§254の二つの順序反映は対象ビルドで成功した。
次に同じ色別同値の下で、活動的な逆転対の寄与と二重有限和を照合する。
新しい経路・作用・同値を定義するものではなく、既存の指定同値の法則。
以下で `γ=c.2`、`ε=positiveCompositeInnerCut u v k c`、
`w=(positiveCompositeCutWord u v k c.1).val`、`v₊=(positiveWord v).val`、
`ι b=BarrattEccles.insertedPosition m (n+1) k b`、
`E b=insertedColorPathOrderIso u v k c b` と略記する。
`x` と `y` はそれぞれ `↥(colorPositions γ w (ι b))` と同じ `b'` の型。

```lean
lemma insertedColorPathOrderIso_active_inversionTerm ... (b b' : Fin (n + 1))
    (x : ↥(colorPositions γ w (ι b))) (y : ↥(colorPositions γ w (ι b'))) :
    (if x.val ∈ activeVertexPositions γ w ∧ y.val ∈ activeVertexPositions γ w then
      IntervalCuts.positionInversionTerm (label γ w) x.val y.val else 0) =
    (if (E b x).val ∈ activeVertexPositions ε v₊ ∧
        (E b' y).val ∈ activeVertexPositions ε v₊ then
      IntervalCuts.positionInversionTerm (label ε v₊) (E b x).val (E b' y).val else 0)

lemma insertedColorPathOrderIso_active_inversion_sum ... (b b' : Fin (n + 1)) :
    (∑ x : ↥(colorPositions γ w (ι b)), ∑ y : ↥(colorPositions γ w (ι b')),
      if x.val ∈ activeVertexPositions γ w ∧ y.val ∈ activeVertexPositions γ w then
        IntervalCuts.positionInversionTerm (label γ w) x.val y.val else 0) =
    (∑ x : ↥(colorPositions ε v₊ b), ∑ y : ↥(colorPositions ε v₊ b'),
      if x.val ∈ activeVertexPositions ε v₊ ∧ y.val ∈ activeVertexPositions ε v₊ then
        IntervalCuts.positionInversionTerm (label ε v₊) x.val y.val else 0)
```

有限点検を先に行った：`check-inserted-inversion-pairs.py`、全12,233組。
各元の挿入頂点対で、活動性・位置順序・色順序を含む0/1の寄与が一致した。
証明は§250の活動性、§254の順序、挿入色番号の共通の平行移動、
既存の `Fintype.sum_equiv` による二重和の再添字付けを用いる。各証明200行以内の見込み。

mainの指示書§33も確認した。3b-4aの取り込み後はTotの群を先にし、
その段0は待つ間に紙で準備する。G10の部品を自分で作ることはしない。

## 258. C452の色別逆転和を元の指数へ接続する法則の型

一覧：済み 12／全体 48（うち追加 4）

§257の二重和のビルドは成功した。これを元の内側の逆転指数へ結ぶため、
既存の有限和を色のfiberでまとめる二つの法則を使う。
以下は新しい逆転数の定義ではなく、同じ `positionInversionCount` の式の変形である。

```lean
lemma sum_colorPositions {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (f : Fin (m + q + 1) → ℕ) :
    (∑ a : Fin r, ∑ x : ↥(colorPositions s v a), f x.val) = ∑ x, f x

lemma positionInversionCount_eq_sum_color_pairs {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) :
    IntervalCuts.positionInversionCount (label s v) (activeVertexPositions s v) =
    ∑ a : Fin r, ∑ b : Fin r,
      ∑ x : ↥(colorPositions s v a), ∑ y : ↥(colorPositions s v b),
      if x.val ∈ activeVertexPositions s v ∧ y.val ∈ activeVertexPositions s v then
        IntervalCuts.positionInversionTerm (label s v) x.val y.val else 0
```

§257の略記で、最後の接続の型は次のとおり。

```lean
lemma positiveComposite_inserted_inversion_sum ... :
    (∑ b : Fin (n + 1), ∑ b' : Fin (n + 1),
      ∑ x : ↥(colorPositions γ w (ι b)), ∑ y : ↥(colorPositions γ w (ι b')),
      if x.val ∈ activeVertexPositions γ w ∧ y.val ∈ activeVertexPositions γ w then
        IntervalCuts.positionInversionTerm (label γ w) x.val y.val else 0) =
    permutationExponent ε v₊
```

有限点検：`check-inserted-inversion-sum.py`、12,233組。
元の全挿入色対の寄与の総和が、同じ内側の全活動頂点の逆転数に一致した。
既存のfiberwise sum、部分型の有限和、和の交換、§257と
`permutationExponent_eq_active_inversions`で証明する。各証明200行以内の見込み。

## 259. C452の全挿入色の逆転和：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§254・257〜258の法則を、新規4モジュール233行で証明した。
異なる挿入色を含む元の全頂点対の順序反映、活動逆転対の寄与と色別二重和の一致、
同じ逆転数の色のfiberによる分解を通し、全挿入色同士の逆転和が
**元の内側切断の `permutationExponent`** に一致するところまで接続した。
退化しないという追加仮定を使わず、同じ指定切断・色別同値・逆転数を比較している。

対象ビルドは `m14-inserted-cross-order-01.log`（2,895 jobs）、
`m14-color-inversion-sums-01.log` の挿入色二重和の対象（2,897 jobs中の当該一本）、
最終 `m14-composite-inserted-inversion-sum-01.log`（2,898 jobs）が成功。
途中、if内の命題の書き換えをsimpにし、有限和の交換則のimportと関数引数を明示した。
最終ソースの対象警告0。心拍数・再帰上限は増やしていない。

小監査 `audit-m14-inserted-inversion-sums.log` は
**4モジュール・12宣言、標準三公理のみ**。sorry・独自公理0。
`git diff --check`成功。各ビルド・監査で鍵を一回ずつ取り、終了してから返した。
他レーン・共有入口・共有監査・drafts・界面・mainの作業木は変更していない。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| InsertedColorCrossOrder | 56 |
| InsertedColorInversions | 73 |
| ColorInversionSums | 67 |
| CompositeInsertedInversionSum | 37 |
| **計** | **233** |

M14実測は**20,940行**、L12aは**5,733行**。
C452の全指数比較は未完。残り色同士と交差項の逆転和、§253の位置指数の全和が残る。
C452やL12a全体を完了には数えず、一覧12/48（追加4）のまま。
§256の外枠超過リスクも解消したとは主張しない。
完備化後のP⁰の比較は§223・255の未供給の比較を残しており、
(c)のcoherentなP⁰が不可避という新しい結論には至っていない。
次も同じL12aの法則を進め、main§33のTotの段0は紙で準備する。

## 260. main §33 の Tot 九欄：段0の型案と受け取りの条件（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

mainの指示書§33を確認した。3b-4aの取り込み後、M14を区切ってTotの群を先にする。
この節はその待ち時間の紙の準備で、TotのLean・界面・Assemblyは変更していない。
M14の48本と、以下のTotの九欄の一覧は別であり、M14の完了数に足さない。

### 260.1 型案：既存欄を同じBEの実例で埋める

紙の略記として、`CA S := CAlg_R S`、`U S := cAlgForgetDerived S`、
`D S := discreteCAlgUnderEmbedding S`、`CD S := barrattEcclesOfCdga S`、
`res f := barrattEcclesRestrict f`、`Q S := ComplexLimits.complexOrdinaryDerivedSource S`とする。
`FunctorIso`・`nativeConeLeg`・`nerveVertex`・`simplicialHomotopyVertexEdge`は、
Interface/Theory.leanと同じKerodonの宣言。`Complex`・`CosimplicialRingAlgebra`・
`CosimplicialCDGA`・`TotalizationCone`・`cosimplicialNerve`も同じInterfaceの宣言。
以下は略記を展開してから型検査する紙の型で、検証済みのLeanとは主張しない。

```lean
-- T01
 def barrattEcclesOfCosimplicial (S : Type u) [CommRing S] :
     nerve (CosimplicialRingAlgebra S) ⟶ CA S
-- T02
 def barrattEcclesOfCosimplicial_forget (S : Type u) [CommRing S] :
     FunctorIso (barrattEcclesOfCosimplicial S ≫ U S)
       (nerveMap (cosimplicialCochains S) ≫ Q S)
-- T03
 def barrattEcclesOfCosimplicial_cone (S : Type u) [CommRing S]
     (X : CosimplicialRingAlgebra S) :
     TotalizationCone (cosimplicialNerve X ≫ D S)
       (atVertex (barrattEcclesOfCosimplicial S) (nerveVertex X))
-- T04
 def barrattEcclesOfCosimplicial_restrict {S T : Type u} [CommRing S] [CommRing T]
     (f : S →+* T) :
     FunctorIso
       (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj
         (restrictRingAlgebra f)) ≫ barrattEcclesOfCosimplicial S)
       (barrattEcclesOfCosimplicial T ≫ res f)
-- T05
 def barrattEcclesOfCosimplicialCdga (S : Type u) [CommRing S] :
     nerve (CosimplicialCDGA S) ⟶ CA S
-- T06
 def barrattEcclesOfCosimplicialCdga_cone (S : Type u) [CommRing S]
     (X : CosimplicialCDGA S) :
     TotalizationCone (cosimplicialNerve X ≫ CD S)
       (atVertex (barrattEcclesOfCosimplicialCdga S) (nerveVertex X))
-- T07
 def barrattEcclesOfCosimplicialCdga_discrete (S : Type u) [CommRing S] :
     FunctorIso
       (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj (discreteCDGA S)) ≫
         barrattEcclesOfCosimplicialCdga S) (barrattEcclesOfCosimplicial S)
-- T08
 def barrattEcclesOfCosimplicialCdga_evalZero (S : Type u) [CommRing S] :
     SSet.Homotopy (barrattEcclesOfCosimplicialCdga S)
       (nerveMap ((evaluation SimplexCategory (CommMon (Complex S))).obj ⦋0⦌) ≫ CD S)
-- T09
 theorem barrattEcclesOfCosimplicialCdga_evalZero_leg (S : Type u) [CommRing S]
     (X : CosimplicialCDGA S) :
     (simplicialHomotopyVertexEdge (barrattEcclesOfCosimplicialCdga_evalZero S)
       (nerveVertex X)).edge =
     (nativeConeLeg (barrattEcclesOfCosimplicialCdga_cone S X).val
       (ULift.up (nerveVertex (⦋0⦌ : SimplexCategory)))).edge
```

T08は評価0への変換であり、Functors全体の同型を要求する欄ではない。
T09は同じ錐の脚の等式であって、無関係な評価射を新たに選ぶ欄ではない。
T03・T06は任意の同値な頂点でなく、T01・T05の指定頂点と一致する証明を保持する。

### 260.2 受け取るものと使う順序

③-bのmain上の報告§152・160を読んだ。
3b-4aのR01〜R05・R11/R12のTot部分には、元のBEの計算関手、全図式射の錐族、
そのnative極限性、Uを通した全錐族の比較、離散・係数変更への制限が含まれる予定。
G10の完成だけをもってこれらのBEの全族も供給済みとはしない。

実装順序は T05/T06 → T08/T09 → T01/T03 → T02/T07/T04 を候補とする。
厳密cdgaからBEの既存 `barrattEcclesOfCdga` への全関手を前合成し、
3b-4aの同じnative錐族を引き戻す。
離散代数は同じcdgaの埋め込みに制限する。
T02はR11の離散比較とG10の `cosimplicialModuleConeFamily`・
`cosimplicialModuleCone_homology` の全族比較で、同じ `cosimplicialCochains` の
複体との比較を保持して作る。対象ごとのホモロジー同型だけで全FunctorIsoとしない。

`cAlgForgetDerived_mapJoinCone_isLimit`は無条件で本体にあることを再確認した。
ただし「Uが極限を保存する」だけから元のBEの錐が極限だとは逆向きに推論しない。
元の極限性はR03から受け取り、そのU像の検収に既存の保存定理を使う。
T04/T07/T09は全図式射と指定境界・脚の比較を必要とする。
G10・BEのnative橋を自分で作らず、BFの作用をこの九欄の前提にしない。

### 260.3 置き場所と暫定の規模

新規実例ファイルは `EInfinity/BarrattEccles/Theory/` の下を候補とする。
③-bの `StrictDiagramTotalizationComparison*` 等そのものは触らない。
受け渡しで型の穴があれば、界面を変えたり仮定を足したりせず報告する。
共通入口・監査登録は調整役。Assemblyへの供給は九欄の検証後にする。

| まとまり | 既存・供給予定の原料 | 新規見込み |
| --- | --- | ---: |
| T05/T06 | R01〜R03、既存ofCdga、同じ全錐族 | 300〜550 |
| T08/T09 | R02の評価0と同じ脚・全パラメータ | 200〜400 |
| T01/T03 | 既存discreteCDGA・ofCdga_discrete、離散制限 | 150〜300 |
| T02/T07 | R04/R11、G10離散全族、同じコチェイン比較 | 350〜650 |
| T04 | R12の係数変更と指定錐族 | 200〜400 |
| Assembly・小監査前の照合・import | 既存欄を保つ包装 | 100〜200 |
| **計** | 3b-4aの上記全族を受領する前提 | **1,300〜2,500** |

これは前提を無償に自己供給する見積もりではなく、3b-4aの完成した型を受け取った後の
包装の暫定見積もり。2倍の規則なら外枠5,000行、見込みの半分の1,250行で途中報告。
受け渡しの実際の宣言名・型が確定したらその対応表を先に更新する。
Tot九欄の新規行数をM14の未証明分から勝手に控除せず、別に記録する。

この紙の準備はM14のP⁰の_totや完備化後のP⁰の完成ではない。
M14は§259の実測20,940行・一覧12/48（追加4）から続ける。

## 261. C452の残り色どうしの重み付き逆転和（法則の型）

一覧：済み 12／全体 48（うち追加 4）

元の区間長は§246で一致しているので、残り色どうしでは元の語の位置で直接比較できる。
以下は同じ指定位置・指定重みの法則で、新しい作用や構成ではない。
各証明200行以内の見込み。まず元の位置対、次に既存の全出現の順序同値で再添字付けする。

```lean
lemma positiveComposite_remaining_inversionTerm {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p p' : Fin (m + d + 1))
    (hp : (positiveWord u).val p ≠ k) (hp' : (positiveWord u).val p' ≠ k) :
    (if compositeFirstPosition u v k c.1 p < compositeFirstPosition u v k c.1 p' ∧
        (positiveCompositeCutWord u v k c.1).val (compositeFirstPosition u v k c.1 p') <
          (positiveCompositeCutWord u v k c.1).val (compositeFirstPosition u v k c.1 p) then
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
          (compositeFirstPosition u v k c.1 p) *
        intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
          (compositeFirstPosition u v k c.1 p') else 0) =
    (if p < p' ∧ (positiveWord u).val p' < (positiveWord u).val p then
      intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p *
        intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p' else 0)

lemma remainingWordPositionOrderIso_inversion_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (a b : {a : Fin (m + 1) // a ≠ k}) :
    (∑ p : ↥(Surjection.occurrences (positiveWord u).val a.val),
      ∑ p' : ↥(Surjection.occurrences (positiveWord u).val b.val),
      if p.val < p'.val ∧ (positiveWord u).val p'.val < (positiveWord u).val p.val then
        intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p.val *
          intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p'.val else 0) =
    (∑ p : ↥(Surjection.occurrences (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.remainingPosition m (n + 1) k a)),
      ∑ p' : ↥(Surjection.occurrences (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.remainingPosition m (n + 1) k b)),
      if p.val < p'.val ∧ (positiveCompositeCutWord u v k c.1).val p'.val <
          (positiveCompositeCutWord u v k c.1).val p.val then
        intervalLength c.2 (positiveCompositeCutWord u v k c.1).val p.val *
          intervalLength c.2 (positiveCompositeCutWord u v k c.1).val p'.val else 0)
```

有限点検：`check-remaining-weighted-inversions.py`、全12,233組。
退化も含め、元の残り位置の全ての対について、位置順序・色順序と両区間長を
掛けた0/1の重み付き寄与が一致した。
証明の原料は `compositeFirstPosition_strictMono`、
`positiveCompositeFirstPosition_label`、`IntervalCuts.remainingPosition_lt_iff`、
`positiveComposite_remaining_intervalLength`、`remainingWordPositionOrderIso`。
これをC452全体の完成として扱わない。

## 262. C452の二つの活動集合を水平fiberで数える法則

一覧：済み 12／全体 48（うち追加 4）

§261の残り色の和は元の語の区間長、§259の挿入色の和は活動頂点の対で表した。
両者を結ぶため、既存 `positionInversionCount_comp_monotone` と同じ証明を、
左右が別々の有限集合の場合で使う。既存の逆転寄与を再添字付けする法則で、
新しい数や作用の定義ではない。型は次。証明200行以内の見込み。

```lean
lemma sum_positionInversionTerm_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (S T : Finset (Fin N)) :
    (∑ x ∈ S, ∑ y ∈ T, IntervalCuts.positionInversionTerm (v ∘ f) x y) =
      ∑ i : Fin M, ∑ j : Fin M, if i < j ∧ v j < v i then
        (S.filter (fun x => f x = i)).card * (T.filter (fun y => f y = j)).card else 0
```

有限点検：長さ0〜3、水平値域1〜3、二色の全ラベル列、全ての二有限部分集合を
独立に選んだ7,414例で一致した。単調写像に等しい値がある場合、
逆転する色対は同じ水平fiber内にないことが、元の既存証明と同じ理由になる。
左右を同じ集合に狭めたり、色順序の条件を省いたりしない。

## 263. C452の色別の重み付き和と活動頂点の和を結ぶ法則

一覧：済み 12／全体 48（うち追加 4）

§262は対象ビルドで成功した。次は同じ色の水平fiberの濃度を元のintervalLengthで読み、
既存の色別の二つの表記を結ぶ。以下は既存の有限和・濃度の法則と証明分割であり、
新しい構成や作用ではない。各証明200行以内の見込み。

```lean
lemma sum_ite_and_eq_filter {α β : Type*} (S : Finset α) (T : Finset β)
    (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q]
    (F : α → β → ℕ) :
    (∑ x ∈ S, ∑ y ∈ T, if P x ∧ Q y then F x y else 0) =
      ∑ x ∈ S.filter P, ∑ y ∈ T.filter Q, F x y

lemma active_color_horizontal_fiber_card {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin r) (i : Fin (m + 1)) :
    (((activeVertexPositions s v).filter (fun x => label s v x = a)).filter
      (fun x => s.horizontal x = i)).card = if v i = a then intervalLength s v i else 0

lemma weighted_color_inversion_sum_eq_active {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin r) :
    (∑ i : ↥(Surjection.occurrences v a), ∑ j : ↥(Surjection.occurrences v b),
      if i.val < j.val ∧ v j.val < v i.val then
        intervalLength s v i.val * intervalLength s v j.val else 0) =
    (∑ x : ↥(colorPositions s v a), ∑ y : ↥(colorPositions s v b),
      if x.val ∈ activeVertexPositions s v ∧ y.val ∈ activeVertexPositions s v then
        IntervalCuts.positionInversionTerm (label s v) x.val y.val else 0)
```

有限点検を先に行った：水平幅0〜3、垂直幅0〜2、全二色列（非全射も含む）、
全経路と全色対の1,400例。色別fiberの濃度と、重み付き・活動頂点の両逆転和が一致。
同じ色対の逆転が零になる場合や、同じ水平位置に複数頂点がある場合も含む。
元の符号・区間長・活動性の定義は変えない。

### 263.1 部分型の二重和の明示的な証明分割

一覧：済み 12／全体 48（うち追加 4）

条件式を含む二重和では、`sum_coe_sort`の暗黙の関数推論で進まなかったので、
同じ `Finset.sum_subtype` を二回適用する形に分ける。新しい定理の内容はなく、
有限和の同じ添字の表示の照合。型は次（証明200行以内）。

```lean
lemma sum_finset_subtype_pair {α β : Type*} (S : Finset α) (T : Finset β)
    (F : α → β → ℕ) :
    (∑ x : ↥S, ∑ y : ↥T, F x.val y.val) = ∑ x ∈ S, ∑ y ∈ T, F x y
```

## 264. C452の全色対の和を四つに分ける法則

一覧：済み 12／全体 48（うち追加 4）

§263の色別の二つの逆転和の表記はビルドで一致した。
全色対の和を残り色同士・残り→挿入・挿入→残り・挿入色同士へ分ける際は、
新しい色の同値を作らず、既存 `operadInsertionEquiv` の有限和の法則を使う。
型は次。各証明200行以内。

```lean
lemma sum_insertion_positions (m n : ℕ) (k : Fin (m + 1)) (F : Fin (m + n) → ℕ) :
    (∑ a, F a) =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, F (BarrattEccles.remainingPosition m n k a)) +
      ∑ b : Fin n, F (BarrattEccles.insertedPosition m n k b)

lemma sum_insertion_position_pairs (m n : ℕ) (k : Fin (m + 1))
    (F : Fin (m + n) → Fin (m + n) → ℕ) :
    (∑ a, ∑ b, F a b) =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : {b : Fin (m + 1) // b ≠ k},
        F (BarrattEccles.remainingPosition m n k a) (BarrattEccles.remainingPosition m n k b)) +
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : Fin n,
        F (BarrattEccles.remainingPosition m n k a) (BarrattEccles.insertedPosition m n k b)) +
      (∑ a : Fin n, ∑ b : {b : Fin (m + 1) // b ≠ k},
        F (BarrattEccles.insertedPosition m n k a) (BarrattEccles.remainingPosition m n k b)) +
      (∑ a : Fin n, ∑ b : Fin n,
        F (BarrattEccles.insertedPosition m n k a) (BarrattEccles.insertedPosition m n k b))
```

有限点検：m,n=0〜3の全kについて40例。零arityも含み、
同じ残り色・挿入色の番号が全色を重複なく覆い、四つの対の和が元の二重和に一致した。
C452へは正の内側arity n+1で適用する。

## 265. C452の逆転指数を元の交差和へ帰着する法則

一覧：済み 12／全体 48（うち追加 4）

§261と§263で同じ残り色の活動逆転和を移し、§264で全色対を分け、
挿入色同士の和を§259で元の内側指数に戻す。新しい数学や構成でなく、
ここまでに証明した有限和の接続。型は次。各証明200行以内の見込み。

```lean
lemma positiveComposite_remaining_active_inversion_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (a b : {a : Fin (m + 1) // a ≠ k}) :
    (∑ x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.remainingPosition m (n + 1) k a)),
      ∑ y : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.remainingPosition m (n + 1) k b)),
      if x.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val ∧
          y.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val then
        IntervalCuts.positionInversionTerm (label c.2 (positiveCompositeCutWord u v k c.1).val)
          x.val y.val else 0) =
    (∑ x : ↥(colorPositions (positiveCompositeOuterCut u v k c) (positiveWord u).val a.val),
      ∑ y : ↥(colorPositions (positiveCompositeOuterCut u v k c) (positiveWord u).val b.val),
      if x.val ∈ activeVertexPositions (positiveCompositeOuterCut u v k c) (positiveWord u).val ∧
          y.val ∈ activeVertexPositions (positiveCompositeOuterCut u v k c) (positiveWord u).val
        then IntervalCuts.positionInversionTerm
          (label (positiveCompositeOuterCut u v k c) (positiveWord u).val) x.val y.val else 0)

lemma positiveComposite_permutationExponent_color_decomposition {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    let δ := positiveCompositeOuterCut u v k c
    let ε := positiveCompositeInnerCut u v k c
    let w := (positiveCompositeCutWord u v k c.1).val
    let uPos := (positiveWord u).val
    permutationExponent c.2 w =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : {b : Fin (m + 1) // b ≠ k},
        ∑ x : ↥(colorPositions δ uPos a.val), ∑ y : ↥(colorPositions δ uPos b.val),
        if x.val ∈ activeVertexPositions δ uPos ∧ y.val ∈ activeVertexPositions δ uPos then
          IntervalCuts.positionInversionTerm (label δ uPos) x.val y.val else 0) +
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : Fin (n + 1),
        ∑ x : ↥(colorPositions c.2 w (BarrattEccles.remainingPosition m (n + 1) k a)),
        ∑ y : ↥(colorPositions c.2 w (BarrattEccles.insertedPosition m (n + 1) k b)),
        if x.val ∈ activeVertexPositions c.2 w ∧ y.val ∈ activeVertexPositions c.2 w then
          IntervalCuts.positionInversionTerm (label c.2 w) x.val y.val else 0) +
      (∑ a : Fin (n + 1), ∑ b : {b : Fin (m + 1) // b ≠ k},
        ∑ x : ↥(colorPositions c.2 w (BarrattEccles.insertedPosition m (n + 1) k a)),
        ∑ y : ↥(colorPositions c.2 w (BarrattEccles.remainingPosition m (n + 1) k b)),
        if x.val ∈ activeVertexPositions c.2 w ∧ y.val ∈ activeVertexPositions c.2 w then
          IntervalCuts.positionInversionTerm (label c.2 w) x.val y.val else 0) +
      permutationExponent ε (positiveWord v).val
```

§259・261・263・264の有限点検済みの同じ色番号・同じ寄与だけを用いる。
この式の残り二つの交差和を、外側の指定色kとの和とg_iの補正へ戻すことが残る。
位置指数の全和もまだ未証明であり、C452やL12aを完了には数えない。

## 266. C452の交差項に使う連続区間の幅の和

一覧：済み 12／全体 48（うち追加 4）

§265の合成逆転指数の分解が対象ビルドで成功した。
交差項では、一つの挿入部分語の全区間長をまとめる必要がある。
まず既存 `hi_eq_lo_succ` と `lo_le_hi` から、同じ連続区間の幾何学的な幅の和を
元の両端へまとめる法則を示す。新しい構成ではなく既存の両端の貼り合わせの法則。
型は次（証明200行以内の見込み）。

```lean
lemma sum_consecutive_intervalWidths {m q : ℕ} (s : Cut m q)
    (a L : ℕ) (h : a + L < m + 1) :
    (∑ z : Fin (L + 1), (hi s ⟨a + z.val, by have hz := z.isLt; omega⟩ -
      lo s ⟨a + z.val, by have hz := z.isLt; omega⟩)) +
      lo s ⟨a, by omega⟩ = hi s ⟨a + L, h⟩
```

有限点検：水平幅0〜4、垂直幅0〜3の全経路と全ての非空連続区間、1,344例。
元のhi−loの和に元の最初のloを足すと、元の最後のhiに一致した。
この幅の法則だけでcaesuraの個数やC452を証明済みにはしない。

## 267. 完備化後のP⁰の紙の続き：(a)の台を項別完備化で表す候補

一覧：済み 12／全体 48（うち追加 4）

§32の三案のうち、(a)の「完備化した項を使う」に関して、
単にambientな実現と完備化を交換する§223.2の案とは別に、
**実現後の鎖模型の項別完備化**を使う候補を整理する。
ここも紙のみ。以下の未供給の構成を48本へ自己承認で追加してLeanに入ることはしない。

### 267.1 台の完備化を計算する候補の前提を明示する

Bを `perfectPrismRing/p` の実際のmod p係数、dを実際のprismの元の像とする。
固定した係数の非零の枝はW(R♭)であり、B≅R♭の指定比較を供給すればBは完全でreduced。
零環の枝も別途同じ比較で処理する。比較を証明せずBへPerfectRingインスタンスがあると
扱ったり、dの正則性を仮定したりはしない。

自分の推論：reducedな環ではd^r b=0 (r>0)から(db)^r=0、従ってdb=0。
よってBのd冪ねじれはdで殺されるという一様な境界を持つ。
[Stacks Lemma 15.95.1–2](https://stacks.math.columbia.edu/tag/0BKF)を再確認した。
この有界性のもとでは、principalなKoszul塔と通常の商の塔が同じ導来完備化を計算する。
これは一般のBや任意のdへ正則性なしで通常の商に置き換えてよい、という主張ではない。

さらに、rawな対象を表す**項別に平坦かつK平坦な**B上の厳密BE代数Kを選べれば、
K⊗^L_B B/d^rは項別の商K/d^rで計算できる。
この商の塔は複体の各次数で全射だから、導来逆極限を項別の通常の逆極限で表す候補になる。
ここで選ぶKは既に実現した複体の模型であり、二重模型の各項を完備化してから
ambientな実現と交換したことにはしない。

本体の `cofibrantCarrierKFlat` は実際に**K平坦性**の型であることを読み直した。
その宣言だけで項別の平坦性まで証明済みとはしない。
項別平坦な厳密BE代数模型を選ぶ際は、セルの次数付きの台とretractからその性質を供給し、
同じraw対象・指定Frobeniusの辺との比較を保持する必要がある。

### 267.2 連続な作用へ進める理由と、まだ残る穴

厳密なB線形BE代数の有限arityの作用は、各入力のd進フィルトレーションに関して連続。
p入力のMayの鎖の式は、各入力がd^r倍なら出力がd^{pr}倍になる。
これは同じB線形のp入力作用からの推論で、完成したP⁰の自然性だけからの推論ではない。
従って、項別完備化した複体へ同じ有限arityの作用・微分・operadの法則を
連続に延ばす厳密な候補がある。
ただし現在のκへの制限の後の模型を、理由なくB線形の模型だとはしない。

ここから完成までは次が不足している。

1. 項別完備化した厳密BE代数と、実際のnativeな `directPerfectionValue/p` の同じ比較。
   台の複体の計算だけでCAlgの同じ反射・単位の比較も終えたとはしない。
2. L44の二重模型から、上で選ぶKへ同じP⁰・同じFrobeniusを運ぶ比較。
   K平坦な置き換えをしただけで、L44の明示的なprimitiveも移ったとは扱わない。
3. P⁰と指定Frobeniusの差を与える**同じprimitiveの連続性**。
   両辺の鎖の式が連続であることだけでは、ホモロジー上の等式を完備化へ移せない。
   ここが(a)の候補でも消してはいけない主要な証明義務。
4. Frobeniusはdをd^pへ送る半線形の辺であり、通常のB線形自己射としない。
   フィルトレーションの添字の共終な変更と、指定されたnativeな辺まで追う。

特に、denseなraw鎖でP⁰とFrobeniusがホモロジー上で一致するという理由だけで、
完備化した鎖のホモロジーでも一致すると主張することはしない。
continuousなprimitiveまたは商での同じ等式が要る。

### 267.3 (a)(b)(c)の現在の比較

(a)は上の項別完備化の模型を使えば、§223.2のambientな実現との交換を
仮定しない別の構成候補になる。ただし(1)〜(4)は未供給で、完成済みではない。
(b)の単位による全射性は依然として一般に成り立たず、§255のKoszul商での検出案も
相対barとTotの比較の穴を残す。
(c)については、(a)の連続なprimitiveと(b)の商での検出の両方が不可能とはまだ示していない。
従ってcoherentなSp値P⁰が不可避という判定は、現段階では出さない。
一方で、いずれかの候補が未証明であることを「May案で完備化も通った」とは報告しない。
同じprimitive/商の比較がcoherentなP⁰なしには供給できないと判明したら、§32どおり止める。
この節は承認済みの並行する紙の比較であり、新しい厳密完備化のLeanは書いていない。

## 268. C452の残り色・四つの色対・同じ交差和への帰着：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§261〜266の**8モジュール410行**を検証した。
残り色の元の重み付き逆転寄与・全出現位置の二重和、左右が別の活動集合の水平fiber、
色別の重み付き和と同じ活動頂点の和の一致、同じ全色対の四つへの分解を証明した。
これらを§259の内側指数と接続し、元の合成の `permutationExponent` を、
**元の外側の残り色対の和＋同じ二方向の交差和＋元の内側指数**へ帰着した。
また、次の交差項に使う連続区間の幾何学的な幅の和を元の両端へまとめた。
既存の公開宣言・符号・型は変更していない。元の圏の同じ指定切断を比較している。

最終の対象ビルド（全て成功）：

- `m14-remaining-inversion-sums-01.log`：2,863 jobs。
- `m14-mixed-vertex-inversion-fibers-01.log`：1,169 jobs。
- `m14-color-pair-weighted-inversions-04.log`：1,171 jobs。
- `m14-insertion-color-sum-decomposition-01.log`：976 jobs。
- `m14-composite-permutation-color-decomposition-02.log`：2,914 jobs。
- `m14-consecutive-interval-widths-03.log`：2,208 jobs。

途中、部分型の二重和の関数引数・同じlabel関数の等式・filterの集合等式を明示し、
現行API名 `Finset.notMem_empty` と有限和の差の括弧を修正した。
未使用simp引数を除去し、最終ソースの対象警告0。心拍数・再帰上限は増やしていない。

小監査は今回の新規分だけを二回で検収：

- `audit-m14-composite-permutation-colors.log`：7モジュール・17宣言。
- `audit-m14-consecutive-interval-widths.log`：1モジュール・8宣言。

合計**8モジュール・25宣言、標準三公理のみ**。sorry・独自公理0。
各ハンドルの終了コード0、`git diff --check`成功。
鍵は各一回の対象ビルド/小監査の間だけ使用し、終わるたびに返した。
root・大きい監査・他レーン・共有入口・共有監査・drafts・界面・mainは変更していない。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| RemainingWeightedInversions | 39 |
| RemainingInversionSums | 45 |
| MixedVertexInversionFibers | 52 |
| ColorPairWeightedInversions | 107 |
| InsertionColorSumDecomposition | 40 |
| CompositeRemainingActiveInversions | 43 |
| CompositePermutationColorDecomposition | 47 |
| ConsecutiveIntervalWidths | 37 |
| **計** | **410** |

M14実測は**21,350行**、L12aは**6,143行**。
今回、残り色同士・挿入色同士を元の和へ戻したが、二つの交差和の補正と
§253の位置指数の全和はまだ未証明であり、C452・L12aを完了には数えない。
§245の残りC452上端323を、ここまでの実測増分1,268へ置き換えるだけの比較でも、
他の旧見込みを据え置いた上端は**32,904行＋C452の未供給分**となる。
これは確定行数や下界ではなく、古い工程見込みとの機械的比較。
外枠31,000行に収まるとは主張せず、旧完成見込みを再利用しない。
約25,000行での止まらない中間報告の指定は維持し、その時点で実測と残りを出し直す。
§267の新しい完備化模型の候補の仕事を、無料の前提として控除していない。

次は交差項で要る、同じ挿入部分語のcaesura数・区間長の和の法則。
同じL12aの有限和・既存構成の法則として型を先に報告して進める。
完備化後のP⁰の三案は§267に追加で整理したが、(c)が不可避との判定には至っていない。
Totの九欄は§260の紙のまま、3b-4aの取り込み後にmain§33の順に切り替える。
これは途中の取り込み点で、goalはactiveのまま。

## 269. C452の挿入部分語の区切り数を数える法則の型

一覧：済み 12／全体 48（うち追加 4）

§266の幾何学的な幅の和に、同じ部分語の区切り数を足す。
まず既存lineRankの有限集合の濃度と、その連続区間での差の法則を使う。
部分語の末尾の項を分ける有限和の表示も、同じ添字の証明分割として明示する。
以下は既存の構成の法則であり、新しい演算・作用・定理のまとまりではない。
各証明200行以内の見込み。

```lean
lemma lineRank_succ_at {n l : ℕ} (v : Fin l → Fin n) (j : Fin l) :
    Surjection.lineRank v (j.val + 1) =
      Surjection.lineRank v j.val + if Surjection.Caesura v j then 1 else 0

lemma sum_consecutive_caesuraIndicators {n l : ℕ} (v : Fin l → Fin n)
    (a L : ℕ) (h : a + L ≤ l) :
    (∑ z : Fin L, if Surjection.Caesura v
        ⟨a + z.val, by have hz := z.isLt; omega⟩ then 1 else 0 : ℕ) +
      Surjection.lineRank v a = Surjection.lineRank v (a + L)

lemma sum_fin_last {L : ℕ} (hL : 0 < L) (F : Fin L → ℕ) :
    (∑ z, F z) = (∑ z : Fin (L - 1), F ⟨z.val, by have hz := z.isLt; omega⟩) +
      F ⟨L - 1, by omega⟩
```

有限点検：長さ0〜6の全二色列、全ての開始位置と区間長の2,815例。
一位置ごとの順位の増加、全区間の0/1区切り数と順位差、末尾を分けた和が一致した。
空区間の和を零に保ち、部分語が一文字の場合も末尾の一項だけになる。

## 270. C452の同じ部分語の区切り総数と元の成分次数

一覧：済み 12／全体 48（うち追加 4）

§269を元の分割の開始位置と長さに適用し、部分語の内部の区切り数を
同じ `segmentDegree` に戻す。元の末尾の区切りは、次の同色出現があることと同値。
いずれも既存の位置と区切りの法則で、新しい構成や作用の法則のまとまりではない。
型は次。各証明200行以内の見込み。

```lean
lemma positiveOccurrencePosition_caesura_iff {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1))
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    Surjection.Caesura (positiveWord u).val (positiveOccurrencePosition u k i) ↔
      i.val + 1 < Surjection.occurrenceCount u.val k

lemma positiveComposite_segment_caesura_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (r.val i).val, if Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) then 1 else 0 : ℕ) =
      Surjection.segmentDegree v.val r i +
        if Surjection.Caesura (positiveWord u).val (positiveOccurrencePosition u k i) then 1 else 0
```

有限点検：`check-segment-caesura-sum.py`、全12,233組。
各元の部分語の区切りの総数が、元の内側の区切り数g_iと外側の元の区切りの和に一致。
一文字の部分語、末尾に同じ内側位置を共有する部分語も含む。
元の外側区切りの0/1を勝手にすべて1としない。

## 271. C452の元の部分語の区間長の和を外側と成分次数へ戻す法則

一覧：済み 12／全体 48（うち追加 4）

§269の幅と区切り数の有限和を、同じ元の部分語の両端で合わせる。
既存 `positiveCompositeOuterCut_endpoints` に渡す位置が同じことも型にする。
以下は既存の両端・有限和・同じ重みの法則で、構成の置き換えではない。
各証明200行以内の見込み。

```lean
lemma sum_nonempty_consecutive_intervalWidths {m q : ℕ} (s : Cut m q)
    (a L : ℕ) (hL : 0 < L) (h : a + L ≤ m + 1) :
    (∑ z : Fin L, (hi s ⟨a + z.val, by have hz := z.isLt; omega⟩ -
      lo s ⟨a + z.val, by have hz := z.isLt; omega⟩)) +
      lo s ⟨a, by omega⟩ = hi s ⟨a + (L - 1), by omega⟩

lemma positiveCompositeSegmentPosition_endpoints {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    positiveCompositeSegmentPosition u v k r i ⟨0, r.positive (by omega) i⟩ =
        compositeFirstPosition u v k r (positiveOccurrencePosition u k i) ∧
      positiveCompositeSegmentPosition u v k r i
        ⟨(r.val i).val - 1, by have hp := r.positive (by omega) i; omega⟩ =
        compositeLastPosition u v k r (positiveOccurrencePosition u k i)

lemma positiveComposite_segment_intervalWidth_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (c.1.val i).val,
      (hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z) -
        lo c.2 (positiveCompositeSegmentPosition u v k c.1 i z))) +
      lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) =
      hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i)

lemma positiveComposite_segment_intervalLength_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (c.1.val i).val,
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (positiveCompositeSegmentPosition u v k c.1 i z)) =
      intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val
        (positiveOccurrencePosition u k i) + Surjection.segmentDegree v.val c.1 i
```

有限点検：`check-segment-interval-length-sum.py`、全12,233組。
各部分語の幅の和と外側の両端、区間長の総和と元の外側区間長＋g_iが一致した。
退化する切断、長さ1の部分語も含む。
一般の非空長の幅の表示は§266の同じ法則の添字の表示を変えたもの。
この法則から交差和のg_iの補正を出す有限和の接続はまだ別に残る。

## 272. C452の残り位置と挿入部分語の交差寄与を戻す法則

一覧：済み 12／全体 48（うち追加 4）

§271の全区間長の式はビルドで成功した。
残り位置pと部分語iの位置zの前後は、元のpと指定色の第i出現の前後と同じ。
色順序も残り色と挿入色の元の順序規則へ戻り、同じ交差寄与を読む。
型は次。既存の指定位置と有限和の法則で、各証明200行以内の見込み。

```lean
lemma positiveComposite_remaining_segment_order {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    (compositeFirstPosition u v k r p < positiveCompositeSegmentPosition u v k r i z ↔
      p < positiveOccurrencePosition u k i) ∧
    (positiveCompositeSegmentPosition u v k r i z < compositeFirstPosition u v k r p ↔
      positiveOccurrencePosition u k i < p)

lemma positiveComposite_remaining_segment_cross_inversionTerm {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k r).val
        (compositeFirstPosition u v k r p) (positiveCompositeSegmentPosition u v k r i z) +
      IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) (compositeFirstPosition u v k r p) =
    IntervalCuts.positionInversionTerm (positiveWord u).val p (positiveOccurrencePosition u k i) +
      IntervalCuts.positionInversionTerm (positiveWord u).val (positiveOccurrencePosition u k i) p

lemma positiveComposite_segment_cross_intervalLength_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (c.1.val i).val,
      (IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k c.1).val
          (compositeFirstPosition u v k c.1 p) (positiveCompositeSegmentPosition u v k c.1 i z) +
        IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k c.1).val
          (positiveCompositeSegmentPosition u v k c.1 i z) (compositeFirstPosition u v k c.1 p)) *
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (compositeFirstPosition u v k c.1 p) *
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (positiveCompositeSegmentPosition u v k c.1 i z)) =
    (IntervalCuts.positionInversionTerm (positiveWord u).val p (positiveOccurrencePosition u k i) +
      IntervalCuts.positionInversionTerm (positiveWord u).val (positiveOccurrencePosition u k i) p) *
      intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p *
      (intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val
        (positiveOccurrencePosition u k i) + Surjection.segmentDegree v.val c.1 i)
```

有限点検：`check-remaining-segment-cross.py`、12,233組。
全残り位置・全部分語の全相対位置で、両方向の位置順序と元の交差寄与が一致した。
区間長の和は§271で同じ例を先に点検済み。この三つを用いて一部分語の交差和を畳む。
全色・全位置の交差和の再添字付けと、B_i/Pとのmod 2の照合はまだ別に残る。

## 273. C452の全合成位置の和を同じ既存の位置へ戻す法則

一覧：済み 12／全体 48（うち追加 4）

既存の `positiveCompositePosition_remaining_or_segment`、元の接頭位置の単射性、
`positiveCompositeSegmentPosition_sigma_injective` を有限和に適用する。
新しい分割・写像を公開定義せず、同じ二種類の位置の全和の法則だけを置く。
型は次。証明200行以内の見込み。

```lean
lemma positiveComposite_wordPosition_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ h, F h) =
      (∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
        F (compositeFirstPosition u v k r p.val)) +
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F (positiveCompositeSegmentPosition u v k r i z)
```

有限点検：`check-composite-word-position-sum.py`、12,233組。
元の残り位置と全挿入相対位置の像が、全合成位置を重複なく覆うことと、
その上の試験的な自然数値の和の一致を点検した。
既存の位置の全称的な分解・単射性を用いてLeanでは任意のFに示す。
交差和と位置指数の有限和を同じ指定位置で分けるために使う。

## 274. C452の全交差和への接続：次の既存の有限和の法則の型（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§265は活動頂点の色対、§272は元の語の位置ごとの重み付き交差を用いた。
両者は§263で色対ごとには既に一致している。全色・全位置での接続では、
以下の有限和の再添字付けを使う。新しい全体の経路同値や作用を作る必要はない。
以下は次の工程の型で、まだ実装した宣言には数えていない。
各証明200行以内の見込み。既存構成の法則と証明分割で一覧の項目数は増やさない。

```lean
lemma sum_occurrences {r l : ℕ} (w : Fin l → Fin r) (F : Fin l → ℕ) :
    (∑ a : Fin r, ∑ h : ↥(Surjection.occurrences w a), F h.val) = ∑ h, F h

lemma sum_non_slot_occurrences {r l : ℕ} (w : Fin l → Fin r) (k : Fin r)
    (F : Fin l → ℕ) :
    (∑ a : {a : Fin r // a ≠ k}, ∑ h : ↥(Surjection.occurrences w a.val), F h.val) =
      ∑ h : {h : Fin l // w h ≠ k}, F h.val

lemma positiveComposite_remaining_wordPosition_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ a : {a : Fin (m + 1) // a ≠ k},
      ∑ h : ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k a)), F h.val) =
      ∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
        F (compositeFirstPosition u v k r p.val)

lemma positiveComposite_inserted_wordPosition_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ b : Fin (n + 1),
      ∑ h : ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.insertedPosition m (n + 1) k b)), F h.val) =
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F (positiveCompositeSegmentPosition u v k r i z)
```

有限点検：`check-composite-word-color-aggregates.py`、12,233組。
残り色の全出現の和と元の残り位置の和、挿入色の全出現の和と全部分語の位置の和を
同じラベル・同じ試験関数で比較した。

証明の接続は次とする。

1. `sum_occurrences` は既存のfiberwise sumと `Finset.sum_subtype`。
   `sum_non_slot_occurrences` は定義域を w h≠k、値域をa≠kへ制限した同じfiberwise sum。
2. 残り色の和は `remainingWordPositionOrderIso` で色ごとに元の出現へ戻し、
   その後 `sum_non_slot_occurrences` を使う。
3. 挿入色の和は、`sum_occurrences` と§264の色の二分解で全位置の和へ戻す。
   残り色の和を(2)で同じ元の和へ戻し、§273の全位置の和の分解と比較し、
   **同じ残り位置の和をNatの加法で消去**する。新しい挿入色の逆写像を選ばない。
4. §265の二つの交差和は、まず§263で元の位置の重み付き和にし、
   有限和を交換して(2)(3)で再添字付けする。その後§272で各部分語の相対位置zを畳む。

これで元の交差和に現れるg_iの補正を露出させる。
B_iとPのmod 2の照合、および§253の位置指数の全和の比較は依然として残る。
§267の完備化後のP⁰の未供給の比較も、これら有限和の証明で閉じたとはしない。

## 275. C452の部分語の区間長と一部分語の交差和：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§269〜273の**9モジュール505行**を証明・検証した。
既存lineRankの一位置の増加と連続区間の区切り数、元の外側出現の区切り判定、
同じ部分語の区切り総数・ブロック両端・全区間幅を合わせた。
これにより同じ部分語の全区間長を
**元の外側区間長＋同じ内側成分次数g_i**へ戻した。
残り位置と部分語内の位置の両向きの順序・色順序を元の外側の交差寄与へ戻し、
一部分語にわたる重み付き交差和を、この区間長の式で畳むところまで接続した。
全合成位置の和は、既存の全位置の分解・単射性で同じ残り位置と全部分語の位置の和へ戻した。

最終の対象ビルド（全て成功）：

- `m14-consecutive-caesura-counts-03.log`：1,568 jobs。
- `m14-composite-segment-interval-lengths-02.log`：2,885 jobs。
- `m14-composite-segment-cross-sum-03.log`：2,920 jobs。
- `m14-composite-word-position-sums-03.log`：2,874 jobs。

途中の修正は、Finの移送前の型と値・加算の括弧を明示すること、
依存する添字の証明を壊さずcongrArgで順位の等式を渡すこと、
元の部分長の正性・必要な色順序のimport・書き換えの証明引数を明示すること、
Sumの左右への評価と行長を直すこと。
最終ソースの対象警告0。心拍数・再帰上限の増加なし。
200行を超える証明・ファイルなし。既存の公開宣言・符号・仮定・界面は変更していない。

小監査 `audit-m14-segment-cross-fold.log` は、今回の新規分だけの
**9モジュール・65宣言、標準三公理のみ**。sorry・独自公理0。
全ハンドルの終了コード0を確認し、鍵は一回の対象ビルド/小監査ごとに返した。
整理券は一枚ずつ。常駐セッション・rootビルド・大きい監査は使っていない。
`git diff --check`成功。他レーン・drafts・共有入口・共有監査・mainの作業木は変更していない。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| ConsecutiveCaesuraCounts | 68 |
| PositiveOccurrenceCaesuras | 44 |
| CompositeSegmentCaesuraCounts | 61 |
| CompositeSegmentIntervalWidths | 97 |
| CompositeSegmentIntervalLengths | 32 |
| RemainingSegmentOrder | 58 |
| RemainingSegmentCrossInversions | 41 |
| CompositeSegmentCrossSum | 42 |
| CompositeWordPositionSums | 62 |
| **計** | **505** |

M14実測は**21,855行**、L12aは**6,648行**。
一部分語の補正を閉じたが、全色・全位置の交差和へ戻す再添字付け、
その補正のB_i/Pとのmod 2の照合、§253の位置指数の全和は未証明。
§274は次の既存の有限和の法則の型と証明の筋だけで、まだ実装した宣言ではない。
C452・L12a全体、実テンソル・nullary、L13以降を完了に数えない。
一覧は12/48（追加4）のまま。goalはactive。

外枠31,000行は変更しない。§268で報告した古い見込みの上端の超過リスクは残る。
今回505行を足してC452の全和の未供給分を除いた機械的比較でも上端は33,409行となり、
この古い見込みを完成の新しい見込みとして再利用しない。
約25,000行で止まらず実測と残りを出し直す指定を維持する。
完備化後のP⁰は§267の連続なprimitive・同じnative対象/辺との比較を未供給のまま残す。
(c)が必要だという判定には至っておらず、そうなれば§32に従って止める。
Tot九欄の紙の準備は§260。mainの3b-4aを受領後に§33の順へ切り替える。

## 276. §274の全色・全位置の再添字付けを実装する

一覧：済み 12／全体 48（うち追加 4）

前ターンのab1d13fa5を基点に、§274の四つの型を同じ名前で実装する。
追加の有限点検として、値域0〜3・語長0〜4の全有限語158例で、
全色/指定色以外の全出現の和が元の全位置/指定色以外の和に一致した。
空語・値域零の唯一の空の写像も含む。
今回は§274の型を変更せず、任意の自然数値の関数Fについて証明する。
まだビルド・監査の完了ではなく、検証後に実測・登録一覧を別に記録する。

## 277. C452の二方向の交差和を同じ位置対へ戻す法則の型

一覧：済み 12／全体 48（うち追加 4）

§274の四つの法則は対象ビルドで成功した。
二つの変数に順に適用して、同じ元の残り位置と部分語の位置の対へ戻す。
以下はその有限和の交換と接続の型で、新しい構成ではない。
各証明200行以内の見込み。

```lean
lemma positiveComposite_remaining_inserted_wordPosition_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : Fin (n + 1),
      ∑ p : ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k a)),
      ∑ h : ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.insertedPosition m (n + 1) k b)), F p.val h.val) =
    ∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F (compositeFirstPosition u v k r p.val) (positiveCompositeSegmentPosition u v k r i z)

lemma positiveComposite_inserted_remaining_wordPosition_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ a : Fin (n + 1), ∑ b : {b : Fin (m + 1) // b ≠ k},
      ∑ p : ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.insertedPosition m (n + 1) k a)),
      ∑ h : ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k b)), F p.val h.val) =
    ∑ h : {h : Fin (m + d + 1) // (positiveWord u).val h ≠ k},
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F (positiveCompositeSegmentPosition u v k r i z) (compositeFirstPosition u v k r h.val)
```

有限点検：`check-composite-cross-word-position-sums.py`、12,233組。
同じ二つの色の全出現の対と、元の残り位置・部分語位置の対の試験的二変数関数の和を
両方向で比較した。Leanでは任意の自然数値二変数関数Fについて証明する。
反対方向は和を交換して同じ前向きの再添字付けに適用し、別の逆写像を作らない。

## 278. C452の全交差和を元の外側の位置の和へ畳む法則

一覧：済み 12／全体 48（うち追加 4）

§277の両方向の再添字付けは対象ビルドで成功した。
元の0/1の逆転寄与に区間長の積を掛ける表示を揃え、§272へ接続する。
以下は既存の寄与・区間長・有限和の法則。各証明200行以内の見込み。

```lean
lemma weighted_word_inversionTerm_eq {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) (p h : Fin (m + 1)) :
    (if p < h ∧ w h < w p then intervalLength s w p * intervalLength s w h else 0) =
    IntervalCuts.positionInversionTerm w p h * intervalLength s w p * intervalLength s w h

lemma weighted_word_inversionPair_eq {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) (p h : Fin (m + 1)) :
    (if p < h ∧ w h < w p then intervalLength s w p * intervalLength s w h else 0) +
      (if h < p ∧ w p < w h then intervalLength s w h * intervalLength s w p else 0) =
    (IntervalCuts.positionInversionTerm w p h + IntervalCuts.positionInversionTerm w h p) *
      intervalLength s w p * intervalLength s w h

lemma positiveComposite_cross_intervalLength_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    let δ := positiveCompositeOuterCut u v k c
    let w := (positiveCompositeCutWord u v k c.1).val
    let uPos := (positiveWord u).val
    (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : Fin (n + 1),
      ∑ p : ↥(Surjection.occurrences w (BarrattEccles.remainingPosition m (n + 1) k a)),
      ∑ h : ↥(Surjection.occurrences w (BarrattEccles.insertedPosition m (n + 1) k b)),
      if p.val < h.val ∧ w h.val < w p.val then
        intervalLength c.2 w p.val * intervalLength c.2 w h.val else 0) +
    (∑ a : Fin (n + 1), ∑ b : {b : Fin (m + 1) // b ≠ k},
      ∑ p : ↥(Surjection.occurrences w (BarrattEccles.insertedPosition m (n + 1) k a)),
      ∑ h : ↥(Surjection.occurrences w (BarrattEccles.remainingPosition m (n + 1) k b)),
      if p.val < h.val ∧ w h.val < w p.val then
        intervalLength c.2 w p.val * intervalLength c.2 w h.val else 0) =
    ∑ p : {p : Fin (m + d + 1) // uPos p ≠ k},
      ∑ i : Fin (Surjection.occurrenceCount u.val k),
      (IntervalCuts.positionInversionTerm uPos p.val (positiveOccurrencePosition u k i) +
        IntervalCuts.positionInversionTerm uPos (positiveOccurrencePosition u k i) p.val) *
        intervalLength δ uPos p.val *
        (intervalLength δ uPos (positiveOccurrencePosition u k i) + Surjection.segmentDegree v.val c.1 i)
```

有限点検：二つの重み0〜3と二つの0/1寄与の全64例で、点ごとの積と因数分解を確認。
さらに `check-composite-cross-interval-length-sum.py`、12,233組で、
全色の二方向の重み付き交差和が、元の外側の位置とg_iによる右辺に一致した。
退化する切断も含む。Leanでは既存の和の再添字付けと、同じ一部分語の和を使う。
この式から全逆転指数のmod 2、位置指数の釣り合いまで済んだとは扱わない。

## 279. C452の元の外側交差和に要る指定色の全出現の和

一覧：済み 12／全体 48（うち追加 4）

§278の全交差和の右辺の外側区間長の部分を、元の外側逆転指数へ戻すため、
既存の指定色の全出現をその元の番号で読む。元の語長の移送の法則も明示する。
全色対の分解は§264のarity 1の既存の分解を用い、別の分割を作らない。
各証明200行以内の見込み。

```lean
lemma positiveOccurrencePosition_complete {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p = k) :
    ∃ i : Fin (Surjection.occurrenceCount u.val k), positiveOccurrencePosition u k i = p

lemma positiveWord_slot_position_sum {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1)) (F : Fin (m + d + 1) → ℕ) :
    (∑ p : ↥(Surjection.occurrences (positiveWord u).val k), F p.val) =
      ∑ i : Fin (Surjection.occurrenceCount u.val k), F (positiveOccurrencePosition u k i)

lemma sum_position_pairs_with_slot (m : ℕ) (k : Fin (m + 1))
    (F : Fin (m + 1) → Fin (m + 1) → ℕ) :
    (∑ a, ∑ b, F a b) =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : {b : Fin (m + 1) // b ≠ k}, F a.val b.val) +
      (∑ a : {a : Fin (m + 1) // a ≠ k}, F a.val k) +
      (∑ b : {b : Fin (m + 1) // b ≠ k}, F k b.val) + F k k
```

位置の有限点検は§270・274の全出現の列挙と同じもの、
色対は§264のarity 1の同じ色番号の分解である。
指定色同士の逆転寄与が零になることと合わせ、外側の交差和を元の指数へ戻す。
``sum_position_pairs_with_slot``は任意のFに対して対角F k kも残し、
一般の和でその項が零だという仮定は付けない。

## 280. C452の元の外側の交差和と逆転指数を結ぶ有限和の法則

一覧：済み 12／全体 48（うち追加 4）

§278の元の位置ごとの式に、外側の元の逆転指数を合わせる。
既存の和を色のfiberでまとめ、指定色の出現だけを元の番号で読む。
以下は既存の有限和の再添字付けと証明分割。各証明200行以内の見込み。

```lean
lemma permutationExponent_eq_sum_occurrence_pairs {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) :
    permutationExponent s w =
    ∑ a : Fin r, ∑ b : Fin r,
      ∑ p : ↥(Surjection.occurrences w a), ∑ h : ↥(Surjection.occurrences w b),
      if p.val < h.val ∧ w h.val < w p.val then
        intervalLength s w p.val * intervalLength s w h.val else 0

lemma positiveWord_remaining_slot_position_sum {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1))
    (F : Fin (m + d + 1) → Fin (m + d + 1) → ℕ) :
    (∑ a : {a : Fin (m + 1) // a ≠ k},
      ∑ p : ↥(Surjection.occurrences (positiveWord u).val a.val),
      ∑ h : ↥(Surjection.occurrences (positiveWord u).val k), F p.val h.val) =
    ∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
      ∑ i : Fin (Surjection.occurrenceCount u.val k), F p.val (positiveOccurrencePosition u k i)

lemma positiveWord_slot_cross_position_sum {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1))
    (F : Fin (m + d + 1) → Fin (m + d + 1) → ℕ) :
    (∑ a : {a : Fin (m + 1) // a ≠ k},
      ∑ p : ↥(Surjection.occurrences (positiveWord u).val a.val),
      ∑ h : ↥(Surjection.occurrences (positiveWord u).val k), F p.val h.val) +
    (∑ b : {b : Fin (m + 1) // b ≠ k},
      ∑ p : ↥(Surjection.occurrences (positiveWord u).val k),
      ∑ h : ↥(Surjection.occurrences (positiveWord u).val b.val), F p.val h.val) =
    ∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
      ∑ i : Fin (Surjection.occurrenceCount u.val k),
        (F p.val (positiveOccurrencePosition u k i) + F (positiveOccurrencePosition u k i) p.val)
```

有限点検の原料は§276〜279の同じ全出現・元の番号・色対の分解。
全和の交換と指定色の全出現の列挙だけを使い、対象ごとに別の出現を選ばない。
対角の指定色同士の逆転は実際に零であることを元のラベルの等式から確認して用いる。

## 281. C452の逆転指数の整数としての釣り合い（法則の型）

一覧：済み 12／全体 48（うち追加 4）

ここまでの同じ有限和を接続する。外側の元の逆転指数は、残り色同士と
元の指定色との交差へ分かれる。合成の交差の外側区間長の部分をその和へ戻すと、
成分次数g_iの補正が残る。型は次。既存の逆転指数と区間長の法則の接続で、
新しい構成・作用ではない。各証明200行以内の見込み。

```lean
lemma positiveWord_permutationExponent_with_slot {m d q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1)) (s : Cut (m + d) q) :
    let w := (positiveWord u).val
    permutationExponent s w =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : {b : Fin (m + 1) // b ≠ k},
        ∑ p : ↥(Surjection.occurrences w a.val), ∑ h : ↥(Surjection.occurrences w b.val),
        if p.val < h.val ∧ w h.val < w p.val then
          intervalLength s w p.val * intervalLength s w h.val else 0) +
      ∑ p : {p : Fin (m + d + 1) // w p ≠ k},
        ∑ i : Fin (Surjection.occurrenceCount u.val k),
        (IntervalCuts.positionInversionTerm w p.val (positiveOccurrencePosition u k i) +
          IntervalCuts.positionInversionTerm w (positiveOccurrencePosition u k i) p.val) *
          intervalLength s w p.val * intervalLength s w (positiveOccurrencePosition u k i)

lemma positiveComposite_permutationExponent_cross_balance {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    let δ := positiveCompositeOuterCut u v k c
    let ε := positiveCompositeInnerCut u v k c
    let w := (positiveWord u).val
    permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val =
      permutationExponent δ w + permutationExponent ε (positiveWord v).val +
      ∑ i : Fin (Surjection.occurrenceCount u.val k),
        Surjection.segmentDegree v.val c.1 i *
        (∑ p : {p : Fin (m + d + 1) // w p ≠ k},
          (IntervalCuts.positionInversionTerm w p.val (positiveOccurrencePosition u k i) +
            IntervalCuts.positionInversionTerm w (positiveOccurrencePosition u k i) p.val) *
            intervalLength δ w p.val)
```

有限点検：`check-composite-permutation-cross-balance.py`、12,233組。
元の逆転指数は、mod 2だけでなくこの自然数の等式として一致した。
対角の指定色同士の逆転は同じ色なので零、成分次数の補正は非負のまま残す。
この等式の後に、括弧内の交差寄与をB_i/Pに照合するmod 2の仕事が残る。
位置指数の釣り合いも未完であり、C452全体を完了には数えない。

## 282. 完備化後のP⁰の紙の続き：実際のmod p係数の既存API

一覧：済み 12／全体 48（うち追加 4）

§267.1で未供給として残した係数の比較について、実際の本体とMathlibの型を読み直した。
Leanの新しい完備化の構成は書かず、次の既存の宣言まで確認した。

- 本体 `BhattScholze/Prism/Perfectoid/AinfClassical.lean`、名前空間Semiperfectoidの
  `ainfClassicalCoefficients_of_nonunit` は、固定した係数環がWittVector p (PreTilt R p)である式。
  同じファイルの `ainfClassicalCoefficients_of_isUnit` と
  `perfectoid_subsingleton_of_isUnit` は、pが単元の枝をRと零環へ戻す。
- Mathlib `RingTheory/WittVector/Complete.lean` の `WittVector.quotientPEquiv` は、
  完全な標数p環kに対するWittVector p kの(p)による商とkの環同型。
  `quotientPEquiv_mk` は同じWitt代表元の像を第0係数で与える。
- Mathlib `RingTheory/Perfection.lean` のPreTiltの定義と直後の三つのinstanceは、
  実際のPreTiltのCommRing・CharP・PerfectRingを供給している。

従って非単元の枝の**通常の係数環の商**については、上の固定した式を移送して
`quotientPEquiv`を適用する筋が本体の既存APIから具体化した。
これはBを任意のreducedな係数に取り替える仮定ではない。
prismの元dのmod pの像も、同じ第0係数の像を追う必要がある。
単元の枝は既存のSubsingletonの結論で処理し、除外しない。

ただしこの環同型だけで、実際のCAlgの導来mod pとd進完備化の交換、
同じnativeな `directPerfectionValue/p`、同じFrobeniusの辺までの比較を供給したとはしない。
§267の項別に平坦な模型、連続なBE作用と同じprimitiveの移送も残る。
§255の(b)の相対bar/Totの比較も別の未供給の工程である。
(c)のcoherentなP⁰が不可避との結論には至っていない。
新しい係数仮定・型の変更・完備化のLeanを追加していない。

## 283. C452の逆転指数と交差補正の整数の釣り合い：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§274・276〜281の**12モジュール651行**を検証した。
全色と全位置の同じ再添字付け、元の指定色の全出現の和、
元の色対の二分解と同じ外側交差和を接続した。
`positiveComposite_permutationExponent_cross_balance` により、元の合成逆転指数が
**元の外側指数＋元の内側指数＋成分次数g_iと元の外側交差寄与による補正**と、
自然数の等式として一致するところまで閉じた。
非退化性や追加の模型の仮定を足さず、同じCut・区間長・元の指定位置を比較している。

最終の対象ビルド（全て成功）：

- `m14-composite-word-color-sums-01.log`：2,885 jobs。
- `m14-composite-cross-word-position-sums-01.log`：2,886 jobs（後続の対象で行長修正も検証）。
- `m14-slot-occurrence-and-cross-sums-01.log` のPositiveOccurrenceSumsと
  CompositeCrossIntervalLengthSumsの対象（全束のSlotColorPairSumsのimport不足は次で修正）。
- `m14-outer-slot-cross-position-sums-01.log`：2,253 jobs（SlotColorPairSumsのimport修正済み）。
- `m14-composite-permutation-cross-balance-02.log`：2,965 jobs。

途中、既存のFinの一項の和のimport、行長と、語型に依存する書き換えをsimpへ直した。
最終ソースの対象警告0。心拍数・再帰上限を増やしていない。
200行を超える証明・ファイルなし。既存の公開宣言・界面・符号・仮定は変更していない。

今回新規分だけの小監査 `audit-m14-permutation-cross-balance.log` は
**12モジュール・25宣言、標準三公理のみ**。sorry・独自公理0。
全ハンドルの終了コード0を確認し、`git diff --check`成功。
鍵は一回の対象ビルド/小監査の間だけ取得し、整理券一枚ずつ、終わるたびに返した。
常駐セッション・rootビルド・大きい監査・他レーン・共有入口・共有監査・drafts・mainの作業木は変更していない。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| OccurrenceFiberSums | 57 |
| CompositeRemainingWordPositionSums | 40 |
| CompositeInsertedWordPositionSums | 34 |
| CompositeCrossWordPositionSums | 84 |
| WeightedWordInversionPairs | 35 |
| CompositeCrossIntervalLengthSums | 76 |
| PositiveOccurrenceSums | 50 |
| SlotColorPairSums | 35 |
| WordColorInversionSums | 48 |
| SlotCrossWordPositionSums | 71 |
| OuterPermutationSlotSum | 54 |
| CompositePermutationCrossBalance | 67 |
| **計** | **651** |

M14実測は**22,506行**、L12aは**7,299行**。
整数の逆転指数の補正まで閉じたが、括弧内の元の交差寄与とB_i/Pのmod 2の照合、
§253の位置指数の全和はまだ未証明。C452全体・L12a全体・実テンソル・nullary・
L13以降を完了に数えず、一覧12/48（追加4）のまま。goalはactive。
外枠31,000行は変更せず、旧見込みの上端の超過リスクも解消したとは主張しない。
約25,000行で止まらず実測と残りを出し直す指定を維持する。
完備化後のP⁰の未供給の仕事も無料の前提へ置かない（§282）。
(c)が必要と判明すれば§32に従って止める。Totの紙の準備は§260、3b-4aの受領後は§33の順へ切り替える。

次は§281の補正の括弧を、元の外側の他色の先行活動頂点数B_iと
元のprefixOutputDegreeのPへmod 2で照合する。
既存の重み付き有限和と水平fiberの濃度を使い、同じ切断と元の出現位置で読む。

## 284. C452の交差補正と二つの接頭和の整数の法則

一覧：済み 12／全体 48（うち追加 4）

前ターンafe18f779の整数の逆転指数の釣り合いを基点にする。
指定位置pより前の小さい色の重みは、他色の先行数Bと全小色の重みPで二度数える。
従って交差寄与Cにその重みの二倍を足すとB+Pになる。
以下は元の位置順序・色順序と有限和の法則で、新しい演算や構成ではない。
型は次。各証明200行以内の見込み。

```lean
lemma word_cross_weight_term_balance {r l : ℕ} (w : Fin l → Fin r)
    (k : Fin r) (p : Fin l) (hp : w p = k) (j : Fin l) (a : ℕ) :
    (IntervalCuts.positionInversionTerm w j p + IntervalCuts.positionInversionTerm w p j) * a +
      2 * (if j < p ∧ w j < k then a else 0) =
    (if j < p ∧ w j ≠ k then a else 0) + (if w j < k then a else 0)

lemma word_cross_weight_balance {r l : ℕ} (w : Fin l → Fin r)
    (k : Fin r) (p : Fin l) (hp : w p = k) (a : Fin l → ℕ) :
    (∑ j : {j : Fin l // w j ≠ k},
      (IntervalCuts.positionInversionTerm w j.val p +
        IntervalCuts.positionInversionTerm w p j.val) * a j.val) +
      2 * (∑ j : Fin l, if j < p ∧ w j < k then a j else 0) =
    (∑ j : Fin l, if j < p ∧ w j ≠ k then a j else 0) +
      (∑ j : Fin l, if w j < k then a j else 0)
```

有限点検：値域0〜3・語長0〜4の全語と指定位置534例。
点ごとの重み0〜3と、位置ごとの試験重みについて等式とmod 2を点検した。
同色の位置と指定位置自身の寄与は零であり、全和から除くことをLeanでも示す。
この段のaは任意の自然数重み。次に元のintervalLengthを代入して同じ活動頂点数へ戻す。

## 285. C452のB_iを元の水平位置の重み付き和で読む法則

一覧：済み 12／全体 48（うち追加 4）

§284の任意の重みに元のintervalLengthを代入する。
元の活動頂点を水平fiberで数え、同じ外側位置pの前の他色の濃度へ戻す。
型は次。既存の有限濃度・水平座標の順序・区間長の法則で、各証明200行以内の見込み。

```lean
lemma active_filter_horizontal_card {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) (P : Fin (m + 1) → Prop) [DecidablePred P] :
    ((activeVertexPositions s w).filter (fun z => P (s.horizontal z))).card =
      ∑ j : Fin (m + 1), if P j then intervalLength s w j else 0

lemma other_before_iff_horizontal_before {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) (k : Fin r) (p : Fin (m + 1)) (hp : w p = k)
    (x j : Fin (m + q + 1)) (hx : s.horizontal x = p) :
    (j < x ∧ label s w j ≠ k) ↔ (s.horizontal j < p ∧ label s w j ≠ k)

lemma other_active_prefix_card_eq_weighted {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) (k : Fin r) (p : Fin (m + 1)) (hp : w p = k)
    (x : Fin (m + q + 1)) (hx : s.horizontal x = p) :
    ((activeVertexPositions s w).filter (fun z => z < x ∧ label s w z ≠ k)).card =
      ∑ j : Fin (m + 1), if j < p ∧ w j ≠ k then intervalLength s w j else 0
```

有限点検：`check-native-cross-prefix-counts.py`。
水平幅0〜3・垂直幅0〜2の全経路、全二色列と各元の頂点1,796例で、
B_iのnativeな先行他色数、水平位置の重み付き和、小色の全数、交差寄与のmod 2が一致した。
任意の同じ水平位置の頂点xで他色の先行数が変わらないことも含む。
指定色自身の先行頂点をB_iへ混ぜず、元のラベルの不等式を保持する。

## 286. C452の同じnativeな先行数と元のPへのmod 2の移送

一覧：済み 12／全体 48（うち追加 4）

§284の整数の法則と§285の元の水平fiberの濃度を合わせる。
小さい色の出力次数の和は既存 `prefixOutputDegree_eq_active_card` で元の活動頂点数。
元の `positiveNestedPrefixDegree` の再帰的な和も、同じ有限添字でこのPに一致させる。
型は次。既存の有限濃度・次数・mod 2の法則で、各証明200行以内の見込み。

```lean
lemma cross_intervalLength_modeq_prefix {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin r) (p : Fin (m + 1)) (hp : v.val p = k)
    (x : Fin (m + q + 1)) (hx : s.horizontal x = p) :
    Nat.ModEq 2
      (∑ j : {j : Fin (m + 1) // v.val j ≠ k},
        (IntervalCuts.positionInversionTerm v.val j.val p +
          IntervalCuts.positionInversionTerm v.val p j.val) * intervalLength s v.val j.val)
      (((activeVertexPositions s v.val).filter (fun z => z < x ∧ label s v.val z ≠ k)).card +
        ∑ b ∈ Finset.univ.filter (fun b : Fin r => b < k), outputDegree s v b)

lemma positiveNestedPrefixDegree_eq_prefixOutputDegree {m d q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1)) (s : Cut (m + d) q) :
    positiveNestedPrefixDegree u k s =
      ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) => b < k), outputDegree s (positiveWord u) b
```

元のnativeな頂点xは任意の同じ水平位置pでよく、B_iには既に指定した最初の順位を使う。
Pの前方因子自身を含めず、同じ出力次数を使う。
有限点検の原料は§285の1,796例と、既存のprefixFamilyの同じ有限添字の表示である。
この移送ではCAlg・BE作用・Tot・界面に触れない。

## 287. C452の元のB_iと逆転指数のmod 2を接続する型

一覧：済み 12／全体 48（うち追加 4）

§286のgenericなnative頂点の式に、§253で指定した同じ色別の最初の順位を代入する。
`positiveCompositeOtherActivePrefix` の定義は§253の型・本体のまま。
別の水平和で定義し直さず、既存の `colorIntervalFirst` と `colorPositionEquiv` を使う。
接続の補題の型は次。各証明200行以内の見込み。

```lean
lemma positiveComposite_crossWeight_modeq {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    Nat.ModEq 2
      (∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
        (IntervalCuts.positionInversionTerm (positiveWord u).val p.val
            (positiveOccurrencePosition u k i) +
          IntervalCuts.positionInversionTerm (positiveWord u).val
            (positiveOccurrencePosition u k i) p.val) *
          intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p.val)
      (positiveCompositeOtherActivePrefix u v k c i +
        positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c))

lemma positiveComposite_permutationExponent_modeq {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (_h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Nat.ModEq 2 (permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val)
      (permutationExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
        permutationExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
        (∑ i, Surjection.segmentDegree v.val c.1 i *
          (positiveCompositeOtherActivePrefix u v k c i +
            positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c))))
```

有限点検：`check-composite-permutation-modeq-native-prefix.py`、12,233組。
B_iには同じ外側切断のその区間の最初のnative頂点を用い、
元の活動頂点の先行他色数と小色の全数Pで元の逆転指数のmod 2が一致した。
`positiveComposite_permutationExponent_modeq`の非退化性の仮定は§253の型どおりに残す。
同じ整数の釣り合いと各iでの合同に成分次数を掛けて足すだけで接続する。
位置指数の全和は依然として未完であり、C452全体は完了に数えない。

## 288. C452の位置指数を外側と部分語内部へ分ける法則の型

一覧：済み 12／全体 48（うち追加 4）

§287の逆転指数のmod 2はビルドと新規7本22宣言の小監査が成功した。
残る位置指数では、同じ全合成位置の和を§273で分け、
残り位置と各部分語の末尾を元の外側の区切り・高さへ戻す。
型は次。既存の区切りと両端、有限和の接続の法則で各証明200行以内の見込み。

```lean
lemma positiveWord_position_sum {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (F : Fin (m + d + 1) → ℕ) :
    (∑ p, F p) =
      (∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k}, F p.val) +
      ∑ i : Fin (Surjection.occurrenceCount u.val k), F (positiveOccurrencePosition u k i)

lemma positiveComposite_remaining_positionTerm {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    (if Surjection.Caesura (positiveCompositeCutWord u v k c.1).val
        (compositeFirstPosition u v k c.1 p) then
      hi c.2 (compositeFirstPosition u v k c.1 p) else 0) =
    (if Surjection.Caesura (positiveWord u).val p then
      hi (positiveCompositeOuterCut u v k c) p else 0)

lemma positiveComposite_segment_positionTerm_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (c.1.val i).val,
      if Surjection.Caesura (positiveCompositeCutWord u v k c.1).val
          (positiveCompositeSegmentPosition u v k c.1 i z) then
        hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z) else 0) =
    (if Surjection.Caesura (positiveWord u).val (positiveOccurrencePosition u k i) then
      hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) else 0) +
    ∑ z : Fin ((c.1.val i).val - 1),
      if Surjection.Caesura v.val
          ⟨c.1.start i + z.val, by have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩
      then hi c.2 (positiveCompositeSegmentPosition u v k c.1 i
        ⟨z.val, by have hz := z.isLt; omega⟩) else 0

lemma positiveComposite_positionExponent_decomposition {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    positionExponent c.2 (positiveCompositeCutWord u v k c.1).val =
      positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin ((c.1.val i).val - 1),
        if Surjection.Caesura v.val
            ⟨c.1.start i + z.val, by have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩
        then hi c.2 (positiveCompositeSegmentPosition u v k c.1 i
          ⟨z.val, by have hz := z.isLt; omega⟩) else 0
```

有限点検：`check-composite-position-exponent-decomposition.py`、全12,233組。
元の合成位置指数が、元の外側位置指数と部分語内部の区切り高さの和に一致した。
共有端点は外側の元の区切りへ戻し、各部分語の末尾を内部の和へ重ねない。
内側切断の同じ順位とこの内部の高さの和の比較は、まだ残る工程。

## 289. C452の位置指数の残る順位・高さ・全和の接続（次の型、紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§288の合成側の位置指数の分解は検証した。
次は既存の同じ内側辺の高さと色別順位を使い、内部の各項を比較する。
以下は次の工程の型で、実装済みの宣言には数えない。
すべて既存の構成の法則、有限位置の分解・数え上げ、同じ指定射の照合、証明分割。
各証明200行以内の見込み。新しいCut・作用・位相的な比較を作るものではない。

```lean
lemma caesura_word_eq_mp {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l)
    (p : Fin l') (q : Fin l) (hpq : p.val = q.val) :
    Surjection.Caesura (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val p ↔
      Surjection.Caesura v.val q

lemma caesuraRank_word_eq_mp {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l)
    (p : Fin l') (q : Fin l) (hpq : p.val = q.val) :
    Surjection.caesuraRank (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val p =
      Surjection.caesuraRank v.val q

lemma positionExponent_eq_edge_sum {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) :
    positionExponent s w =
      ∑ a : Fin m, if Surjection.Caesura w a.castSucc then (cutHeights s a).val else 0

lemma sum_overlap_internal_positions {t n e : ℕ}
    (r : Surjection.OverlapPartition t ((n + 1) + e)) (ht : 0 < t)
    (F : Fin (n + e) → ℕ) :
    (∑ a, F a) = ∑ i : Fin t, ∑ z : Fin ((r.val i).val - 1),
      F ⟨r.start i + z.val, by have hb := r.start_add_length_le i; have hz := z.isLt; omega⟩

lemma sum_internal_caesuraIndicators {r t n e : ℕ}
    (w : Fin ((n + 1) + e) → Fin r)
    (o : Surjection.OverlapPartition t ((n + 1) + e)) (i : Fin t) :
    (∑ z : Fin ((o.val i).val - 1), if Surjection.Caesura w
      ⟨o.start i + z.val, by have hb := o.start_add_length_le i; have hz := z.isLt; omega⟩
      then 1 else 0 : ℕ) = Surjection.segmentDegree w o i

lemma positiveComposite_segment_internal_height_balance {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin ((c.1.val i).val - 1)) :
    hi (positiveCompositeInnerCut u v k c) (positiveCompositeSegmentInnerPosition u v k c i
        ⟨z.val, by have hz := z.isLt; omega⟩) + positiveCompositeOtherActivePrefix u v k c i =
      hi c.2 (positiveCompositeSegmentPosition u v k c.1 i
        ⟨z.val, by have hz := z.isLt; omega⟩) +
      Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i)

lemma positiveComposite_inner_positionExponent_decomposition {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val =
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin ((c.1.val i).val - 1),
        if Surjection.Caesura v.val
            ⟨c.1.start i + z.val, by have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩
        then hi (positiveCompositeInnerCut u v k c) (positiveCompositeSegmentInnerPosition u v k c i
          ⟨z.val, by have hz := z.isLt; omega⟩) else 0
```

有限点検：`check-composite-position-inner-height-balance.py`、全12,233組。
全部分語の全内部位置で「同じ内側の右端順位＋元のB_i＝元の合成の高さ＋元の区切り順位」を確認。
内側位置指数が同じ内部位置の和になることも確認した。退化する切断も含む。

既存の宣言で進める筋は次。

1. 語長の二つの移送は `word_eq_mp_value` と同じく長さの等式を消去し、同じ値のFinを等置する。
2. 元の位置指数の最後の位置には後続位置がないのでCaesuraは偽。
   `sum_fin_last` と `cutHeights` の定義で元の辺の和へ書き直す。
3. 内部位置の有限和は開始位置＋zで写す。逆の所属番号は既存 `segmentEdgeOwner`。
   `segmentEdgeOwner_start_le`・`segmentEdgeOwner_end_gt`・`segmentEdgeOwner_unique` により
   同じ辺を重複なく読む。新しい公開の所属写像を作らない。
4. 内部区切り数の式は§270の証明内ですでに使った
   `sum_consecutive_caesuraIndicators` と同じ行順位の差を単独で再利用する。
5. 高さの式は、内部辺aの所属番号がiであることを同じuniqueで確かめ、
   `compositeInnerEdge_val` からその像が元の部分語の同じ位置であることを示す。
   `positiveCompositeInnerCut_rank_mem`・`positiveCompositeInnerCut_vertices`、
   `colorRank_add_other_active_prefix` をその同じ辺へ適用する。
   B_iは `other_active_prefix_eq_on_interval` で元の最初の順位と同じに戻す。
   最後に語長の区切り順位の移送を使う。
6. 内側位置指数の式は(2)(3)と同じ語長のCaesuraの移送で得る。
   各内部位置で(5)を同じCaesuraの0/1で重み付けして足し、(4)で一定のB_i・順位の和をg_i倍へ戻す。
   §288と合わせれば、§253の `positiveComposite_positionExponent_balance` の型へ接続する。

その後の元の係数の接続は、§287の逆転指数のmod 2と§253の位置指数の釣り合い、
`compositionExponent_add_prefixRanks` を合わせる。
成分次数の総和 `sum_segmentDegree` でPの和をe*Pへ戻し、
元の `positiveCompositeCutCoefficient_eq_nested_of_modeq` に渡す。
この数値の符号の接続を、実テンソル・nullaryやL12a全体の完成と混同しない。

## 290. C452の逆転指数のmod 2と合成位置指数の分解：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§284〜288の**10モジュール485行**を検証した。
元の交差補正に二度数える先行小色を足す整数の式、同じ水平fiberによるB_iの濃度、
元の小色の出力次数Pとの比較を合わせた。
`positiveComposite_permutationExponent_modeq` は、§253と同じB_i・P・非退化性の型で完成。
B_iは§253どおり同じ `colorIntervalFirst`・`colorPositionEquiv` によるnativeな定義を使用した。
さらに、元の合成位置指数を**元の外側位置指数＋同じ部分語内部の区切り高さの全和**へ分解した。

最終の対象ビルド（全て成功）：

- `m14-word-cross-weight-balance-03.log`：855 jobs。
- `m14-cross-interval-prefix-modeq-01.log`：2,893 jobs。
- `m14-composite-permutation-modeq-02.log`：2,991 jobs（前方次数の行長修正も検証済み）。
- `m14-composite-position-exponent-decomposition-02.log`：2,898 jobs。

途中、指定位置そのものの場合を分けて関数の値の等式を明示し、
同じ定義等式の照合には `backward.isDefEq.respectTransparency false` をOtherActivePrefixCountsで使った。
心拍数・再帰上限は増やしていない。B_i/Pの別名は定義を展開して揃えた。
位置指数では同じ内側位置の記法を展開した。最終ソースの対象警告0。
200行を超える証明・ファイルなし。既存の公開宣言・界面・符号・仮定は変更していない。

新規分だけの小監査：

- `audit-m14-composite-permutation-modeq.log`：7モジュール・22宣言。
- `audit-m14-position-exponent-decomposition.log`：3モジュール・20宣言。

合計**10モジュール・42宣言、標準三公理のみ**。sorry・独自公理0。
全ハンドルの終了コード0を確認し、鍵は各一回の対象ビルド/小監査の間だけ使用して返した。
整理券は一枚ずつ。常駐セッション・rootビルド・大きい監査・他レーン・共有入口・共有監査・
drafts・mainの作業木は変更していない。`git diff --check`成功。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| WordCrossWeightBalance | 57 |
| ActiveHorizontalFilterCounts | 35 |
| OtherActivePrefixCounts | 51 |
| CrossIntervalPrefixModeq | 37 |
| NestedPrefixDegreeSum | 35 |
| CompositeOtherActivePrefix | 59 |
| CompositePermutationModeq | 37 |
| PositiveWordPositionSums | 38 |
| CompositePositionTerms | 84 |
| CompositePositionExponentDecomposition | 52 |
| **計** | **485** |

M14実測は**22,991行**、L12aは**7,784行**。
逆転指数のmod 2は閉じたが、§289の内側の同じ順位・高さの全和の接続は紙のまま。
§253の位置指数の釣り合い・元の係数の接続は未完で、C452/L12a全体を完了には数えない。
実テンソル・nullary・L13以降も未完であり、一覧12/48（追加4）のまま、goalはactive。
外枠31,000行は変更せず、旧見込みの上端の超過リスクは残す。
約25,000行で止まらず実測と残りを出し直す指定を維持する。
完備化後のP⁰の未供給の工程は§267・282のまま、無料の前提へ置いていない。
(c)が必要との判定には至っておらず、その判定なら§32どおり止める。
Tot九欄の段0は§260。3b-4aを受領したらmain§33の順へ切り替える。
次は§289の型の法則を同じ指定辺・同じ順位で証明する。


## 291. C452：位置指数の釣り合いと元の整数係数の厳密な一致、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§289の七つの型をすべて実装し、§253の位置指数の釣り合い、§243の全指数のmod 2、
§199の `positiveCompositeCutCoefficient_eq_nested` へ接続した。
同じcompositionSignとcutSignの積が、元の二段切断の整数係数そのものに一致する。
元の非退化性の仮定は保持し、指数の合同を追加仮定にはしていない。
ホモトピー圏や別の符号規約への変更はない。

証明は同じ内部辺の所属を既存 `segmentEdgeOwner_unique` で指定し、
`positiveCompositeInnerCut_rank_mem`・`positiveCompositeInnerCut_vertices` の元の順位を使う。
同じ区間内の先行他色の集合の等式でB_iへ戻し、各内部位置の高さの等式を区切りの有無で
重み付けして足した。内部区切り数は `sum_internal_caesuraIndicators` で同じ成分次数へ戻した。
その釣り合いと証明済みの逆転指数の合同・合成指数の補和・成分次数の総和を合わせ、
元の `positiveCompositeCutCoefficient_eq_nested_of_modeq` に追加の合同仮定なしで渡した。

有限点検は§289の全12,233組を使用。Leanは有限点検に依存しない全称証明。
語の略記に存在しないtoWord射影を一度使ったため既存のWordそのものへ直した。
部分語長の正値性を明示し、有限和の引数名とPropの移送を現行APIに合わせた。
高さの最終照合は同じCutの定義展開だけを許す透明性設定で閉じた。
心拍数・再帰上限を増やしていない。証明・ファイル200行超なし。
最終ソースの対象警告0。

対象ビルド（/tmp/bsw16/）：

- `m14-position-helpers-01.log`：語長の区切り・順位の移送。
- `m14-position-helpers-02.log`：辺の和、内部区切り数、内部位置の和、2,239 jobs成功。
- `m14-inner-height-balance-03.log`：同じ内部辺の高さの釣り合い。
- `m14-position-exponent-balance-01.log`：内側位置指数の再添字付け。
- `m14-composite-cut-coefficient-01.log`：警告の改行修正を含む最終三本、3,009 jobs成功。

途中の失敗を含むログの個別成功行と、最終対象ビルドの終了コード0を確認した。
新規分だけの別の小監査 `audit-m14-composite-cut-coefficient.log` は
**9モジュール・44宣言、標準三公理のみ**。sorry・独自公理0。
鍵は一回の対象ビルドまたは一回の小監査の間だけ使用して返した。整理券は一枚ずつ。
既存の公開宣言・界面・drafts・main作業木・共有入口・共有監査は変更していない。
rootビルド・大きい監査・常駐セッションなし。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| WordCaesuraLengthTransport | 35 |
| PositionExponentEdgeSum | 32 |
| InternalCaesuraIndicators | 30 |
| OverlapInternalPositionSums | 59 |
| CompositeInternalHeightBalance | 74 |
| CompositeInnerPositionExponent | 42 |
| CompositePositionExponentBalance | 70 |
| CompositeCutExponentModeq | 47 |
| CompositeCutCoefficient | 26 |
| **計** | **415** |

M14実測は**23,406行**、L12aは**8,199行**。
C451・C452・C453の数値・指定面の比較は閉じたが、同じ実テンソルとnullaryへの接続は残る。
L12a全体・L13以降を完成に数えず、一覧12/48（追加4）、goalはactiveのまま。
外枠31,000行まで実測の残り7,594行。完成見込みの上端が外枠を超えるリスクは残る。
約25,000行で止まらず実測・残りを出し直す指定を維持する。
完備化後のP⁰は§267・282の未供給箇所を残し、仮定を足して消していない。
(c)が必要との判定には至っていない。3b-4a未受領のためTot九欄の実装は始めない。


