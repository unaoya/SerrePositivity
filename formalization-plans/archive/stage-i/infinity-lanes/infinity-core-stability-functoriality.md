# F2-St：安定 ∞ 圏側での懸垂・非連結 K の関手性（設計評価）

2026-10-27。状態：設計評価のみ。Lean 実装・既存ファイル変更・既存監査への登録は行わない。
所有：本ファイルのみ（300 行以内）。以下の新 API 名は仕様案であり、存在する宣言ではない。
既存界面の評価は現チェックアウトの宣言型を根拠とし、計画の完了表示だけでは判定しない。

## 結論（A〜E）

- A：dg では対象計算、正しい写像空間を持つ StableInfinity では関手性、という分離を支持する。
  ただし cone の Ind 添字、connective K の fiber 性、冪等完備性、局所化定理の論証を修正する必要がある。
- B：F1 の Cat∞ 値分類は有限標準単体底まで。空間値分類や Ind-S (5)(8) だけでは一般底分類にならない。
  P-d は固定二対象の全保存関手圏の随伴双対性までで、対象を動かす全 Pr の双対性は未完。
- C：Ind の自由完備化の全関手圏同値、compact 制限、局所化の全関手圏普遍性を流用できる。
  最短候補は Ind 専用の普遍性の族化。HTT 3.2 全体の完成を最初の必須工程にしない。
- D：推奨する専用経路の調査・実装・限定検証は延べ 184〜368 時間を暫定枠とする。
  一般 Cat∞ 値分類も完成させる経路は追加 120〜240 時間程度。K・dg 比較本体は別枠。
- E：最大の危険は対ごとの同値や二胞体の選択を全高次の関手性と取り違えること。
  専用経路にも coherent な族の構成が必要で、単なる choice と恒等・合成の点同型では完成しない。

## A 数学的な修正

1. BGT の cone は Fκ(C) := (Indω(C))^κ、懸垂は Σκ(C) := Fκ(C)/C。
   κ は非可算正則、ω は通常の filtered 完備化。Indκ(C)^κ ではない。
   実際、既存 `Compact.compactIndEquivalence` は
   Idem(C) ≃ Indκ(C)^κ を証明する。C が冪等完備なら提案式の商は零になり、目的を満たさない。
   BGT Definition 9.1・Lemma 9.4 が原典。可算和の閉性には ω < κ を使う。
2. C → Fκ(C) → Σκ(C) は安定圏の exact/Verdier 列として扱う。
   connective K がこの一般列をスペクトルの fiber 列へ送るとは置かない。
   swindle は K(Fκ(C)) ≃ 0 を与えるが、そこから直ちに
   K(C) ≃ ΩK(Σκ(C)) は出ない。ΩK(Σκ(C)) の π₋₁ は K₀(Σκ(C)) になり得る。
   まず自然な構造射 K(C) → ΩK(Σκ(C)) と必要な非負次数の比較を構成し、
   それを反復した逐次図式の colim で Kⁿᶜ を定義する（BGT Definition 9.6）。
   既存 K-6 計画の保証も、指定 BF fiber への非負次数 π 同型であり、この区別に整合する。
3. raw stable Verdier 商と、その冪等完備化を区別する。
   Cat∞^perf 上の自己関手が必要なら Σκ^perf(C) := Idem(Fκ(C)/C) を採る。
   raw 商を反復するなら Cat∞^ex 上で構成し、最後に Morita／冪等完備化不変性を示す。
   いずれも C ↪ Fκ(C) の充満忠実性・核・商普遍性を同じ実射で保持する。
4. Verdier 商の普遍性は商関手の関手性を与えるが、Kⁿᶜ の局所化不変性そのものではない。
   Fκ・Σκ の exact 列保存、K の必要な局所化比較、反復・Sp の逐次余極限との整合が別に要る。
   BGT Proposition 9.5 と §9.2 の議論を省略しない。BGT の filtered colimit 条件も別義務。
5. `StableCategory` は安定性だけを持ち、冪等完備性を持たない。
   従って既存 `StableInfinity` は Cat∞^perf と同一ではない。
   全 StableInfinity に拡張するか、冪等完備対象の全部分圏を定義して包含との比較を付ける。
   さらに既存 `IsVerdierSequence.kernel` は essential image そのものとの一致を要求する。
   一般の非 thick な安定部分圏では核は retract 閉包へ広がるので、この型は自動では得られない。
   最初は冪等完備入力の C↪Fκ(C) に限定し、全域へは Idem 経由で拡張するのが安全。
6. 対象ごとの dg 比較は登録先の値の同定に使えるが、dg 側の自然同値を主張する根拠にはならない。
   ν 自身の全単体の関手性・exact 性と、必要なら Morita 降下を別に確認する。
   W1 の二胞体充填も最初の段階であり、全高次の整合を含む図式が完成条件。

## B/C (1)：Cat∞ 値 straightening の現在の到達点

名前空間は特記なければ `SerrePositivity.InfinityCategories`。

| 読み取った入口 | 実際に供給するもの | 今回への利用と限界 |
| --- | --- | --- |
| `F1/Cocartesian/FiniteSimplexEquivalence` | `cocartesianFiniteSimplexStraighteningEquivalence n`、同じ主写像の同値性 | 底は nerve(ULift(Fin(n+1)))。任意の有限単体集合や任意 quasicategory まで完成したとは言えない |
| `F1/Cocartesian` | 分類主写像、base change、相対 Hom、二単体・境界比較を集約 | 独立の明示入口。docstring は一般 Cat∞ 値構成を休止中とし、F1 主入口には含めない |
| `F1/StraighteningLeft` | left fibration と空間値図式の分類 | Kan 値の段階と評価・全族比較に使用。非可逆射を持つ Ind(C) の分類には代用不可 |
| Ind-S (5) | `exists_cocartesianKanUnstraighteningUnit` | p:E→nerve I、通常圏 I、R:SSet→KanObject、単位 η から厳密な底を持つ全族写像と fiber 単位の FunctorIso |
| Ind-S (8) | `representableHomCoherentIso x` | 固定 x の豊穣 representable Hom の coherent 実現と共変 Hom 図式の全 FunctorIso |

Ind-S (5) は R を通した空間値の比較であり、一般 fiber 圏の完全な復元ではない。
Kan 化した全空間の情報から元の fiber 内の非可逆射を回復する主張を追加しない。
Ind-S (8) の x 方向の追加自然性は未公開。対象を動かす二変数・多変数の mate の整合は別工程。
両者は評価・Hom 普遍性の照合に有効だが、HTT 3.2 の Cat∞ 値分類そのものではない。

一般経路で新たに必要な仕様：

1. 任意の底 S の cocartesian fibrations と cocartesian 辺を保つ射の ∞ 圏。
2. Fun(S,Cat∞) との分類同値、元の主写像の Hom 作用・fiber 評価・base change の比較。
3. 有限標準単体上の結果を、共有境界を固定した相対延長、有限セル、骨格へ降下する API。
   個別の各 Δⁿ の同値を並べるだけでは面・退化と整合する逆写像にならない。
4. 一般底の本質的全射性と宇宙変更、小さい fiber の本質的小性。
5. Ind の全空間 EInd→StableInfinity と、その cocartesian 辺の実構成。
   分類定理は既にある族を分類する道具であり、族の存在を自動的に与えない。

既存 F1 計画の一般充満忠実性 40〜80 時間は部分工程の過去の暫定値。
一般底の本質的全射性・宇宙・今回の EInd の構成まで含む総額ではない。

## B/C (2)：随伴の関手性と P/P-d

f:C→D に対する前層の制限は f*:P(D)→P(C)、左随伴は
f! := Lan(f^op):P(C)→P(D)。添字と反変方向を明示する。
固定模型の前合成の厳密合成則に加え、Cat∞ の全 Hom・全単体上の作用を用意する。

HTT 5.2.2.5 の正確な内容は、既存の Cartesian fibration p:X→S が
cocartesian でもあることと、全遷移 f* が左随伴を持つことの同値。
各 f* の随伴の存在だけから、まだ構成していない全空間 X を作る定理ではない。
実装には次の三段階を分ける：

1. 制限 f* を遷移に持つ前層の Cartesian 族を構成・分類する。
2. fiber の随伴を局所 cocartesian lift として実現し、Cartesian 性から大域 cocartesian 性へ移す。
3. 得られた同じ族を共変に分類し、遷移が元の Lan と随伴単位ごと比較されることを示す。

調査範囲の公開入口では、この三段全体を行う汎用 5.2.2.5 API は確認できなかった。
F1B の辺・局所輸送の道具から組む場合も、随伴の Hom 同値と lift の同定が必要。

| 既存界面 | 接続点 | 残る義務 |
| --- | --- | --- |
| `F2/Ind/IndLeftKanExtension` の `ind_exists_leftKanExtension` | 元の Yoneda に沿う延長 G と指定 β を返す | これは f^op に沿う前層全体の Lan そのものではない |
| `indLeftKanExtension_unit_isIso`・`indLeftKanExtensionRecoveryIso` | 同じ Yoneda 制限の回収 | 恒等・合成の比較をこの回収へ正規化する |
| `indLeftKanExtension_preservesSmallKappaFilteredColimits` | 延長の κ-filtered 保存 | 全小余極限保存、exact 性は別に示す |
| `indKappaContinuousRestrictionEquivalence` | Fun^κ(Indκ(C),D)≃Fun(C,D) の全関手圏同値 | 固定 C,D の逆同値の選択だけでは C,D を動かす関手にならない |
| P の `exists_leftAdjoint_iff_accessible_preservesLimits` | presentable 間の f* に左随伴を得る | 前層模型の presentable 性、accessibility、極限保存を代入する |
| P の `exists_rightAdjoint_iff_preservesSmallColimits` | Ind 延長等の右随伴の存在判定 | 右随伴の κ-filtered 保存は存在だけでは従わない |
| P-d の `presentableAdjointFunctorEquivalence C D` | PrLFunctorSpace C D ≃ (PrRFunctorSpace D C).op、全変換を含む | 三対象の合成・恒等・全 Pr の対応は P-d 計画でも残件 |

P-d の core 版 `adjointMappingEquivalence` と全関手圏版を区別する。
StableInfinity の Hom は exact functor 圏の core なので、必要な核心には core 版も使えるが、
対象を動かす全単体の合成との整合をそれで消すことはできない。

注意：一般 f の f* は Indκ(D) を Indκ(C) へ送るとは限らない。
例えば C は一点、D は離散二点、f は一方の点を選ぶと、他方の表現可能前層の制限は空。
Indκ(一点) の唯一の本質的対象は一点前層なので、制限は閉じない。
従って前層圏で随伴を取り、左側 f! の filtered-colimit／representable 保存から Ind に制限する。
または自由完備化の普遍性から、yD∘f の延長 Indκ(f) を直接構成する。

## B/C (3)：cone・compact・Verdier 商の必要 API

### Ind と compact

正しい目標は exact f に対する Fκ(f):(Indω C)^κ→(Indω D)^κ。
`Indκ(−)^κ` 自体の関手化は Idem の関手化として意味があるが、cone には使用しない。

- 既存 `F2/Ind/UnconditionalStableCompactGeneration` 等は Ind の安定性・compact 生成の入口。
  対象の安定性と、Indω(f) の exact 性を区別して接続する。
- `F2/Presentable/CompactFunctorRestriction` の `kappaCompactRestriction κ G hG` と
  `_inclusion` は実射と包含の全単体の厳密可換性を既に提供する。
  hG は各 compact 頂点の保存証明であり、呼出側が供給する。
- arbitrary な左随伴は同じ κ の compact 対象を保つとは限らない。
  Indω(f) は compact 生成子を compact へ送ることから右随伴の filtered 保存を証明し、
  Map(Lx,−)≃Map(x,R−) により同じ κ の compact 保存を導く経路を推奨。
  代案は κ-small な compact 生成子の余極限・retract 表示からの保存。
- compact 部分の小模型と包含を固定し、選択した小模型間の射・自然同値を同時に輸送する。
  一対象ごとの essentially-small 性だけでは同じ宇宙内の cone 自己関手にならない。
- ω-completion、非可算 κ の compact 部分、StableInfinity の宇宙を別パラメータで設計する。
  必要な宇宙拡大を最初に固定し、反復ごとの際限のない ULift を避ける。

### Verdier 商

既存 `KST/LocalizingInvariants/VerdierSequence` の `IsVerdierSequence` は
充満忠実性・核一致・`IsLocalization` を持ち、`universal` は元の全前合成の同値を返す。
この構造は商の存在を主張しない（モジュールにも明記）。
`StableInfinity` は exact functor 圏の core で豊穣化した `StableQCat` の coherent nerve。
新構成はこの Hom に作用するか、全 simplex を直接与える必要がある。

必要な追加仕様：

1. 核が essential image と一致する thick な安定完全包含 i:A→B に対する
   実商 q:B→Q と `IsVerdierSequence i q` の存在。一般包含は retract 閉包との比較を別に持つ。
2. 包含間の coherent square (a,b,α) に対し Q→Q′ を降下させ、q′b と q の比較を保持する。
   b が essential image と cofiber 分母を保つことを exact 性と α から証明する。
3. 全関手圏の普遍性を exact functor 部分圏へ制限する。降下射の exact 性の反映が必要。
4. 任意パラメータ K の変換・自然同値も同じ前合成同値で降下する API。
   恒等・合成・三単体以上を共有境界を固定して整合させる。
5. raw 商の Σ、必要ならその後の Idem、自然変換 Id→Fκ→Σ を同じ図式として公開する。
6. Fκ と Σ の exact 列保存を別に証明する。quotient の一意性だけで代用しない。

局所化の宇宙移送は Ind-S (4) の `IsLocalization.ulift` と
`IsLocalization.precomposition_isFullyFaithful_ulift` を流用できる。
これらは任意の商の存在・exact 性・大域関手性を追加するものではない。
基盤 F1/F2 から KST を逆 import せず、一般 API と StableInfinity への接続葉を分離する。
Ind-S (8) の限定的な推移 import 例外を新レーンへ自動拡張しない。

## D 実装順序と暫定工数

下表は一人相当の延べ実作業時間。設計探索・新規葉・限定ビルド／公理監査を含む。
既存上流が利用可能という条件付き。見積りは実証済みの速度保証ではなく、不確実性が大きい。

| 順 | 工程・受入条件 | 時間 |
| --- | --- | --- |
| 0 | cone、raw/perf、宇宙、connective 構造射の型を確定 | 8〜16 h |
| 1 | Ind の全関手圏普遍性を族化し、Yoneda 回収を保持した全単体の Indω 作用を構成 | 40〜80 h |
| 2 | Indω(f) の exact 性、compact 保存、compact 制限、小模型と恒等・合成の整合 | 32〜64 h |
| 3 | 商の存在・exact 降下・全パラメータの普遍性、Σ の関手化 | 64〜128 h |
| 4 | Id→Fκ→Σ、exact 列保存、StableInfinity 接続と限定監査 | 40〜80 h |
| 合計 | 専用経路の cone／懸垂の基盤。Kⁿᶜ 本体は含まない | 184〜368 h |

工程1 の第一受入条件は、単一射の延長でなく
core Funex(C,D)→core Funex(Indω C,Indω D) の作用と、合成を含む全族の構成方針の検証。
それが困難なら一般分類経路へ切り替える。対ごとの逆同値を choice で選ぶだけでは受理しない。
まず一つの二単体とその共有境界を保つ試験で、族化の難所を顕在化させる。

一般経路は任意底 Cat∞ straightening と随伴族化を追加で 120〜240 h と見込む。
専用工程と作業が重なるため単純合算は上限寄り。一般分類は他用途に広く再利用できる。
K の豊穣 S• 作用・Sp への接続・構造射・局所化定理・dg 比較は各所有者の別見積り。
特に既存 K-6 の指定 BF 射と固定 K 射の比較を、この基盤見積りへ隠さない。

## E リスク・代替案・引渡し条件

- 専用経路：既存 Ind 普遍性を最大限利用できる。選択した延長の高次整合が主要リスク。
  一般 HTT 分類を完成させずとも、契約可能な延長データの族から構成する余地がある。
  ただしその族の相対延長／可縮性を実際に証明する必要がある。
- 一般経路：Cartesian 前層族→5.2.2.5→cocartesian 分類。数学的に体系的だが上流工数が大きい。
  P-d の全 Pr 双対性を完成させる経路も同様に対象可変の整合が要る。
- W1 先行：必要な S→Fun(N,Sp) だけを ν 経由で構成する範囲限定策。
  大域 Kⁿᶜ_∞ の完成と同一視せず、二胞体に続く全高次・反復の自然性を受入条件にする。
- dg の quasi-functor／bimodule に替える案は導来 Hom を修正する代案だが、
  今回の ∞ 圏登録方針の中核工程ではない。strict dg quotient の剛性を再要求しない。
- 対象別比較の完成を全自然比較の完成と報告しない。登録は完成した実 ∞ 関手に対して行う。
- 完成条件は新規主定理の型への直接適用、元の射・単位・包含・商比較の回収、限定ビルド、
  標準三公理のみの監査。今回それらの実装・ビルド・監査は行っていない。

原典： [BGT, §9](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/BGT.pdf)、
[HTT, §3.2・Cor.5.2.2.5・§5.2.6・§5.3.5](https://www.math.ias.edu/~lurie/papers/HTT.pdf)。
既存計画：`infinity-core-F1.md`、`infinity-core-ind-supply.md`、
`infinity-core-presentable-duality.md`、`archive/stage-i/kst-lanes/L3-fibration.md`。

## 追補：工程3「Ind の普遍性からの直接族化」の詳細設計

2026-10-27 追加。今回の工程3・4・5はユーザーの分担番号で、上の工数表の番号とは別。
以下は数学的な型の仕様案。新しい宣言名は未実装であり、既存 API の存在仮定として追加しない。
S := StablePerfInfinity（提案：既存 StableInfinity の冪等完備対象の全部分圏）、J:S→StableInfinity を包含とする。
宇宙は作業宇宙 U と模型用の上位宇宙 V を先に固定し、κ∈U・ω<κ・正則を共通入力とする。
Indω(C) は V 側、Fκ(C) と Idem 商は U-small な代表を選ぶ。全単体の比較ごと代表へ戻す API を要し、反復で宇宙を上げない。

### 3a 補題/API の対応表

| 提案する仕様名 | 必要な数学的命題・保持する実データ | 既存界面と追加義務 |
| --- | --- | --- |
| `indExtensionUniversal` | res_C,D:Fun^ω(Indω C,D)→Fun(C,D) は元の Yoneda 制限で同値 | `indKappaContinuousRestrictionEquivalence` を κ=ω で使用。ここでの ω と cone の κ は別 |
| `indExtensionRecovery` | exact f:C→D の延長 Lf と βf:yD∘f≃Lf∘yC、Lf の filtered 保存 | `ind_exists_leftKanExtension`、`indLeftKanExtension_unit_isIso`、`indLeftKanExtensionRecoveryIso`、`indLeftKanExtension_preservesSmallKappaFilteredColimits` |
| `indRestrictionClosed` | exact f の前層制限 f* が Indω(D) を Indω(C) へ送る。Rf の作用は元の前合成の制限 | 新規核心。有限余極限を持つ C,D と f の有限余極限保存から証明する。HTT 5.3.5.13 に対応し、一般 f の反例とは衝突しない |
| `indRestrictionPreserves` | Rf は filtered 余極限と全小極限を保つ、各 Indω(C) は presentable | 前層の点別計算・Ind 包含の生成／極限の作成を接続。accessibility も確認する。単なる右随伴の存在と混同しない |
| `indExtensionAdjunction` | QCatAdjunction Lf Rf と、βf の Yoneda 単位が同じ随伴単位に対応する全自然比較 | 普遍性・密度から Hom 同値を構成するのが第一案。P の `exists_leftAdjoint_iff_accessible_preservesLimits` は Rf の左随伴存在を供給する代案 |
| `indAdjointIdentified` | AFT が返した L′ と元の Lf の比較を βf まで指定し、全 K で回収する | P-d `presentableAdjointFunctorEquivalence` は固定二対象の随伴対応、`_adjunction` は元の随伴を回収。全体の合成則は新規 |
| `indExtensionFamily` | 全 C,D の core Funex(C,D) 上の延長族と、任意の合成列・共有境界で整合する作用 | res の homotopy fiber の core は可縮。だが raw res の境界延長を自動視せず、isofibration 置換と相対 lift の照合を証明する |
| `indExactCompact` | Lf は exact、ω-compact 生成子を保ち、Rf の filtered 保存から Lf の κ-compact 保存を導く | `indExtensionRecovery`・安定 Ind・Map(Lx,−)≃Map(x,R−)。全小余極限保存は随伴から、exact 性は安定性から得る |
| `coneRestrictionFamily` | 全単体の L 作用を κ-compact fiber へ制限し、Fκ:S→S と i:IdS⇒Fκ を作る | `kappaCompactRestriction`・`kappaCompactRestriction_inclusion` は各実射の入口。K×fiber 上の制限、模型移送、恒等・合成は追加 |
| `coneThick` | iC は充満忠実・exact、essentialImage(iC) は安定かつ retract 閉 | Yoneda・compact 生成を使用。retract を充満忠実性で C 内の冪等へ戻し、C の完備性で分裂する |
| `rawQuotientExactUniversal` | qC:Fκ(C)→QC、IsVerdierSequence iC qC、および Funex(QC,E)≃Funex_iC=0(Fκ(C),E) | `IsVerdierSequence.universal` と `inverts_iff_kills_inclusion`。商存在、降下射の exact 性と全族制限を工程4が追加 |
| `completedQuotientUniversal` | ∀E∈S, Funex(Idem QC,E)≃Funex_iC=0(Fκ(C),E)、元の射による前合成 | `IsIdempotentCompletion.pre_isQCatEquivalence`／`idemYonedaUniversalEquivalence` と上行を合成。exact 部分への制限と対象可変の整合は追加 |

`Funex_i=0` は零化する exact 関手の全部分圏を表す。指定零化 homotopy を扱う場合は、その零関手への同値の空間も保持する。
Ind-S (5)(8) は値・Hom の回収比較に使い、上表の `indExtensionFamily` や cartesian 族の存在の代用品にはしない。

### 3b 全高次 cartesian 族 → 左随伴 → cocartesian の依存順

T0（全高次入力）：exact 関手の core の全単体に前合成を作用させ、R:S.op→Cat∞、R(C)=Indω(C) を構成する。
元の前層の制限をまず全単体で構成し、`indRestrictionClosed` で全部分 fiber へ制限する。op と可逆変換の向きの比較も明示する。
T1（cartesian 族）：p:EInd→S、CartesianFibration p、eC:EInd_C≃Indω(C) と、辺 f の cartesian transport と Rf の全族比較を構成する。
辺空間は Map_E((C,x),(D,y)) の f 上の fiber ≃ Map_IndC(x,Rf y) を満たす。全 n-simplex の面・退化と共有境界を保存することも仕様に含める。
T0→T1 は一般 HTT 3.2 を仮定せず、この R に対する相対 nerve／専用 unstraightening の補題として証明する必要がある。ここが独立の未供給工程。
T2（各遷移の随伴）：T1 と `indExtensionUniversal/Recovery` から Lf を選び、`indExtensionAdjunction` で Lf⊣Rf を得る。
単位 ηf,x:x→Rf(Lf x) が T1 の同じ辺空間で e:x→Lf x に対応し、その単位による Hom 比較が全自然な同値であることを示す。
T3（局所から大域）：CartesianFibration p と全 f の上記随伴から CocartesianFibration p を導く（HTT Cor.5.2.2.5）。
証明は η に対応する辺の局所 cocartesian 性→cartesian 族内での大域性→全頂点の lift 存在。三対象の随伴の選択を先に厳密合成させる必要はない。
T4（共変作用）：同じ p の cocartesian 輸送を分類する専用 API `indCovariantClassifier` により L:S→Cat∞ を得て、βf を全 K で回収する。
T3 だけで分類写像が Lean 上に存在するとはしない。T4 は専用分類または全合成列の相対 lift から直接 simplex 写像を構成する追加証明。
T4 の直接案では、指定するのは個別辺の空間だけでなく、各 σ:Δ[n]→S 上の全延長図式の空間と全境界との matching 射である。
その射の自明 Kan fibration 模型を実構成して切断し、全 n と面・退化を同時に保持する。点 fiber の可縮性だけではこの条件を満たさない。
T5（cone）：`indExactCompact` の後、EInd の κ-compact 頂点による全部分圏を取ると cocartesian lift に閉じる。
従って pκ:EF→S は cocartesian。Rf の compact 保存は一般にはないので、pκ まで cartesian と主張しない。小模型移送後に Fκ と i を得る。
依存 DAG は「T0→T1→T2→T3→T4→T5」。AFT は T2 の補助、P-d は同じ L の同定の補助であり、T0/T1/T4 を省略しない。

### 3c 冪等完備性・thick 性の統一案

主構成は S=Cat∞^perf 上の Fκ と Σκ:=Idem∘Qκ とする。既存 StableInfinity の定義を変更しない。
全安定圏用の登録は、別に全高次の冪等完備化 P:StableInfinity→S を構成し、Knc_perf∘P として拡張する。ν 入力にも P を明示する。
P の対象値・安定性・exact 性には `Idempotent/UniversalProperty`・`CompletionStability`・`CompletionExact` を使い、関手化は別義務とする。
coneThick は「零・cofiber 閉性＋retract 閉性」を証明し、商の一般核=retract 閉包の定理と合わせて既存 `IsVerdierSequence.kernel` を放電する。
kernel は同じ qRaw の実頂点について証明する。perf 商への包含 QC→Idem QC が零を反映することも別に示す。
重要：qPerf:Fκ(C)→Idem QC に対し、任意 quasicategory 標的の `IsLocalization` を一般には要求できない。
従って `IsVerdierSequence iC qRaw` は raw 商用に保持し、perf 商用には完備標的だけの上表の普遍性を使う。既存構造の意味を弱めない。

### 3d 工程4（Verdier 商・Sp）／工程5（K∞・K-S•）への引渡し型

工程3の出力 `ConeFamilyκ`（仕様案）：(Fκ:S→S, i:IdS⇒Fκ)、Fκ(C)≃(Indω C)^κ、自然な Yoneda 包含比較、全 C の coneThick と可算和。
その可算和は関手 T_C(x)=⊕N x と id⊕T≃T を持ち、f と全高次で比較される族として渡す。点別 swindle の存在だけにはしない。
工程4の入力は ConeFamilyκ。出力 `SuspensionFamilyκ` は Qκ:S→StableInfinity、qRaw:JFκ⇒Qκ、Σκ:S→S、δ:Qκ⇒JΣκ と δC の完備化証明。
加えて V:S×(Δ[1]×Δ[1])→StableInfinity を出力し、各 VC は元の iC,qRawC を辺に持つ既存 `VerdierDiagram`、残りの角は指定零圏とする。
perf の零化四角形は V に δ を後続させた別の全族で保持し、qPerf を辺にする `VerdierDiagram` の存在を誤って要求しない。
商の写像の型は、包含間の coherent square (a,b,α:b∘i≃i′∘a) ↦ (Q(a,b,α):Q→Q′, q′∘b≃Q(a,b,α)∘q)。全 K と貼合せを要求する。
工程4は raw/perf 普遍性、Σ の恒等・合成、exact 列保存を供給。Sp 側へは完成した V と、必要な零化 homotopy を渡す。
工程5の第一出力型は K∞:StableInfinity→Sp と、各 C の指定 connective K 模型との比較。既存 `sExactInfinityEndofunctor n` は各 Sn の全高次作用に流用する。
Sn の存在に加えて Δ.op 方向・反復 S•・core・実現・BF の全自然な整合を要求し、既存 dg 入力用豊穣関手からの逆算で代用しない。
次の出力は θ:K∞J⇒Ω∘K∞JΣκ という Fun(S,Sp) 内の自然変換と、その指定 K-6/BF 構造射の回収比較。
θ を作るとき K∞(QC)→K∞(Idem QC) を使用するならその実射・自然性を要求する。同値性や任意の完備化不変性を無断で仮定しない。
Sp 側の受入型は Seqκ:S→Fun(N(Nat),Sp)、Seqκ(C)(n)=ΩⁿK∞(JΣκⁿC)、遷移は ΩⁿθΣκⁿC、Knc=colimN∘Seqκ。
Ω・colimN の ∞ 関手性と実構造射の比較は Sp 側の義務。既存 `sequentialLevelColimitFunctor` は通常の BF 模型の関手なので、この型との全自然比較を別に渡す。
局所化登録の型は raw VerdierDiagram d ごとの IsPullbackSquare(d.square≫Knc_all)、Knc_all:=Knc∘P と零保存。P による raw 列の perf-exact 列への移送も必要。
Σ への θ は段ごとのスペクトル同値を要求しない。各工程の完成条件は対象比較に加え、同じ実射・全 K・共有境界の回収とする。

工数判断：本追補は既存総枠の内訳を精密化したもの。T0/T1/T4 の専用構成が総枠成立の主要リスクで、未供給を解消済みとは扱わない。
最初の受入試験は exact な二射と指定合成二単体の全族回収、続いて指定境界の三単体、最後に全 n の matching 補題。有限試験だけでは完了にしない。
原典の対応：[HTT 5.3.5.10・13／5.2.2.5](https://www.math.ias.edu/~lurie/papers/HTT.pdf)。コード・ビルド・監査登録は今回実施しない。
