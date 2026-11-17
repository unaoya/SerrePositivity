# BS-W16 の報告（report-codex-w16.md） — 改訂 D79／May と M14 の型一覧（§98〜§112、2026-11-13）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## §98　改訂 D79／May の最初の区切り（11-13）

ユーザー承認の §96.7・指示書 §26 に従い、May 経路を再開した。
main を math/bs-impl に取り込んだ（merge 5a94b4d6c）。界面・Assembly・drafts の
型は、局所化が済むまで変更しない。既存の 10,216 行は保存している。

### 98.1　今回の出力と登録候補

| モジュール（EInfinity/PowerOperation/） | 行数 | 出力 |
|---|---:|---|
| MayCyclicGroup | 75 | 置換群内の巡回部分群、右回転の生成元、位数と生成性 |
| MayNormalization | 58 | 単元としての ν(n)、全整数の指数 −n(p−1)、p=2 の規格化 |
| MayResolution | 66 | 巡回自由解像度 W、制限した BE の射影解像度、増大を保つ W→BE |
| MayZeroCoefficient | 78 | 同じ比較の零次係数、増大が 1、既存 aritySection とのホモトピー |
| MayRepeatedInput | 97 | 同じ代表射の反復入力と、単位を第二因子にした挿入の厳密な照合 |
| MayZeroOperation | 87 | 同じ D₀ の H⁰ 上の値が、既存の可換環構造の p 乗であること |
| 合計 | 461 | 新規 May 実装の実測 |

May, Definitions 1.2・2.1・2.2、Proposition 2.3 の規約を使う。
生成元は既存の加法的な +1 生成元の逆（右回転）を取った。
ν(n) は半階乗の単元の整数乗を使い、負の整数でも定義する。
W→BE は射影解像度の比較を使い、その同じ零次係数を作用へ入力した。
D₀ の計算は、増大が同じ二係数のホモトピーと既存の合成ホモトピーから得た。
全次数での代表元独立性・加法性・局所化を、この零次の計算で代用してはいない。

### 98.2　検証

六本すべての対象ビルドが通った。最後の MayRepeatedInput・MayZeroOperation の
ビルドは /tmp/bsw16/may-zero-operation-07.log、警告なし。
専用監査 /tmp/bsw16/audit-may-first.lean は **184 モジュール・1,495 宣言、
標準三公理のみ**で成功した。sorry・追加公理はない。
既存の公開宣言の型・定義、本体の入口、共通監査スクリプトは変更していない。
上の六本が調整役への登録候補である。

### 98.3　次と凍結への対応

最初の区切りを報告し、そのまま代表元独立性・加法性・自然性へ進む。
新規 461 行は、中間報告の約 10,000 行・停止外枠約 20,000 行に対する実測。
11-13 の凍結は予告段階で、18 時の確定連絡を待つ。
検証済みは夕方までにコミットし、凍結確定後の夜はコミットを控える。

## §99　May の零次の降下と全係数の境界（11-13、途中報告）

§98 の取り込み候補は **1908ec200** にコミットした。その後も承認済みの順序で続行。
今回の登録候補は同じ EInfinity/PowerOperation/ の次の二本。

| モジュール | 行数 | 証明したこと |
|---|---:|---|
| MayZeroHomology | 83 | 同じ D₀ の H⁰ への降下、代表射を選び直しても一致、全厳密 BE 射で自然、F_p 上で加法的 |
| MayResolutionCoordinates | 63 | 同じ W→BE の全係数 e_s の像と、境界のノルム／右回転の差の公式 |

零次の操作は、最初から Frobenius と定義するのではなく、同じ指定係数の作用へ
選んだ代表を入力して定義した。その値が p 乗という §98 の結果から、
代表元独立性を証明した。自然性は既存 homologyAlgebraFunctor の厳密射から得た。
加法性は二項定理と F_p の代数写像による `(p : H⁰ X) = 0` を使う。
H⁰ X が零環の場合も含み、その環で CharP p を無条件に要求しない。

全係数の境界は mayResolutionComparison の鎖写像の可換式を
`.single 1 1` で評価し、既存 regularHomEvaluation_action・_norm へ送って証明した。
新しい同変比較を仮定せず、零次と同じ増大付きの指定射を使っている。

対象ビルド：MayZeroHomology は /tmp/bsw16/may-second-01.log の当該対象成功、
MayResolutionCoordinates は /tmp/bsw16/may-coordinates-02.log で成功。最終ソースの警告なし。
専用監査 /tmp/bsw16/audit-may-new-two.lean は **2 モジュール・26 宣言、標準三公理のみ**。
§98 と合わせて May 新規 **607 行、8 モジュール・85 宣言**を監査済み
（§98 の全 184 モジュール・1,495 宣言に今回の 26 宣言を追加）。sorry・追加公理なし。

残りは、非零の係数次数での cycle、代表元独立性と混合入力による加法性、
全次数の自然性、ho(CAlg) への局所化である。零次での完了を全次数の完了とはしていない。
界面・Assembly・Shared/A4 は未変更、他レーンのファイルとの重複なし。
鍵は今回も各対象ビルド／各監査の間だけ取り、監査完了後に返却済み。
凍結確定の連絡はまだなく、検証済みのこの二本を報告とともにコミットする。

## §100　May の全次数の同次値・巡回不変性・閉性（11-13）

§99 の後も §26 の順で続行した。新規六本、562 行を検証した。

| EInfinity/PowerOperation/ の登録候補 | 行数 | 出力 |
|---|---:|---|
| MayRepeatedCycles | 78 | 全整数次数での同次反復入力、次数 n*q、閉性、全複体射での自然性 |
| MayRepeatedPermutation | 114 | 隣接交換と全置換の作用が sign(σ)^{q*q} になる厳密な等式 |
| MayHomogeneousAction | 119 | 同次 BE 作用の微分公式・二変数線形性・自然性・同時置換の等変性・閉性の判定 |
| MayCoefficientAction | 111 | 同じ実係数表現の作用との一致、生成元の差とノルムの評価、標数 p で係数境界の作用が零 |
| MayCyclicInputInvariant | 64 | 奇素数で巡回置換の符号が 1、標数 2 で整数単元の作用が恒等、反復入力の巡回不変性 |
| MayDValues | 76 | 同じ W→BE 比較による θ(e_s ⊗ a^{⊗p})、全厳密 BE 射に自然、閉入力から実閉元を作る |

May, Definition 2.1 の値を実際の作用で作った。全次数の閉性では、
係数の境界を §99 の同じ指定比較の境界公式へ戻している。
奇数段は生成元の差、偶数段はノルムで、前者は巡回不変性、後者は
p 倍のスカラーが零になることにより作用後に消える。正次数の係数を
零次の収縮で置き換えていない。全置換の符号は、同次純テンソル上の
実 Koszul 交換と隣接互換の生成性から証明した。

反復入力の次数は右括弧に沿う mayRepeatedDegree で保持し、
mayRepeatedDegree_eq が n*q と同定する。これは後の次数移送のための実装上の選択であり、
全複体の無限直和を有限積へ読み替えたり、複体の有界性を追加したりしていない。

対象ビルドは /tmp/bsw16/may-d-values-02.log で成功（最終ソースの警告なし）。
専用監査 /tmp/bsw16/audit-may-cycles.lean は **六本・89 宣言、標準三公理のみ**で成功。
sorry・追加公理はない。既存の宣言・入口・共通監査・界面・drafts は未変更。
May 新規の累計は **1,169 行**（前回 607 + 今回 562）、途中報告の約 10,000 行より下。
鍵は対象ビルドまたは監査の間だけ取り、最後の監査の鍵も返却済み。

次は P⁰ の次数を保つ添字・ν をこの閉元へ接続し、代表元独立性へ進む。
今回の出力は閉元と厳密射に沿う自然性までであり、全次数のホモロジー演算・加法性・
擬同型での不変性・ho(CAlg) への降下はまだ完了していない。
通常のテンソルのホモトピーを同変ホモトピーとして流用することはしない。
凍結は引き続き予告段階なので、検証済みの六本をコミットし、未検証分は分けて進める。

## §101　May の代表元独立性と規格化した P⁰ のホモロジー上の値（11-13）

§100 の六本は **67c62e9d2** にコミットした。その後、下記十一本・745 行を検証した。
今回も EInfinity/PowerOperation/ の新規ファイルのみであり、界面・Assembly・Shared/A4 の
移行は、加法性と局所化が済むまで保留している。

### 101.1　登録候補

| モジュール | 行数 | 出力 |
|---|---:|---|
| MayClosedCycles | 71 | 実微分の kernel、次数の移送、複体射の閉元への制限、指定 D_s の閉元と自然性 |
| MayPowerZeroCycles | 54 | i=−n(p−1) と ν(n) による規格化、全整数次数の P⁰ の閉元、正次数での零、自然性 |
| MayClosedHomology | 122 | 実 cycles・homology との比較、類写像の全射性、零類の境界判定、代表と自然性 |
| MayFreeProbeHomotopy | 49 | 既存の自由 probe のホモロジー関手は擬同型を反転し、鎖ホモトピックな射を同じ射に送る |
| MayProbeCycles | 51 | 同じ probe の自明 fibration による、元の閉元の厳密な持ち上げ |
| MaySphereHomotopy | 85 | 同じホモロジー類の二閉元の sphere 射の鎖ホモトピー、単位生成元の回収 |
| MayProbeEvaluation | 75 | 同じ単位・比較射・自由持ち上げによる評価、普遍閉元の厳密な回収と全ホモロジーでの一致 |
| MayDClasses | 65 | 全指定 D_s の実ホモロジー類・自然性・全次数の代表元独立性 |
| MayPowerZeroClasses | 72 | 規格化した P⁰ の実ホモロジー上の関数、代表元独立性、正次数で零、全厳密 BE 射で自然 |
| MayNormPolynomial | 44 | F_p[X] の (X−1)^{p−1}=∑_{i<p}X^i、非可換 F_p 代数への評価 |
| MayCyclicNorm | 57 | 同じ生成元の位数と冪による列挙、同じ巡回表現での T^{p−1}=N |

### 101.2　代表元独立性の接続

既存の **freeProbeFunctor** と **freeProbeFunctor_map_quasiIso** を再利用した。
自由 probe の全次数ホモロジー関手は、複体の擬同型を反転する。
Mathlib の **ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization** と
**AreEqualizedByLocalization.map_eq_of_isInvertedBy** により、鎖ホモトピックな複体射は
この関手の下で厳密に同じホモロジー射になる。

二つの閉元の類が等しいとき、その差は元の複体の境界である。
**complexSphereHomEquiv**・**complexSphereToDisk_comp** と
**complexDiskContractingHomotopy** により、二つの sphere 射の鎖ホモトピーを作った。
同じ sphere の生成元を元の cofibrant probe へ厳密に持ち上げ、自由代数へ含める。
二つの評価射は上の意味で全ホモロジー上で一致するため、同じ普遍元の D_s の類を
二方向へ送った値が一致する。評価が元の入力を回収する等式は元の複体で証明した。
この結果が **mayDClass_independent** であり、規格化後の
**mayPowerZeroClass_independent**・**mayPowerZeroHomology** へ接続した。

この工程は、既存のモデル構造を使った実例側の証明である。
公開する主張に [ModelCategory SSet] を要求せず、実際の
projectiveModelCategory と BE の modelCategory を持つ既存の自由 probe を使った。
通常のテンソルのホモトピーを同変ホモトピーとして流用したり、
以前の未完成な positive-Hom/orbit の次数同型を鎖同型と仮定したりしていない。
既存の 10,216 行は保存している。native な orbit・norm・Tate は使っていない。

### 101.3　検証・現在の範囲

代表元比較の束は /tmp/bsw16/may-power-zero-classes-03.log で、
MayPowerZeroClasses まで成功した。ノルムの最終対象ビルドは
/tmp/bsw16/may-cyclic-norm-02.log で成功した。最終ソースの警告なし。
全 May モジュールを含む専用監査の結果は本節の末尾に記す。

新規 May の累計は **1,914 行**（前回 1,169 + 今回 745）。
途中報告の約 10,000 行・停止外枠約 20,000 行より下である。
mayPowerZeroHomology は、現段階では **ホモロジー上の自然な関数**であり、
まだ AddMonoidHom・ho(CAlg) 上の NatTrans には束ねていない。
零次の既存の p 乗計算と新しい全次数の関数の照合も、これから接続する。
界面の型を変更したとは報告しない。

### 101.4　次の加法性の接続

[May, Proposition 2.3(ii)](https://www.math.uchicago.edu/~may/PAPERS/10.pdf) を再確認した。
混合語の和 Δ(a,b)=(a+b)^{⊗p}−a^{⊗p}−b^{⊗p} を、巡回軌道代表の和 c のノルム Nc として表す。
既存 **cyclicBinaryTensorWord_fixed**・**cyclicBinaryTensorWord_orbit_injective** を再利用する。
残りは、同次の色付き入力の置換公式、反復入力の二項展開、
軌道代表での和の照合、および次の係数による境界表示である。
全ての入力の次数が同じなので、巡回置換の Koszul 符号は §100 と同じ理由で消える。

係数の次の段の微分が N の場合は、その係数に c を入力する。
微分が T の場合は、次の係数に T^{p−2} を作用させ、今回の
**mayCyclicNorm_eq** で T^{p−1}=N と照合する。
同時置換の等変性で係数のノルムと入力のノルムを移し、差が境界であることを示す。
加法性の証明後に可換群値の自然変換へ束ね、ho(CAlg) への局所化へ進む。
この段階の加法性そのものは未実装である。

### 101.5　監査完了・コミット時の状態

専用監査 **/tmp/bsw16/audit-may-all.lean** は **May の全25モジュール・320宣言、
標準三公理のみ**で成功した（/tmp/bsw16/audit-may-all.log）。
本体に sorry・追加公理なし、linter の抑制なし。監査の鍵も返却済み。
今回の十一本を報告とともにコミットする。新規ファイルだけなので他レーンとの重複なし。
共通の入口と監査への登録候補は §100・§101.1 の計十七本。
凍結の確定連絡はまだなく、検証済みを枝に保存した状態にする。


## 102. May の加法性・厳密自然変換・ho(CAlg F_p) への局所化（11-13）

### 102.1 今回閉じた主張

May, Proposition 2.3(i)(ii) の代表元独立性（§101）に、加法性を接続した。
**mayDClass_add** は全 s : ℕ・q : ℤ で、同じ指定 W→BE 比較による D_s の
実ホモロジー類が閉入力の和に加法的であることを示す。
**mayPowerZeroAddHom** は、規格化 ν と次数移送の後の P⁰ を、全整数次数の
実ホモロジーの可換群の準同型に束ねる。

**mayStrictPowerZero** は全厳密 BE 代数射に自然な可換群値の NatTrans。
**mayHomologySourceIso** は既存の忘却比較・厳密複体の全次数ホモロジー比較から、
全厳密代数への引き戻しを実ホモロジー関手と同定する。
**mayLocalizedPowerZero** は ho(CAlg F_p) の全射に自然な同じ P⁰。
**mayLocalizedPowerZero_source** により、源への引き戻しは同じ指定厳密演算の共役であり、
局所化で別の演算を選んでいない。
**mayLocalizedPowerZero_pos** は n > 0 の消滅を自然変換全体の等式で示す。

### 102.2 加法性の実装の筋

[May, Proposition 2.3(ii)](https://www.math.uchicago.edu/~may/PAPERS/10.pdf) の混合差の証明を使った。
二色語に対する隣接交換・一般置換の符号公式を元のテンソル複体で示し、
標数 p の巡回作用では符号が消えることを照合した。
混合語の自由巡回軌道と代表の和から Δ(a,b)=Nc を得る。

同じ W→BE 比較の次の係数に、必要なら T^{p−2} を作用させる。
§101 の T^{p−1}=N により、その微分は前の指定係数のノルムとなる。
実 BE 作用の同時置換の等変性で係数の norm と入力の norm を移す。
ノルム係数そのものが実境界なので、閉混合入力とのテンソルは零類である。
この最後の一般補助 **mayClosedTensor_class_zero_left** は sphere 射の実鎖ホモトピーを
テンソルして証明し、平坦性・有界性の仮定を追加していない。

使用した norm は有限群作用の線形写像の和であり、Sp の orbit・norm・Tate の模型は使わない。

### 102.3 登録候補（今回の新規十八本）

全て SerrePositivity/EInfinity/PowerOperation/ の下。

- MayColoredValues、MayWordAdjacent、MayHomogeneousSwap、MayColoredPermutation
- MayColoredCyclic、MayMixedWordOrbits、MayPureMixedWords、MayMixedInputNorm
- MayCoefficientNormTransfer、MayCoefficientPrimitive、MayClosedTensor、MayNormCoefficient
- MayDClassAdditivity、MayPowerZeroAdditivity、MayStrictNaturalTransformation
- MayHomologySourceComparison、MayLocalizedPowerZero、MayLocalizedPositive

新規十八本 **1,197 行**、検証済み May の累計 **3,111 行・43モジュール**。
約 10,000 行の途中報告・約 20,000 行の外枠より下。
共通入口と全体監査の登録は行っていない。他レーンと重なる既存 Lean ファイルへの変更なし。

### 102.4 検証と残り

対象ビルドは /tmp/bsw16/may-localized-05.log で、MayLocalizedPositive まで成功。
同じ一回のコマンドで追加検査した未検証補助 MayNormBaseField のみが失敗したため、
コマンド全体の終了値は 1 だった。原因は ZMod.castHom の引数（標数零の等式でなく
p ∣ p を要求）であり、当該補助だけ修正して後続で検証する。
検証済み十八本の新規警告は、letI を let に直して消した。依存先の既存の長行警告は残る。
専用監査の最終結果は本節の末尾に追記する。

局所化までの今回の本体は小さい宇宙の F_p に対するもの。
EInfinityTheory.{u} の基底環は Type u なので、界面の本欄に置く F_p は ULift して
同じ宇宙に置く必要がある。そのための素体別名・同じ係数の移送と規格化の補助は、
まだ未検証の下書きとして作業木に置き、今回の十八本とは分ける。
界面・Assembly・Shared/A4 の型の移行はまだ行っていない。

零次の以前の p 乗計算と全次数の P⁰ との照合、離散・cosimplicial の top operation、
_tot・filtered 塔・二重模型の実現比較は残る。最後の実現比較は指示どおり G10 の後。
旧 10,216 行は削除していない。凍結の確定連絡はまだない。


### 102.5 監査完了

/tmp/bsw16/audit-may-additive.lean は、検証済み **43モジュール・467宣言、
標準三公理のみ**で成功した（/tmp/bsw16/audit-may-additive.log）。
全宣言の公理を検査し、sorry・追加公理なし。監査の鍵も返却済み。
今回の十八本と本報告をコミットし、持ち上げた素体の補助の検証へ続ける。


## 103. D79 改訂の界面・Assembly・Shared/A4 への接続（11-13、取り込み点）

### 103.1 本欄と宇宙

**EInfinityPrimeField.{u} p := ULift.{u} (ZMod p)** を、模型に依存しない
Interface/PrimeField.lean に置いた。EInfinityTheory.{u} の基底環は Type u なので、
素体をその宇宙へ置くための同じ環の持ち上げである。
**eInfinityPrimeFieldEquiv** は元の ZMod p との環同型、
**eInfinityPrimeFieldMap p k** は一般の標数 p の k への標準構造射。
一般 k を界面の本欄へ戻す変更は行っていない。

界面の **homotopyGroupsOnHo k U n := hoMap U ⋙ additiveCohomologyOnHo k (-n)** を使い、
powerOp0 は次の型へ変更した。

```lean
powerOp0 (p : ℕ) [Fact p.Prime] (n : ℤ) :
  homotopyGroupsOnHo (EInfinityPrimeField.{u} p) (forget (EInfinityPrimeField.{u} p)) n ⟶
    homotopyGroupsOnHo (EInfinityPrimeField.{u} p) (forget (EInfinityPrimeField.{u} p)) n
```

通常の可換群値の NatTrans で、全整数 n・全 ho(CAlg) 射に自然。
_zero は pi0_forget の成分で p 乗を読む等式、_pos は n > 0 の成分が零の等式。
_discrete・_tot は F_p 上の Frobenius の自己射から誘導する写像との、
**全整数 n の加法群準同型の等式**であり、coherent な Sp 値の辺を要求しない。
型は §96.3 の案の素体を同じ宇宙に持ち上げたもの。
toSpectra とその二つの比較の欄は変更せず、旧 10,216 行も削除していない。

### 103.2 同じ規格化からの実例と一般係数での読み出し

素体の持ち上げに必要な係数計算を、F_p の多項式の等式を標準環準同型で移して示した。
**mayCyclicNorm_baseField**・**mayBaseFieldAdditivityCoefficient_boundary** から、
同じ閉元・境界・実作用の証明で **mayBaseFieldDClass_add** を得る。
これは持ち上げた素体にも使える係数計算の補助であり、一般 k の本欄を増やしていない。

**mayNormalizedClass** は同じ D_i を指定係数 c で規格化し、代表元独立性と加法性を証明する。
実例では c := ULift.up (mayNu p n : ZMod p) とし、全次数のホモロジー比較で局所化する。
**mayPrimeFieldPowerZero**・**mayPrimeFieldPowerZero_source**・**mayPrimeFieldPowerZero_pos** が
任意の宇宙の素体の全関手版と同じ指定演算の引き戻し・正次数消滅を与える。

実例の公開名は **barrattEcclesPowerOp0**・**barrattEcclesPowerOp0_pos**。
Assembly はこの二つを固定し、powerOp0 と powerOp0_pos の引数を外す。
残り十九欄のうち冪作用については _zero・_discrete・_tot の三つだけが引数に残る。
零次の旧 p 乗計算をまだ全次数の P⁰ に同定したとは主張しない。

一般 k の利用者のため、Interface/PowerOperation.lean に
**EInfinityTheory.restrictHomotopyGroupsIso** と **EInfinityTheory.powerOp0Over** を置いた。
前者は restrict_forget と restrictD_homologyIso を合成する自然同型。
後者は素体への制限に本欄を適用し、その自然同型で共役するだけの定義である。
新しい Sp 値の作用や新しい自然性の仮定を追加しない。
Interface/ には模型の直接 import・模型の API を使う宣言・[ModelCategory _] の欄を足していない。

### 103.3 drafts の移行

Shared/EInfinityPowerOperation の powerOperationZero は powerOp0Over の成分を
homotopyCohomology で共役して読む型へ移した。
離散・Tot の比較も、全整数次数のホモロジー写像と係数比較の成分の等式へ移した。
強い三出力 powerOperationZero_natTrans・_primeField・_component は、
本ファイルでは作らず補完へ回すことを明記した。
それらを要求する他の drafts の参照はなかった。

A4/Perfectoidization の Lemma 8.4(a) の証明の筋は、素体へ制限したホモロジー演算を使う形へ変更。
同じ shift の作用は可逆、正次数の P⁰ は零、係数比較で H^{-n} の消滅へ戻す。
二重模型の実現上の Frobenius 比較は A4 の局所補題として、G10 の後に残す。
Lemma 8.4(a)(b) の主張の型は変更していない。
A1 の二本・A0・A3 は触っていない。drafts はビルドしていない。

### 103.4 登録候補

本段の新規モジュールは次の十五本。

- EInfinity/Interface/：PrimeField、PrimeFieldMap、PowerOperation
- EInfinity/BarrattEccles/Theory/：MayPowerOperation
- EInfinity/PowerOperation/：MayNormBaseField、MayBaseFieldPrimitive、MayBaseFieldNormCoefficient、MayBaseFieldDClassAdditivity
- 同上：MayNormalizedClasses、MayNormalizedNaturalTransformation、MayNormalizedSourceComparison
- 同上：MayPrimeFieldLocalization、MayPrimeFieldPositive、MayZeroClassComparison、MayUnitEvaluation

最後の二本は、次の零次の接続に使う同じ類の表示と単位評価の補助。
新規十五本は 693 行、May*.lean の累計は 3,672 行。
新設の界面・実例四本は別に計132行（May の数に含めない）。既存四ファイルの差分は別記する。
本段も約 10,000 行の途中報告・約 20,000 行の外枠より下。
一般∞の五本の移動候補は、指示どおり元の場所のまま。
共通入口と全体監査への登録は行っていない。

### 103.5 検証と残り

may-interface-01.log で新しい界面・Assembly と直接の利用者 TheoryInterface のビルドが成功した。
may-interface-02.log で一般係数の補助・May の公開実例・正次数消滅まで成功した。
後続の最終 Assembly・単位評価・専用監査の結果は、本節の末尾に追記する。
既存の長行警告は残し、新規補助の非推奨名・未使用セクション引数は抑制せず修正した。

この取り込み点は界面の型の移行と P⁰・正次数消滅の供給であり、M14 全体の完了ではない。
残りは零次の p 乗との接続、離散、cosimplicial の top operation と _tot、filtered 塔、
および G10 の後の二重模型の実現比較。次は零次の同じ単位射の照合から続ける。


### 103.6 最終検証・取り込み点

**/tmp/bsw16/may-interface-03.log** で、P⁰ と正次数消滅を固定した Assembly と
MayUnitEvaluation の対象ビルドが成功した。新規十五本の最終ソースに新しい警告なし。
Assembly・Theory・依存先の既存の長行警告は残る。

**/tmp/bsw16/audit-may-interface.lean** は **60モジュール・638宣言、標準三公理のみ**で成功した
（/tmp/bsw16/audit-may-interface.log）。May の全54モジュールと、変更した界面・実例・Assembly を検査した。
本体に sorry・追加公理なし。Interface/ の模型直接 import と [ModelCategory _] の仮定は追加なし。
ビルドと監査は別々の一回の鍵で行い、どちらの鍵も返却済み。
root ビルド・全体監査・入口登録は調整役の取り込み時に委ねる。

**取り込み点**：本節の十五本・界面・Assembly・Shared/A4 の移行と報告をコミットする。
§100〜§102 と未登録分が重ならないよう、登録候補は各節の一覧を使ってほしい。
次の零次比較の MayRepeatedZeroInput.lean は未検証の新規下書きとして作業木に残し、
今回のコミットと監査には含めない。
凍結の確定連絡はまだなく、検証済みの分を18時前に保存した。


## 104. M14 の零次の照合（11-13）

### 104.1 厳密代数で閉じた計算

**MayRepeatedZeroInput** は、同じ同次反復入力を零次に移した値と、
単位複体からの同じ射を全入力へ入れた値の一致を示す。
**MayZeroActionEvaluation** は、同じ W→BE 比較の零次係数の単位射による評価と
全次数の mayHomogeneousAction の評価を照合する。

**MayNormalizedZero** で、全次数の mayNormalizedHomology の零次の値を、
以前の mayDZeroRepresentative_value に接続した。
mayNormalizedHomology_zero_value は、ν(0)=1 の指定演算について、
任意の厳密 BE 代数 X の実 H⁰ の環で x ↦ x^p であることを示す。
源の仮定は [Fact p.Prime]・[CharP k p] であり、H⁰ の環の非自明性は要求しない。
添字の等式を先に指定する mayNormalizedClass_index_view を使い、
依存する次数の移送を指定した。同じ元・同じ係数・同じ作用の厳密な照合である。

### 104.2 native な欄への接続の実装

**MayPiZeroSourceComparison** は、既存 barrattEcclesPi0_forget の構成を、
同じ mayNormalizedHomologySourceIso と照合する。
忘却前の加群値の比較を mayModuleHomologySourceIso として読み、台の加法群へ忘れると
同じ比較になることは定義上の等式である。
mayPiZeroForget_source_square とその各点の等式、および比較による冪の保存を証明した。
環構造は全て既存の homologyCommRing X であり、同じ H⁰ を返す関手の型に合わせて
局所インスタンスを明示しているだけである。

**MayZeroIsoTransport** は通常の圏の補助。
環値関手 P、可換群値関手 H、その指定自然同型、α : H ⟶ H に対し、
α が零次の環で p 乗を誘導する性質は、対象の同型に沿って運べる。
新たな coherent な Sp 値の出力や ∞ 圏の仮定は要求しない。

**MayPrimeFieldZeroSource** は、指定演算の源への引き戻しと ν(0)=1 を使って
上の厳密な計算を源へ運び、ordinaryAlgebraHoSource_isLocalization と
Mathlib の Localization.essSurj で全 ho(CAlg F_p) 対象へ移す実装である。
公開実例の欄の名前は **barrattEcclesPowerOp0_zero**（Theory/MayPowerOperationZero）。
この接続と公開欄は may-native-discrete-02.log でビルドが成功した。公理監査の結果は末尾に記す。

### 104.3 登録候補と検証の範囲

本段の登録候補は、次の七本。

- EInfinity/PowerOperation/：MayRepeatedZeroInput、MayZeroActionEvaluation、MayNormalizedZero
- 同上：MayPiZeroSourceComparison、MayZeroIsoTransport、MayPrimeFieldZeroSource
- EInfinity/BarrattEccles/Theory/：MayPowerOperationZero

対象ビルドのログは /tmp/bsw16/may-zero-input-01.log、may-normalized-zero-*.log、
may-native-zero-*.log。厳密な零次の計算と、π₀ の源の比較・冪の保存までは通っている。
本体の公理監査・公開欄の検証・最終実測・コミットは本節末尾へ追記する。
共通入口と全体監査への登録は行っていない。

離散の欄の MayPowerOperationDiscrete.lean も検証が通った。零次の計算と他次数のホモロジー消滅を使う
実装で、次節に記す。
18時までには、停止点に届かない場合も検証済みの分を保存する。


## 105. M14 の離散比較と Assembly（11-13）

### 105.1 全整数次数の離散比較

**barrattEcclesPowerOp0_discrete** を本体に置いた。
F_p 上の離散代数 B、環射 f : B → B、全ての元で f(a)=a^p という指定に対し、
**全整数 n** で同じ P⁰ がこの f によるホモトピー可換群の写像と一致する。

零次では、mayDiscretePiZero_frobenius が barrattEcclesPi0_discrete の自然性と環同型から
π₀ 上の f を p 乗と同定する。barrattEcclesPowerOp0_zero と
barrattEcclesPi0_forget の自然性で、同じ H⁰ の比較のもとの等式を得る。
零次以外では、既存 discreteCAlgUnderEmbedding_underlyingDisc による IsZero から
台の群を Subsingleton として二つの準同型の一致を示す。
新しいスペクトルの模型・G10・非自明性の仮定を使っていない。

登録候補は **EInfinity/BarrattEccles/Theory/MayPowerOperationDiscrete.lean** の一本。
§104 の七本と合わせて本段の新規は八本。
may-native-discrete-02.log で零次の公開欄と離散の公開欄まで成功した。

### 105.2 組み立て

Assembly は P⁰・零次・正次数・離散比較を全て構成済みのものに固定する。
**barrattEcclesTheoryOfRemaining の引数は十九欄から十七欄へ**減り、
冪作用に関して残るのは powerOp0_tot のみ。
_zero・_discrete を仮定に残した条件付きの供給とはしない。
他の未供給欄は従来どおり引数として残し、全 EInfinityTheory が無条件に出来たとは主張しない。
組み立ての最終ビルドと専用監査・実測・コミットの結果は末尾に追記する。

### 105.3 次の範囲

次は指示書 §26 の順で、cosimplicial の top operation と _tot、filtered 塔の照合、
最後に G10 の後の二重模型の実現比較。
今回の離散の比較から、全次数の演算が任意の Tot・実現と可換すると推論することはしない。
指定された BE 作用・規格化 ν・模型の比較を追う必要がある。


### 105.4 最終検証・保存

**/tmp/bsw16/may-native-discrete-02.log** で native な零次と全整数次数の離散比較が成功した。
**/tmp/bsw16/may-zero-discrete-assembly.log** で、それらを固定した Assembly の対象ビルドも成功した。
新規八本の最終ソースに新しい警告なし。依存先と Assembly の既存の長行警告は残る。

**/tmp/bsw16/audit-may-zero-discrete.lean** は、新規八本と Assembly の
**9モジュール・62宣言、標準三公理のみ**で成功した
（/tmp/bsw16/audit-may-zero-discrete.log、17:11 JST 確認）。
本体に sorry・追加公理なし。[ModelCategory SSet] などの仮定なし。
ビルドと監査はそれぞれ別の一回の鍵で行い、いずれも返却済み。
root ビルドと全体監査・入口登録は調整役に委ねる。

本段の新規八本は **559行**。May*.lean の累計は **4,128行**。
見込みの半分の約10,000行・外枠約20,000行より下である。
§104.3 の七本と §105.1 の一本を登録候補として報告する。
検証済み八本・Assembly・本報告を18時前にコミットして保存する。
凍結の確定連絡はまだ受けていない。

一般 k の補助 powerOp0Over について、この段で新たに示した性質はない。
Shared の一般 k の性質は drafts のままであり、係数制限のホモロジー比較と
π₀ の環比較の整合性も、その証明時に確認する必要がある。
今回の native な F_p の零次・離散比較は、それらの未証明の一般 k の性質を使っていない。

## 106. cosimplicial top operation：切断項の計算と、一般の BF 作用の不足（11-13）

### 106.1 今回の検証済み出力

main の零次・離散比較の登録 f63686a85 を枝へ取り込んだ。その後、
任意次元の単体に対する切断の支持を、既存の ShufflePath で構成した。
登録候補は次の三本（全て EInfinity/SimplexCuts/、計 **162行**）。

| モジュール | 行数 | 証明済みの出力 |
| --- | ---: | --- |
| Expanded | 77 | 切断の展開位置から (色,単体の頂点) への写像。非退化性をその単射性として定義し、同色の頂点列が狭義単調であること、頂点数の上界 |
| Balanced | 35 | top degree の頂点数の等式のもとで、各色の頂点数が q+1 であること |
| TopTerm | 50 | 各色の面写像が同じ q 単体の恒等射であり、一つの非退化切断項の積が X^q の環での a^r になること |

主な型は次のとおり（既に対象ビルドを通した宣言）。

```lean
colorPositions_card_of_top
    (h : Nondegenerate s u) (htop : m + q + 1 = r * (q + 1))
    (a : Fin r) : (colorPositions s u a).card = q + 1

fullColorFace_eq_id
    (h : Nondegenerate s u) (a : Fin r)
    (hcard : (colorPositions s u a).card = q + 1) :
    fullColorFace s u a hcard = 𝟙 ⦋q⦌

topTerm_eq_power (X : CosimplicialObject CommRingCat)
    (h : Nondegenerate s u)
    (hcard : ∀ a, (colorPositions s u a).card = q + 1)
    (a : X.obj ⦋q⦌) : topTerm X s u hcard a = a ^ r
```

r=p、語次数 d=q(p−1)、m+1=p+d の場合に頂点数の等式が成立する。
これは n=−q に必要な **同じ次数 q の各項の値**の計算である。
通常の cup 積によって次数を pq に移す操作ではない。
ただし、まだ符号付き総和の係数を 1 と示しておらず、May の同じ W→BE 比較を評価した
P⁰ の計算でもない。上の三本だけで n<0 の主張を完了と数えない。

TopTerm までの対象ビルドは /tmp/bsw16/simplex-top-term-02.log で成功。
専用監査 /tmp/bsw16/audit-simplex-cuts.lean は **3モジュール・18宣言、標準三公理のみ**で成功
（/tmp/bsw16/audit-simplex-cuts.log）。新しい警告・sorry・追加公理なし。
ビルドと監査は別々の一回の鍵で実行し、鍵を返した。共有入口・全体監査は変更していない。

### 106.2 G10 より前に必要なもの

§96.5 で注意したとおり、既存 IntervalCuts.cochainAction の入力は
Surjection.complex A r ⊗ interval A、出力は power (interval A) r であり、Δ¹ 専用である。
CochainActionComponents・CutSigns・CompositionCutSums も頂点／辺の分岐で証明しており、
q を引数として適用する形にはなっていない。
TableReduction.operadMap と Surjection の operad 自体は再利用できるが、
これらが任意の正規化 cosimplicial 複体に作用するという宣言は、別に供給しなければならない。
Assembly の ofCosimplicial と ofCosimplicial_forget も、現時点では未供給の引数である。

原典 [Berger–Fresse §2.2.6–7](https://arxiv.org/pdf/math/0109158#page=34) の一般の切断公式を
複体射と operad 作用へまとめた後で、TR に沿って同じ BE 作用に制限する必要がある。
同論文 §3.2.3–10 の suspension と係数の評価は top 計算への経路になるが、
既存の公開 API にその全次元版の比較はない。
また §3.2.5 の直後の注意のとおり、下の複体の Eilenberg–Zilber 比較を取るだけでは
BE 代数の比較を得たことにならない。複体の擬同型だけから同じ CAlg 対象とは報告しない。

不足を、次の順の証明義務として切り分ける。以下の bf* は **紙の新規名**で、
新たな仮定を本体に入れたものでも、型検査済みの宣言でもない。

```lean
-- 任意次元の単体の正規化鎖上の χ 作用。
bfSimplexAction (A : Type u) [CommRing A] (q r : ℕ) :
  Surjection.complex A r ⊗ bfSimplexChains A q ⟶
    power (bfSimplexChains A q) r

-- 微分・単位・置換・部分合成・単体の射での自然性を証明して作る。
-- この段では既存 interval 上の作用との一致も照合する。
bfNormalizedAlgebra (A : Type u) [CommRing A] :
  CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra

bfNormalizedUnderlyingIso (A : Type u) [CommRing A] :
  bfNormalizedAlgebra A ⋙ Operad.Algebra.forget _ ≅
    bfNormalizedCochains A

-- 正規化から交代余面への、指定した自然な擬同型を保持する。
bfNormalizationComparison (A : Type u) [CommRing A] :
  bfNormalizedCochains A ⟶ cosimplicialCochains A

-- 厳密 BF 代数上で、指定係数の演算を直接評価する最終形。
-- κ は界面と同じ EInfinityPrimeField p。ν は mayNormalizationUnit の像。
bfMayTopValue (p : ℕ) [Fact p.Prime]
    (X : CosimplicialAlgebra κ) (n : ℤ)
    (a : MayClosed ((bfNormalizedAlgebra κ).obj X).carrier (-n)) :
  mayNormalizedClass p ((bfNormalizedAlgebra κ).obj X) n ν a =
    mayClosedClass _ (-n) (bfFrobeniusClosed X n a)
```

bfFrobeniusClosed は、同じ次数の a↦a^p が正規化した閉元を保つことを証明して作るもの。
ここを P⁰ の定義に置き換えるのではない。指定 W→BE を計算できる比較へ移す際も、
増大を保つ equivariant な鎖ホモトピーと、反復入力で T・N の項が消える計算を保持する。
ν の逆冪・逆巡回生成元・TR と BF の符号を一致させる必要がある。

同じ CAlg 対象との接続では、bfNormalizedAlgebra の nerve を既存の
algebraCAlgSource へ送った関手を具体的な ofCosimplicial の候補とし、
上の指定した正規化比較から ofCosimplicial_forget を供給する。
任意に選んだ ofCosimplicial と台の比較だけを仮定して、上の演算の一致を結論しない。
その候補と native な Tot の **指定錐・Frobenius の辺**との比較だけが G10 待ちである。
**今回まだ G10 の待ちの境界には到達していない。G10 の部品は作っていない。**

### 106.3 見込みの改訂と規模による中間停止

§96.6 の top operation と _tot の **1,000〜1,800行**は過小な見込みだった。
区間専用であることは §96.5 に記載済みだったが、一般の作用の微分・operad 法則を
再利用済みの部分に近く数えてしまっていた。今回、その証明の入力型を確認して修正する。
IntervalCuts の205本は約20,124行で、下の見込みはその全量を作り直す値ではない。
Surjection・TR・ShufflePath・テンソルの共通 API は再利用し、区間に特殊化した
切断の符号と境界・二段切断の証明を一般次元へ拡張する分を数える。

| 残る束 | 暫定の新規見込み | 再利用／不足の根拠 |
| --- | ---: | --- |
| 一般の切断、符号、正規化での消滅、微分、単体の射での自然性 | 3,000〜5,500 | ShufflePath・χ の微分・tensorLift は既存。IntervalCuts の頂点／辺の境界分類は一般次元版が必要 |
| 単位・置換・部分合成、TR による同じ BE 作用 | 3,000〜5,000 | χ と TR の operad は既存。二段切断と合成の全符号の比較は Δ¹ の証明を直接適用できない |
| 正規化した cosimplicial 代数の全関手と指定比較 | 1,200〜2,200 | Dold–Kan の複体の比較は再利用。BE 作用の保存と同じ CAlg の選択は未供給 |
| May の係数、ν、同じ次数での Frobenius の照合 | 1,200〜2,000 | 今回の各項の積と既存 May のホモトピー不変性を再利用。符号付き総係数は未証明 |
| native Tot の指定比較への適用（G10 自体を除く） | 500〜900 | 全整数 H/π と現在の source 比較を再利用 |
| A4 の二重模型の実現比較（G10 自体を除く） | 1,500〜2,800 | §96.6 の未完了分を保持 |
| filtered 塔・A4 の利用側 | 300〜550 | §96.6 の未完了分を保持 |
| **残り計** | **10,700〜18,950** | |

改訂 May の完成済み4,128行と今回162行を足すと、現時点の完成見込みは
**14,990〜23,240行**。これは必要行数の下界ではなく、現ソースからの暫定見込みである。
ただし上端が指示書 §26 の外枠約20,000行を超えるため、coordination.md §2 の
「上限を超えそうなときは報告して止める（止まる前に、それまでの検証済みの分をコミット）」
に従い、検証済みの三本を保存して **この線の Lean を中間停止**する。
実測が10,000行に達したという停止ではなく、一般 BF 作用を含めた残りの見込みによる停止。

界面・型・範囲は変更しない。一般の BF 作用の供給を含むこの経路の規模・分担を
調整役が判断できるように不足を明示し、代わりの作業である M15 の段0の紙を進める。
G10 の取り込みだけでこの不足が解消するとは報告しない。

## 107. M15 段0の続き：弱同値不変性の既存出力と restriction の条件（紙のみ、11-13）

M14 の §106 の規模停止の後、指定された代わりの紙の作業として §95・§97 を続けた。
M15 の Lean・界面・drafts の型は変更していない。一般 R 加群の担当も自己決定しない。

### 107.1 固定した厳密 BE 模型から既存 dg 加群へ

最初の不足は §97 の barrattEcclesAssociativeForget A のまま。
標準零単体の単位・合成を元の圏で照合して、台を変えずに Mon (Complex A) へ送る。
ホモロジー上の結合性や BE→Comm の増大は、この厳密な忘却の代用にならない。
以下で B_X はその関手の X での値とする。

その後の固定 X の型と、全厳密 BE 射 f による拡大については、
新しい module ∞ 圏を最初から構成する必要はない。既存宣言を確認した。

| 宣言（InfinityCategories/Project/DerivedCategories/） | 確認した仮定・出力 |
| --- | --- |
| dgAlgebraDerivedInfinityCategory A B_X | B_X 上の右半自由 dg 加群の dg nerve |
| dgAlgebraDerivedInfinityCategory_isStable | 同じ圏の安定性。B_X の可換性を仮定しない |
| dgAlgebraExtensionInfinity A g | dg 代数射 g:B_X→B_Y に対する実 ∞ 関手 −⊗ᴸ_{B_X}B_Y |
| dgAlgebraExtensionInfinity_isExactFunctor | その実 ∞ 関手の完全性。A 上の平坦性を追加しない |
| dgAlgebraMap_quasiEquivalence | QuasiIso g.hom から同じ一対象 dg 関手の準同値 |
| dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso | QuasiIso g.hom から同じ拡大関手の実 ∞ 圏同値 |

最後の二つは DGAlgebraMoritaInfinity.lean に証明済みで、Morita 同値を新たな仮定にする必要はない。
特に §95 の「BE の弱同値に対する module 圏の同値」の **厳密な一辺での部分**は、
台を変えない忘却が完成すれば、この宣言へ直接帰着できる。
新しい紙の候補の型は次の形となる（assocForget はまだ未供給、未型検査）。

```lean
strictModuleExtend {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    dgAlgebraDerivedInfinityCategory A (assocForget.obj X) ⟶
    dgAlgebraDerivedInfinityCategory A (assocForget.obj Y) :=
  dgAlgebraExtensionInfinity A (assocForget.map f)

strictModuleExtend_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : IsQCatEquivalence (strictModuleExtend f)
```

hf は忘却の台の一致を介して同じ dg 代数射の QuasiIso へ運ぶ。
ただし、この一辺の同値性だけでは、native CAlg の全辺と合成に対する module 圏の族を
降下したことにはならない。拡大の合成・恒等比較と、その coherence を保つ降下は残る。
既存 dgModuleExtensionYonedaNerveIso は全関手の比較に利用できるが、
変わる BE 代数を含む全族をこれだけで供給しているとは数えない。

### 107.2 restriction と随伴で残る型の条件

通常の閉零射の圏では DifferentialGraded.dgModuleExtensionRestrictionAdjunction が
既に graph 拡大と moduleRestriction の随伴を与えている。
ただし native な半自由模型で右随伴を作るときは、次の条件を飛ばせない。

DGModuleDerivedFunctor.lean の dgModuleDerivedFunctor とその comparisonIso は、
入力の dg 関手 F に対して

```lean
hF : ∀ M, dgModuleProjectiveProperty A D M →
  dgModuleProjectiveProperty A E (F.obj M)
```

を要求する。一般の B_X→B_Y の restriction に、この条件を無条件で入れることはできない。
例えば B_Y 自身は自由な右 B_Y 加群でも、B_X 上の dg 射影的な加群であるとは限らない。
したがって「既存 dgModuleDerivedFunctor を restriction にそのまま適用」で
native な右随伴を供給したとはしない。

受け渡しでは、restriction が擬同型を保つことに沿う局所化、または restriction の後の
指定した解像度との比較を含め、実 ∞ 関手としての右随伴を要求する。
通常圏の随伴の単位・余単位を、その指定した比較で native に運び、三角形を照合する。
この不足は §95 の 700〜1,400行の「台・単位・全 restriction/extension・弱同値不変性」
に含める対象であって、その上へ別枠として二重加算しない。

### 107.3 分担時の受け取り条件と見込み

HA の地図の 4.2.1.15・4.5.2.1 は通常圏の場合の部分一致、4.5.3.1 は未供給という判定のまま。
一般 R の模型の供給者からは、固定 X の安定圏だけでなく、少なくとも次を同時に受け取る必要がある。

1. 同じ台と単位を持つ厳密 BE→dg 代数の忘却。
2. 全厳密射の拡大・制限の実 ∞ 関手、随伴、恒等・合成比較。
3. 弱同値での上記の同値と、native な CAlg の辺・合成への降下。
4. 同じ一般 R 加群の相対テンソルと、その単位・結合性・対称性・底変換。
5. M15 の指定した R→S の辺、その fiber と指数射を、この同じ単位とテンソルで読む比較。

§95 の一般 R の束の2,500〜4,500行は暫定のまま。今回、厳密な拡大の弱同値不変性は
既存宣言で済むことを明確にした一方、restriction の hF を省略できないことも明記した。
相対テンソルの対称性を結合的 dg 代数への忘却だけから供給したとはしない。
担当と受け渡す全関手の型を決める前に、この見込みを実装承認や完了数へ読み替えない。

**保存**：§106 の検証済み三本と報告は 9f27a22de に17:54 JSTにコミットした。
本節は紙のみの追記。凍結確定の連絡はまだ受けていない。

## 108. 5a-5a：一般 BF 作用の固定した型一覧（11-13、実装前の紙）

### 108.1 範囲・数え方・構成

§106 に対するユーザー承認に従い、上の三行を共通の **5a-5a** として切り出す。
見込み7,200〜12,700行、外枠25,400行。M14 の残り四行・native Tot・G10 は含めない。
置き場所は EInfinity/SimplexCuts/ と新設 EInfinity/Cosimplicial/。
既存 IntervalCuts/・Operad/ の公開定義は変えない。共有入口と全体監査への登録は調整役に委ねる。
他レーンの同じ新規ファイルを発見した場合は編集前に止めて報告する。

数え方は inf-supply-w2.md §14 と、今回のユーザー指示のとおり。
下の L01〜L28 が新しい数学の一覧。**証明の分割は数えず、型を追記する。
前提計算（既存構成の単位・自然性・係数移送の法則）は各 L ごとに3本まで。
照合は I01〜I03 の全体3本まで。それ以外の新しい数学は型と漏れた理由を報告して止める。**
定義を作る際の恒等・合成のフィールドも下の法則に含める。
「構造を引数に要求する」ことで下の法則を仮定に逃がさない。

構成は次の二層に分ける。

- 一般の単体集合の正規化鎖 C_A(S) 上に χ の切断余作用を構成し、TR:E→χ に沿って制限。
- 標準単体 Δ[q] のその余代数と X^q の離散 BE 代数から、既存 convolutionAlgebra を作る。
  ∏q Hom(C_A(Δ[q]),disc(X^q)) のうち、全 α:q→r で前合成と後合成が一致するものを、
  **通常の BE 代数の等化子**として取る。この台と正規化したコチェイン複体を同定する。
  native な ∞ 圏の Tot・錐の比較はここでは作らない。

後半の convolutionFunctor・convolutionPre/Post と Operad.AlgebraLimits は再利用する。
一般次元の cochain の operad 法則をもう一度直接証明する経路にはしない。

### 108.2 型のために固定する定義と記号

以下は **紙の Lean 型案、未型検査**。未供給名は新規定義として構成するもので、公理・仮定ではない。
`A : Type u [CommRing A]`、`S T : SSet.{0}`、`X Y : CosimplicialAlgebra A` とする。
`C S := (BarrattEccles.normalizedFunctor A).obj S : Complex A`。
`χ := Surjection.operad A`、`E := BarrattEccles.operad A`。
`cmap f := (BarrattEccles.normalizedFunctor A).map f`。
`gen S q x : (C S).X (-(q:ℤ))` は既存の normalized generator を extend の同型で運んだもの。

組合せの入口では `s : Cut m q`、`u : Surjection.Word r (m+1)`。
`colorPositions s u.val a` は §106 の定義をそのまま使う。
`vertices s u a` は、その順序列を s.vertical で読む OrderHom。
`outputDegree s u a := (colorPositions s u.val a).card-1`。
`face s u a : ⦋outputDegree s u a⦌ ⟶ ⦋q⦌` はその単調写像。
空の色がないことは L01 で証明する。非退化性がなくても face は定義する。
`lo s i`・`hi s i` は水平座標 i の fiber の最初・最後の垂直座標。

BF §2.2.3–6 の符号は次の定義で固定する。

```lean
intervalLength s u i := hi s i - lo s i + if Surjection.Caesura u.val i then 1 else 0
permutationExponent s u := ∑ i, ∑ j,
  if i < j ∧ u.val j < u.val i then intervalLength s u i * intervalLength s u j else 0
positionExponent s u := ∑ i, if Surjection.Caesura u.val i then hi s i else 0
cutSign s u : ℤ := (-1) ^ (permutationExponent s u + positionExponent s u)
```

`cutTensor A S s u x` は、各色の `gen S _ (S.map (face s u a).op x)` の
既存テンソル冪への純粋テンソル。総次数は L02 で合わせる。
`cutTerm` は cutSign 倍の cutTensor、`cutSum` は全 s に関する和。
退化な face は normalized generator によって零となるため、符号の定義を変えずに保持する。
`rawComponent` は係数の自由基底と単体の自由基底から線形拡張した切断和。
`component` は L07 により正規化へ降ろし、整数次数へ延長した双線形成分。

余単体的正規化の入口は `N X : Complex A` とし、
`(N X).X (q:ℤ)` を全 codegeneracy σ_i の核の共通部分、負次数を零とする。
微分は交代余面の和の制限。`normInclusion X : N X ⟶ cosimplicialCochains A |>.obj X`。
これは P⁰ や levelwise Frobenius を用いて定義するものではない。

`P_X := ∏q convolutionAlgebra (hopf A) (simplexBECoalgebra A q) (discAlg(X^q))`。
`Q_X := ∏(α:q→r) convolutionAlgebra (hopf A) (simplexBECoalgebra A q) (discAlg(X^r))`。
`post_X, pre_X : P_X ⟶ Q_X` は各 α における後合成と前合成。
`bfNormalizedAlgebra.obj X := equalizer post_X pre_X`、射は L22 による。
台の族の次数 k を評価するとき、内部 Hom の微分の符号を保持する。
正次数 k の評価と N X の比較には `(-1)^(k*(k+1)/2)` の次数ごとの係数を入れ、
その微分の式を L24 で証明する。符号を省いた評価を複体射と主張しない。

### 108.3 残る数学の型一覧：切断と余作用

以下の `u` の引数は上の Word、degree d の際は BasisWord へ特殊化する。
総次数の eqToHom は L02 が供給する等式で統一する。arity零は L14 で別に処理する。

```lean
-- L01 色の出現と非空性。
colorPositions_nonempty (s : Cut m q) (u : Surjection.Word r (m+1)) (a : Fin r) :
  (colorPositions s u.val a).Nonempty

-- L02 各色の頂点数と全出力次数（非退化性を前提にしない）。
outputDegree_sum (s : Cut m q) (u : Surjection.Word r (m+1)) :
  ∑ a, outputDegree s u a = m + q + 1 - r

-- L03 面の非退化性と §106 の対の単射性の同値。
faces_mono_iff (s : Cut m q) (u : Surjection.Word r (m+1)) :
  (∀ a, Mono (face s u a)) ↔ Nondegenerate s u.val

-- L04 退化な切断項は実テンソルで零。
cutTensor_eq_zero (h : ¬Nondegenerate s u.val) (x : S _⦋q⦌) :
  cutTensor A S s u x = 0

-- L05 正規化生成元と色ごとの面の引き戻しを保つ自然性。
cutTerm_map (f : S ⟶ T) (x : S _⦋q⦌) :
  (TensorPowers.map (cmap f) r).f _ (cutTerm A S s u x) =
    cutTerm A T s u (f.app _ x)

-- L06 切断和の生成元公式（rawComponent の線形拡張の値）。
rawComponent_value (u : Surjection.BasisWord (r+1) d) (x : S _⦋q⦌) :
  rawComponent A S (r+1) d q (Surjection.basis A u) (ModuleCat.freeMk (ULift.up x)) =
    cutSum A S u x

-- L07 入力の退化を消す。標準単体の退化も、一般 S の退化も含む。
cutSum_degenerate (u : Surjection.BasisWord (r+1) d)
    (i : Fin (q+1)) (x : S _⦋q⦌) :
  cutSum A S u (S.σ i x) = 0

-- L08 正規化した成分でも同じ切断和を復元。
component_generator (u : Surjection.BasisWord (r+1) d) (x : S _⦋q⦌) :
  component A S (r+1) (-(d:ℤ)) (-(q:ℤ)) _ (by omega)
    (Surjection.complexBasis A u) (gen S q x) = cutSum A S u x

-- L09 微分の項ごとの切断和の等式。q=0,d=0 の境界も含む。
-- boundaryCoefficient / boundarySimplex は既存の χ の微分／交代面和。
cutSum_boundary (u : Surjection.BasisWord (r+1) d) (x : S _⦋q⦌) :
  dTensor (cutSum A S u x) =
    cutSumLinear A S (boundaryCoefficient u) x +
      (-1 : ℤ)^d • cutSumLinearSimplex A S u (boundarySimplex x)

-- L10 全整数の双線形 Leibniz 則。
component_d (r : ℕ) (i j : ℤ)
    (a : (χ.arity r).X i) (b : (C S).X j) :
  (power (C S) r).d (i+j) (i+j+1) (component A S r i j _ rfl a b) =
    component A S r (i+1) j _ (by omega) ((χ.arity r).d i (i+1) a) b +
      i.negOnePow • component A S r i (j+1) _ (by omega) a ((C S).d j (j+1) b)

-- L11 置換に対する全切断和の Koszul 符号。
cutSum_permutation (σ : Equiv.Perm (Fin r)) (u : Surjection.BasisWord r d)
    (x : S _⦋q⦌) :
  cutSum A S (Surjection.rename σ u) x =
    ((permutationAction (C S) r σ).asIso.hom).f _ (cutSum A S u x)

-- L12 二段の切断と合成語の切断の同じ実テンソルでの一致。
-- compositeCutSum は既存 OverlapPartition と compositionSign の有限和。
-- nestedCutSum は外側の色の一つを内側の切断で置き換えた有限和。
cutSum_composite (u : Surjection.BasisWord (m+1) d)
    (v : Surjection.BasisWord n e) (i : Fin (m+1)) (x : S _⦋q⦌) :
  compositeCutSum A S u v i x = nestedCutSum A S u v i x

-- L13 unary の単位切断。q は任意。
cutSum_unit (x : S _⦋q⦌) :
  cutSum A S Surjection.unitWord x = (oneIso (C S)).inv.f _ (gen S q x)

-- L14 nullary の余作用と、nullary を含む部分合成。
coaction_nullary : coaction A S 0 =
  (nullaryCoefficient A ⊗ₘ chainsAugmentation A S) ≫ (λ_ (𝟙_ (Complex A))).hom
coaction_comp_nullary (m : ℕ) (i : Fin (m+1)) :
  (χ.comp m 0 i ▷ C S) ≫ coaction A S m =
    ((β_ (χ.arity (m+1)) (χ.arity 0)).hom ▷ C S) ≫
    (α_ _ _ _).hom ≫ (χ.arity 0 ◁ coaction A S (m+1)) ≫
    tensorCoInsertionAction (C S) (χ.arity 0) m 0 i (coaction A S 0)

-- L15 全整数の余作用の自然性。正規化生成元上の L05 から。
coaction_natural (f : S ⟶ T) (r : ℕ) :
  (χ.arity r ◁ cmap f) ≫ coaction A T r =
    coaction A S r ≫ TensorPowers.map (cmap f) r

-- L16 正の内側 arity の、実複体射の全部分合成則。
coaction_comp (m n : ℕ) (hn : 0<n) (i : Fin (m+1)) :
  (χ.comp m n i ▷ C S) ≫ coaction A S (m+n) =
    ((β_ (χ.arity (m+1)) (χ.arity n)).hom ▷ C S) ≫
    (α_ _ _ _).hom ≫ (χ.arity n ◁ coaction A S (m+1)) ≫
    tensorCoInsertionAction (C S) (χ.arity n) m n i (coaction A S n)

-- L17 実複体射の等変性・単位（L11,L13 の線形拡張）。
coaction_equivariance (r : ℕ) (σ : Equiv.Perm (Fin r)) :
  (χ.sequence.map (FiniteBijection.permutation r σ) ▷ C S) ≫ coaction A S r =
    coaction A S r ≫ (permutationAction (C S) r σ).asIso.hom
coaction_unit : (χ.unit ▷ C S) ≫ coaction A S 1 ≫ (oneIso (C S)).hom = (λ_ (C S)).hom

-- L18 作用の式を保持して TR による BE 余代数と自然な射へ束ねる。
bfCoalgebra_coaction (r : ℕ) : (bfCoalgebra A S).coaction r =
  ((TableReduction.operadMap A).map.app (FiniteBijection.of r) ▷ C S) ≫ coaction A S r
bfCoalgebraMap_comm (f : S ⟶ T) (r : ℕ) :
  (E.arity r ◁ cmap f) ≫ (bfCoalgebra A T).coaction r =
    (bfCoalgebra A S).coaction r ≫ TensorPowers.map (cmap f) r
```

L09・L12 は境界項の相殺・二段切断の有限添字対応を証明に含む。
退化切断も零として同じ和に保持する。端点・同色の接着・空区間・arity零を捨てない。
L06,L08 の basis 名は現在の自由加群の実 API に合わせて定義する略記であり、
基底の存在や正規化への降下を別の未証明仮定にしない。

### 108.4 残る数学の型一覧：正規化した cosimplicial 代数

```lean
-- L19 正規化部分加群を交代余面の微分が保つ。
normalized_d_mem_exact (q : ℕ) (a : normalizedComponent X q) :
  ∀ i : Fin (q+1), (X.σ i).hom (alternatingCofaces X q a.val) = 0

-- L20 正規化包含の微分・自然性。
normInclusion_d (i j : ℤ) :
  (N X).d i j ≫ (normInclusion X).f j =
    (normInclusion X).f i ≫ ((cosimplicialCochains A).obj X).d i j
normInclusion_naturality (f : X ⟶ Y) :
  (Nmap f) ≫ normInclusion Y = normInclusion X ≫ (cosimplicialCochains A).map f

-- L21 正規化包含の指定ホモトピー逆。余単体的な Dold–Kan の分解を使う。
normalizationHomotopyEquiv (X : CosimplicialAlgebra A) :
  HomotopyEquiv (N X) ((cosimplicialCochains A).obj X)
normalizationHomotopyEquiv_hom : (normalizationHomotopyEquiv X).hom = normInclusion X

-- L22 convolution の等化子への全 X 射。二つの自然性の長方形。
post_naturality (f : X ⟶ Y) : Pmap f ≫ post_Y = post_X ≫ Qmap f
pre_naturality (f : X ⟶ Y) : Pmap f ≫ pre_Y = pre_X ≫ Qmap f
bfNormalizedAlgebra_map_id (X) : bfMap (𝟙 X) = 𝟙 _
bfNormalizedAlgebra_map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : bfMap (f ≫ g) = bfMap f ≫ bfMap g

-- L23 等化子の斉次元を恒等 q 単体で読む評価とその逆。
evaluation_mem (q : ℕ) (a : bfCarrier X |>.X (q:ℤ)) :
  scaledEvaluation X q a ∈ normalizedComponent X q
reconstruction_evaluation (q : ℕ) (a : bfCarrier X |>.X (q:ℤ)) :
  reconstruct X q (scaledEvaluation X q a) = a
evaluation_reconstruction (q : ℕ) (a : normalizedComponent X q) :
  scaledEvaluation X q (reconstruct X q a) = a
bfCarrier_isZero_negative (i : ℤ) (hi : i<0) : IsZero ((bfCarrier X).X i)

-- L24 評価の次数係数と微分の比較。符号なしの評価ではない。
evaluation_d (i j : ℤ) :
  (bfCarrier X).d i j ≫ evaluationComponent X j =
    evaluationComponent X i ≫ (N X).d i j

-- L25 同じ評価の全 X 射での自然性。
evaluation_naturality (f : X ⟶ Y) (i : ℤ) :
  (bfMap f).hom.f i ≫ evaluationComponent Y i =
    evaluationComponent X i ≫ (Nmap f).f i

-- L26 全関手の台の同型と指定された正規化比較。
bfNormalizedUnderlyingIso :
  bfNormalizedAlgebra A ⋙ Operad.Algebra.forget E ≅ bfNormalizedCochains A
bfNormalizationComparison : bfNormalizedCochains A ⟶ cosimplicialCochains A
bfNormalizationComparison_app : (bfNormalizationComparison A).app X = normInclusion X
bfNormalizationComparison_quasiIso (X) : QuasiIso ((bfNormalizationComparison A).app X)

-- L27 構成した代数の作用の、各 q への射影の評価公式。
-- wedgeProjection は等化子から同じ convolution 代数への射。
bfAction_projection (r q : ℕ) :
  ((bfNormalizedAlgebra A).obj X).action r ≫ (wedgeProjection X q).hom =
    (𝟙 _ ⊗ₘ TensorPowers.map (wedgeProjection X q).hom r) ≫
      (simplexConvolution X q).action r

-- L28 同じ作用を正規化コチェインの元で読む明示的な BF 切断公式。
-- lhs は L26 の同型で運んだ「実際の」BE作用。rhs は TR の実係数を用いた切断和。
bfAction_formula (r d : ℕ) (e : (E.arity r).X (-(d:ℤ)))
    (degrees : Fin r → ℕ) (a : ∀ c, normalizedComponent X (degrees c)) :
  normalizedActionValue X e degrees a = bfCutEvaluation X e degrees a
```

L19 の codegeneracy の添字は Fin(q+1)。
L14 の nullaryCoefficient A : χ.arity 0 ⟶ 𝟙_ (Complex A) は、
Surjection.zeroAugmentation と正次数の基底が空であることから定義する同じ係数射。
χ 全体の operad augmentation の存在は仮定しない。
L21 の複体のホモトピー同値には Mathlib の Dold–Kan の分解を反対圏で用いる。
L23 の reconstruction は、各 q 単体の単射 θ:[k]→[q] の生成元を X.map θ の像へ送り、
非単射 θ は零とする式。全 α の自然性と codegeneracy の核の条件の同値もこの主張に含む。
L28 の出力次数は ∑c degrees c−d、負なら零。r=0・d=0 の単位の式も含める。
ここで Frobenius・ν・May の P⁰ の係数の総和はまだ計算しない（M14 側の残り）。

### 108.5 照合の三枠と既存の再利用

I01 は区間の版との必須の照合として予約する。

```lean
-- I01 Δ¹ の同じ正規化鎖の同型に沿う、全部分余作用の厳密な一致。
intervalCoaction_compare (r : ℕ) :
  (χ.arity r ◁ intervalCarrierIso A |>.hom) ≫ IntervalCuts.cochainAction A r =
    coaction A Δ[1] r ≫ TensorPowers.map (intervalCarrierIso A).hom r
```

intervalCarrierIso は定義的に同じ場合は Iso.refl、extend の表現差があればその既存の標準同型。
BE の方は、この同じ式に TableReduction.operadMap を前置した帰結とし、別の新規数学には数えない。
I02・I03 は未使用のまま残す。二項 AW や別の模型の比較を便利さだけで追加しない。

再利用する既存宣言：ShufflePath.horizontal_surjective、vertex_strictMono_on_color、
AlexanderWhitney.generator_map_of_not_mono、normalization_restrictToNormalized、
既存 tensorLift・ι_tensorLift、Surjection の complexPartialComposition と compositionOnWords、
Operad.restrictCoalgebraObj、convolutionAlgebra・convolutionPre・convolutionPost、
AlgebraLimits、Mathlib Dold–Kan の normalized/alternating のホモトピー同値。
[原典 BF §2.2.3–7](https://arxiv.org/pdf/math/0109158#page=33) の一般の切断と符号を用いる。
証明の順は L01〜L18 → I01 → L19〜L28。定義・既存構成の組み立ては依存順に挟む。
完成時が調整役への取り込み点。検証済み小束は枝に保存するが、native Tot の完了とはしない。

### 108.6 実装に伴う証明分割の型と計数（進行中）

L01〜L03 は Outputs・Faces の対象ビルドに成功した（simplex-faces-01.log）。
L04〜L06 は同じ一覧の範囲で実装中。検証中のファイルはまだコミットしていない。
型一覧と数え方の紙は **18ca0ea4a** に保存済み。

証明分割の補題は次の型。L02 の頂点数の分割、L03 の狭義単調性、
L04 の零因子の消滅は、それぞれ一覧の主張の同じ証明を分けたもの。

```lean
-- L02 の分割（検証済み）。
colorPositions_card_eq s u a : (colorPositions s u.val a).card = outputDegree s u a + 1
colorPositions_card_sum s u : ∑ a, (colorPositions s u a).card = m + q + 1
-- L03 の分割（検証済み）。
vertices_strictMono (h : Nondegenerate s u.val) (a : Fin r) : StrictMono (vertices s u a)
-- L04 の分割。
tensorValue_eq_zero (K : Complex A) (n : ℕ) (d : Fin n → ℕ)
  (v : ∀ i, K.X (-(d i:ℤ))) (i : Fin n) (h : v i = 0) : tensorValue K n d v = 0
-- L07 の分割：入力で一つの退化を合成すると、少なくとも一つの色の面が退化する。
face_comp_sigma_not_mono (s : Cut m (q+1)) (u : Surjection.Word r (m+1))
  (i : Fin (q+1)) : ∃ a, ¬Mono (face s u a ≫ SimplexCategory.σ i)
```

L05 の前提計算は次の三本で **3/3**。新しい構成や新しい数学の枠には拡張しない。

```lean
gen_naturality f q x : (cmap f).f (-(q:ℤ)) (gen A S q x) = gen A T q (f.app _ x)
tensorValue_map f n d v : (TensorPowers.map f n).f _ (tensorValue K n d v) =
  tensorValue L n d (fun i => f.f _ (v i))
component_index_naturality (f : K ⟶ L) (h : i=j) (x : K.X i) :
  f.f j ((eqToHom (congrArg K.X h)).hom x) =
    (eqToHom (congrArg L.X h)).hom (f.f i x)
```

lo・hi の定義に用いる intervalPositions_nonempty は、L01 の既存の horizontal_surjective
の評価を切り出したもの。照合 I01〜I03 はまだ0/3、その他の L の前提計算も0/3。
凍結確定の連絡はまだ受けていない。

## 109. L09 の境界計算で一覧外と判定した数学（11-13、型の報告）

L01〜L08 の実装・検証を進める間に、次の L09 の有限和の証明を具体化した。
一般次元では、テンソルの出力面の削除・χ の文字の削除・入力単体の面の削除を
対応させ、残る境界項を符号を反転させて対にする必要がある。
既存 IntervalCuts のその対応は頂点／辺に特殊化されている。
**§108 の一覧は境界の総和の等式だけを L09 に書き、この対応の構成を型に落としていなかった。**

必要と判断した追加候補は次の型。以下は紙のみで、Lean の定義・証明は追加していない。
`u : BasisWord (r+1) d`、`u' := positiveWord u` とする。
全ての退化項・境界次数零の項も零として残した有限添字を使う。

```lean
abbrev BoundaryBalanceIndex (u : Surjection.BasisWord (r+1) d) (q : ℕ) :=
  (Σ s : Cut (r+d) q, Σ a : Fin (r+1), Fin (outputDegree s (positiveWord u) a + 1)) ⊕
  ((Fin (r+d+1) × Cut (r+d-1) q) ⊕ (Fin (q+1) × Cut (r+d) (q-1)))
```

第一群が出力のテンソルの一面を削除する項、第二群が係数語の一文字を削除する項、
第三群が入力単体の一面を削除する項。第二・第三群は L09 の右辺から左辺へ移す符号も含める。
d=0 の第二群、q=0 の第三群、および次数零の出力の面は零とする。
非全射・隣接値が等しくなる係数語の削除も零として保持する。
これらの規約で、各添字の実テンソル値を次の型で定義する必要がある。

```lean
boundaryBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord (r+1) d) (q : ℕ) :
  BoundaryBalanceIndex u q → S _⦋q⦌ →
    (power (chains A S) (r+1)).X (-((d+q : ℕ):ℤ) + 1)

-- 追加候補 L09a（未承認・未実装）。
boundaryBalance_pairing (u : Surjection.BasisWord (r+1) d) (q : ℕ) :
  ∃ τ : Equiv.Perm (BoundaryBalanceIndex u q),
    Function.Involutive τ ∧
    (∀ j, τ j = j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      boundaryBalanceTerm A S u q j x = 0) ∧
    (∀ j, τ j ≠ j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      boundaryBalanceTerm A S u q (τ j) x = -boundaryBalanceTerm A S u q j x)
```

これは既存の構成の単位・自然性・係数移送の式ではなく、任意次元の境界項の
**新しい組合せ的な対応と符号の主張**である。L09 の総和の等式より強い項ごとのデータを作るため、
「heartbeat のための同じ内容の証明分割」や前提計算3本の枠へ自己判断で入れない。
漏れた理由は、§108 の作成時に L09 のゴールの型で境界計算を一括し、
その証明に使う一般次元の有限添字の対応を独立の数学として数えなかったこと。

ユーザーの「それ以外の新しい数学の補題が要ったら止まって報告」に従い、
**L09a の定義・証明には進まない**。先行する L01〜L08 の検証・修正・保存を終えて報告する。
外枠25,400行を理由にした停止ではない。照合I01〜I03も未使用のまま。

## 110. 方針の再比較：May＋一般 BF と coherent Sp 値 P⁰（11-13、紙・判断待ち）

### 110.1 最新の指示と作業状態

**最新の指示により、5a-5a の切り出しは未決に戻す。Lean の編集・ビルド・監査は停止した。**
§108 の「承認された独立段」という扱いは、最新の判断としては採用しない。
以下は実装の再開や界面変更の承認を先取りしない紙の比較である。

指示変更前に、§108 の紙を18ca0ea4aへ保存し、切断の下書きを進めていた。
新しい切断の11本・**568行**は個別の対象ビルドで通過したが、専用監査・コミットは未実施。
RawAction（52行）・DegenerateInput（46行）・Normalization（87行）の**185行**は未検証。
RawAction の語長の cast と自由加群の評価に型検査の失敗が残っている。
これらの修正を含め、指示変更後は Lean を触っていない。
既存の§106の三本162行とは区別する。未検証185行を完成分として見込みから引かない。
最後の対象ビルドのセッションは終了済みで、鍵・整理券を持っていない。
§108.6・§109 の紙と本節は作業木に保持し、この比較中に追加コミットはしない。
凍結確定の連絡はまだ受けていない。

### 110.2 残りの新規量を同じ基準で比較する

**既存実測と残りの見込みを混ぜない。** coherent 案の§94.2は、既にV・π/Hの7,194行と
鎖模型の3,022行を除いた「残り」の表である。そこから10,216行を再度控除しない。
同様に May の4,128行は完成分であり、§106.3はそれと当時の切断162行を除いた残り。

#### (a) May 案＋一般次元の Berger–Fresse 作用

§106.3の一般BFの三行7,200〜12,700行から、今回の個別コンパイル済み568行を暫定控除する。
この568行は切断・面・符号・生成元・その自然性の束で、微分・部分合成・cosimplicial代数の
全関手はまだ含まない。未監査のため、正式な完成認定とは区別した比較用の控除である。

| 残る新規 | §106.3の残り | 現時点の残りの暫定見込み |
| --- | ---: | ---: |
| 一般切断・符号・正規化・微分・自然性 | 3,000〜5,500 | 2,432〜4,932 |
| 単位・置換・部分合成とTRによる同じBE作用 | 3,000〜5,000 | 3,000〜5,000 |
| 正規化cosimplicial代数の全関手と指定比較 | 1,200〜2,200 | 1,200〜2,200 |
| **一般BFの残り** | **7,200〜12,700** | **6,632〜12,132** |
| May係数・ν・Frobeniusの照合 | 1,200〜2,000 | 1,200〜2,000 |
| native Totの指定比較への適用（G10自体を除く） | 500〜900 | 500〜900 |
| A4の二重模型の実現比較（G10自体を除く） | 1,500〜2,800 | 1,500〜2,800 |
| filtered塔・A4の利用側 | 300〜550 | 300〜550 |
| **残り合計** | **10,700〜18,950** | **10,132〜18,382** |

既存May4,128行・以前の切断162行・今回の568行を加えた完成時の見込みは、
§106と同じ14,990〜23,240行。作業を進めた分を控除しただけで、見積もり全体を縮めた値ではない。
568行を正式な完成分と数えない保守的な比較では、残り10,700〜18,950行をそのまま使う。

#### (b) coherent な Sp 値 P⁰

§94以降、こちらの鎖模型→nativeの未完成部分を閉じる実装は進めていない。
新しいMayのho上のNatTransは、Sp値のFunctorHomを供給しない。
W→BE・混合色・零次の環比較は再利用候補だが、coherentな演算との同定は別に要るので、
May4,128行や今回のBF568行を、そのまま次の表から引かない。

| §94.2からの残りの新規 | 現在の見込み | 既存分の控除の扱い |
| --- | ---: | --- |
| 正のHomと実orbit全複体の鎖同型 | 900〜1,600 | 次数同型・指定包含・座標は既存。微分可換性は残る |
| native orbit・norm・Tateの全自然比較 | 3,000〜5,500 | hG本体は既存として既に考慮。比較・norm・指定境界は残る |
| 完全入力のexact性・降下・T_pの延長 | 2,800〜4,800 | p入力・準同型保存・混合色の自由性は既存として控除済み |
| スペクトル的な右k作用とe | 2,800〜5,000 | 鎖のseed・H⁰計算は既存。右作用とcoherentな照合は未供給 |
| BE作用によるP⁰とRem 2.2.7 | 1,800〜3,200 | 既存BE作用を使う。Mayのhoの演算との比較を自動では仮定しない |
| 離散・Totの最後の照合 | 1,000〜2,000 | 原表のG10後の工程。一般BF作用はこの経路の前提にしない |
| **§94.2の範囲での残り** | **12,300〜22,100** | **10,216行はこの外側の完成済み実測** |

ただし、公平なBS用の比較には、原表の一行で明示していなかった次も数える必要がある。
現在のV_AにはsourceIsoとπ/H比較があるが、任意のnative極限・実現を保つという公開定理を
今回の調査では確認できなかった。Gammaの有限極限保存だけではcosimplicial Totの保存にならない。
またA4の外側の単体的実現・filtered塔への指定Frobeniusの比較は、§96.5で明示した追加義務である。

coherent案ではこれを一般の自然変換の移送で処理する候補とし、
Vの必要な極限・実現保存とその指定比較に500〜1,000行、外側の実現・filteredとA4への適用に
500〜1,400行を**暫定の追加リスク**として置く。
原表の離散・Totの1,000〜2,000行は成分計算・同じTotへの適用に使い、この二つの一般比較と分ける。
これを含むBS用の残りは **13,300〜24,500行**。
この追加1,000〜2,400行は未実装の工程見込みであり、既存宣言で短縮を検証した数字ではない。

両案とも、③-bが供給するG10・一般のnative錐の橋そのものは上の新規量へ加えていない。
それがゼロ作業という意味ではなく、どちらにも必要な共通の外部依存として別に扱っている。

### 110.3 Totの群は一般BF作用を必須にしない

ここは§106.2の読みを修正する。
**一般のBerger–Fresse作用が、ofCosimplicialや厳密BE図式のTotを作るために必ず要る、とは言えない。**
それは厳密な正規化コチェイン代数を先に作る一つの経路であり、native極限を先に作る経路がある。

同じUについて、次は既に無条件で証明済みである。

| ファイル・宣言 | 実際の出力 |
| --- | --- |
| BarrattEccles/FreeProbeDerivedFreeForget.lean：cAlgFreeForgetDerivedAdjunction | 既存CAlg_Rと既存D(A)の間の全∞随伴。A可換環のみが入力 |
| 同：cAlgForgetDerived_mapJoinCone_isLimit | 任意のKと同じ指定極限錐cを、同じUで送った錐が極限錐 |
| 同：cAlgForgetDerived_hasLimit_postcomp | CAlg側の極限の存在からD(A)側の存在 |
| BarrattEccles/Theory.lean：barrattEcclesCore.forget_preservesLimits | 上の実定理が既に中核の欄へ代入済み |

OfTransportという条件付き版もあるが、FreeProbeUnitLocalTransport.freeProbeUnitTransportConditionを
代入した上の無条件版が本体にある。係数拡大・制限の随伴と取り違えていない。
**Uの極限保存を新たな数千行のBF構成に帰着させる必要はない。**

native先行の手順は次のとおり。

1. Xを離散CAlgのcosimplicial図式へ送り、その**同じnative極限錐**を作る。
2. Uの上の既存定理で同じ錐をD(A)の極限錐へ送る。
3. discrete_forgetとG10の全関手・射・指定錐の比較を用い、台を指定した交代余面複体と比較する。
4. パラメータX全体での極限の関手性によりofCosimplicialを作り、
   ofCosimplicial_forgetをFunctorIsoとして、_coneを元の指定錐として供給する。

**残る点**：右随伴であることはCAlgの極限の「存在」や、Uが極限を「創出」することの証明ではない。
D(A)で極限を取って、代数構造が自動で付いたとはしない。
第一段のCAlgのnative錐の存在・全関手性・厳密なReedy/frame模型との指定比較が③-bの3b-4の仕事である。
通常のBE代数圏の極限だけを、そのnative極限錐と同一視しない。
G10の一般部品を本レーンで再実装する案でもない。

| 利用先 | May＋BFの場合 | coherent Spの場合 |
| --- | --- | --- |
| ofCosimplicial・_forget・_cone（5a-5） | native先行なら一般BF作用は不要。Mayのn<0の演算計算には別途BF作用が要る | native先行なら一般BF作用は不要 |
| ③-b 3b-4の厳密BE図式のTotとU | Reedy/frameによるnative錐と既存Uの極限保存で進める経路があり、一般BF作用は必須でない | 同じ。P⁰の選択とは独立 |
| M14のcosimplicial Frobeniusとの一致 | 現在の直接計算経路は同じBF作用を要する。台の擬同型だけでは足りない | coherentなSp値自然変換と極限保存の比較で進める候補。BF作用を用いる必要はない |

coherent案の最後の行は「各射影でπ_nが一致する」だけの議論ではない。
離散入力でP⁰とFrobeniusがcoherentな図式の射として一致すること、
W=U⋙Vの必要な極限保存、および同じ極限錐の射の一意性を使う。
離散Eilenberg–MacLane対象間の写像空間の0切断性から離散計算を全図式へ運ぶ比較も明記して証明する。
その後にπ_nを取る。ho上の自然性だけのMay演算にこの手順を適用してはならない。
外側の単体的実現でもWの該当する保存と指定辺の比較が必要であり、「coherentだから」の一語で省略しない。

### 110.4 KSTで減らせる部分と、減らせない部分

KST/SpectraのBFはBousfield–Friedlanderのスペクトル模型であり、
ここで検討しているBerger–Fresseの一般コチェイン作用とは別である。

| 既存KST宣言 | coherent経路で再利用する範囲 | 供給したことにならないもの |
| --- | --- | --- |
| homotopyFixedPoints、GroupAction.diagramFunctor | 実際の厳密作用図式のhG対象 | orbit、norm、Tate |
| homotopyFixedPointsInfinityCone・_vertex・_isLimit | **元のhG対象**を頂点とするnative極限錐 | 今の周期係数模型とこの図式との全自然同定 |
| homotopyFixedPointsMap、OmegaSpectrum.homotopyLimitMap | 同変射・図式の射での実スペクトル射 | orbit→fixedのnorm自然変換 |
| homotopyTotalizationInfinityCone・_isLimit | 実スペクトルの指定Totのnative極限性 | CAlgやVの極限保存そのもの |
| GroupActionCochains.levelMap_piIsomorphism、FreeActionFamily.endMap_piIsomorphism | 自由作用のcochain・endの不変性 | Tateのexact性、T_pの全入力への延長、右k作用 |

従ってhG対象・指定錐を新たに作る費用は**ゼロ**。
ただし§94.1は既にこのKSTのhGとnative錐を認識した上で§94.2を見積もっている。
3,000〜5,500行からその構成費をもう一度引くのは二重控除になる。
同じp入力の実作用図式との比較を作った後で、残額の中のhG側をこの既存APIへつなぐ。

今回KST/SpectraとSpectra/の公開宣言を調べた範囲では、
当該入力のnative homotopy orbit、orbit→fixedのnorm、指定境界を持つTateの全関手、
スペクトル的な右k作用とeは確認できなかった。
スペクトルの安定性や一般のcofiberの道具があっても、norm射の構成と自然性・指定境界の同定は別に要る。
加群上の有限和としてのnormや、鎖の周期Homをnative Tateの定義済み実例と数えない。
GroupNerveNormalizedCohomologyの正次数消滅はCharZeroの体を仮定するため、F_p係数の代用にはならない。

原典[DAG XIII Construction 2.2.6・Remark 2.2.7・Warning 2.2.8](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf#page=35)
では、指定Tate類からスペクトルの演算を作る。一般kではk線形な演算ではない。
既存のk線形なpowerOperationCoefficientSeedとそのH⁰の値だけで、
この右作用・指定類の射eを供給したとはしない。
[BS Lemma 8.4](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf#page=63) の
二重模型の実現上のFrobeniusの主張は、どちらの経路でも最後まで範囲に残す。

### 110.5 推奨と判断点

**推奨は、May案を当面維持しつつ、Totの群と3b-4はnative錐先行で進める方針。**
一般BF作用を共通部品として独立承認する理由に「Totの構成にも必須」を使わない。
一般BF作用が要るのは、現May経路の同じ作用でのtop operationを直接計算する工程である。
その仕事の費用はM14の比較から消さず、残り約10,100〜18,400行（保守的には10,700〜18,950行）として示す。

理由は、(1) Mayの演算・局所化・零次・離散までが既に出来ている、
(2) 残りの型は鎖・切断の有限計算と指定されたBE比較であり、
(3) coherentへ戻す場合はnative norm/Tate・exactな延長・右k作用eという
別々の未供給の束が依然として残るため。
ただし二案の見込みの幅は重なっており、行数の下界やMayが必ず短いという証明ではない。
coherent出力を今後の∞基盤にも優先して供給する方針なら、その再利用価値を理由に後者を選ぶ判断はあり得る。

coherentへ戻す場合の判断は、残り12,300〜22,100行の元工程と、
BS用の未積算比較を含めた13,300〜24,500行の暫定見込み、界面を再び強くする範囲・分担をセットで行う。
現ho値の界面のまま内部だけcoherentな実例を作る案も可能であり、界面変更は必須ではない。
いずれも自己判断では採用しない。

**本比較を報告して判断を待つ。5a-5aの独立段の新設・Leanの再開・界面の変更はしない。**
待ちの間はM15の段0の紙だけを進める。

## 111. 判断待ちのM15段0：極限保存と一般R加群の境界（紙のみ、11-13）

§110で再確認したU:CAlg_A→D(A)の全∞随伴と極限保存は完成済みである。
ただし、これは§95・§97・§107の一般R加群の模型の不足をそのまま解消するものではない。

- 固定したAと、変わるE∞頂点Rを区別する。必要なMod_Rの台の忘却は、
  上のCAlg_Aの忘却とは始域が違う。
- §107のdgAlgebraExtensionInfinityと準同型不変性は、厳密BE→同じ台のdg代数という
  忘却が出来た後の固定模型で再利用する。全Rと全辺への降下・restrictionの右随伴は引き続き必要。
- CAlgでAmitsur図式のnative極限錐を作ってUで送れても、M15の指定R加群の単位、
  R→Sのfiber、相対テンソルの反復と指数射の同定は別である。
  D(A)のテンソルをMod_Rの相対テンソルに読み替えない。
- coherentなP⁰に必要な「スペクトル的な右k作用e」は、固定した係数kでの構成。
  それを作るだけで一般のE∞底R上のmodule族・対称相対テンソルを得たとは数えない。
  逆方向にも、既存のk線形dg双加群だけで一般の非k線形P⁰を得たとはしない。

担当を決める際の最初の受け渡しは、§107.3の五点（同じ台の厳密忘却、拡大・制限の全関手と随伴、
弱同値・nativeの辺と合成への降下、相対テンソルと底変換、指定単位とfiber・指数射）を維持する。
一般Rの模型の2,500〜4,500行は暫定のままで、今回の紙の比較から新しい実装の担当や上限を決めない。

本節を含め、最新指示後の作業は報告書のみ。Lean編集・ビルド・監査・追加コミットなし。
§110の二案の判断を待ち、未検証の下書きは作業木に保持する。

## 112. M14再開：残り全体の型一覧（11-13、実装前の紙）

### 112.1 採用範囲と停止規則

§110に対する最新のユーザー承認でMay案を続ける。
一般次元のBF作用は**独立段5a-5aではなく、M14の_totの直接計算の部品**とする。
§108のL01〜L28の数学の型を、このM14の前半の一覧として引き継ぐ。
§108の独立段という呼称・25,400行の枠は採用しない。
外枠は**M14全体25,000行（完成したMay4,128行を含む）**、12,500行で途中報告して続行する。

証明の分割は数えず型を記録。前提計算は一覧のLごとに3本、照合は全体3本。
L05の既存構成の自然性・次数移送の前提計算は§108.6の三本で3/3。
I01（IntervalCutsとの一致）は予約済み・未使用、I02・I03も未使用。
それ以外の新しい数学は、検証済みを保存して型と漏れた理由を報告し停止する。
凍結確定の連絡後はコミットしない。今回まだ確定連絡を受けていない。

最初は未検証185行を修正して検証する。個別ビルド済み568行は専用監査後にコミットする。
以下の紙の一覧を載せた後、承認待ちを挟まずこの順に進める。
G10・③-bのnative錐や一般の実現の橋は作らず、受け渡し後の指定比較を適用する。
5a-5・3b-4に一般BF作用を前提として追加しない。

### 112.2 L01〜L28の補充：境界と合成の有限項の対応

L01〜L28の全型は§108.3・§108.4、証明分割は§108.6に固定したもの。
L09に対して§109で止めた追加候補を、今回の**実装前の全一覧**にL09aとして含める。
BoundaryBalanceIndexとboundaryBalanceTermの型・零次数と退化項の規約も§109のとおり。

```lean
-- L09a：テンソルの面／係数の文字削除／入力の面の符号付き項を対にする。
boundaryBalance_pairing (u : Surjection.BasisWord (r+1) d) (q : ℕ) :
  ∃ τ : Equiv.Perm (BoundaryBalanceIndex u q), Function.Involutive τ ∧
    (∀ j, τ j = j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      boundaryBalanceTerm A S u q j x = 0) ∧
    (∀ j, τ j ≠ j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      boundaryBalanceTerm A S u q (τ j) x = -boundaryBalanceTerm A S u q j x)
```

L12の部分合成についても、有限和の等式だけで添字の対応を省かない。
`CompositeBalanceIndex u v i q`は、既存OverlapPartitionによる係数合成と一段切断の項と、
外側の切断のi色の出力を内側で切る二段切断の項の直和。
`compositeBalanceTerm`は第一群を正、第二群を負とする、同じ実テンソルでの符号付き値。
正規化で消える合成語・面は零の項として保持する。新規の型は次。

```lean
-- L12a：二段切断の項の対応。nullaryも含む。
compositeBalance_pairing (u : Surjection.BasisWord (m+1) d)
    (v : Surjection.BasisWord n e) (i : Fin (m+1)) (q : ℕ) :
  ∃ τ : Equiv.Perm (CompositeBalanceIndex u v i q), Function.Involutive τ ∧
    (∀ j, τ j = j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      compositeBalanceTerm A S u v i q j x = 0) ∧
    (∀ j, τ j ≠ j → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
      compositeBalanceTerm A S u v i q (τ j) x = -compositeBalanceTerm A S u v i q j x)
```

上の二つは、既存の符号規約を変えず、各値に現れる面写像の合成とKoszul符号を比較する主張。
L09a→L09→L10、L12a→L12→L14・L16の順に使う。
L11の置換、L13の単位、L14のnullary、L15の自然性、L18のTR制限、
L19〜L28の正規化・convolution等化子・台の指定比較は元の一覧どおり残る。

### 112.3 L29〜L37：同じ係数のtop operationを直接計算する

以下も**紙の新規名・型案（未型検査）**。κ := EInfinityPrimeField.{u} p、
ν p n := ULift.up (mayNu p n : ZMod p)。r>0のBF作用と同じχ・TRを使う。
`bfTopScalar p q e : κ`は、eをTRの実基底係数で展開した切断和のtop degreeのスカラー。
切断符号に加え、L28の**実際の**convolution評価・テンソルの交換・指定次数移送の符号を含める。
νの逆数となるようにこのスカラーを定義しない。
`coefficientOf f s`は、Wの自由生成元e_sにfを適用して実BE係数へ運んだ値。

```lean
-- L29：増大を保つ同変比較の変更が、同じD_iのホモロジー類を変えない。
mayDClass_comparison (f g : (mayResolution p κ).complex ⟶ (mayArityResolution p κ).complex)
    (hf : f ≫ (mayArityResolution p κ).π = (mayResolution p κ).π)
    (hg : g ≫ (mayArityResolution p κ).π = (mayResolution p κ).π)
    (X : (operad κ).Algebra) (i : ℕ) (j : ℤ) (a : MayClosed X.carrier j) :
  mayDClassWith f X i j a = mayDClassWith g X i j a

-- L30：計算可能な標準の周期bar比較。Wと同じ右回転生成元・増大を使う。
canonicalCyclicComparison : (mayResolution p κ).complex ⟶ (mayArityResolution p κ).complex
canonicalCyclicComparison_augmentation :
  canonicalCyclicComparison p ≫ (mayArityResolution p κ).π = (mayResolution p κ).π
canonicalCyclicComparison_even (s : ℕ) :
  coefficientOf (canonicalCyclicComparison p) (2*s) = canonicalEvenBarSum p s
canonicalCyclicComparison_odd (s : ℕ) :
  coefficientOf (canonicalCyclicComparison p) (2*s+1) = canonicalOddBarSum p s

-- L31：非退化top切断の各色は全q単体。§106の積の計算を実作用へ運ぶ。
bfAction_top_value (X : CosimplicialRingAlgebra κ) (q : ℕ)
    (e : (operad κ).arity p |>.X (-((q*(p-1):ℕ):ℤ)))
    (a : normalizedComponent X q) :
  bfRepeatedActionValue X q e a = bfTopScalar p q e • frobeniusNormalizedValue X q a

-- L32：標準bar和のtop係数。全符号を含む零次・一次・帰納式。
canonicalTop_zero : bfTopScalar p 0 (coefficientOf (canonicalCyclicComparison p) 0) = 1
canonicalTop_one :
  bfTopScalar p 1 (coefficientOf (canonicalCyclicComparison p) (p-1)) =
    (-1 : κ)^((p-1)/2) * (((p-1)/2).factorial : κ)
canonicalTop_succ (q : ℕ) :
  bfTopScalar p (q+1) (coefficientOf (canonicalCyclicComparison p) ((q+1)*(p-1))) =
    (-1 : κ)^((q+1)*((p-1)/2)) * (((p-1)/2).factorial : κ) *
      bfTopScalar p q (coefficientOf (canonicalCyclicComparison p) (q*(p-1)))

-- L33：巡回bar和で寄与する隣接対の列挙と符号の集計。
-- SignedTopBarIndexはL32の実有限和の非零添字。signedTopBarWeightはその実係数。
canonicalTop_pair_count (q : ℕ) :
  ∑ b : SignedTopBarIndex p q, signedTopBarWeight p q b =
    (-1 : κ)^(q*(q+1)*((p-1)/2)/2) * (((p-1)/2).factorial : κ)^q

-- L34：逆冪で定義したMayのνとの一致。p=2を含む。
canonicalTop_normalized (q : ℕ) :
  ν p (-(q:ℤ)) *
    bfTopScalar p q (coefficientOf (canonicalCyclicComparison p) (q*(p-1))) = 1

-- L35：同じ正規化した閉元のp乗。codegeneracyと微分を保つ。
frobeniusNormalized_mem (X : CosimplicialRingAlgebra κ) (q : ℕ)
    (a : normalizedComponent X q) : (a.val^p) ∈ normalizedComponent X q
frobeniusNormalized_closed (X : CosimplicialRingAlgebra κ) (q : ℕ)
    (a : MayClosed ((bfNormalizedAlgebra κ).obj X).carrier (q:ℤ)) :
  MayClosed ((bfNormalizedAlgebra κ).obj X).carrier (q:ℤ)

-- L36：全整数nの同じMay演算とlevelwise Frobeniusの実ホモロジーでの一致。
bfMayTopValue (X : CosimplicialRingAlgebra κ) (f : X ⟶ X)
    (hf : ∀ j a, (f.app j).right.hom a = a^p) (n : ℤ)
    (a : MayClosed ((bfNormalizedAlgebra κ).obj X).carrier (-n)) :
  mayNormalizedClass p ((bfNormalizedAlgebra κ).obj X) n ν p n a =
    mayClosedClass _ (-n) (mayClosedMap ((bfNormalizedAlgebra κ).map f).hom (-n) a)

-- L37：標準単体の同じ余代数によるconvolutionはBE代数の右frame。
bfSimplexConvolutionFrame (B : (operad κ).Algebra) :
  SimplexCategory ⥤ (operad κ).Algebraᵒᵖ
bfSimplexConvolutionFrame_obj (B : (operad κ).Algebra) (q : ℕ) :
  ((bfSimplexConvolutionFrame B).obj ⦋q⦌).unop =
    convolutionAlgebra (hopf κ) (simplexBECoalgebra κ q) B
```

canonicalEvenBarSum / OddBarSum は、Wの周期微分T・Nに対し、BEの実bar収縮で
自由生成元の像を再帰的に持ち上げた、同じ置換列の有限和。
偶数では巡回群の元で添字づける各二列の和、奇数では同じ巡回生成元の追加を含む。
L30で実置換列の式を検証し、L33でその寄与と符号を計算してL32へ渡す。
計算中に生成元の逆や係数の符号を公開定義の変更で吸収しない。
L35のclosedは定義の型だけで終わらせず、L26の指定比較でa↦a^pを読む生成元公式も供給する。
L37はframeのmatching射のfibration・各単体の収縮・augmentationを含める。
G10の一般native比較をL37の仮定に入れて作ったことにはしない。

### 112.4 L38〜L44：指定native Tot・filtered塔・A4の二重模型

ここで`nativeTot`とそのcone、実現の全関手と指定比較は③-bの供給物を使う。
以下の型のG10/3b-4の引数は**外部の受け渡しに含まれる証明**であり、
このレーンで新しい同名の構造を作って仮定を隠すものではない。
正式な受け渡しの公開名に合わせる際は、数学の範囲を変えず名前を追従する。

```lean
-- L38：同じBF模型が持つnative錐。標準単体の同じframeで高次成分を作る。
bfCosimplicialCone (X : CosimplicialRingAlgebra κ) :
  JoinCone (cosimplicialNerve X ≫ discreteCAlgUnderEmbedding κ)
bfCosimplicialCone_vertex (X) :
  (bfCosimplicialCone X).vertex =
    atVertex (nerveMap (bfNormalizedAlgebra κ) ≫ algebraCAlgSource κ) (nerveVertex X)

-- L39：G10とnative側の同じ錐の全関手比較を適用する。
bfToNativeTotIso (G10 : SpecifiedG10Comparison κ) (BE : SpecifiedNativeBETotComparison κ) :
  FunctorIso (nerveMap (bfNormalizedAlgebra κ) ≫ algebraCAlgSource κ) (nativeOfCosimplicial κ)
bfToNativeTotIso_frobenius (G10) (BE) (X) (f : X ⟶ X) :
  (bfToNativeTotIso G10 BE).hom.app (nerveVertex X) ≫ nativeTotMap X f =
    bfNativeMap X f ≫ (bfToNativeTotIso G10 BE).hom.app (nerveVertex X)

-- L40：現界面の_tot。指定された同じFrobenius辺で、全整数次数。
barrattEcclesPowerOp0_tot (G10) (BE)
    (X : CosimplicialRingAlgebra κ) (f : X ⟶ X)
    (hf : ∀ j a, (f.app j).right.hom a = a^p) (n : ℤ) :
  (barrattEcclesPowerOp0 p n).app (mk (nativeTotVertex X)) =
    (homotopyGroupsOnHo κ (cAlgForgetDerived κ) n).map
      (homMk (nativeTotFrobeniusEdge X f))

-- L41：filtered群の余極限における自然な演算の一意性。
filteredOperation_desc {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ AddCommGrpCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (P Q : c.pt ⟶ c.pt)
    (h : ∀ i, c.ι.app i ≫ P = c.ι.app i ≫ Q) : P = Q

-- L42：同じFrobenius塔のshiftとP⁰。Πの指定余極限保存を入力として明記。
frobeniusTower_powerOp (D : ℕ ⥤ hoCAlg κ) (f : D ⟶ D)
    (c : Cocone D) (hc : IsColimit c) (n : ℤ)
    (hπ : IsColimit ((Π κ n).mapCocone c))
    (hP : ∀ i, (powerOp0 p n).app (D.obj i) = (Π κ n).map (f.app i)) :
  (powerOp0 p n).app c.pt = (Π κ n).map (colimitEndomorphism c hc f)

-- L43：単体的余単体的可換Fp代数の同じ厳密二重模型でのMay差の境界。
-- doubleRealizationModelはBFの各列の作用と、外側の実際のshuffleを使う模型。
-- F_Xはlevelwise Frobeniusから来る同じ複体射。Hは閉元ごとの明示的な原始元。
doubleMayDifferencePrimitive (X : SimplicialObject (CosimplicialRingAlgebra κ))
    (n : ℤ) (a : MayClosed (doubleRealizationModel X).carrier (-n)) :
  ∃ H : (doubleRealizationModel X).carrier.X (-n-1),
    (doubleRealizationModel X).carrier.d (-n-1) (-n) H =
      mayNormalizedValue p (doubleRealizationModel X) n ν p n a - (F_X.f (-n) a.val)

-- L44：③-bの指定実現の橋を適用したA4-localな全整数次数の比較。
a4_realization_powerOp (G10) (BERealization : SpecifiedBERealizationComparison κ)
    (X : SimplicialObject (CosimplicialRingAlgebra κ)) (n : ℤ) :
  (powerOp0 p n).app (mk (nativeDoubleRealizationVertex X)) =
    (Π κ n).map (homMk (nativeDoubleFrobeniusEdge X))
```

L39のappは紙の記法。実際は既存FunctorIsoの辺・自然性と指定join錐の脚を用いる。
L38〜L40はG10の後。そこに到達したら区切って報告し、外部の橋は作らずM15の紙へ移る。
L41は通常圏の群の余極限の普遍性。L42でΠがfiltered余極限を保つこと自体は、
界面の保存の欄／別工程の忘却のsifted保存と既存のホモロジー比較から受け取る。
その依存を供給せずに、BE実例の全filtered保存までM14で完成したとは報告しない。

L43では単にΠをlevelwiseに取って実現の余極限へ交換しない。
指定のshuffle・係数の微分・全複体のKoszul符号で差の原始元を作る。
必要な数学を次の二つとして一覧に含める。

```lean
-- L43a：同じshuffle実現に沿うBE作用の、全係数・全射での比較。
doubleRealization_action (X) (r : ℕ) :
  realizationAction X r = doubleShuffleAction X r

-- L43b：L43の原始元の明示的有限展開の微分。
-- finiteMayPrimitiveは同じW係数・BF切断・外側のshuffleから定義し、
-- 入力の閉条件で消える項も、係数微分とともに保持する。
finiteMayPrimitive_d (X) (n : ℤ)
    (a : MayClosed (doubleRealizationModel X).carrier (-n)) :
  (doubleRealizationModel X).carrier.d (-n-1) (-n) (finiteMayPrimitive X n a) =
    mayNormalizedValue p (doubleRealizationModel X) n ν p n a - F_X.f (-n) a.val
```

同じ実現模型・指定射・底の全複体との比較は、③-bの正式な受け渡しに照らして適用する。
その前段に新しい一般の厳密化やnative錐の定理を作らない。
この一覧にない新しい数学が要ると分かった時点で、その型と漏れた理由を報告する。

### 112.5 証明順・照合の枠

修正・監査→L01〜L08→L09a,L09,L10→L11〜L18（L12aを先に）→I01→L19〜L28→
L29〜L36→L37,L38→G10/3b-4受け取り後にL39,L40→L41,L42→L43a,L43b,L43,L44。
L32とL33は組合せの和を先に計算して規格化へ運ぶ。
新しい独立段の取り込み点は設けず、M14の途中の検証済み分として保存する。

I01以外のI02・I03は未使用。比較の定義の表現差だけなら型を記録してこの枠で処理する。
比較そのものが新しい数学なら、照合の名で継続しない。
以上を残り全体の開始時の型一覧とする。承認待ちを挟まず、まず568行の監査と185行の修正へ進む。

### 112.6 最初の568行の監査と保存

/tmp/bsw16/audit-m14-cuts-first.log：**11モジュール・101宣言、標準三公理のみ**で成功。
568行を保存する。対象はEInfinity/SimplexCuts/の次の11本。
Outputs、Faces、HomogeneousTensor、NormalizedGenerators、CutTensor、TensorNaturality、
CutNaturality、Signs、SignedTerms、SignedNaturality、CollapsedFace。
いずれも個別対象ビルドに通った版から数学の変更なし。sorry・追加公理なし。

以前のExpanded・Balanced・TopTermの162行と合わせ、切断の検証済み部分は730行。
May4,128行を足した本経路の現在の基礎実測は4,858行。
RawAction・DegenerateInput・Normalizationの修正中の分は、ここに含めない。
新規ファイルのdocstringに残る5a-5a L番号は§108の旧一覧の参照であり、
今後はM14のL番号として読む。独立段を作ったという意味にはしない。

全体の入口登録・rootビルド・全体監査は行っていない。
本コミットは枝の中間保存で、独立した5a-5aの完成／取り込み点ではない。
監査の鍵は返却済み。未検証三本の修正版は別の一回の対象ビルドで検証中。

### 112.7 三本の修正完了・監査と夜の運用

RawAction・DegenerateInput・Normalizationの修正版は **208行**。
/tmp/bsw16/m14-normalization-05.log：三本すべてを含む対象ビルド成功。
最後の三本に新しい警告なし。語長の等式を明示的に移送し、
自由加群の拡張を既存freeDescで作り、現行Type圏の束ねた射を指定して評価した。
退化入力の消滅とMoore正規化への降下、同じ係数と生成元での値は型を変えていない。

/tmp/bsw16/audit-m14-normalization.log：**3モジュール・44宣言、標準三公理のみ**で成功。
sorry・追加公理なし。検証済み三本を枝へ保存する。
May4,128行と切断の検証済み938行を合わせ、本経路の基礎実測は **5,066行**。
L09aのBoundaryIndexの新しい下書きはこの検証済み数とコミットに含めない。

23時の最新連絡で、B3の凍結はmainのみとなった。各枝の編集・コミットは続行してよい。
それ以前の「確定後は枝へコミットしない」は今回は適用しない。
本レーンは対象ビルドと小さい専用監査だけを、一回ごとに鍵を取って実行している。
mainへの取り込み・B4の追従は調整役からの連絡を待つ。

### 112.8 L09aの前提計算1：既存の正規化生成元の微分

既存AlexanderWhitney.generator_dを同じembeddingDownNatへ運ぶ法則を用いる。
新しい境界の分類ではなく、既存の複体射・指定係数移送の法則としてL09aの前提計算**1/3**。
内部のchains_d_negはこの同じ移送の証明分割とする。

```lean
gen_d (A : Type u) [CommRing A] (S : SSet.{0}) (q : ℕ) (x : S _⦋q+1⦌) :
  (chains A S).d (-((q+1:ℕ):ℤ)) (-(q:ℤ)) (gen A S (q+1) x) =
    ∑ i : Fin (q+2), (-1:ℤ)^i.val • gen A S q (S.δ i x)
```

§112.7の三本は **bea1aab1b** に保存済み。次はL09aの有限添字とこの指定微分の計算。

### 112.9 L09aの前提計算2：一つの出力次数を下げる移送

既存の有限和のupdateの式による次数計算を、L09aの前提計算**2/3**として記録する。

```lean
degreeSum_delete (d : Fin n → ℕ) (i : Fin n) (h : 0 < d i) :
  degreeSum n (Function.update d i (d i-1)) + 1 = degreeSum n d
```

これは切断の新しい分類ではなく、境界項を同じ全次数成分へ送るための移送の法則。

