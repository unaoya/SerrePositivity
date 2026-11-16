# SC-W1 G4：核の全複体から元の増大複体への残りの比較

2026-11-16。現在の同じ核の短完全列と条件付きのF8の消去は対象ビルド・81宣言の所有監査済み。以下は**残りの紙の筋で、これらの比較の実装・検証は未完**。外枠20,000行で同じ型・範囲を進める。

## 現在の入力と必要な出力

`DegreeOneProjectiveModel.perfectCechTupleSquareLeftKernelTotal_acyclic_of_right` は、同じ中心側のRightKernelのtotalの完全性を仮定して、同じY側のLeftKernelのtotalの完全性へ戻す条件付きの結果。RightKernelの仮定を追加した一般のproper降下や最終定理は作らない。

元の `schemePerfectCechTupleDouble g U p hp hR` は外水平零次に基底のsingle、後続水平次数n+1に元のC_nを持つ。各次数の係数・実際の射・増大はそのまま使う。対象を同型の別のHの計算へ置き換えるだけでは足りない。

## 左右の核の配置と符号（紙の計算）

各成分の核を標準同型で取れば、LeftKernelは元のRが(0,0)、C_n^bが(n,b+1)の配置に比較する。元の増大二重ČechのC_n^bは(n+1,b)に置かれる。同じtotal次数での再索引を各直和入射について構成する。C側の内部微分の負符号とtotalの符号の積は、`(-1)^n * (-1) = (-1)^(n+1)`で、元の増大二重複体の縦微分の符号と一致する。根のRの増大の辺も同じ写像で照合する。

RightKernelは中心Sが(0,1)、E_n^bが(n,b+2)の配置に比較する。元の中心側の増大totalより全次数が1上がる。自然数添字で「零次を零、後続次数を元の複体、後続微分を元の微分」とする**符号を変えない次数のずらし**と比較する案なら、E_n^bの成分に`(-1)^b`、中心Sに`-1`を掛ける。これが内部微分と中心の`-center`を元の増大へ戻す。Mathlibの整数添字の符号付きshiftと同じものと仮定しない。ずらした複体の完全性も元の各次数の完全性から照合する。新しい次数のずらしの定義を作らず、Mathlibの `ComplexShape.embeddingUp'Add (1 : ℕ) 1` に沿う `HomologicalComplex.extend` を使える。この埋め込みはup ℕからup ℕへのn↦n+1で、`extend_exactAt_iff` は後続次数、`extend_exactAt` は像にない零次の完全性を供給する。整数添字のsigned shiftとの混同を避けられるが、RightKernelのtotalからこのextendへの同型と符号の照合はなお未実装。

この段落は配置と符号の紙の照合であり、標準同型・直和の射・微分との可換性の証明は残る。

## 核とtotalの標準比較を使う案

元のtotalの短完全性 `cechIntegerLiftTotal_shortExact` は供給済み。同じtotalFunctorの加法性を各ιTotalで照合し、Mathlibの `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` に同じ短完全性を渡した核保存まで実装済み（dfa0a19c2）。`cechIntegerLiftTotalKernelIso` と包含を保つ `cechIntegerLiftTotalKernelIso_hom_ι` は、元の同じkernelのtotalを比較する。元の増大複体からの射・逆射の構成はなお残る。

これにより元のkernelのtotalと、同じtotalの射のkernelを `PreservesKernel.iso` で比較できる。元の増大totalからY側の全F8図式のtotalへの射を各入射で作り、基底の正次数の商への合成が零であることから同じkernelへ持ち上げる案がある。逆向きの射と二つの合成の式を示し、元のkernelを別のものへ無説明に替えない。単位・合成・自然性は元の標準比較を再利用する。

## アフィン環の出口

`affineCechNerveTupleGlobalAugmentation_quasiIso` は、元のアフィンnerveのΓのsingleから元のタプル被覆の複体への、各列の準同型を供給する。この射の正の縦次数の成分は零加群からの射で、一般には全射ではない。既存の全成分全射を仮定する列のtotal判定へ、そのまま代入しない。

この射の各成分のmonoは `affineCechNerveTupleGlobalAugmentation_mono_f` で実装済み。既存のcokernelの短完全列、各列のcokernelの完全性、同じtotalの短完全性を使う `cechIntegerLiftTotal_quasiIso_of_mono_columns` へ代入し、`affineCechNerveTupleGlobalTotal_quasiIso` を得た。全射の場合の対角線の消去の証明は作り直していない。これはまだ増大項を除く実際のΓ図式の比較である。Γ–Specと元の環のconerveの自然同型、同じ増大の因子分解を使い、基底環の増大を含めて元のアフィン環の全正次数まで含むAugmentedRingCechExactへ戻す接続は残る。

## 相対proper fppf・Noether帰納の接続

Spec R上の平坦全射の元の二重Čechのtotalの完全性は供給済み。Lemma 2.6の中間のblowup上のproper fppfは非アフィン基底の場合を含むので、相対の接続も要る。元の有限アフィン交叉での平坦な環の完全性と共通アフィン細分・B1の同じ判定を使い、実際の底変換の射と合成の消去へ渡す。非アフィン基底のΓの平坦性に置き換えない。

帰納では、元の閉像を小さくするNoether帰納の仮定を、中心上の全てのNoetherなアフィン基底変更へ渡す。底変換後のアフィンT自身の次元が下がるとは仮定しない。2dの実際のblowup rとその底変換の射影表示、中心外の同型、G3の閉中心・nilimmersionの部品を保持する。アフィン交叉のFrobenius係数のnil不変性も、元の全ての射に自然に供給する。

## G5と最終型

G2の実際の被覆模型と `coefficientVCoverModelCechComparison`、既存のFrobeniusの環の射とconerveの自然性、B1のfiltered完全性を使う。二つのfilteredな余極限との自然な比較を結び、元のv被覆の同じ増大環図式の完全性を、Noether性・模型の存在を追加仮定にせず結論する。G4の不足を2hのH03へ移さない。

一覧：済み1／全体3（うち追加0）。
