# SC-W1 G4：核の全複体から元の増大複体への残りの比較

2026-11-16。現在の同じ核の短完全列と条件付きのF8の消去は対象ビルド・81宣言の所有監査済み。以下は**残りの紙の筋で、これらの比較の実装・検証は未完**。外枠20,000行で同じ型・範囲を進める。

## 現在の入力と必要な出力

`DegreeOneProjectiveModel.perfectCechTupleSquareLeftKernelTotal_acyclic_of_right` は、同じ中心側のRightKernelのtotalの完全性を仮定して、同じY側のLeftKernelのtotalの完全性へ戻す条件付きの結果。RightKernelの仮定を追加した一般のproper降下や最終定理は作らない。

元の `schemePerfectCechTupleDouble g U p hp hR` は外水平零次に基底のsingle、後続水平次数n+1に元のC_nを持つ。各次数の係数・実際の射・増大はそのまま使う。対象を同型の別のHの計算へ置き換えるだけでは足りない。

## 左右の核の配置と符号（紙の計算）

各成分の核を標準同型で取れば、LeftKernelは元のRが(0,0)、C_n^bが(n,b+1)の配置に比較する。元の増大二重ČechのC_n^bは(n+1,b)に置かれる。同じtotal次数での再索引を各直和入射について構成する。C側の内部微分の負符号とtotalの符号の積は、`(-1)^n * (-1) = (-1)^(n+1)`で、元の増大二重複体の縦微分の符号と一致する。根のRの増大の辺も同じ写像で照合する。

RightKernelは中心Sが(0,1)、E_n^bが(n,b+2)の配置に比較する。元の中心側の増大totalより全次数が1上がる。自然数添字で「零次を零、後続次数を元の複体、後続微分を元の微分」とする**符号を変えない次数のずらし**と比較する案なら、E_n^bの成分に`(-1)^b`、中心Sに`-1`を掛ける。これが内部微分と中心の`-center`を元の増大へ戻す。Mathlibの整数添字の符号付きshiftと同じものと仮定しない。ずらした複体の完全性も元の各次数の完全性から照合する。新しい次数のずらしの定義を作らず、Mathlibの `ComplexShape.embeddingUp'Add (1 : ℕ) 1` に沿う `HomologicalComplex.extend` を使える。この埋め込みはup ℕからup ℕへのn↦n+1で、`extend_exactAt_iff` は後続次数、`extend_exactAt` は像にない零次の完全性を供給する。整数添字のsigned shiftとの混同を避けられるが、RightKernelのtotalからこのextendへの同型と符号の照合はなお未実装。

この段落は配置と符号の紙の照合であり、標準同型・直和の射・微分との可換性の証明は残る。

左右の座標の法則と、Y側の同じ各ιTotalによる次数ごとの再索引、その次数ごとの左逆は `CechAugmentedSquareLeftComponents`・`CechAugmentedSquareRightComponents`・`SchemePerfectCechTupleLeftTotalComponents`・`SchemePerfectCechTupleLeftTotalRetraction` で検証済みになった。前向きの比較の水平自然性と根の基底の交代和零も同じ下書きの検証を通した。ただしσの鎖写像性、基底射影への合成零と分裂の第二式、元の同じ核との同型はまだ残る。

中心側では同じ左側の比較を複製する前に、実際のfとその恒等矢印・逆像被覆を左側の比較へ代入して再利用する。各頂点の右側の複体は、その中心の同じ左側の複体のunsignedな縦方向の一段のextendと、既存のrightEι/rightCenterιとleftCπで比較する。中心は-1、Eのb次は(-1)^bの符号を付ける。元の基底射影にも同じ符号の比較を入れて可換性を保ち、元のkernelを比較する。縦方向のextendのtotalをunsignedなtotalのextendと照合すれば、左側の既存の再索引を使い直せる。これは残りの実装案であり、この比較も検証済みとは数えない。

## 核とtotalの標準比較を使う案

元のtotalの短完全性 `cechIntegerLiftTotal_shortExact` は供給済み。同じtotalFunctorの加法性を各ιTotalで照合し、Mathlibの `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` に同じ短完全性を渡した核保存まで実装済み（dfa0a19c2）。`cechIntegerLiftTotalKernelIso` と包含を保つ `cechIntegerLiftTotalKernelIso_hom_ι` は、元の同じkernelのtotalを比較する。元の増大複体からの射・逆射の構成はなお残る。

これにより元のkernelのtotalと、同じtotalの射のkernelを `PreservesKernel.iso` で比較できる。元の増大totalからY側の全F8図式のtotalへの射を各入射で作り、基底の正次数の商への合成が零であることから同じkernelへ持ち上げる案がある。逆向きの射と二つの合成の式を示し、元のkernelを別のものへ無説明に替えない。単位・合成・自然性は元の標準比較を再利用する。

## 同じ核の比較で照合する分裂の式（検証待ちの紙）

比較射σの複体の射としての可換性を示した後、逆射を最初から複体の射として証明する代わりに、各全次数で同じ直和の二つの補助射を使える。Kは元の増大total、Lは元のY側の正の図式のtotal、P:L→Qは元のpositiveBaseLeftProjectionのtotalそのものとする。σの各脚は下書き `SchemePerfectCechTupleLeftTotalComponents` のとおり。

次数ごとのψ:Lⁿ→Kⁿは、Lの(a,b+1)のCの座標をKの(a+1,b)へ戻し、Lの(0,0)のRだけを根へ戻し、(a+1,0)の余分なRを零へ送る。r:Qⁿ→Lⁿは正の外次数の零次のRの座標を同じLの(a+1,0)へ入れ、他の零の座標を零へ送る。ここでψとrを複体の射とは仮定しない。各元のιTotalで

- σⁿ ≫ ψⁿ = 𝟙 Kⁿ、
- ψⁿ ≫ σⁿ + P.f n ≫ rⁿ = 𝟙 Lⁿ、
- σ ≫ P = 0

を照合すれば、各次数の短完全性が従う。Mathlibの既存の `ShortComplex.Splitting` がこの三つの式をそのまま受け取るため、`Splitting.shortExact` と既存の次数ごとの判定へ代入する。実際P(x)=0なら第二式でx=σ(ψ(x))、第一式でσは単射である。Pの全射性は元の既存の成分全射性・totalの短完全性から取る。この方法なら新しい無限和の消去は不要で、ψの鎖写像性を別に仮定する必要もない。

この短完全性から同じσがPのkernelであることを取り、元のkernelの普遍性と `cechIntegerLiftTotalKernelIso` で、**元の同じLeftKernelのtotal**との同型と包含の式へ戻す。Qの既存の完全性だけを用いて別の対象の完全性を仮定する置き換えはしない。中心側も元のRightKernelとその元のPを保ち、unsignedな一段のextend、Eの(-1)^b、中心の-1を入れた同じ分裂の式を使う。この節は補助射と三つの式をまだ形式化していない紙の計画である。

## 比較射σの微分との可換性の照合順（下書き検証待ち）

`SchemePerfectCechTupleLeftTotalComponents` の下書きでは、同じ各直和入射からのσの式に加え、水平方向の座標の自然性を各余面の交代和へ渡す式と、基底の外零次の水平微分が零になる式を置いた。以下はその式を使う鎖写像性の証明順であり、まだ形式検証済みとはしない。

元のKの(a,b)から前合成し、既存のtotal_d_summandで横微分と縦微分に分ける。(a,b)=(0,0)ではσは同じsingleObjXSelfからLの(0,0)への入射である。Lの横方向の辺は基底のid二つの差で零、縦方向の辺は元のスカラーとleftCιの合成である。これはKの根から(a,b)=(1,0)への元の増大と一致する。a=0,b>0の出発項は元のsingleの零項なので、二つの射の一致はその零性から取る。

残りの出発項は(a+1,b)で、Lの(a,b+1)へ写る。横方向は同じa番目の余面の交代和で、各余面のleftCι_naturalityを同じ和へ渡す。縦方向はleftCι_dの負符号とLのtotalの符号(-1)^aの積が、Kのtotalの符号(-1)^(a+1)に一致する。したがってこの場合も二つの辺の和が一致する。各補題の型を確定し、元のιTotalの式へ代入してからtotal.hom_extで全体の式を取る。正次数で全射でない元の増大を全射と仮定したり、微分の可換性を追加の仮定にしたりしない。

検証再開順：現在生存する同じ共有鍵待ちのセッション63342の左座標の結果を受け取り、必要な修正後に左右座標と再索引・水平自然性をまとめたmodule形式の下書きを検証する。通った同じバイトだけを本体へ移し、対象と直接importerの入口の小ビルド、別の共有鍵で所有宣言の小監査を行う。鎖写像性の照合はその後であり、未検証の下書きを完成した同型と数えない。

## 必要な完全性を元の短完全列で移す経路（下書き、未検証）

同じσの短完全列K.total→L.total→Q.totalができれば、元のQ.totalは既存の定数の正次数の列なので完全である。これよりK.totalとL.totalの完全性は既存のacyclic_X₁/acyclic_X₂で同値になる。一方、元のPPそのもののkernelSequenceをtotalへ渡す短完全列は、元の同じLeftKernel.total→L.total→Q.totalである。同じ判定から元のLeftKernel.totalとK.totalの完全性を同値にできる。これがF8の出口に必要な型である。

中心側も、中心自身の恒等矢印を同じ左側の比較へ代入し、中心の元の増大totalの完全性からその同じ左側の全totalの完全性へ渡す。その左側の全totalのunsignedな一段のextendと、元の右側の全totalを、元のC/Eの座標と中心の-1・Eの(-1)^bで直接比較する。元の右側の射影のkernelSequenceと同じ正次数の基底列から、元のRightKernel.totalの完全性を得る。F8が返す元のLeftKernel.totalへ上の同値を使えば元の増大totalに戻る。この方法では元のPPとkernelを保ち、完全性の結論を既存の短完全列のAPIで渡す。補助のkernel同型や一般のtotalとextendの交換のAPIは、この完全性の移送に先立つ必須の仮定とはしない。右側の全totalの直接比較を含め、完成したとはまだ数えない。

## アフィン環の出口

`affineCechNerveTupleGlobalAugmentation_quasiIso` は、元のアフィンnerveのΓのsingleから元のタプル被覆の複体への、各列の準同型を供給する。この射の正の縦次数の成分は零加群からの射で、一般には全射ではない。既存の全成分全射を仮定する列のtotal判定へ、そのまま代入しない。

この射の各成分のmonoは `affineCechNerveTupleGlobalAugmentation_mono_f` で実装済み。既存のcokernelの短完全列、各列のcokernelの完全性、同じtotalの短完全性を使う `cechIntegerLiftTotal_quasiIso_of_mono_columns` へ代入し、`affineCechNerveTupleGlobalTotal_quasiIso` を得た。全射の場合の対角線の消去の証明は作り直していない。

増大項を含む比較は `schemePerfectCechTupleAugmentedGlobalDoubleMap` で実装済み。元の基底項では恒等射、正次数では同じΓ増大で、`affineCechNerveTupleAugmentedGlobalTotal_quasiIso` が同じtotalの擬同型を供給する。`cechIntegerTotalToRowZeroIso` は零次行だけに台を持つ同じtotalの標準軸射影を同型にし、`cechSingleAugmentedTotalIso` は既存のsingleCompEvalIsoSelfとB1.mapAugmentedCochainIsoで元の増大複体へ戻す。したがって `affineCechNerveTupleAugmentedGlobal_acyclic_iff` によりタプルtotalの完全性と同じΓ増大の完全性が一致する。

元のスカラーR→Γ(Y)の環のconerveへの出口は、`affineScalarPerfectAugmentedIso` と `affineScalarPerfectCech_exact_iff_tuple_total_acyclic` で実装済み。元のAugmentedRingCechExact、基底環の増大、全正次数を保つ。一般の環準同型ρ:R→Sへの最後のΓSpecの係数移送も `SpecScalarPerfectTupleTotal` で実装済み。`specScalarFrobeniusArrowIso` は元のΓSpecIso_inv_naturalityを同じ実際のFrobeniusの矢印へ移し、`specScalarFrobeniusAugmentedIso` は既存の増大conerveの関手へ渡す。`ringFrobeniusCech_exact_iff_spec_tuple_total_acyclic` は元のρの同じ増大環図式のAugmentedRingCechExactと、同じSpec.map ρのタプルtotalの完全性を同値にする。Sの標数条件はρとRの標数条件から内部で供給する。したがってこのアフィン環の出口は閉じたが、F8の核の比較とNoether帰納・G5は依然として残る。

## 相対proper fppf・Noether帰納の接続

Spec R上の平坦全射の元の二重Čechのtotalの完全性は供給済み。Lemma 2.6の中間のblowup上のproper fppfは非アフィン基底の場合を含むので、相対の接続も要る。元の有限アフィン交叉での平坦な環の完全性と共通アフィン細分・B1の同じ判定を使い、実際の底変換の射と合成の消去へ渡す。非アフィン基底のΓの平坦性に置き換えない。

帰納では、元の閉像を小さくするNoether帰納の仮定を、中心上の全てのNoetherなアフィン基底変更へ渡す。底変換後のアフィンT自身の次元が下がるとは仮定しない。2dの実際のblowup rとその底変換の射影表示、中心外の同型、G3の閉中心・nilimmersionの部品を保持する。アフィン交叉のFrobenius係数のnil不変性も、元の全ての射に自然に供給する。

## G5と最終型

G2の実際の被覆模型と `coefficientVCoverModelCechComparison`、既存のFrobeniusの環の射とconerveの自然性、B1のfiltered完全性を使う。二つのfilteredな余極限との自然な比較を結び、元のv被覆の同じ増大環図式の完全性を、Noether性・模型の存在を追加仮定にせず結論する。G4の不足を2hのH03へ移さない。

一覧：済み1／全体3（うち追加0）。

## 2026-11-17深夜：帰納の量化の順序の確認（紙、未実装）

固定したNoether基底Sの閉部分Cについて、C上の固有全射fごとに「全てのNoetherアフィンT→Cで、fのその底変換の元のタプルtotalが完全」という性質を証明する。まずC上のfを固定して2dの被約化・実際のblowup rとproper fppfの細分を選び、それからTへの任意の底変換を扱う。rの中心はCの真の閉部分C'で、rの中心上の射はC'上の固有全射である。したがってIH(C')は、中心のTへの底変換にも同じ射のまま適用できる。Tの次元やT上で新たに選んだ中心の像の次元が下がるとは主張しない。

「C上の全てのTについて、そのT上の任意のv被覆」を先に量化し、Tごとに新しい平坦化中心を選ぶ形では、その中心のCへの像が真に小さいとは限らない。この形の帰納へ置き換えない。G1の一般のfppf–proper細分を最終のv被覆へ使うのは、固定した固有射についてのこの普遍的な底変換後の完全性を閉じてからである。

相対fppfの接続では、中間B=blowup J上の有限アフィン被覆A→Bを使う場合も、Γ(A)⊗_{Γ(B)}Γ(A)をΓ(A×_B A)と無条件で同定しない。Bが分離的でAがアフィンならA×_B Aのアフィン性は対角の閉埋め込みで扱えるが、テンソル積を取る基底はBの各アフィン開に局所化する必要がある。B1の一般の増大二重図式の比較と、元の開被覆・底変換の自然な射を使う。これらの接続はまだ未検証であり、Spec R上のflat totalの定理のみを相対の場合の完成とは数えない。

## 2026-11-17深夜：G5の二つのfiltered余極限の既存材料（紙）

G2の同じ模型図式D=`coefficientVCoverModelSmallArrowDiagram (ZMod p) g`を使う。`coefficientVCoverModelSmallArrow_vCover`、両端のfiniteType/noetherian、`coefficientVCoverModelSmallArrow_finitePresentation`と`coefficientVCoverModelSmallArrow_comp_algebraMap`が各段のNoetherなv被覆と標数を供給する。模型を選び直したり、元の環のNoether性・有限表示性を最終の仮定へ足したりしない。

既存の `frobeniusArrowSmallDiagramMap` は模型の各可換四角形を同じAsSmall ℕの図式の自然変換へ送る。恒等・合成は各nで元の同じ四角形であることから照合し、J→(AsSmall ℕ→Arrow CommRingCat)の実際の二変数図式へまとめる。`frobeniusArrowCocone_map` と `frobeniusArrowSmallColimitIso_naturality` が、それぞれ元の脚と実際のFrobenius順極限の矢印に自然な比較を与える。増大conerveへの比較は `frobeniusAugmentedConerveColimitIso_naturality` を再利用する。

二つの余極限の交換にはMathlib `CategoryTheory.Limits.colimitFlipCompColimIsoColimitCompColim` とその `ι_ι_hom` の式を使えることをソースで確認した。片方を先に取れば模型の実際のArrowのcolimit（`coefficientVCoverModelSmallArrowCoconeIsColimit`）、もう片方を先に取れば各模型の実際のFrobenius矢印のcolimit（`frobeniusArrowSmallIsColimit`）になる。各方向の標準脚を保つことを同じ式で確認してから、元の矢印のFrobenius順極限と同定する。任意のCommRing上に標数を仮定しないFrobenius関手や、別のperfectionの定義を作る必要はない。

各段のG4の結論を `frobeniusAugmentedRingCoefficients_exact_iff` で同じ実際のFrobenius矢印の `IsCechExact` へ移し、B1の `isCechExact_colimit` を模型のfiltered添字に適用する。上の同型と元の増大係数の同じ `exact_iff` で戻す。最終出力は元のv被覆の `AugmentedRingCechExact (frobeniusAugmentedRingCoefficients …)` のままである。これらはG5の予定の法則であり、G4のNoetherな完全性の供給も、二つの余極限の交換のこの図式への実装も、まだ完成・検証済みとは数えない。

## 相対flatの入口で使える既存のアフィン性の法則（2026-11-17、紙）

Mathlib `Morphisms/Separated.lean` の `IsAffineHom.of_comp` は、k:A→B、q:B→Sについて、k≫qがアフィンでqが分離的ならkもアフィンとする。したがってBがSpec R上で分離的で、Aがアフィンなら、A→Bの各アフィン開の逆像もアフィンになる。一般のBのΓに平坦性を仮定する必要はない。

2dのproper fppf g:W→Bのqcな始域に有限アフィン開被覆𝒰を取り、既存の有限直和T=∐𝒰.Xとm=Sigma.desc 𝒰.fを使う。m≫gの平坦性と局所有限表示性は、元のsigmaOpenCoverの各項で𝒰.f i≫gとなることとIsZariskiLocalAtSourceから得られる。全射性は同じ開被覆とgの全射性から得る。Tは有限なアフィンの直和なのでアフィンで、上のof_compを使えばT→Bはアフィンである。この同じTのisoSpecを用いる手順はG1の `exists_affine_finitePresentation_vCover_refinement` と同じ選択で、別の模型を作る必要はない。

この結果、TのB上の相対Čech nerveの正次数は、アフィン射の底変換とTのアフィン性によりアフィンになる。Bの各アフィン開に制限すれば、平坦全射の実際の環写像へのB1の入力が得られる。ただしこれだけでは、B自体が非アフィンな場合のΓのČech列の完全性や、B→Spec Rとの合成の消去を証明したことにはならない。元のBのアフィン被覆との比較と、元の増大二重図式へ渡す自然性が残る。G4の相対proper fppf・合成の束でこれらを照合する。

## Noether帰納の固定基底をアフィンに取る整理（2026-11-17、紙）

G4の必要な出口は、任意のNoether環R上の固有全射と、その任意のNoetherアフィン基底変更についての元の増大totalの完全性である。そこで帰納の固定基底SをSpec Rに取り、P(C)ではSへの閉埋め込みj:Y→Sとrange j=C、その上の固定した固有全射を量化する。Yは閉埋め込みがアフィン射であることからアフィンであり、Γ(Y)のSpecとの実際のisoSpecを使える。被約化後のYと、真に小さい閉中心Zもアフィンである。

このため、任意のT=Spec A→Yを扱う際に、まず非アフィンなYを新たにアフィン開へ分割する必要はない。Y.isoSpec.invを モジュール `BlowupAffineProjectiveModel` の `nonempty_blowupAffinePullbackProjectiveModel` の開埋め込みjへ入れ、元のblowupのΓ(Y)上の次数一表示を得る。T→Yを同じisoSpecでSpec間の射へ戻し、未検証の `DegreeOneProjectiveModel.baseChange` の法則と実際のpullbackの同型を用いる。任意の係数移送のProjのCartesian性は、既存の `isPullback_projectiveCoefficientMap` を使う。逆像イデアルのblowupと任意の底変換を同一視する工程はない。

中心Z→Sの閉像はCの真部分集合で、ZはSの閉部分スキームである。中心のTへの底変換はAのイデアルによる商のSpecとして扱い、IH(C')を同じ元の中心上の固有射とそのアフィン基底変更に適用する。TのKrull次元の減少を仮定しない。この整理はG4で必要な任意のNoetherアフィン基底上の主張を保ち、一般の非アフィン基底の降下を追加の定理として作らないという内部の証明の選択である。中間のblowup B上の相対proper fppfは依然として非アフィン基底を含むので、前節の相対比較の不足は残る。

G5の再利用の補足（2026-11-17）：既存の `FrobeniusArrowMapLaws` を再確認し、`frobeniusArrowSmallDiagramMap_id`・`frobeniusArrowSmallDiagramMap_comp` と、実際の順極限の `frobeniusDirectLimitArrowMap_id`・`frobeniusDirectLimitArrowMap_comp` も既に供給されていることを確認した。模型からの二変数図式を作る際はこれらをそのまま用い、同じ恒等・合成の証明を新しく作り直さない。G5の元の模型への自然なcolimit比較と一般のv被覆の完全性は依然として未完である。
