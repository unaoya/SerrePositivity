# CLMST とその準備の形式化計画

作成・更新日：2026-10-13。状態：共通の長さ・almost・導来完備性の実装と既存コードの移行段階。
原典は `paper/refs/CLMST-2209.04046v4.pdf`（手元のみ）と
[同じ版の HTML](https://arxiv.org/html/2209.04046v4)。実装の到達点は §0 に記す。

具体的な型の設計、共通基盤の抽出順、接続の受入条件は
[実装境界と作業単位](clmst-interfaces.md)にまとめる。
完備化の平坦性と剰余体拡大側との共通工程は、
[完備化の統合計画](adic-completion-integration.md)を正本とする。

対象とする版：Cai–Lee–Ma–Schwede–Tucker, *Perfectoid signature, perfectoid Hilbert–Kunz
multiplicity, and an application to local fundamental groups*, arXiv:2209.04046v4
（以下 CLMST）。準備として、Faltings の正規化長さ、perfectoid 塔、Bhatt–Scholze の perfectoid 化を含む。

## 0. 実装の進捗（2026-10-13）

初回の共通層抽出を実装した。有限段・塔・有限表示降下・λ**／λ*／λ∞の数値定義、
完備化の環、任意の正規化長さの係数制限、Koszul の冪ねじれを論文非依存のモジュールに分けた。
既存の宣言名を保持し、旧 Paper モジュールから互換 import する。
数値関数には全射による λ* の単調性と、有限表示加群での λ*≤λ** の証明も追加した。

C1/C2 の仮定と利用先の [監査](clmst-length-audit.md)を作成した。
初回抽出時には引用を既存の二宣言に保持していた。以下の続きで両性質を証明する。
等標数の表示情報の伝播など、必要な変更を監査に記録した。

有限整域拡大の分数体の分離性から、非零元を逆にして有限 étale にする一般定理も実装した。
最小多項式条件からの系と標数零の場合の系も証明した。
この定理の証明に新しい引用は追加していない。
原典の CLMST の引用の新配置、導来完備化と almost 同型のモデル、接続 B1〜B7 は後続段階である。
今回の抽出を、CLMST の原典結果そのものの証明や既存の未証明依存の解消とは数えない。

検証：全体ビルド3854ジョブ成功。`scripts/audit_axioms.lean` と
新しい `scripts/audit_clmst.lean` が成功し、共通層と finite étale の新規証明に
`sorryAx` 依存がないことを確認した。主定理に到達する未証明入力は従来どおり15件（文献13件と保留降下2件）で、増加していない。
新しい層から Paper への推移的 import がないこともソースで確認した。

### 続き：有限生成一致の解消と almost・導来完備性

C1 は `FiniteGeneration.lean` で証明し、旧宣言の直接の `sorry` を除いた。
Noether 局所基底、素数 p、座標の極大イデアル所属で足り、正則・完備・標準表示は不要。
有限表示の場合の λ**＝λ*＝λ∞ も証明した。必要な前提は HasSup・有限近似・perfection の利用先へ渡した。
C1 に関しては、当初検討した「標準冪級数表示を全入口へ伝播する」工程は不要になった。
この段階では C2 の加法性はまだ引用だった。後述の一般加法性で解消する。

almost zero と写像の核・余核による条件、冪等イデアル下での実際の almost 局所化圏、
冪ねじれの almost 同型から長さ一致への接続を証明した。
完備性は実導来圏の全次数の射の消滅で具体的に定義し、冪で消える複体・加群で確認した。
CLMST の長さの定義域にある加群の導来 p 完備性も接続した。
原典の perfectoid ideal の mod p^N での basic setup、導来完備化関手、
原典引用の新配置と全接続は未完成である。未証明依存は14件（文献12件と保留降下2件）に減った。

検証：全体ビルド3864ジョブ、新旧の公理監査が成功。
解説の引用一覧と README の件数も更新した。

### 続き：一般加法性と正規化長さの構成

`AdditivityFinite`、`AdditivityApproximation`、`AdditivityFinitelyGenerated` で、
Noether 局所基底・素数 p・座標の極大イデアル所属の下の一般加法性を証明した。
有限表示の有限段実現、有限生成分母での商の下限、有限表示冪ねじれ被覆、
有向な部分加群の上限を順に使い、C2 自体や旧 `towerLength` は使わない。
`RootTowerLength.normalizedLength` とその HasSup も、この証明から構成できた。

ここで「加法性の数学的証明」と「既存の本体から C2 引用を外すこと」を区別する。
新 API は正当な基底・座標の仮定を明示するが、旧 `towerLength` は任意の局所基底で作られている。
その型と利用先を切り替える移行は未実施であり、主定理に到達する旧 C2 引用はまだ残る。
新しい一般論・長さ構造には未証明依存がない。

perfectoid 化の普遍性から誘導射・恒等射・合成の法則と、主イデアルに対する kernel の単調性も整備した。
mod p^N の商環作用と raw almost 条件の一致、全加群の almost 圏から冪ねじれ部分圏への同型の移送を証明した。
この移送により、長さの比較の接続を部分圏内の同型だけへ制限しない。
`CLMST/Almost` と `AlmostLength` では actual な perfectoid ideal を使ってこの接続を具体化した。
mod p^N の像イデアルの冪等性と almost zero から長さ零の結果は、独立した入力として保持する。
選択された perfectoid 化を参照する結果の型には、既存の存在引用への依存が到達する。
新しい引用・公理は追加していない。

検証：全体ビルド3883ジョブ、公理監査と新モジュールの依存監査が成功。
証明した加法性、新しい正規化長さと HasSup は標準3公理のみで、C2 の引用に依存しない。
主定理に到達する未証明入力は引き続き14件。新しい層から Paper への推移的 import はない。

次の移行：旧 C2 と無条件の長さ構成の利用先を、新しい仮定つきの証明済み構成へ切り替える。
その後、原典の basic setup、almost 消滅・商の長さの引用を新しい層で述べ、具体的な適用へ接続する。

### 続き：既存コードの長さ構成の移行

旧 C2 の直接の `sorry` を共通層の一般加法性への適用に置き換えた。
`towerLength` は `RootTowerLength.normalizedLength` を参照し、
`towerLengthOn`、`completedTowerLength`、近似商の `μT` もこの構成から作る。
いずれも Noether 局所基底・素数 p・座標の極大イデアル所属を明示する。
これらの条件は既存の利用先で供給でき、標準冪級数表示や新たな外部入力は追加しない。

Section 2 の perfection・混標数構成・定理2.5、Section 5 の有限近似・正値性へ
条件を伝播した。座標の span が極大イデアルに等しい箇所では、そこから所属を導く。
数値関数の定義は同じであり、変えたのは構造の法則の証明と必要条件の明示である。

検証：全体ビルド3887ジョブ、`audit_clmst.lean` と `audit_axioms.lean` が成功。
四つの長さの入口・旧 C2 の互換定理・HasSup に `sorryAx` はなく、
主定理に到達する未証明入力は13件（文献11件と保留降下2件）に減った。
引用一覧・README・解説 PDF も同期した。新しい引用は追加していない。

次の着手点は原典の basic setup と almost zero からの長さ零の接続である。
導来完備化関手とその比較、原典引用の新配置 T2 と接続 T3-b〜e は引き続き残る。

### 続き：巡回評価から almost 消滅・長さ比較への接続

`SupPropertyComap` で、任意の環準同型による係数制限が HasSup を保つことを証明した。
`RootTowerLength/CompletedNormalized` は完備塔上の正規化長さと HasSup を Paper 非依存で構成する。
Paper の `completedTowerLength` はこの構成への互換入口となった。

`LengthAlgebra/AlmostVanishing` は、任意の可換環・イデアル I,J と HasSup を持つ長さについて、
各巡回商 `R/(J^n + I)` の長さ零から、一様な J 冪ねじれの I-almost zero 加群の長さ零を導く。
逆向きも証明した。この帰着には Noether 性・I の冪等性は不要で、
各元の巡回像による被覆と長さの上限を使う。

文献入力 `CLMST/Inputs/AlmostLength` では、Prop 4.0.10 全体を引用する代わりに、
その証明中の標準混標数基底上の巡回商の長さ評価を明示して引用する。
ここには g=p の評価、mod p の Frobenius 比較と増大評価、g=p^c g' の扱いが残る。
`CLMST/NormalizedAlmostLength` が一般加群へ適用し、
旧 `Inputs.clmst_length_eq_zero_of_perfectoidIdeal_annihilates` の直接の `sorry` を除く。
引用を消したという意味ではなく、引用と帰着の境界を狭めたものである。

mod p^N の perfectoid ideal の冪等性は、別の `CLMST/Inputs/BasicSetup` で名前付きに引用する。
根拠は CLMST §2.4 の Lemma 2.4.3 直前の段落と Bhatt–Scholze Remark 10.7。
引用するのは冪等性だけであり、basic setup の平坦性等を実装済みとは扱わない。
指数ゼロは零環の命題として証明した。
`CLMST/BasicSetup` は局所的な Fact で全加群の almost 圏と局所化関手を構成する。
全域の instance は登録しない。

`AlmostQuotientAction` は、元の加群に p^N を法とする作用を実際に与え、
商環の全 almost 圏での同型から元の加群の長さの一致を導く。
一様な冪ねじれの二つの加群に共通の p^N を選べることも証明した。
これにより Prop 4.0.10 の比較は、未知の長さ零条件や冪等性を引数として要求せず、
二つの明示した文献入力から証明する。単一の線形写像の存在には弱めていない。

検証：全体ビルド3900ジョブと両公理監査が成功。一般の帰着・係数制限・商環作用・
共通指数の定理は標準3公理のみ。新しい6入口から辿る139モジュールに Paper import はない。
旧零長さ宣言に直接の sorry はなく、巡回評価と既存の perfectoid 化の存在入力へ到達する。
一般の almost 比較には、これらに加えて冪等性の名前付き入力が到達する。
主定理に到達する未証明入力は13件のままである。

main の消滅への接続は冪等性の新引用を使わない。従来の零長さ引用を巡回評価へ置き換えるため、
主定理に到達する引用の件数は変わらない。原典の Cor 4.0.4 の一般形と g の選択、
Prop 4.0.14 の一般 n の商比較、導来完備化関手の整備は後続工程である。

### 続き：Corollary 4.0.4 の原典入力と g の選択

`CLMST/EtaleLocus` で、正則局所基底から標数零整域への有限単射拡大について、
基底環の非零元 g を反転すると有限エタールになることを証明した。
完備性・perfectoid 化・消滅の引用はこの g の存在証明に使わない。

`CLMST/Inputs/CohomologyVanishing` は固定した g と標準局所化のエタール性を受け取り、
Cor 4.0.4 の両成分を明示して引用する。局所コホモロジーの下次数での消滅と、
任意の有限段 `A_n ⊗[A] D` のパラメータ系の正次数 Koszul 消滅を同じ入力に保持した。
引用の結論へ g の存在を含めず、n=0 だけへ弱めない。

局所コホモロジーは D 上の Mathlib の Ext の余極限による実対象を使う。
`LocalCohomologyAction` は C の元の D 線形乗法が誘導する具体的な自己射を定義し、
単位元・積の関手的な法則を証明した。引用の零化は、この射が零という形で述べる。
Mathlib の現行の関手には加法性・線形性の instance がないため、
未証明の C または A∞ 加群作用は導入しない。C 上の別の台を持つ局所コホモロジーへ置換もしない。

`CLMST/StageAlgebra` は実際の有限段のテンソル積と、RPerfd への標準 D 代数写像を構成する。
零段の基底環との同型、`D_0 ≃ D`、零段の局所性・有限性・標準写像の単射全射性を証明した。
`CLMST/CohomologyVanishing` は零段へパラメータ系を移し、原典の全段の引用を適用する。
既存の `Inputs.clmst_exists_perfectoidIdeal_annihilates_koszul` はこの証明への互換入口となり、
直接の sorry を除く。一般段の局所性は引用の型でその構造を明示して受け取り、
今回の既存本体への適用には証明済みの零段の構造を使う。

`CLMST/TensorOrder` は原典の `D ⊗[A] A∞` と既存の `A∞ ⊗[A] D` の順序を比較する。
交換同型を通じて同じ RPerfd が perfectoid 化の普遍性を満たし、D の包含も一致する。
新しい perfectoid 化の選択や存在引用は追加しない。

検証：全体ビルド3908ジョブと両公理監査が成功。g の有限エタール化、零段の同型・
有限性・局所性、局所コホモロジーの実対象と乗法の関手的法則は標準3公理のみ。
新しい4入口から辿る277モジュールに Paper import はない。
主定理の未証明入力は13件（文献11件と保留降下2件）のままであり、
旧 g の存在＋Koszul 消滅引用は原典の `CLMST.Inputs.corollary_4_0_4` に置き換わった。

この工程は Cor 4.0.4 自体の証明ではなく、原典の型での引用と既存本体への接続である。
その証明に必要な局所コホモロジーと Koszul の比較・スペクトル系列は別に残る。
次は Prop 4.0.14 の一般 n の商の長さ比較と、perfectoid 化を制御する入力の分離である。

### 続き：Proposition 4.0.14 の一般段と零段への移送

`CLMST/Inputs/ParameterLength` に Prop 4.0.14 の一般 n の公式を明示した。
任意の有限段 `D_n=A_n⊗[A]D` のパラメータ系 y について、
`λ∞(RPerfd/(y)) = e((y),D_n) / p^(nh)` を引用する。
有限段からの標準写像、完備塔に制限して測る具体的な長さ、D_n 自身の重複度を保つ。
零段への特殊化を引用のステートメントへ含めない。

`StageFiniteness` はすべての段の D 上の有限性、D が A 上有限なときの A 上の有限性、
A または D の Noether 性から段の Noether 性を証明する。
零段の Noether 性には素数の仮定も不要である。
一般段の局所環構造は先の Cor の入力と同じく明示して受け取り、
既存本体への適用は証明済みの零段の構造を使う。

`CommutativeAlgebra/HilbertSamuelEquiv` で、環同型に沿う商の長さ、Samuel 関数、
Samuel 多項式と Hilbert–Samuel 重複度の不変性を定義から証明した。
多項式が存在しないときの零という分岐も比較し、Noether 性・局所性・準素性は要求しない。
重複度公式の不変性を新しい引用として置くことはしない。

`CLMST/ParameterLength` は零段の同型に沿ってパラメータ系と重複度を移し、
`p^(-0h)=1` を計算して D の商の長さの公式を導く。
さらに、正則基底の重複度の階数公式から原典の「特に」の公式を証明した。
`m_A` を RPerfd に拡大したイデアルによる商として、階数との一致を明示する。

旧 `Inputs.clmst_parameter_quotient_length` はこの接続への互換入口となった。
これで `Inputs/CLMST.lean` の三つの既存入口はすべて直接の sorry を持たず、
Paper 非依存の原典入力と一般論の適用として証明される。
文献入力そのものを証明済みとしたわけではなく、主定理の未証明依存は引き続き残る。

検証：全体ビルド3917ジョブと両公理監査が成功。一般段の有限性・Noether 性と
環同型による Samuel 関数・多項式・重複度の不変性は標準3公理のみ。
新しい3入口から辿る317モジュールに Paper import はない。
主定理の未証明入力は13件のままで、零段専用の旧引用が
`CLMST.Inputs.proposition_4_0_14` の一般段の入力へ置き換わった。

残る大きな工程は、Bhatt–Scholze の perfectoid 化・塔の引用の原典単位への分離、
Prop 2.4.7 の導来圏の零射と導来完備化関手、
一般段の局所性・次元と、原典の消滅・長さ比較そのものの証明である。
Serre 接続の三つの旧入力の移行と、これらの深い結果の証明を区別する。

### 続き：一般段の局所性・次元と入力条件の供給

`CLMST/StageBaseChange` で、実際のテンソル積 `A_n⊗[A]D` と
D 上で座標の像の根を添加した `TowerStage D (algebraMap A D ∘ t) p n` を
D 代数として同定した。係数と根の座標の一致も証明する。
この同型には素数性・Noether 性・局所性は不要である。

`StageDimension` は単項式基底の D への基底変更を使い、D 上の自由性、
標準写像の単射性と Krull 次元の保存を証明する。
`rank_D D_n=p^(nh)` も証明し、長さの正規化係数と段のランクを照合した。
非零な D と素数 p で足り、A→D の単射性や有限性、Noether 性・局所性は要求しない。

`StageLocality` は基底変更の同型を通じて、D 上の根の塔の局所性を適用する。
座標の像が m_D に属するという条件は、基底の像がパラメータ系であることから供給する。
これにより任意の段の局所環構造を、未知の仮定や新しい文献入力として受け取らない。
有限単射性と局所性を用いて、D のパラメータ系を各段へ移すことも証明した。

Cor 4.0.4 と Prop 4.0.14 の原典入力から、明示的な局所環構造の引数を除いた。
入力に既に含まれる数学的条件から、その構造を計算して供給する。
`parameter_quotient_length_at_stage` は、D のパラメータ系を任意の段へ移し、
同じ perfectoid 商の長さをその段の重複度と p^(-nh) で評価する。
零段の長さ比較は、この一般段の適用の特殊化にまとめ直した。

検証：全体ビルド3923ジョブと両公理監査が成功。基底変更同型、基底・ランク・単射性・
次元保存、局所性とパラメータの移送は標準3公理のみ。新しい4入口の321モジュールの
import 閉包に Paper 依存はない。主定理の未証明入力は13件（文献11件と保留降下2件）のまま。
新しい引用は追加していない。

一般段の有限性・Noether 性・局所性・単射性・次元と、パラメータの移送の確認まで揃った。
ここで証明したのは段の構成と引用への適用条件であり、
原典の消滅・長さ比較や、Bhatt–Scholze の深い結果自身の証明は引き続き残る。
次は perfectoid 化の存在入力の原典との対応と、導来圏の錐の制御の入力を整理する。

### 続き：存在入力の原典単位への分離と実導来錐の制御

Bhatt–Scholze の著者公開版を照合した。Theorem 1.17(1) は任意の整 R 代数 S の
普遍 perfectoid 環の存在を直接述べる。Theorem 10.11 は整射の p 進完備化の
prismatic perfection の離散性、Proposition 8.5 は派生的な構成の普遍性を述べる。
有限表示性や有界 p∞ねじれを Theorem 1.17(1) の仮定へ追加しない。

`BhattScholze/Inputs/Perfectoidization` に Theorem 1.17(1) の環としての普遍性を引用した。
`BhattScholze/Perfectoidization` は有限代数の整性を供給し、旧存在入力へ適用する。
`Inputs.exists_perfectoidization_of_finite` の直接の sorry は除き、
有限表示の引数は既存利用先との互換性のため維持した。既存の選択の定義は変えない。
`Inputs/PerfectoidTower` は原典の Example 2.4.2 の入力を保持し、
依存を純粋な完備化の定義へ切り替えて Paper import を除いた。

`PerfectoidizationCompletion` は任意の環から整 perfectoid 環への写像の
古典 p 進完備化への一意延長を証明する。環準同型が p の冪を保存するので、
連続性を未知の追加条件として受け取らない。零環も扱う。
完備化と元の環の間で、同じ目標環を使って perfectoid 化の普遍性を両方向へ移せる。
これから整代数の古典完備化の普遍 perfectoid 環の存在も導く。
古典完備化と導来完備化の一致や prismatic perfection 本体を定義したとはしない。

`DerivedModuleCone` は加群写像を零次数の複体に入れ、標準 mapping cone の導来像を構成する。
完全三角形・スカラー自己射を実際の圏で定義し、導来射の零性から
核・余核を同じ冪で零化することを証明した。始域で g が正則なら単射性も導く。
`CLMST/PerfectoidizationCone` は選んだ標準 perfectoid 化への線形写像とこの錐を構成する。

`CLMST/Inputs/PerfectoidIsogeny` は Prop 2.4.7 を、R perfectoid、J 有限生成、
S 有限かつ有限表示、V(J) の外での有限エタール性、S の有界 p∞ねじれを明示して引用する。
結論は各 g∈J に対する実際の D(R) のスカラー射の零性であり、
ホモロジーの零化だけへ弱めない。単射性や p ねじれなしも引用の仮定に追加しない。
`CLMST/PerfectoidIsogeny` は、原典入力から核・余核の消去と、正則性を別途確認した場合の
単射性・余核の消去を証明して導く。

検証：全体ビルド3937ジョブと両公理監査が成功。完備化との普遍性の移送、実導来錐と
その核・余核への帰結は標準3公理のみ。新しい4入口の84モジュールの import 閉包に
Paper 依存はない。主定理の未証明入力は13件のままで、旧有限存在の引用は
`BhattScholze.Inputs.exists_perfectoidization_of_integral` に置き換わった。
Prop 2.4.7 の新しい引用は主定理の依存先には入っていない。

この新しい isogeny 入力は独立した後続 API で、まだ主定理の証明へ組み込んでいない。
主定理では旧有限存在引用が整代数の原典入力へ置き換わり、未証明入力の件数は変わらない。
次は混標数の具体的テンソル代数に対する p∞ねじれの有界性・g の正則性・エタール性の確認、
Prop 4.0.14 の証明への利用、導来完備化関手や prismatic perfection の基礎を整理する。

### 続き：テンソル代数の条件確認と isogeny の適用

`EtaleAwayBaseChange` は標準局所化後のエタール性を任意の基底変更へ移す。
有限表示性の下で、像 g が生成する主イデアルの各元の局所化へも移す。
これにより、命題2.4.7の「J の全ての元」に対する条件を J=(g) で供給できる。
このエタール性の移送に、基底変更の平坦性は不要である。

`RootTower/CompletionFlat` は未完備塔の基底環上の平坦性と、
正則元が生成する主イデアルの完備化上で、その元が正則であることを証明する。
特に、基底で p が正則なら完備塔でも p が正則である。Noether 条件は不要。
`RegularBaseChange` は平坦な A 代数 R によるテンソル積上で g の正則性を移し、
p が正則なら p∞ねじれの有界性を指数 N=0 で供給する。

`CLMST/TensorIsogeny` は、Noether A 上の有限代数 D、平坦な perfectoid A 代数 R、
D 上の g・p の正則性、g の外でのエタール性から、
R⊗_A D の標準 perfectoid 化写像の単射性と余核の g 冪による零化を導く。
有限性・有限表示性と主イデアル全体のエタール性は既存および新しい一般補題で供給する。
この適用定理は既存の perfectoid 化の存在引用と命題2.4.7に相対的である。
新しい引用・sorry は追加していない。

検証：全体ビルド3946ジョブと両公理監査が成功。新しい一般補題は sorry 非依存。
二つの新入口の推移的 import に Paper 依存はなく、主定理の未証明入力は13件のまま。

**残る条件は完備塔の A 上の平坦性。** 完備塔そのものの p 正則性から、
完備塔⊗_A D 上の p 正則性を無条件には導けない。
Mathlib の完備環の平坦性は、その環自身の Noether 性を要求し、未完備塔には適用できない。
次は「Noether A 上の平坦加群の p-adic 完備化の平坦性」を、
有限イデアルのテンソルと逆極限の比較を用いて証明する。
別案として有限表示 D とのテンソル積と完備化の交換を証明し、
未完備塔⊗_A D 上の正則性から直接導く経路を検討する。
いずれも未証明の一般論であり、具体的な完備塔への命題2.4.7の適用は未完了である。
その後に余核の作用の比較と Koszul・長さへの接続、命題4.0.14の引用の解消へ進む。

さらに `AdicCompletionInjective` で、誘導フィルトレーションの一様な比較から
任意の加群の完備化写像の単射性を導く定理を証明した。有限性・Noether 性を要求しない。
有限終域の単射について、その一様な比較を Artin–Rees から供給する定理も独立に公開した。
この比較の平坦テンソル積への移送は、以下の続きで証明した。
有限表示加群と完備化のテンソル比較・完備塔の平坦性は未証明。

### 続き：Artin–Rees の平坦テンソル積への移送

`AdicCompletionExact` は、一様なフィルトレーション比較を仮定として、
右全射な完全列の完備化後の完全性を証明する。加群の有限性や Noether 性を要求しない。
各次数の持上げを選び、比較条件からその列が Cauchy であることを導く。

`FlatTensorFiltration` はイデアル倍部分加群のテンソル像を計算し、
平坦性と商写像の完全性から、部分加群の逆像がテンソル積で保存されることを証明する。
これを用いて、一様なフィルトレーション比較を同じずれ k で平坦テンソル積へ移す。
Noether 基底で終域が有限の単射には、Artin–Rees の比較からその条件を供給できた。
さらに有限な中間加群をもつ短完全列の、平坦テンソル積・完備化後の
単射性と完全性まで証明した。平坦な加群自体は有限でなくてよい。

次は有限表示加群 N の有限自由表示を用いて、
N⊗_A P̂ と (N⊗_A P)^ の比較写像が同型であることを示す。
有限自由加群での完備化との交換と今回の完全性から余核を比較する。
その後、有限イデアルの包含について単射性を移し、P̂ の A 上の平坦性を導く。
現時点でこの交換同型や完備塔の平坦性を証明済みとは扱わない。
新しい引用・sorry は追加していない。
検証：全体ビルド3954ジョブと両公理監査が成功。追加7宣言の sorry 非依存と
Paper への推移的 import がないことを確認し、主定理の未証明入力は13件のまま。

### 続き：テンソル比較と加群版の完備化の平坦性

統合計画2a〜2c・3を実装した。`AdicCompletionTensor` は比較写像の構成、
標準写像との両立、自然性、有限自由の場合の同型と有限加群の場合の全射性を証明する。
Noether 基底で有限 N・平坦 P の場合には核を挟んだ完全列から単射性も導き、比較同型を構成した。
`AdicCompletionFlat.flat_adicCompletion_of_flat` は自然性とイデアルの包含の単射性を使い、
任意の平坦加群の完備化の基底上の平坦性を証明する。新しい引用・sorry はない。
次は統合計画4の、加群の完備化と拡張イデアルによる環の完備化の係数制限の比較。
加群版だけで完備塔の平坦性を完成扱いしない。
検証：全体ビルド3959ジョブと両公理監査が成功。追加10宣言は sorry 非依存。

### 続き：環の完備化の平坦性と具体的な isogeny

統合計画4とCLMST側の5を実装した。`AdicCompletionScalarRestriction` は各冪商の比較から
拡張イデアルによる完備化と加群版の A 線形同型を構成し、標準写像・評価の両立を証明する。
`flat_adicCompletion_algebra_of_flat` と `flat_completedTower_over_base` により、
未完備塔自身の Noether 性を要求せず、完備塔の A 上の平坦性を供給できた。
`CLMST/CompletedTensorIsogeny` では非零gの選択・正則性・エタール性の確認を接続し、
選択された普遍環への標準写像の単射性と余核のg冪による零化を導く。
命題2.4.7の原典入力への依存は保持する。
一般の正則性を `AdicCompletionRegular` へ移し、塔の旧入口を互換 import とした。
別作業でも同じ代数版を剰余体拡大へ適用して引用1の入口を証明へ置換した。
共通の完備化基盤は揃い、次は余核の作用とKoszul・長さへの接続を進める。
検証：全体ビルド3964ジョブ、CLMST・可換環論・主定理の監査が成功。
統合作業ツリーの主定理の未証明入力は12件。引用1の置換は可換環論側の変更に属する。

### 続き：余核の代数作用と有限段の Koszul 制御

`AlgebraMapCokernel` は S→C の余核をS加群として構成し、R線形な標準写像の余核と
係数制限の同型で比較する。像のS安定性をR部分加群に未知の仮定として加えない。
同じ零化元の移送と、標準写像が単射な場合の実際の短完全列も証明した。
`KoszulScalarControl` は錐・Koszul関手の線形性と、係数加群の零化元が全次数の
Koszulホモロジーを同じ元で零化することを証明する。係数の短完全列も保存する。
これらの一般論にNoether性・有限性・正則列の仮定は不要。

`CLMST/PerfectoidCokernel` は選択された同じ普遍環のS加群の余核に、isogenyの冪を移す。
`StageTensor` の実際の段写像で係数制限し、`CompletedCokernelKoszul` は一つのNを
全段n・任意の列z・全次数qへ同時に供給する。標準写像・余核からのKoszul短完全列も接続した。
深い入力は従来のperfectoid化の存在と命題2.4.7であり、新しいsorry・引用はない。

次は、段写像を経由する普遍環の作用と既存の `toRPerfd` の作用の明示的な比較、
短完全列のホモロジーの完全列と正規化長さの誤差評価を接続する。
同じ冪で消えることだけから長さ零や命題4.0.14の公式を結論しない。
必要な有限性・冪ねじれ・誤差の漸近評価を別途確認する。
検証：全体ビルド3969ジョブと両公理監査が成功。新しい共通層と段写像の20宣言はsorry非依存。
新入口からPaperへの推移的importはない。主定理の未証明入力は12件のまま。

## 1. 目的と二つの前提

最終目標は、本論文の定理2.5（混標数の長さ代数の二つの長さの性質、
`mixedPerfectoid_length_properties`）が依存している CLMST の結果を、
**CLMST 自身の形で**述べ直し、そこから本論文への接続を `sorry` なしで証明することである。
CLMST 全体（signature の理論、局所基本群への応用）は対象外とし、本論文で使う範囲に限る。

次の二つを前提とする。

1. **CLMST の形式化と、本論文への接続を分離する。**
   CLMST の層は本論文（`Paper/`）を import しない。接続は別の層に置く。
2. **引用は原典の形で述べて `sorry` にし、接続は形式化する。**
   CLMST の主張は、原典の番号・仮定・結論（almost の主張を含む）のまま名前付きの `sorry` 定理として置く。
   本論文で必要な形への変換（almost から λ へ、`n = 0` への特殊化、塔への制限、設定の変換）は証明する。

### 以前の方針からの変更

現在の `Inputs/CLMST.lean` の三つの引用は、本論文で使う形に特殊化された主張
（Prop 4.0.10 の N = 0 版、Notation 4.0.1 と Cor 4.0.4 を合わせた存在命題、Prop 4.0.14 の n = 0 版）
になっている。この計画では、これらを原典の形の引用に置き換え、
現在の三つの主張は接続層で証明される補題に格下げする。

## 2. 三層の構成

| 層 | 中身 | `sorry` の扱い | import してよいもの |
| --- | --- | --- | --- |
| L0 共通の土台 | 塔 `A_n`・`A^nc_∞`・`A_∞`、perfectoid の定義、Koszul、パラメータ系、重複度、三つの数値関数の定義 | 数値関数の定義と証明済み API。具体的な `NormalizedLength` の組立と perfectoid 化の選択の引用依存は別に管理 | Mathlib、論文非依存の一般層 |
| L1 CLMST 層（`SerrePositivity/CLMST/`、namespace `CLMST`） | CLMST の定義と、引用する主張を原典の形で述べたもの | 引用文は `sorry`。P/G のタグを付ける | L0 と Bhatt–Scholze の入力・構成。`Paper/` は import しない |
| L2 接続層（`SerrePositivity/Bridge/CLMSTToSerre.lean`） | L1 の主張から定理2.5の二つの長さの性質を導く | 直接の **`sorry` なし** | L0、L1。必要な長さ比較も先に共通層へ抽出し、最終的に `Paper/` を import しない |

`Paper/Section2/MixedLengthAlgebra.lean` はそのまま残し、依存先を `Inputs.CLMST` から L2 に変える。

この分離の利点は、**後で L1 の G の項目を証明しても、L2 と本論文の側は変わらない**ことである。
CLMST 由来の直接の `sorry` の所在と依存を記録する。
generic étaleness 等の古典的引用を採用する場合は別枠で記録し、CLMST の外に未証明依存がないとは言わない。
`#print axioms` は `sorryAx` の存在を示すが、引用名の内訳はソース・依存宣言の台帳でも確認する。

## 3. L1：CLMST の層

### 3.1 設定（Notation 4.0.1）

原典の Notation 4.0.1 を、具体的な環・写像・座標・元と明示的な仮定で表す。
最初の実装は section の引数で述べ、論文専用の結論を fields に詰めた `CLMST.Setup` は作らない。
将来データをまとめる場合も、局所環の表示等の数学的データに限り、
almost 消滅・長さ公式・未証明定理を構造の fields に入れない。

- `R`：完備局所整域、混標数 `(0, p)`、剰余体 `k` は完全体。
- `x = (p, x_2, …, x_d)`：`R` のパラメータ系。
- `A = W(k)[[x_2,…,x_d]] ⊆ R`、`R` は `A` 上有限。
- `0 ≠ g ∈ A`：`A[1/g] → R[1/g]` が有限エタールになる元。

**原典との差 (i)**：`A` は冪級数環そのものではなく、同型
`e : A ≃+* MvPowerSeries … (WittVector p k)` を持つ形で扱う。
字義どおりにすると、接続層で `Perfectoidization` などを `e` に沿って運ぶ必要があり重い。
数学的には同じなので、docstring の「原典との差」に記録する（§8 の決定事項 2）。

### 3.2 定義

| CLMST | Lean | 備考 |
| --- | --- | --- |
| Def 2.2.1（λ**、λ*、λ_∞） | 共通層の定義を `CLMST.normalizedLength` として参照 | 原典の A 上の長さと実装の A_n 上の長さの比較には、既存の `length_eq_of_common_residueField` と `residue_surjective_towerStage` を適用する。有限段公式・降下も既存。下限による λ** の定義と原典の選択による定義の対応を明記する |
| §4 での `A_∞` 加群の λ_∞ | `CLMST.normalizedLengthA∞`：`A_∞` 加群を `A^nc_∞` に制限して測る | 原典は §4 で `A_∞ - Mod_{m_A}` 上の λ_∞ を断りなく使う。制限で定めることを「原典との差」に書く（Lech §3.3 が同じ説明：`Λ/p^N ≅ A_∞/p^N`） |
| §4 の `(g)_perfd` | `CLMST.perfdIdeal g := ker(A_∞ → (A_∞/g)_perfd)` | 現在の `perfectoidIdeal`（`CommutativeAlgebra/Perfectoidization.lean`）を移すか別名にする |
| almost zero、almost flat、almost faithful | ideal による零化、Tor・テンソル積で定義 | 冪ねじれ加群での almost 同型と、導来 p 完備対象での almost 理論を区別する。単なる環の同型を要求しない |
| `R^{A_∞}_perfd` | 共通の選択を用い、実装は `(A_∞ ⊗_A R)_perfd` | 現在の `MixedPerfectoid` と順序を揃える。原典の `R ⊗_A A_∞` とはテンソル積の交換同型で対応し、作用の両立を示す |

Serre に要らない `I_∞` と `s_perfd` は今回定義しない。
`e_perfd`（Def 4.0.8）と Cor 4.0.18 は Lech との共有用の追加段階とし、
Serre の接続の最初の完了条件には含めない。

### 3.3 引用する主張（すべて `sorry`）

P：当面の深い外部入力として引用する。将来の証明を禁止する意味ではない。
G：後で L1 の中で、P の項目と一般論から証明する候補。

| 番号 | 原典の形（要旨） | タグ | 後で証明するときの材料 |
| --- | --- | --- | --- |
| Prop 2.2.3 | λ_∞ は well-defined。有限生成なら λ*、有限表示なら λ** と一致する | 証明済み | `RootTowerLength/FiniteGeneration` と既存の有限表示降下・有限段公式 |
| Prop 2.2.6 | (a) 短完全列で加法的。(b) 推移写像が単射、または全射で各値が有限のとき、帰納極限で連続 | G | Faltings Appendix 2、Gabber–Ramero Thm 14.5.75 |
| Ex 2.4.2(1) | `A_∞`（`A^nc_∞` の p 進完備化）は perfectoid | P | |
| Prop 2.4.7 | perfectoid R、有限生成 ideal J、有限・有限表示 R 代数 S、V(J) 外で有限 étale、S の p^∞ 捩れが有界。各 g∈J に対し錐への g^N 倍が D(R) で零 | P | 導来圏での零射とホモロジー零化を区別。S_perfd の存在と同定を先に構成 |
| Thm 4.0.3 | (a) 全ての `i > 0` と A 加群 `M` で `(g)_perfd · Tor_i^A(RPerfd, M) = 0`。(b) almost faithful | P | |
| Cor 4.0.4 | `i < d` で `(g)_perfd · H^i_m(RPerfd) = 0`。したがって `A_n ⊗_A R` の任意のパラメータ系 y で、`i > 0` について `(g)_perfd · H_i(y; RPerfd) = 0` | G | Thm 4.0.3、局所コホモロジーの Koszul による表示、Koszul と RΓ_m のスペクトル系列 |
| Prop 4.0.10 | `M, N ∈ A_∞ - Mod_{m_A}` で `M^a ≃ N^a`（`(g)_perfd` に関して）なら `λ_∞(M) = λ_∞(N)` | G | 加法性、巡回加群への帰着、g=p の場合の評価、一般 g の mod p Frobenius 比較と A/(p,g) の低次元長さ評価 |
| Prop 4.0.14 | `A_n ⊗_A R` のパラメータ系 y で `λ_∞(RPerfd/(y)) = p^{-nd} e(y, A_n ⊗_A R)`。特に `λ_∞(RPerfd/m_A RPerfd) = rank_A R` | G | Prop 2.4.7、Prop 2.2.6、Cor 4.0.4、Prop 4.0.10 |
| Def 4.0.8、Cor 4.0.18 | `e_perfd(J; R) := λ_∞(RPerfd/J RPerfd)`。m 準素な I で `e_perfd(I) ≤ e(I)`、パラメータ系で生成されれば等号 | G | Prop 4.0.14、極小 reduction（剰余体が有限のときは剰余体の拡大、Prop 4.0.17） |

Bhatt–Scholze の perfectoid 化の存在（Thm 10.11、Prop 8.5。現在の `Inputs/Perfectoidization.lean`）も、
同じ規律で `BhattScholze/` に置く（タグ P）。現在の有限・有限表示代数版は複数結果と完備化を合わせた系であり、
それを原典の定理そのものと呼ばない。古典的／導来的完備化の比較と普遍対象の一意性を接続に含める。
原典どおりの一般範囲で述べるのに必要な対象のモデルは、M0 で先に固定する。

Def 4.0.8 と Cor 4.0.18 は本論文では使わず、Lech の論文の Theorem 3.1 (3)（混標数の `λ(C/HC) ≤ e(H, D)`）で使う。
CLMST の層は Lech の論文の形式化と共有する（[Lech の計画](lech.md)）。

**確認状況（2026-10-13）**：上の表の主張は原典の該当箇所で確認した。
Lean の主張の草案との一字一句の突き合わせは M0 で行う。

### 3.4 主張の書き方の規則

1. **仮定は原典のとおりに置き、本論文に合わせて特殊化しない。**
   一般の `n`、一般の加群 `M` も、本論文で `n = 0` しか使わなくてもそのまま書く。
2. **結論も原典の形で書く。** almost の主張は「`(g)_perfd` で消える」のまま書き、λ に言い換えない。
3. **原典との差は、Lean 上の慣習に限る。** それぞれ docstring に書く。
   - `A` を同型付きで扱う（§3.1 の (i)）。
   - 値域 ℝ ∪ {∞} を `ℝ≥0∞` にする。
   - 原典が暗黙に置く「derived p-complete」（Caution 2.4.4）を明示する。
     `IsAdicComplete` と名前だけを取り替えて同一視しない。
   - `Perfectoidization` は具体的に選んだものを使う。
4. 各文の docstring には、番号、日本語の要旨、P/G、証明の出典を書く。
5. 名前は `CLMST.prop_4_0_10` のような番号の名前とし、必要なら内容を表す別名を付ける。
6. 新しい恒久的な `axiom` は入れない。class と axiom インスタンスの方式は、
   別プロジェクトとの共有が必要になったときに再検討する。

## 4. L2：接続層

| 補題 | 内容 | 重さ |
| --- | --- | --- |
| B1 設定の変換 | 具体的な環と座標の引数を合わせ、非零 g と有限 étale 条件を供給する | g の存在は独立の一般可換環論。定義の変換だけではない |
| B2 環の同一視 | `CLMST.RPerfd` と `MixedPerfectoid` を作用と両立して比較する | 同じ選択を参照すれば `rfl`。別々の普遍対象を選んだ場合は代数同型と自然性を証明 |
| B3 長さの同一視 | CLMST の λ_∞（`A^nc_∞` 上）と `completedTowerLength`・`towerLengthOn` の比較 | 中くらい。既存の `towerLengthOn_eq_completedTowerLength` を使う |
| B4 almost から λ へ | Prop 4.0.10 を `N = 0` にして、現在の `clmst_length_eq_zero_of_perfectoidIdeal_annihilates` を出す（`M^a ≃ 0` は「`(g)_perfd` で消える」こと） | 軽い。almost 同型の定義との整合だけ |
| B5 任意のパラメータ系での Koszul の almost 消滅 | Cor 4.0.4 の後半を `n = 0`（`A_0 ⊗_A R = R`）にして、現在の `clmst_exists_perfectoidIdeal_annihilates_koszul` を出す | 軽い（注意 2） |
| B6 重複度 | Prop 4.0.14 を `n = 0` にし、CLMST の e とリポジトリの `HilbertSamuel.multiplicity` を同一視する | 軽いか中くらい |
| B7 冪ねじれ | `isPowTorsion_completedTower_koszul` | 証明済み |

B1〜B7 が揃えば、現在の `Inputs/CLMST.lean` の三つの定理は L2 の補題として直接の `sorry` なしで証明する。
移行中は旧ファイルに互換 wrapper を残せる。実際の定義と証明の正本は新しい層に一つだけ置く。
ファイル削除そのものを完了条件にはしない。

### 注意

1. **g の取り方（B1）。** CLMST は g に「`A[1/g] → R[1/g]` が有限エタール」を課す。
   現在の存在命題は `g ≠ 0` だけを主張している。標数 0 では分離性が自動なので、generic étaleness から g は取れる。
   これは CLMST ではなく古典的な可換環論の事実で、証明するか、
   別の引用ファイルに置くかを決める。原則は一般可換環論として証明する。
   Mathlib に有限 étale・分離拡大・局所化の API はあるが、必要な存在定理の接続は追加調査する。
   有限 étale 条件の意味を定義してから引用するのであり、未知の述語を仮定に追加するだけでは済ませない。
2. **B5 は軽い。** Cor 4.0.4 は局所コホモロジーの almost 消滅に加えて、
   `A_n ⊗_A R` の任意のパラメータ系の Koszul ホモロジーの almost 消滅まで主張している（原典で確認）。
   `n = 0` で R の任意のパラメータ系になるので、接続層に Čech と Koszul の比較は入らない。
   その比較は、Cor 4.0.4 自身を L1 の中で証明するとき（M4）に要る。
   以前この点を接続層の最大の危険としていたが、原典の確認でなくなった。
3. **B4 の一般性。** 現行の長さ零の引用は、任意の非零 g に対して述べている。
   原典の Notation 4.0.1 の形を保った Prop 4.0.10 からは、必要なら R=A として適用する。
   実際の D が g の外で étale であるという新しい仮定を、旧定理へ不用意に足さない。
4. **一般 n。** `A_n ⊗_A R` は原典で局所環として扱われる。
   Lean ではその局所性・次元・剰余体と、n=0 の代数同型を明示してからパラメータ系を扱う。

## 5. ファイル配置

```
CommutativeAlgebra/RootTower/…             ← 有限段・塔・有限表示降下・完備化の共通部分
LengthAlgebra/RootTowerLength/…            ← λ**・λ*・λ∞ と係数制限
CLMST/NormalizedLength.lean                Def 2.2.1、Prop 2.2.3、Prop 2.2.6
CLMST/Notation.lean                        Notation 4.0.1 の具体的引数・作用
CLMST/Almost.lean                          (g)_perfd、AlmostZero・AlmostFlat・AlmostFaithful
CLMST/Perfectoid.lean                      Ex 2.4.2、Prop 2.4.7
CLMST/Section4/AlmostCM.lean               Thm 4.0.3、Cor 4.0.4
CLMST/Section4/Length.lean                 Prop 4.0.10、Prop 4.0.14
BhattScholze/Perfectoidization.lean        perfectoid 化の存在
Bridge/CLMSTToSerre.lean                   B1–B7
Paper/Section2/MixedLengthAlgebra.lean     依存先を Bridge に変えるだけ
```

L1 は推移的にも `Paper/` を import しない。
現在の `CompletedTower.lean` は、完備化の定義だけでなく長さ比較・Koszul の冪ねじれも含むため、
そのまま移動せず役割ごとに分割する。具体的な抽出順は [実装境界](clmst-interfaces.md) を参照。
共通の塔は等標数・Serre・Lech でも使うため CLMST 専用にはしない。
`Paper` 側には互換別名を残して、既存のコードを壊さない。
数値関数と `NormalizedLength` の組立を分け、後者の加法性を証明した一般定理から供給する。
既存 C1/C2 の仮定は原典の標準基底より広いので、M0 でその一般性と利用先を監査する。
その広い型を、根拠のないまま CLMST の原典引用として移さない。

## 6. 依存関係

- L1 の中：Cor 4.0.4 ← Thm 4.0.3、局所コホモロジー比較、有限フィルトレーション、冪ねじれ上の almost ideal の性質。
  Prop 4.0.10 ← Prop 2.2.x と `(g)_perfd`、巡回加群の長さ評価。
  Prop 4.0.14 ← Prop 2.4.7、Prop 2.2.6、Cor 4.0.4、Prop 4.0.10、パラメータの変更と Koszul Euler 公式。
  Thm 4.0.3 を後で証明する場合には Prop 2.4.9 と導来完備化・平坦性の比較等も調査する。
- L2：B4 ← Prop 4.0.10。B5 ← Cor 4.0.4。B6 ← Prop 4.0.14。
  B1 は generic étaleness、B2 は同じ選択または普遍性の比較、B3 は係数制限の比較に依存する。
- 本論文：`mixedPerfectoid_length_properties` ← B1–B7 → 定理2.5。

## 7. マイルストーンと完了条件

| 段 | 作業 | 完了の条件 |
| --- | --- | --- |
| M0 型・引用境界 | 原典照合を型の設計へ進め、導来完備化・almost 同型・general n・引用台帳を確定 | 完成形の数学的主張と必要 API が明示され、弱い別命題を原典の定理と呼ばない |
| M1 共通層の抽出 | 塔・長さ・完備化・perfectoid の選択を依存順に分割移動 | 推移的な Paper import がない。主張と未証明依存の内容が変わらずビルドが通る |
| M2 原典の引用 | 具体的に定義した対象について原典の主張を名前付きで引用 | 各文に番号・P/G・原典との差。新旧の引用対応を台帳で説明 |
| M3 Serre 接続 | B1〜B7と旧 wrapper を証明し、利用先を新しい層へ移す | 旧三定理に直接の sorry がなく、未証明依存が原典引用と明示した基礎結果へ到達する |
| M4-G1 | 有限段の長さ比較、Prop 2.2.3、必要な加法性と連続性を証明 | 引用12・13を対象とする範囲が明示され、自己依存がない |
| M4-G2 | almost と長さの接続、Cor 4.0.4、Prop 4.0.14の候補を順に証明 | 原典の一般性で達成した範囲と残る深い引用を記録 |
| M5 Lech 追加 | Def 4.0.8・Cor 4.0.18 と Lech への接続 | 極小 reduction 等の入力を別途明示。Serre 接続の区切りを拡大しない |

各段で `lake build` と `#print axioms` を確かめる。`native_decide` は使わない。
途中で壊れた部分的な証明を残さない。

## 8. 決めること

1. **原典の入手。** 済み（`paper/refs/CLMST-2209.04046v4.pdf`。`.gitignore` で除外し、commit しない）。
2. **A の書き方。** 同型付きの環と座標を採用する。原典との対応を証明する。
3. **塔の定義の置き場所。** 共通の `CommutativeAlgebra/RootTower/` と `LengthAlgebra/RootTowerLength/` に抽出する案を採用。
   正確なファイル名は抽出時に既存依存に合わせる。
4. **generic étaleness。** 一般可換環論として証明することを第一候補とし、不足 API を先に調査する。
5. **導来完備化と almost 同型。** 数学的意味は固定。具体的モデルと必要比較定理の型は M0 の残る設計課題。

## 9. 次の具体的な作業

1. [実装境界](clmst-interfaces.md)の T0：命題2.4.7の導来圏の零射、命題4.0.10の almost 同型、
   Bhatt–Scholze の原典引用と現在の有限代数版の比較について、具体的な型を確定する。
2. T1：`CompletedTower` の環の定義と長さ・Koszul の API を分け、有限段から順に共通層へ抽出する。
3. T2：定義を実装した上で原典引用を置き、T3 の接続を完了する。
4. G の証明と Lech 追加は、それぞれ独立した後続段階として扱う。

## 10. 参照資料

- CLMST：arXiv:2209.04046v4。
- Gabber–Ramero, *Foundations for almost ring theory*（§14.5）。
- Faltings, *Almost étale extensions*, Astérisque 279 (2002), Appendix 2。
- Bhatt–Scholze, *Prisms and prismatic cohomology*（§8、§10）。
- Bhatt–Iyengar–Ma, arXiv:1803.03229（Lemma 4.1.2 の背景。今回は対象外）。
- 現在のコード：`Inputs/CLMST.lean`、`Paper/Section2/TowerLength.lean`、
  `Paper/Section2/MixedLengthAlgebra.lean`、`Inputs/PerfectoidTower.lean`、`Inputs/Perfectoidization.lean`。
