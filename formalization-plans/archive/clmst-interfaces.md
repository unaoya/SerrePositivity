# CLMST の実装境界と作業単位

> **アーカイブ（2026-10-17）**：この計画は完了したか、ほかへ吸収された。内容の要約先：[CLMST 主計画](clmst.md)。将来は削除する予定で、以下は当時の計画と実施記録のまま。


作成日：2026-10-13。更新日：2026-10-14。状態：必要な数値結果とSerre接続を明示引用から証明済み。
[主計画](clmst.md)の M0〜M3 を具体化する。T1の共通層抽出、T3-a の一般定理、有限生成一致の証明、almost 圏と冪ねじれの導来完備性を実装した。
mod p^N の冪等性の入力と almost 比較、Cor 4.0.4 の原典入力からの適用まで実装した。
Prop 4.0.14 の一般段の公式は、共通Euler理論と有限段の数値評価から引用せずに証明した。
旧Inputs宣言は互換入口として保持する。標準完備塔のperfectoid性はWitt係数表示から証明済み。基礎引用はBSの存在・全射性、
Prop 2.4.7、Cor 4.0.4、およびalmost圏用のイデアル冪等性に分離した。
Prop 4.0.10の数値評価は証明済みであり、直接の引用ではない。
存在入力の整代数版への適用と、実導来錐の零射の入力・核余核への接続も実装した。
導来完備化関手、basic setup の平坦性と深い文献結果の証明は引き続き残る。
完備化の共通工程・証明手順・作業分担は[統合計画](adic-completion-integration.md)を正本とし、
この文書ではCLMSTへの固有の適用と引用境界を扱う。
現在の作業順と引用台帳は[主計画§0・§9](clmst.md)を正本とする。
T0〜T3は達成した設計・工程の記録として読む。末尾の「続きの実装状況」は
当時の経過記録であり、そこにある残作業を現在の未完了項目として扱わない。

## 現在の受渡し状況（2026-10-14更新）

C1（標準完備塔）・F1〜F7は完了済み。
F3は元の二座標Koszul完備化の実際のH⁰に可換環構造を与え、
元の標準写像との一致、標準作用に関する両座標の導来完備性、
完備離散環への任意の環準同型の一意延長、反復環との比較を証明した。
公開入口は[`PDCompletion.lean`](../../SerrePositivity/HomologicalAlgebra/DerivedCompletion/PDCompletion.lean)。
一般の三座標以上への拡張とδ構造の延長は別工程。
F4は`StrictPRecovery`で零環を含むWitt復元、標準商図式、一意性を供給済み。
検証は`scripts/audit_f4.lean`。
F6は`PerfectionPrincipalQuotientKernel`で一般主イデアル商の核を生成する公式まで供給済み。
標準写像の署名、非正則元、零環の商の検証は`scripts/audit_f6.lean`。
F7は`PerfectoidFontaineSeparation`でp正則な整perfectoid環のFontaine核進分離性を供給済み。
BSの比較射への適用を`scripts/audit_f7.lean`で確認した。次はBS成果のCLMSTへの接続。
F5は[主計画§9.3](clmst.md)で
一般加群の分離性、導来／古典的比較、主イデアル商、BS適用監査の5単位を完了した。
公開入口は`AdicBoundedTorsionQuotient`、BSの既存ねじれ入力との接続は`scripts/audit_f5.lean`で監査する。
[主計画§9.7a](clmst.md)のE1〜E5は完了した。深い入力を使わず、
Claim 2.4.8の一般加群版と任意の加群写像の導来錐の零化を証明済み。
公開入口は`CLMST/FiniteFreeConeIsogeny.lean`、検証は`scripts/audit_clmst_elementary.lean`。
B3の一般商の存在・普遍性を受領し、[主計画§9.7b](clmst.md)のC2-1〜5も完了した。
主イデアル商の選択・標準写像・核・作用をB3へ移し、巡回評価・almost長さ比較から旧B-Iを除去。
専用監査は`scripts/audit_clmst_b3.lean`で、証明定数の推移的依存を検査する。
巡回評価にはB-Sのみ、実almost同型の長さ比較にはB-SとB-Rのみが残る。
一般有限代数側のB-Iは維持するため、主定理の7宣言という台帳は変わらない。
旧選択との互換比較は`PerfectoidIdealCompatibility.lean`と専用監査へ分離した。
BS共通要求G1も[主計画§9.7c](clmst.md)のG1-1〜4で完了した。
公開入口は`CommutativeAlgebra/PrincipalAdicFaithfulDescent.lean`の
`SerrePositivity.surjective_algHom_of_principal_residue_baseChange`。
BSのS/(p)、C/(p)を直接使い、mod pでのみ忠実平坦な底変換後の全射性を降ろす。
適用時はMathlibの標準構造を公開する`principalAdicQuotientAlgebra`を局所instanceとして使う。
一般Iの加群版・環商版、公開22宣言と境界例を`scripts/audit_g1.lean`で監査済み。
次は[主計画§9.7d](clmst.md)の統合計画に従う。
G2-1（実導来圏への接続・TorとH⁰の自然比較・標準augmentation）、
G2-2a（加群の導来係数変更）、G2-3（一般複体の完備化・標準単位・完備対象の再構成）は実装・監査済み。
次の実行区切りはG2-2b・G2-4（複体の底変換・剰余比較）。
G2-5〜7はH⁰環・PD完備化との条件付き比較・BS受渡し、D1〜6は零化の降下、
KL1〜6はKoszul–Tor・局所コホモロジー・任意パラメータ系の比較。
元のG2要求のmod p比較には仮定の修正が必要で、S側の完全平坦性だけから
T/pの導来剰余の離散性を推論しない。完備化後の離散性だけによるCpとの環比較も
未確定の一般性として記録し、部分場合の証明で受渡し全体を完了としない。
KL1は一般係数のTor比較・反復錐比較・通常のC上のスカラー作用まで実装・監査済み。
D1・D2・D4・D5とKL5も完了し、D4はG2-3の標準再構成からの零化とD5への接続まで供給した。
残るD3・D6の降下、KL2〜4・KL6の局所コホモロジー比較と
Cor 4.0.4への含意は後続工程とし、既存引用を維持する。
現在の型・成果物・優先順・受入条件は[主計画§9](clmst.md#9-次の具体的な作業2026-10-14更新)を参照。
主定理へ到達する未証明入力は7宣言（外部引用5件・K理論2件）。
以下のレビューと検証件数は当時の記録である。

## 0. 今回の抽象化レビューと整理（2026-10-14）

CLMST・LengthAlgebra・RootTowerの128モジュールを根とするソースのimport閉包を調べ、
Paperへの推移的importが0件であることを確認した。
さらに共通層の71モジュールを根とする閉包には、Paper・CLMST・BhattScholzeの
いずれへのimportもないことを確認した。
`PerfectoidCokernelEuler`は共通のKoszul誤差Euler消去、
`CompletedCokernelFiniteEuler`は共通の余核有限性・Euler比較を適用する。
`SourceEulerEvaluation`は実際の平坦基底変更と有限段の長さ計算を担い、
`ParameterFormulaDescent`はその数値公式を明示的な引数として受ける。
この経路では抽象定理、適用条件の確認、具体的な数値評価が分離されている。
これは当該経路の確認であり、全コードの徹底レビューの完了とは扱わない。

巡回長さの帰着で、利用先が監査以外にない旧入口を整理した。

- 積の包含`hprod`を要求する一次比較と全冪の長さ零を削除。
- pねじれ商のperfectoid性`hQ`を外から要求する比較を、
  その性質を内部で証明して使う`completedLength_cyclic_pow_eq_of_p_factor`へ統合。
- 一元パラメータ系のpで割れない場合だけを扱う未使用入口を削除。
  全ての非零元を扱う`completedLength_cyclic_fin_one_eq_zero`を保持。
- `NormalizedAlmostLength`は旧Inputsのaliasを経由せず、`CyclicLength`の実際の証明を参照する。

一般のイデアル・正規化長さについての`LengthAlgebra/AlmostFactorQuotient`は保持する。
これはCLMST専用の旧入口とは異なる一般性を持つため、同じ理由では削除しない。
監査はこの共通モジュールを明示的にimportし、一般補題のsorry非依存を引き続き確認する。

検証：全体ビルド4157ジョブと両公理監査が成功。
旧Inputsの巡回評価aliasは監査で明示的にimportして互換性を確認する。
主定理へ到達する未証明入力は11宣言のままで、新しい引用・公理は追加していない。

### BS計画の参照による作業の分担（2026-10-14）

以下の候補表は初回調査を保持したもの。採用する実行順は
[主計画§0.2](clmst.md)のS0〜S5/C1〜C2である。
標準完備塔はこの側で進め、任意gの冪等性・全射性は
[BS計画](../bhatt-scholze/notes/bhatt-scholze.md)のB4・B5へ集約する。
古典的／導来完備性は共通基盤として一度証明する。
共通準備P0、並行担当P1、待合せP2、合流P3は主計画§0.2に明記した。
ユーザー指定により、このチャットは共通準備・ホモロジー代数等の共通基盤と
CLMSTの塔・具体的適用を担当する。別チャットはBSのδ環・prismと
一般存在・全射性・冪等性を担当する。
BS側が必要とする共通補題は、型と利用先をBS計画へ記録して受け渡す。
BSの商の存在B3が完成した段階で、巡回商を一般整代数の存在引用から切り離す。
有限代数のperfectoid化の存在引用は、それとは別に残る。

### 追加証明の候補の初回調査

| 候補 | 再利用できる実装 | 残る主要工程 |
| --- | --- | --- |
| 標準完備塔のperfectoid性 | `RootTower/CompletionFlat`のp正則性、有限段の`ModPSurjectivity`・`ModPEquiv`、`PerfectoidFontainePrincipal.isIntegralPerfectoid_of_regular_of_tilt_coeff_kernel` | 有限段の射を塔・完備塔のmod p Frobeniusへ移す。実際のtilt係数射の核をcompatibleなp根で生成することを証明する。完備性・pの非可逆性・p根を供給して四条件へ接続する |
| 任意gのmod p^N像イデアル冪等性 | almost局所化圏と長さ不変性の接続、引用のN=0の証明 | 普遍perfectoid化の核に関する任意gの一般論が必要。根を持つ特別なgの根生成イデアルの冪等性だけでは、現行の引用を置き換えられない |
| BS全射性入力中の完備性比較 | `DerivedCompletion/AdicComparison`で任意の古典的主元進完備加群の導来完備性と、p正則な場合の同値を証明済み | 共通要求F2は解消。一般の商の存在・全射性自体と導来(p,d)完備化は別工程 |

まず標準完備塔のmod p Frobeniusを、独立した共通補題として切り出す候補を優先する。
有限段の射はA/pへの反復Frobenius射であり、完備塔のmod p上のFrobeniusとは
定義域・終域が異なるため、全射性をそのまま適用済みとは数えない。
既存のFontaine核判定は最終接続に使えるが、実際の塔のtilt核の計算はまだ必要である。
この初回調査では三つの引用を新たに証明したとは扱わない。

## 1. 最初の区切り

原典の主張を、具体的に定義した対象について名前付きで引用し、
そこから Serre の混標数の長さ代数への接続を直接の `sorry` なしで証明する。
原典の引用自体を証明する作業と、Lech に必要な追加の不等式は後続段階に分ける。

最初の区切りで必要な出力は次の二つ。

\[
\lambda_\infty H_i(\underline z;C_D)=0\quad(i>0),\qquad
\lambda_\infty(C_D/(\underline z))=e(\underline z,D).
\]

`D` の任意のパラメータ系について述べる。`C_D` は普遍性で選んだ具体的な perfectoid 化。
これらの結論を満たす未知の代数を構造の field に置くことはしない。

## 2. 現在のコードから再利用するもの

| 現在の実装 | 再利用範囲 | 残る引用・比較 |
| --- | --- | --- |
| `TowerStage`・`Tower` | 商による有限段、遷移、有限自由性、局所性、標準剰余体、正則な有限段等 | CLMST の標準的な根の塔との表示の対応を確認 |
| `TowerDescent.exists_descent` | 有限表示加群の有限段への降下 | 数値定義の層へ切り出す |
| `TowerDescent.fgLength_tensor` | 有限段の λ* の公式 | λ∞ の公式は C1 に依存するので区別 |
| `TowerLength` の三つの数値関数 | λ** の下限、λ* の下限、λ∞ の上限 | 数値定義は引用非依存。C1・C2 は Noether 局所基底・素数・座標条件の下で証明済み |
| `length_eq_of_common_residueField` | A と A_n 上の長さの比較 | `residue_surjective_towerStage` から仮定を供給 |
| `CompletedTower` | p 進完備化の環と作用 | 現在は長さ比較・D に関する Koszul 冪ねじれと同居している |
| `IsIntegralPerfectoid`・`IsPerfectoidization` | 環の条件と普遍性の具体的な定義 | 原典の対象・完備化・宇宙との対応を監査 |
| `Perfectoidization`・`MixedPerfectoid` | 引用から選んだ普遍対象、両立する作用 | 存在の引用は残る。選択の一意性・関手性を追加 |
| `towerLengthOn_eq_completedTowerLength` | 係数制限の順序による長さの一致 | 純粋な環の完備化とは別モジュールへ |
| `isPowTorsion_completedTower_koszul` | 任意のパラメータ系での一様な冪ねじれ | almost 消滅とは別に既存証明を使う |

主な所在は [Section2](../../SerrePositivity/Paper/Section2/) と
[FiniteLength](../../SerrePositivity/CommutativeAlgebra/FiniteLength.lean)。
移動のために数学的対象を二重に定義せず、正本を抽出して旧 namespace に互換別名を残す。

## 3. T0：先に確定する型と引用境界

### T0-a：標準基底と長さの一般性

CLMST §2.2 の基底は、完全剰余体を持つ標準的な等標数または非分岐混標数の正則完備局所環。
初回監査時の C1・C2 は、型上では `IsLocalRing A` だけの、さらに広い範囲で述べられていた。

原典の正確な引用をこの広い型へ移すことはしない。最初に次を監査する。

1. 旧 C1・C2 の利用先で、実際にどの基底・座標・素数条件が供給されるか。
2. 広い一般性を別の一般定理として証明できるか、それとも標準表示の仮定を追加するか。
3. 後者の場合に変更が必要な長さの構成と、両標数の利用先。

定理の仮定を狭める変更は、単なるファイル移動と分けてレビューする。
抽象的な `NormalizedLength` 自体の定義や、共通 Euler 理論の一般性は狭めない。

数値定義は一般の塔で定義できるが、そこから `NormalizedLength` を組み立てるには加法性の証明が要る。
この依存をモジュールの境界にも反映する。

### T0-b：almost の二つの水準

イデアル `I` と加群 `M` について、まず `I ≤ Ann(M)` を具体的な零化条件として定義する。
線形写像 `f` の almost 同型は、核と余核がこの条件を満たすこととする。
これと almost 圏における対象の同型 `M^a ≃ N^a` の対応は、別に証明する。
Prop 4.0.10 の結論を、普通の加群同型しか扱わない別命題へ弱めて置かない。

Serre 接続で扱う加群は、一つの冪で加群全体が消える `IsPowTorsion` の対象である。
`p^N M=0` を確認した上で `A_∞/p^N` 上の classical almost 理論を使う。
このイデアルの冪による零化からイデアル自身による零化を導く性質は、必要な quotient 上で証明または原典引用する。
一般の `A_∞` 上の ideal が、条件なしで平坦・冪等であると仮定しない。
`(g)_perfd` は kernel の定義を保持する。根がある場合の根生成 ideal との比較には
p 進閉包が現れるため、閉包を無条件に省かない。冪ねじれ加群への作用で省ける場合は比較補題を証明する。

導来 p 完備対象を扱う一般の almost 理論は、この冪ねじれ加群の場合とは区別する。
最初の接続だけのために一般の almost 代数理論全体を作る必要はないが、
引用する原典の主張の一般性を表現できる対象の定義は必要である。
特に Thm 4.0.3 の入力 M は全ての A 加群である。
M に一律に導来 p 完備の仮定を追加すると原典を弱めるため、Tor・テンソル積の raw な零化条件と
almost 圏の対象条件を分ける。例えば非零加群 A[1/p] も非零性検出の範囲から除外しない。

### T0-c：命題2.4.7の錐

型に含めるのは、perfectoid 環 `R`、有限生成イデアル `J`、有限かつ有限表示な `R` 代数 `S`、
`V(J)` の外の有限 étale 条件、有界な p 冪ねじれ、標準写像 `φ:S→S_perfd`。
結論は、各 `g∈J` について、ある冪による `cone(φ)` への作用が **D(R) で零射**となること。

ホモロジーへの作用が零であることだけでは、この結論の代わりにならない。
一方、Serre 接続や後の Prop 4.0.14 の証明には、ここから核・余核への作用を導く系を使える。
原典の一般定理と、その加群に対する系を別の宣言にする。

Mathlib の導来圏と既存の錐の基盤を調査し、degree-zero の環・加群を実際に埋め込む。
意味を定義しない `ConeKilled` 等の述語を置いて済ませない。

### T0-d：perfectoid 化の選択と完備化

現在の存在入力はBS Thm 1.17(1)の整代数についての普遍性を引用する。
全射性はBS Cor 7.3 / Thm 7.4のpねじれのない完備商への適用形を別に引用する。
全射性に必要な古典的／導来p完備性の比較は、`AdicComparison`でp正則な場合に証明済み。
全射性自体は引き続き名前付き引用として残る。
古典的な p 完備化、導来 p 完備性、普遍写像への接続のそれぞれを台帳に記す。

同じ普遍対象を一度選び、CLMST と Serre の両方が参照する。
別に選んだ対象との比較は、普遍性から代数同型を構成して行う。
`IsPerfectoidization` の一つの universe 内での量化と、原典の普遍性の範囲も照合する。

現在の実装は `A_∞ ⊗_A D` の順序で、原典は `D ⊗_A A_∞`。
実装の順序を正本として保ち、交換同型を通じて原典へ対応させる。
異なる順序で定義した対象の同一視を `rfl` とする計画にはしない。

### T0-e：一般 n の有限段

`D_n=A_n⊗_A D` について、Noether・完備・局所・次元・剰余体を確認する。
局所性はこの塔の特殊な性質であり、一般の有限テンソル積に適用しない。
`D_n` が整域であるという仮定は付けない。

`n=0` の `D_0≃D` は、基底環との同型、代数作用、パラメータ系、
商、Koszul ホモロジー、Hilbert–Samuel 重複度に関する比較まで含めて扱う。
数値係数 `p^(-0d)=1` だけを計算して特殊化が終わったとはしない。

## 4. T1：共通基盤の抽出順

現在の import を保ったまま全ファイルを `CLMST/` へ動かすと、Paper の依存と長さの引用を引き込む。
次の順に、数学的な役割で分割する。

| 順 | 抽出する内容 | 新しい層の候補 |
| --- | --- | --- |
| 0 | 有限段の商の単項式基底 | `CommutativeAlgebra/RootTower/MonomialBasis` |
| 1 | 有限段の商の定義、根、基底、遷移、剰余体・局所性 | `CommutativeAlgebra/RootTower/Stage*` |
| 2 | 塔の有向極限、標準写像、作用、有限自由・平坦性等 | `CommutativeAlgebra/RootTower/Basic*` |
| 3 | 三つの数値関数、零・同型不変の定義的性質 | `LengthAlgebra/RootTowerLength/Defs` |
| 4 | 有限表示降下、有限段の λ**・λ* の公式 | 共通の降下と長さ計算のモジュール |
| 5 | C1・C2 の原典引用または確認済みの一般版、`NormalizedLength` の組立 | 引用の層と、その直後の組立。T0-a の監査結果で配置を確定 |
| 6 | p 進完備化の環の定義・標準写像のみ | `CommutativeAlgebra/RootTower/Completion` |
| 7 | 完備化を経由した長さの係数制限、作用の比較 | `LengthAlgebra/RootTowerLength/Completion` |
| 8 | `D` のパラメータ系の冪ねじれ、`towerLengthOn` との比較 | 一般補題と、Serre への接続を分離 |
| 9 | perfectoid 化の共通選択と両側の作用 | Bhatt–Scholze の入力に依存する構成の層 |

既存の `TowerDescent` は `TowerLength` を import するため、
数値関数だけで証明する部分と、C1 から λ∞ の公式を得る部分を分ける。
これにより「Prop 2.2.3 を証明するために、それで組み立てた長さ構造を先に使う」循環を避ける。
長さの係数制限の一般補題は `NormalizedLength` を引数に取る形で共通層に置き、
CLMST の具体的な長さを代入する結果は引用の後段に置く。

旧 Paper ファイルは互換 import・別名にできる。新しい共通層は、直接だけでなく推移的にも Paper を import しない。
移動の区切りごとに、主張の仮定と引用依存が意図せず変わっていないことを確認する。

## 5. T2：引用を置く順と台帳

現在の名前付き引用と利用先は[主計画§0](clmst.md)の表を参照する。
正規化長さの必要な一致・加法性とProp 4.0.10・4.0.14は証明済みで、
独立した引用として置かない。Cor 4.0.4の局所コホモロジーと全段Koszul消滅を
直接引用し、Thm 4.0.3は別の直接引用宣言としては置いていない。
一般n・一般加群と元の適用条件を保持し、本論文用のn=0への移送は証明する。

台帳には、宣言名、原典の版と番号、P/G、正確な仮定、原典との差、
旧引用との対応、到達する利用先を記す。
引用を原典単位に分割すると宣言数は増え得るため、`sorry` の件数だけで進捗を評価しない。

## 6. T3：接続を小さい証明に分ける

### T3-a：generic étaleness

第一候補は、Noether 整域 `A`、整域 `D`、有限単射、分数体拡大の分離性から
非零 `g∈A` を取り、標準局所化写像 `A[1/g]→D[1/g]` が有限 étale と証明すること。
完備性や標数零をこの一般定理の仮定にする必要はない。

2026-10-13 の Mathlib ソース調査では、次の宣言が候補として存在する。

- `Algebra.FormallyEtale.of_isSeparable`。
- `Algebra.exists_etale_of_isEtaleAt`。
- `Ideal.IsIntegral.under_ne_bot`。
- `Algebra.basicOpen_subset_etaleLocus_iff_etale`。
- `Algebra.Etale.of_restrictScalars`。

分数体での分離性から零素イデアルでの étale 性を出し、étale locus の開性で `D` の元を選ぶ。
有限整拡大のイデアルの収縮を使い、基底の非零元 `g` へ移す。
局所化の有限性、代数構造、scalar tower、元の写像との可換性まで証明する。
この経路を [GenericEtale](../../SerrePositivity/CommutativeAlgebra/GenericEtale.lean) に実装した。
`exists_finite_etale_away_of_separable_fractionRing` が非零元と標準局所化に対する有限 étale 性を返す。
Serre の具体的な分数体・最小多項式の設定へ適用する最後の接続は後続作業である。

### T3-b：長さの比較

三つの数値関数が原典の定義を表すことを有限段公式で証明する。
`length_A(V_n)=length_A_n(V_n)` は既存の共通剰余体の定理を使う。
完備化上の長さは非完備塔への係数制限として定義し、`completedTowerLength` と比較する。
既存の `towerLengthOn_eq_completedTowerLength` は最後の Serre の長さへの移送で再利用する。

### T3-c：almost 零から長さ零

Prop 4.0.10 に零加群を入れるため、ideal による零化から almost 圏で零になることを証明する。
旧定理は D を引数に持たず任意の非零 g に適用できるので、必要なら原典の設定を `R=A` として適用する。
旧型に新しい étale 条件を不用意に追加しない。

### T3-d：パラメータ系とホモロジー

Cor 4.0.4 の Koszul 部分を n=0 に特殊化し、作用・次数を既存の `koszulHomologySelf` と比較する。
Čech／局所コホモロジーとの比較は、Cor 4.0.4 を引用する初期接続には不要。
原典の系そのものを後で証明する段階で必要となる。
既存の冪ねじれ補題から長さの定義域を確認し、T3-c を適用する。

### T3-e：商と重複度

Prop 4.0.14 を n=0 に特殊化する。
`D_0≃D`、perfectoid 化の作用、商イデアル、重複度の同型不変性を確認し、
既存の `clmst_parameter_quotient_length` の型で結論を返す。
旧 `MixedLengthAlgebra` の最後の係数制限は再利用する。

三つの旧引用の wrapper に直接の `sorry` がなくなった時点で、
どの原典引用に依存するかを一覧で報告する。深い外部依存まで消えたとはしない。

## 7. 原典の結果自身を証明する後続作業

これは初期接続の完成とは別の区切りである。

| 対象 | 下から整備するもの | 注意 |
| --- | --- | --- |
| Prop 2.2.3 | 有限表示降下、有限段の長さ、有限生成部分加群の比較 | λ∞ の有限生成一致を前提として自分自身を証明しない |
| Prop 2.2.6 | 有限表示／有限生成近似、短完全列、上限・下限の操作 | 連続性には単射の場合と有限値の全射の場合の条件を保つ |
| Prop 4.0.10 | almost 零の巡回加群への帰着、g=p の評価、一般 g の Frobenius 比較と低次元係数の長さ評価 | 証明済み。極限の存在を使わず、有限段の増大上界で足りる。深い入力はBSの存在・全射性へ分離。almost圏の同型版は冪等性引用も使う |
| Cor 4.0.4 | 局所コホモロジーの比較、Koszul のスペクトル系列、有限フィルトレーション | Mathlib の局所コホモロジーは Ext の余極限による定義。Koszul／Čech との比較はそのファイルで将来作業とされており、既存とは扱わない |
| Prop 4.0.14 | 一様な冪による perfectoid 化の制御、パラメータ変更、Koszul Euler、長さの比較 | 証明済み。BSの存在・全射性、Prop 2.4.7・Cor 4.0.4の基礎引用と証明済みの長さ比較を用いる |
| Cor 4.0.18 | 理想の reduction、重複度の不変性、剰余体拡大との比較 | Lech 用の追加段階。Serre の初期区切りには不要 |

Prop 4.0.14 の余核が g の冪で消えることから、直接その正規化長さが零だとは結論しない。
パラメータ変更、一成分の冪に対する長さ・重複度のスケーリング、Koszul 長完全列による
補正項の比較を、独立した証明工程として記録する。

Cor 4.0.4 の全ステートメントを作る際に局所コホモロジーの具体的な型が不足するなら、
その定義・比較の整備を T2 より前に置く。名称だけの未定義述語で原典引用を先に作らない。

## 8. 検証と次の着手単位

実装時の受入条件：

- 共通層・CLMST 層から Paper への推移的 import がない。
- 環、写像、商、perfectoid ideal、almost 同型、導来圏の錐が具体的に定義されている。
- 任意のパラメータ系、一般 n、一般加群、完備性・ねじれの量化条件が原典と対応する。
- 普遍対象の選択とテンソル積の順序の比較が、基底環・D の作用と両立する。
- 段階の仮定変更と、引用を原典単位へ分ける変更を別に監査できる。
- 対象モジュールと全体のビルド、[公理監査](../../scripts/audit_axioms.lean)と引用台帳で利用先まで確認する。

T0-a の初回監査、T1 の共通層抽出、T3-a の一般定理に加え、C1 と有限表示の場合の一致も証明した。
[長さの監査](clmst-length-audit.md)をもとに、Noether 局所基底・素数・座標条件を明示する。
C1・C2 の証明には標準冪級数表示は不要である。
almost 同型は実際の Serre 局所化で、導来完備性は実導来圏の射の消滅で定義した。
mod p^N の冪等性の文献入力と almost 消滅への接続は下記の続きに記す。
導来完備化関手の整備は残る。
原典引用の新配置は巡回評価から着手し、T3-c の長さ零の帰着を実装した。
Cor 4.0.4 の新配置・全段の入力と n=0 の接続は下記の続きに記す。
Prop 4.0.14 の一般 n の商比較の入力と特殊化は下記の続きに記す。
導来の制御の入力と核・余核への接続は下記の続きに記す。
具体的な混標数の適用条件の供給と、深い結果自体の証明は引き続き残る。

## 続きの実装状況（過去の経過記録）

一般加法性を Noether 局所基底の下で証明し、
`LengthAlgebra/RootTowerLength/Normalized.lean` に引用に依存しない長さの構造と HasSup を構成した。
旧構成の広い署名をそのまま証明したという意味ではない。
旧 C2 はこの一般定理への適用に置き換え、長さの四つの入口と Section 2・5 の利用先を、
Noether 局所基底・素数・座標所属を明示する構成へ切り替えた。

almost 条件を商環へ移す比較は `Almost/Quotient.lean`、
全加群の局所化と冪ねじれ局所化の同型の比較は `Almost/SerreComparison.lean`。
`LengthAlgebra/AlmostBaseChange.lean` と `CLMST/AlmostLength.lean` は、
全加群の almost 圏の同型から、係数制限して測る長さの一致を導く。
像イデアルの冪等性と零長さの条件を明示し、basic setup の証明に置き換えたとは扱わない。

### 巡回評価・mod p^N の almost 比較

- `CompletedNormalized` と `SupPropertyComap`：完備塔の長さと係数制限での上限を引用なしに構成。
- `AlmostVanishing`：巡回商の長さ零と、一般の冪ねじれ almost zero 加群の長さ零の同値を証明。
- `CLMST/Inputs/AlmostLength`：Prop 4.0.10 の証明中の巡回評価を引用。命題全体の引用とは区別。
- `CLMST/Inputs/BasicSetup`：mod p^N の像イデアルの冪等性のみを引用。平坦性は未実装。
- `CLMST/BasicSetup`：文献入力を局所的に供給する具体的な almost 圏。全域の instance は追加しない。
- `AlmostQuotientAction`：元の加群へ実際の商環作用を与え、全 almost 圏の同型から元の長さ一致を証明。
- `CLMST/NormalizedAlmostLength`：未知の長さ零・冪等性を前提にせず、二つの文献入力と一般論を接続。
  旧長さ零宣言はこの層への適用であり、直接の sorry はない。

### 固定 g の全段の消滅と既存本体への適用

`CLMST/Inputs/CohomologyVanishing` は Cor 4.0.4 の局所コホモロジー・全段 Koszul の両成分を引用する。
局所コホモロジーには D 上の実対象と誘導乗法射の零性を使う。
`CLMST/EtaleLocus` の証明で g を選び、`StageAlgebra` の零段同型・有限単射性と
パラメータの移送を用いて D の Koszul 消滅へ適用する。
旧「g の存在＋n=0 の消滅」という一体の引用は、原典引用への適用に置き換えた。
一般段の局所環構造・次元とその供給は、下記の続きで証明した。
`TensorOrder` の普遍性の移送は、新たな選択を使わず原典のテンソル順序と照合する。

### 一般段の商の長さと重複度の移送

`CLMST/Inputs/ParameterLength` は Prop 4.0.14 の一般 n の公式を、
実際の D_n のパラメータ系と重複度、係数 p^(-nh) を保って証明する。
完備化前後のテンソル比較・共通剰余体の長さ一致・Euler比較・倍率の消去を実装済み。
`StageFiniteness` の有限性・Noether 性と `HilbertSamuelEquiv` の環同型不変性は証明済み。
`CLMST/ParameterLength` は零段への特殊化・D への移送と、原典の階数公式を導く。
三つの旧入口は、今や共通層の入力への適用であり、直接の sorry はない。
引用自体の証明や Bhatt–Scholze の複合入力の分離とは別の到達点である。

### 一般段の構成の確認

`StageBaseChange` の D 代数同型で、有限段を D 上の根の塔の表示へ移す。
`StageDimension` の基底・自由性・単射性・次元保存・ランク計算と
`StageLocality` の局所性・パラメータの移送は引用なしに証明した。
Cor 4.0.4 と Prop 4.0.14 の入力は、局所性を未知の引数にせず、基底のパラメータ条件から供給する。
一般段への移送に依存する長さの評価も公開し、零段の比較をその特殊化にした。
この構成の確認と原典の深い結果そのものの証明は区別する。

### 整代数の存在と実導来錐

存在は BS Theorem 1.17(1) の整代数の普遍環の主張を引用し、有限代数版を証明で導く。
Theorem 10.11 の離散な prismatic perfection を同じ型で実装したとは扱わない。
`PerfectoidizationCompletion` の一意延長と普遍性の双方向の移送は引用非依存である。

`DerivedModuleCone` と `CLMST/PerfectoidizationCone` は標準写像の実導来錐を構成する。
Prop 2.4.7 の原典入力は実導来射の零性のまま保持し、核・余核の零化への変換は証明した。
g の正則性を別途供給すれば単射性も導ける。具体的なテンソル代数に対して
その正則性・有界 p∞ねじれ・エタール条件を供給する作業は、原典の引用と分けて残る。

### テンソル代数への適用と残る平坦性

`EtaleAwayBaseChange` で基底変更と主イデアルの各元へのエタール性の移送を証明した。
`RegularBaseChange` は平坦基底変更による正則性保存と、p 正則性からの有界ねじれを証明する。
`CLMST/TensorIsogeny` はこれらを組み合わせ、平坦な perfectoid A 代数 R に対する
R⊗_A D の標準写像の単射性・余核の g 冪による零化を導く。
この平坦性は条件として明示され、原典の命題2.4.7には追加していない。

`RootTower/CompletionFlat` は未完備塔の A 上の平坦性と、主イデアルの生成元の
完備化上の正則性を証明するが、完備塔の A 上の平坦性は未証明。
現行 Mathlib の完備環の平坦性は、未完備塔自身の Noether 性を要し、この対象には使えない。
Noether A上の平坦加群の完備化の平坦性を、有限表示加群とのテンソル比較を経由して証明する。
これは[統合計画](adic-completion-integration.md)の共通工程としてCLMST側が担当する。
可換環論側のNoether判定とは独立に進め、比較同型と平坦性が完成するまで具体的適用として数えない。
`AdicCompletionInjective` では一様なフィルトレーション比較から任意の完備化写像の
単射性を導く判定と、有限終域の単射への Artin–Rees の比較の供給を証明した。
`FlatTensorFiltration` で平坦テンソル積へ同じ次数のずれで比較を移した。
`AdicCompletionExact` の一般完全性判定を使い、有限な中間加群をもつ短完全列の
平坦テンソル積と完備化後の完全性も証明した。
残る作業は有限表示加群と完備化のテンソル比較同型、および有限イデアルの判定を用いた
完備化の平坦性。この二つを今回の完全性の系として証明済みとは扱わない。
比較では有限自由表示の最初の写像に単射性を要求しない。有限自由全射の核Kを挟み、
Kの比較の全射性と有限自由加群での同型から余核を比較する。自然性も独立の受入条件とする。
詳細は統合計画の2a〜2cに集約する。完備塔への適用、一般正則性の共通層への配置整理、
isogenyへの接続はCLMST側、剰余体拡大への適用と外部引用1の置換は可換環論側が担当する。

## 9. 根拠資料

- [CLMST v4](https://arxiv.org/html/2209.04046v4)：§2.2、§2.3、Caution 2.4.4、Prop 2.4.7、Notation 4.0.1、Cor 4.0.4、Prop 4.0.10・4.0.14。
- [現行の CLMST 入力](../../SerrePositivity/Inputs/CLMST.lean)と
  [混標数の接続](../../SerrePositivity/Paper/Section2/MixedLengthAlgebra.lean)。
- [長さの定義](../../SerrePositivity/Paper/Section2/TowerLength.lean)、
  [有限表示降下](../../SerrePositivity/Paper/Section2/TowerDescent.lean)、
  [完備化と長さ比較](../../SerrePositivity/Paper/Section2/CompletedTower.lean)。
- [perfectoid の定義](../../SerrePositivity/CommutativeAlgebra/IntegralPerfectoid.lean)、
  [現在の perfectoid 化の選択](../../SerrePositivity/CommutativeAlgebra/Perfectoidization.lean)。

Mathlib の API 名は、このリポジトリで固定している版のソースを確認したもの。
型の接続がそのまま通ることや、必要な証明が全て揃っていることを保証する一覧ではない。
