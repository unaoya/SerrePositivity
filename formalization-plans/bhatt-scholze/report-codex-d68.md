# 段階 II ⑤b 作業報告

専用 worktree は `../SerrePositivity-bs-d68`、枝は `math/bs-d68`。

## BS-D68 停止点 0（2026-11-07）

- BS 著者版の流れを、Frobenius でひねった Čech 余脈体の擬同型、結晶の橋、余分な δ 座標の収縮、pd de Rham 双複体、Cartier 同型、生成元での照合の順に分けた。双複体の比較は総複体から第 0 行と第 0 列への二つの射影を使う。
- Bockstein は mod p の 0 次類の持ち上げに交代余面微分を施し、p で割って還元する。微分の向きは第 1 頂点の値から第 0 頂点の値を引く。結晶側の p 倍の差を pd de Rham の橋に渡したとき、Cartier の生成元は `X^p` と `[X^(p-1) dX]` になる。この符号と生成元を段 3 の Lean の照合に使う。
- 多変数 pd 包は既存の一変数 pd 包と Mathlib の divided powers、de Rham は Kähler 微分と外積、余単体的な計算は既存の交代余面複体を再利用する。配置と 8,000〜15,000 行の見込みは指示書 §4 で承認済み。ここでは紙の照合を行った。

## BS-D68 段 1 経過（2026-11-07）

### 実装済み

- `b9f95ce24` は多項式 de Rham、余単体的可換代数・cup 積、主イデアル商の短完全列と Bockstein の土台。
- `d320fabd7` は切断付き Čech 余脈体の鎖収縮、cup 積の Leibniz 則、Bockstein の積公式。
- `2846f2a1a` は完備多項式形式の外積。
- `0700a0fb6` は自由多変数 pd 代数の基底変換・単項式基底・階乗による比較、完備自由 δ 環の構造、envelope の一意性、通常の de Rham の Leibniz 則と完備微分の平方零。
- `3d6fa8f13` の `existsUnique_completedFreeDeltaHom` は両座標で完備な δ 環への射を基底射と初期座標で一意に定める。
- `isPrismaticEnvelope_variableSubstitution` は候補環で基底生成元が正則なら、指定座標をその生成元倍へ送る置換が envelope の普遍性を満たすことを示す。
- `cechAlexanderOfAffineTerms` は各次数の affine envelope から頂点写像を構造射へ延長し、恒等射と合成を証明する。`polyCosimplicialAlgebraOfAffineTerms` はこの模型の台の基底代数を取る。
- `completedDeRhamD_wedge` は完備微分と外積の Leibniz 則。完備形式の純テンソルに還元し、完備係数上では連続な線形写像の一意性で通常の Leibniz 則から移す。

- `8eb96865e` の `completedFreeDelta_generator_regular` は有界な基底 prism の生成元の正則性を二段の完備化へ移す。`cardinal_envelope_le` は列の商表示から濃度の上界を与える。
- `15f0a131a` の `pdCompletionResidueEquiv` と `pdCompletionResidueEquiv_unit` は二元完備化の主剰余を主剰余の p 完備化と同定し、標準写像と両立させる。
- `a32aed298` の `completedFreeDeltaResidueEquiv` と `completedFreeDeltaResidueEquiv_unit` は完備自由 δ 環の主剰余を、基底の剰余環上の多項式環の p 完備化と同定する。`completedFreeDelta_residue_bounded` は有界 p 冪ねじれを示す。
- `3c527f9d3` の `completedFreeDelta_completelyFlat` は剰余の完全平坦性を基底の二元イデアルについての完全平坦性へ持ち上げる。`exists_prismaticEnvelope_of_variables` は元の草稿の型どおり、指定変数に沿う有界で完全平坦な envelope の存在を与える。
- `db972ebfb` の `affineEnvelopeTerm` は第 0 copy を固定した差座標変換で次数ごとの envelope を構成する。`cechAlexanderAffine` はこれらを小さい affine 模型に組み立てる。`polyCosimplicialAlgebra` はその基底上の余単体的可換代数で、既存の古典的な `prismSiteAlgebras` を使う。

- `05e3a847a` の `exists_unique_dgHom` は、η⁰ を経由する係数作用と η¹ の平方零から外積への延長を作り、次数 0・1 の照合、微分との両立、一意性を示す。

### ビルドと監査

- main `f48441f89` を `818923803` で取り込み、続いて main `a0e4c7d36` を `43bae15b0` で取り込んだ。de Rham の普遍性の実装後、main `81e593fb9` を `441b1d5fa` で取り込んだ。作業パスを ⑤a の追跡差分・作業木と照合した。
- `scripts/refactor/with_build_lock.sh --wait 1800 -- lake build …` で、新規 37 モジュールすべての対象ビルドが成功した（4,074 jobs）。警告は残る。
- Lake の成果物を import する一時ファイルの `#print axioms` で 188 宣言を確認した。依存公理は `propext`、`Classical.choice`、`Quot.sound` のみ。新規本体の sorry・admit・独自公理は各 0。
- 新規モジュールから本体の 311 モジュールをたどり、E3 界面と `InfinityCategories` に到達する経路は 0。既存の本体宣言の変更と、⑤a とのパスの重複も 0。

### 残り

- コホモロジー上の cup 積の次数付き可換性 `cohomologyCup_comm`。次数 0 の場合は頂点での値が一致することから示せる。正次数同士は cup₁ の余鎖ホモトピーと余境界への降下が残る。A0 の余積性と site の大域切断との比較は草稿に残る。
- 段 1 の途中経過であり、停止点 1 の検収は残る宣言を閉じた後に行う。

### 取り込み時の登録対象

以下の 37 本。うち 27 本は先に報告済み。

```text
SerrePositivity.BhattScholze.Delta.DividedPower.FreeDP
SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBaseChange
SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBasis
SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPFactorial
SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction
SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeMaps
SerrePositivity.BhattScholze.Prismatic.AffinePolynomial
SerrePositivity.BhattScholze.Prismatic.CompletedFreeDelta
SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaBounds
SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaFlat
SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaResidue
SerrePositivity.BhattScholze.Prismatic.Envelope
SerrePositivity.BhattScholze.Prismatic.PrismOver
SerrePositivity.BhattScholze.Prismatic.VariableEnvelope
SerrePositivity.CommutativeAlgebra.DeRham.CompletedCoefficient
SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
SerrePositivity.CommutativeAlgebra.DeRham.CompletedLeibniz
SerrePositivity.CommutativeAlgebra.DeRham.CompletedWedge
SerrePositivity.CommutativeAlgebra.DeRham.Graded
SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCompletion
SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty
SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein
SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinCochains
SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology
SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
SerrePositivity.HomologicalAlgebra.Cosimplicial.CupLeibniz
SerrePositivity.HomologicalAlgebra.Cosimplicial.CupProduct
SerrePositivity.HomologicalAlgebra.Cosimplicial.Homotopy
SerrePositivity.HomologicalAlgebra.Cosimplicial.PrincipalShortExact
SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
SerrePositivity.HomologicalAlgebra.Cosimplicial.ShortExact
SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve
SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue
```

## BS-D68 停止点 1（2026-11-07）

### 実装

- main `faad868f1` を fast-forward で取り込み、調整役による段 1 の 37 モジュールの登録を反映した。その後 main `5697b7aa3` を `c7189ac10` で取り込んだ。
- `c21600ff1` で `SerrePositivity.Cosimplicial.cohomologyCup_comm` を草稿と同じ型で証明した。非正規化余鎖の cup 積は、コホモロジー上で `(-1)^(m*n)` を伴って可換になる。
- KST の正規化 EZ で shuffle 積を経由する場合、現在の非正規化余鎖への正規化比較と双対化が要る。今回は KST の非正規化 Alexander–Whitney 鎖写像と標準単体の収縮を再利用した。AW 対角と符号付き交換後の対角の差を標準単体上で帰納的に埋め、余輪体に評価して余境界とした。これで正規化比較と明示的な cup₁ の面演算子の計算を省ける。KST の参照は完全修飾とし、KL-W1 の移動後は改名表で追従する。

### 検収

- 段 1 の全 38 モジュールの対象ビルドが、`with_build_lock.sh --wait 1800` で成功した。
- 一時ファイルで段 1 の 188 宣言を監査した。使用公理は `propext`、`Classical.choice`、`Quot.sound` のみ。追加公理と `sorryAx` は 0 件。
- 追加の本体宣言は上記の定理。既存の本体宣言の変更なし。対象の推移的 import に `InfinityCategories` と `PerfectoidizationInterface` はなく、⑤a との変更ファイルの重複もない。

### 取り込み時の追加登録対象

```text
SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCommutativity
```

## BS-D68 段 2 途中報告（2026-11-07）

### Lemma 5.4 の基底分解

`8041cbd6b` で `PolynomialFrobeniusCech` を追加した。既存の `polynomialExpandBasis` は任意の変数集合に対して有限台指数の余りを添字に持つ。この基底を項ごとに底変換し、頂点別に並べ替えた。有限変数と無限変数に同じ分解が使える。

| 宣言 | 内容 |
| --- | --- |
| `polynomialCech` | 多項式の Čech 余脈体。各頂点に変数の copy を置く。 |
| `relativeFrobeniusCech` | 係数を保ち変数を p 乗する `MvPolynomial.expand` の自然変換。 |
| `vertexRemainderEquiv` | 指数の余りを頂点ごとの有限台指数と同一視する。 |
| `vertexRemainderEquiv_apply` | 頂点別表示での指数の評価式。 |
| `vertexRemainderEmbed` | 頂点の単射に沿って指数を移す。 |
| `vertexRemainderEmbed_apply_image` | 単射の像では元の指数を保つ。 |
| `vertexRemainderEmbed_apply_of_notMem` | 単射の像の外では指数は零。 |
| `rename_monomial_vertexRemainderEmbed` | 単射に沿う多項式の `rename` を余り指数で計算する。 |
| `vertexRemainderEquiv_succAbove` | 余面で新しい頂点に零指数を挿入する。 |
| `frobeniusPushoutRepr` | 相対 Frobenius に沿う押し出しの各項を、頂点別の余り指数を添字とする自由和に分解する。 |
| `frobeniusPushoutRepr_inl` | 左からの包含は全頂点の指数が零の成分に入る。 |
| `frobeniusPushoutRepr_coface_single` | 余面は係数に N の余面を施し、添字に零指数を挿入する。 |

### 検収と残り

- 新規モジュールの鍵付き対象ビルドが成功した。一時監査の 12 宣言は標準三公理のみ。追加公理と `sorryAx` は 0 件。禁止依存と⑤a との変更ファイルの重複はない。
- Lemma 5.4 の次の作業は全零添字の成分を分離し、それ以外を収縮すること。非零の添字では、最初の非零頂点の直前の零頂点を削り、係数には隣接頂点を併合する余退化を使うと、対応する余面の項が符号つきで打ち消し合う。ここから有限・無限変数の両宣言を閉じる。結晶の橋と余分な δ 座標の収縮はその後。

### 段 2 の取り込み時の登録対象（現時点）

```text
SerrePositivity.BhattScholze.Prismatic.PolynomialFrobeniusCech
```

## BS-D68 段 2 継続（2026-11-07）

作業開始前に、調整役による停止点 1 と `PolynomialFrobeniusCech` の登録（`49d0ca4f1`）を含む main `f261f37cf` を取り込んだ。

### Lemma 5.4

- `deedbbd11` で無限変数の `frobeniusTwist_cech_quasiIso_infinite` と有限変数の `frobeniusTwist_cech_quasiIso` を、草稿と同じ型で証明した。
- 全零添字への射影は余鎖写像になる。残りの成分では、最初の非零頂点の直前の零頂点を削り、係数にはその位置の余退化を符号付きで施す。余面との合成で恒等項が一つ残り、ほかは対消滅する。有限変数版は任意の変数集合での証明の特殊化。
- 鍵付き対象ビルドは成功。一時監査の 2 宣言は標準三公理のみ。

### 結晶の橋の構成

- `92012213f` で `crystallineBasePrism`（生成元 p の ℤₚ の prism）、`cartierBaseEquiv`（剰余と ℤ/p の同型）、`modPrimeCosimplicial` と `modPrimeMap`（各項の p による商）を追加した。`htCech` と `htRings` は affine 模型の余単体的代数と台環、`htBase` と `htGenerator` は基底射と選択生成元、`reducedModel`、`htResidueIso`、`htSec` は剰余模型とその座標を与える。
- `8f1e35778` で `deltaAdjoinDivisionBaseChange_isPushout`（δ 除算関係式の商と通常の底変換）、`crystallineFreeDivisionEquiv`（差の p 除算と自由 δ 環の同型）、`crystallineModPrime_isPushout`（mod p が押し出しを保つこと）を追加した。
- `crystallineTensor_isSMulRegular` は p 完全平坦な底変換での p 正則性を示す。`crystallineCompletelyFlat_frobenius` は剰余が多項式環の場合の Frobenius の p 完全平坦性を与える。`crystallineCompletedFreeDelta_primeRegular` と `crystallineCompletedFreeDeltaResidue` は完備自由 δ 環の正則性と剰余の多項式表示を与える。
- `crystallineCechSource` は完備自由 δ Čech 余脈体。`deltaCoordinatesModP` は多項式 Čech 余脈体の変数を affine 模型の剰余の反復 δ 座標に送る。`crystallineDivision_isPrismaticEnvelope` は生成元 p の基底上の古典的完備 δ 除算の普遍性を示す。`pdDeltaTerm`、`pdDeltaModel`、`pdDeltaRings` は結晶側の完備 p 除算模型を与える。これらの型を保ち、実装には古典的 p 完備化を用いた。
- 二つの束の鍵付き対象ビルドは成功。一時監査はそれぞれ 22 宣言、49 宣言で、標準三公理のみ。追加公理と `sorryAx` は 0 件。禁止依存、既存の本体宣言の変更、⑤a との変更ファイルの重複はない。


### 橋の自然変換と剰余

- `crystallineBridge` は、Frobenius で差が p で割り切れることから、affine envelope の普遍性で構成した自然変換。 `crystallineBridge_generator` は生成元の像が p であることを示し、`crystallineBridgeModP` はその剰余写像。
- `crystallineCechResidueIso` は、完備自由 δ Čech 余脈体の剰余を多項式 Čech 余脈体と同一視する。`crystallineDivisionCompletionModPrimeEquiv` は、p 正則なときに完備 p 除算と未完備の関係式の商の剰余を同一視する。`deltaAdjoinDivisionBaseChange_isDeltaHom` は、係数の底変換が δ 構造を保つことを示す。
- 鍵付き対象ビルドは成功。一時監査の 11 宣言は標準三公理のみ。そのうち 3 宣言は前回監査済み。

### Frobenius の押し出しと分冪模型

- `crystallineAffineDivision_primeRegular` と `crystallineAffineFrobeniusDivision_primeRegular` は、差とその Frobenius 像の p 除算で p 正則性を保つ。`crystallineCompletedDivision_modPrime_isPushout` は、これらの正則性の下で完備模型の剰余に押し出しを移す。
- `crystallineAffineUnitModP` と `crystallineCechResidueIso_hom_deltaCoordinates` は affine への標準射を剰余の多項式座標と照合する。`crystallineCechResidueIso_frobenius_app` は剰余 Frobenius を相対 Frobenius と照合する。
- `pdDelta_modP_frobeniusPushout` は結晶の橋の mod p を Frobenius 押し出しの左脚と同定する。`crystallineBridgeModP_isCohomologyIso` は無限変数の Lemma 5.4 から橋がコホモロジー同型であることを示す。
- `pdRawModel` は頂点差の線形写像から未完備の pd Čech 模型を構成する。`crystallineAddSplitCech_equiv` は任意の余単体的代数に切断付き Čech 因子を加える余鎖ホモトピー同値を与える。
- 鍵付き対象ビルドが成功。一時監査の 20 宣言は標準三公理のみ。追加公理と `sorryAx` は 0 件。禁止依存、既存の本体宣言の変更、⑤a との変更ファイルの重複はない。
- 残りは、結晶模型を pd 模型と正の反復 δ 座標の多項式 Čech 因子に分離し、`pdInclusionModP_isCohomologyIso` に収縮を適用すること。

### 余分な δ 座標の比較の準備（2026-11-08）

- `principalCompletionRingFunctor` と `principalCompletionUnder` は主完備化の H⁰ を可換環と係数環つきの可換環に施す。`pdTerm` と `pdModel` は未完備 pd Čech 模型を項ごとに完備化した模型。
- `crystallinePDRawComparison` は未完備自由 δ 環で先に p 除算しても完備結晶模型の剰余が変わらないことを示す。`crystallineRawCoordinateEquiv` は未完備自由 δ 環を基点の座標、頂点差、正の反復 δ 座標に分ける。
- 鍵付き対象ビルドは成功。一時監査の 16 宣言は標準三公理のみ。余分な座標を分離する同型とその自然性は引き続き証明中。

- `crystallineExtraCechPolynomialIso` は切断付き Čech 余脈体を、各頂点の高次 δ 座標の多項式環と同一視する。`withExtraCoords` はこの余脈体を pd 模型に加えた完備模型。`insertPdFactorModP_isCohomologyIso` は、その包含の mod p のコホモロジー同型を与える。
- `crystallinePDRawToTarget_isIso_modPrime` と `crystallinePrincipalCompletionUnit_isIso_modPrime` は、未完備模型から結晶側の完備模型への射と主完備化の単位が剰余で同型であることを示す。追加の鍵付き対象ビルドと 15 宣言の一時監査が通り、標準三公理のみを使用した。

## BS-D68 停止点 2（2026-11-08）

### 実装

| 宣言 | 内容 |
| --- | --- |
| `frobeniusTwist_cech_quasiIso_infinite`、`frobeniusTwist_cech_quasiIso` | 全零添字を分離し、残りを符号付き余退化で収縮する。任意変数の証明から有限変数版を得る。 |
| `pdDelta_modP_frobeniusPushout` | 結晶模型の mod p を相対 Frobenius に沿う押し出しと同一視し、左脚を橋と照合する。 |
| `crystallineBridgeModP_isCohomologyIso` | 無限変数の Lemma 5.4 を押し出し表示に適用する。 |
| `crystallineRawPDFactor`、`crystallineRawPDSplit` | 未完備結晶模型を階乗部分環で表し、自由分冪因子と高次 δ 座標の多項式因子に分離する。 |
| `crystallineExtraTermIso` | 高次座標の Čech 因子との余積を、通常のテンソル積と同一視する。 |
| `splitDeltaCoordinatesModP` | 基底、通常の頂点座標、高次座標で自然性を確認し、結晶模型の剰余を分離する。 |
| `pdInclusionModP_isCohomologyIso` | 高次座標を零に評価する切断から、pd 因子の包含が mod p のコホモロジー同型を誘導することを示す。 |
| `pdInclusion`、`pdInclusionModP_eq_modPrime` | 比較を整係数の完備模型へ延長し、その還元が mod p の包含に一致することを示す。Bockstein 照合に使える。 |

- D68 の分離同型は mod p で構成した。整係数では比較射とその還元との一致を閉じた。整係数の分離同型 `splitDeltaCoordinates` と整係数の擬同型 `extraCech_comparison` は D69 向けの草稿に残る。
- 実装の最終コミットは `bb7ca252c`。Lemma 5.4 は `deedbbd11`、結晶の橋の同型は `a8eb0a7a3`、完備 pd 模型は `4388fc197`、切断付き高次座標模型は `480cf572f`。

### 検収

- `with_build_lock.sh --wait 1800` で新規 33 モジュールの対象ビルドが成功。整係数の比較射と main に登録済みの `PolynomialFrobeniusCech` も対象に加えてビルドし、段 2 の検収対象は計 35 モジュール。
- 鍵付きビルドの成果物で一時監査を実行した。150 宣言は `propext`、`Classical.choice`、`Quot.sound` のみを使用。追加公理と `sorryAx` は 0 件。
- 推移的 import を調べ、`InfinityCategories` と `PerfectoidizationInterface` への依存がないことを確認した。既存の本体宣言の変更はなく、⑤a との変更ファイルの重複もない。
- 段 3 は pd de Rham 双複体の二つの射影、有限多項式 Cartier 同型、生成元と Bockstein の照合。

### 取り込み時の登録対象

main に登録済みの `PolynomialFrobeniusCech` に加え、次の 34 モジュールを登録する。

```text
SerrePositivity.BhattScholze.Delta.Division.BaseChange
SerrePositivity.BhattScholze.Prismatic.CrystallineAffineDivision
SerrePositivity.BhattScholze.Prismatic.CrystallineAffineEnvelope
SerrePositivity.BhattScholze.Prismatic.CrystallineBase
SerrePositivity.BhattScholze.Prismatic.CrystallineBridge
SerrePositivity.BhattScholze.Prismatic.CrystallineBridgeCoordinates
SerrePositivity.BhattScholze.Prismatic.CrystallineBridgePushout
SerrePositivity.BhattScholze.Prismatic.CrystallineCechResidue
SerrePositivity.BhattScholze.Prismatic.CrystallineCechSource
SerrePositivity.BhattScholze.Prismatic.CrystallineCompletedFreeDelta
SerrePositivity.BhattScholze.Prismatic.CrystallineCompletedPushout
SerrePositivity.BhattScholze.Prismatic.CrystallineCoordinates
SerrePositivity.BhattScholze.Prismatic.CrystallineDivisionCompletion
SerrePositivity.BhattScholze.Prismatic.CrystallineDivisionEnvelope
SerrePositivity.BhattScholze.Prismatic.CrystallineExtraContraction
SerrePositivity.BhattScholze.Prismatic.CrystallineExtraModel
SerrePositivity.BhattScholze.Prismatic.CrystallineExtraPolynomial
SerrePositivity.BhattScholze.Prismatic.CrystallineFreeDivision
SerrePositivity.BhattScholze.Prismatic.CrystallinePDInclusion
SerrePositivity.BhattScholze.Prismatic.CrystallinePDIntegral
SerrePositivity.BhattScholze.Prismatic.CrystallinePDModel
SerrePositivity.BhattScholze.Prismatic.CrystallinePDRawComparison
SerrePositivity.BhattScholze.Prismatic.CrystallinePDTensorPresentation
SerrePositivity.BhattScholze.Prismatic.CrystallinePrincipalResidue
SerrePositivity.BhattScholze.Prismatic.CrystallineRawCoordinates
SerrePositivity.BhattScholze.Prismatic.CrystallineRawPDFactor
SerrePositivity.BhattScholze.Prismatic.CrystallineRawPDSplit
SerrePositivity.BhattScholze.Prismatic.CrystallineReductionPushout
SerrePositivity.BhattScholze.Prismatic.CrystallineTensorRegularity
SerrePositivity.BhattScholze.Prismatic.FrobeniusCechComparison
SerrePositivity.BhattScholze.Prismatic.HodgeTateAffineModel
SerrePositivity.BhattScholze.Prismatic.PDCompletedCech
SerrePositivity.BhattScholze.Prismatic.PDPolynomialCech
SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
```

## BS-D68 段 3 の途中（2026-11-10）

main の `ba84f342e` を `math/bs-d68` に fast-forward してから着手した。

| 宣言 | 内容 |
| --- | --- |
| `pdRawCoefficients`、`pdRawChange`、`pdRawBasis`、`pdRawCoefficients_repr` | 未完備 pd Čech 模型の係数変換を作り、余面・余退化との可換性と単項式基底での係数ごとの表示を示す。 |
| `pdModel_modP` | 完備 pd Čech 模型の剰余と、標数 p の係数上の完備 pd 模型を自然に同一視する。 |
| `freeDPDerivation`、`freeDPDerivation_dp_succ`、`freeDPDerivation_ext`、`freeDPPartial`、`freeDPPartial_dp_succ`、`freeDPPartial_comm` | 平方零拡大で分冪導分を作り、分冪での値と偏微分の可換性を示す。 |
| `pdCoordinates`、`pdRawPartial`、`pdRawPartial_comm`、`pdRawPartial_dp_succ` | 第 0 頂点と差座標での偏微分を二つのテンソル因子から作る。 |
| `CompletedRing`、`principalCompletionLinearMap`、`principalCompletionLinearMap_unit`、`principalCompletionLinearMap_comp` | 係数線形写像を主完備化に延長し、単位と合成との両立を示す。 |
| `pdRow`、`pdRow_contractible` | 頂点の微分形式による余単体的な行を定義し、正次数の行を切断付き Čech 余脈体のホモトピーで収縮する。 |
| `pdVerticalD`、`pdVerticalD_sq`、`pdDeRhamColumn` | 完備偏微分と左外積から列微分を作り、その平方が零であることを示す。 |
| `cochainNatTensorSigns`、`bicomplexRow`、`totalToRowZero`、`totalToColumnZero` | 横微分の符号を正、縦微分を横次数で符号付けし、総複体から両軸への余鎖写像を作る。 |
| `deRhamTerm`、`deRhamTerm_d`、`deRhamClass`、`cartierZero_closed`、`cartierOne_closed`、`cartierZeroClass`、`cartierOneClass` | 通常の多項式 de Rham 複体で `f^p` と `X^(p−1)dX` の閉形式とコホモロジー類を作る。 |
| `formVars`、`affineForms`、`affineCoordinateIso`、`affineCoordinateIso_X`、`affineFormsModule`、`degreeZeroForm`、`affineD`、`affineWedge` | affine 模型の完備形式と次数零の係数環を、変数の宇宙をそろえて定義する。 |
| `cartierCompletedFormsIso`、`cartierCompletedFormsIso_unit`、`cartierCompletedFormsIso_wedge`、`cartierFormsIso` | 標数 p の完備形式と通常の形式を同一視し、完備化単位および外積との両立を示す。 |
| `zeroCocycleRing`、`cohomologyZeroAddEquiv`、`cohomologyZeroAddEquiv_mul`、`cohomologyZeroCommRing`、`cohomologyZeroRingEquiv` | 零次コホモロジーを二つの余面の等化部分環で表し、その積を cup 積と照合する。 |
| `hodgeTateCohomology'`、`bockstein`、`htSecZero`、`hodgeTateMapZero` | affine 模型の mod d コホモロジーと Bockstein、次数零の Hodge–Tate 写像を定義する。 |
| `delta_cochainDifferential_eq_cup_sq`、`cupBockstein_cup_sq_two` | 素数 2 では一次余輪体 `b` の cup 平方は `δ(b)` の余境界。Bockstein の零次からの像へ適用する。 |

- 実装コミットは `44cf577fc`。新規 14 モジュールは `with_build_lock.sh --wait 1800` で対象ビルドに成功し、一時監査は 369 宣言で標準三公理のみ。追加公理と `sorryAx` は 0 件。新規モジュールから E3 と E∞ への推移的 import がなく、⑤a との変更ファイルの重複がないことを確認した。
- 残りは列微分と余単体構造射の可換性、列の pd Poincaré 補題と両射影の擬同型、総複体の積と Bockstein の比較、有限変数の Cartier 同型、η¹ と外積への延長、生成元での照合。目標の二定理は草稿に残っている。
- 停止点 3 の取り込み対象はこの段の完了時にまとめる。この時点の登録候補は `git diff --name-only --diff-filter=A ba84f342e..44cf577fc -- SerrePositivity` の 14 本。

### 段 3 の続き

- `d2eaea838` で `pdDeRhamDifferential` の自然性、`pdDeRhamDoubleComplex`、`pdDeRhamTotal`、`pdDeRhamRowZeroProjection`、`pdDeRhamColumnZeroProjection` を閉じた。連鎖律は、未完備模型の多項式座標と分冪座標で確認してから、主完備化単位上の値で完備模型へ移した。
- `pdRawDerivation` は未完備偏微分の導分則、`pdCoordinateBasis` は第 0 頂点と差座標の微分形式の基底。`principalCompletionLinearMap_ext` と `completedRing_isModuleComplete` はその完備化に使う。
- `totalComponent` と `componentAt` で総複体の成分を取り出し、`totalComponent_ext_zero` で全成分による判定を示した。`totalD_component_succ`、`totalD_component_zeroLeft`、`totalD_component_zeroRight` は二重次数での総微分の成分式。
- `freeDPPartial_monomial`、`freeDPIntegral`、`freeDPPartial_integral` で分冪偏微分と指数を上げる積分を照合した。`exteriorContract` と `exteriorContract_wedgeOne` は外冪に制限した左内部積と、その一次外積に対する公式。
- `polynomialCartierKernel` と `polynomialCartierCokernel` は一変数多項式の微分の核・余核の線形同型。`polynomialCartierRepresentative` と `polynomialCartierExtract` は余核の代表を作る写像とその係数抽出で、`polynomialCartierExtract_representative` と `polynomialCartierExtract_ker` で照合した。
- 新規 19 モジュールの鍵付き対象ビルドが通り、一時監査の 591 宣言は標準三公理のみ。追加公理と `sorryAx` は 0 件。新規モジュールの推移的 import に E3 と E∞ が入らないことを確認した。⑤a の段 1 を取り込んだ main `287fb6e70` を専用枝に取り込んだ。
- 次は正次数の行の収縮から第 0 行への射影の擬同型を示し、分冪積分と外冪の内部積から各列の pd Poincaré 収縮を組む。第 0 列への射影の擬同型と積、有限多変数の Cartier 同型、η¹ と外積への延長、生成元の照合は引き続き必要。
