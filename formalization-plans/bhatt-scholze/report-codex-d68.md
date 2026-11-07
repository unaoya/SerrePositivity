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
