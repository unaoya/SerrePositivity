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
- `existsUnique_completedFreeDeltaHom` は両座標で完備な δ 環への射を基底射と初期座標で一意に定める。
- `isPrismaticEnvelope_variableSubstitution` は候補環で基底生成元が正則なら、指定座標をその生成元倍へ送る置換が envelope の普遍性を満たすことを示す。
- `cechAlexanderOfAffineTerms` は各次数の affine envelope から頂点写像を構造射へ延長し、恒等射と合成を証明する。`polyCosimplicialAlgebraOfAffineTerms` はこの模型の台の基底代数を取る。
- `completedDeRhamD_wedge` は完備微分と外積の Leibniz 則。完備形式の純テンソルに還元し、完備係数上では連続な線形写像の一意性で通常の Leibniz 則から移す。

### ビルドと監査

- main `4fbd8c0b7` を含む時点で新規 27 モジュールの鍵付き対象ビルドが成功した。ビルド成果物に対する一時監査では 153 宣言を確認し、依存公理は Lean 標準の範囲内。
- 追加の登録対象は `SerrePositivity.BhattScholze.Prismatic.CompletedFreeDelta`、`SerrePositivity.BhattScholze.Prismatic.VariableEnvelope`、`SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeMaps`、`SerrePositivity.CommutativeAlgebra.DeRham.CompletedLeibniz`。先の 27 本と合わせて調整役に引き渡す。

### 残り

- 候補環での基底生成元の正則性、商の有界 p ねじれ、完備平坦性を示し、変数 envelope の存在定理を閉じる。差座標の変換、濃度評価、剰余環への構造射を組み立てて、各次数の affine envelope と `polyCosimplicialAlgebra` を得る。
- de Rham の dg 代数としての普遍性と、コホモロジー上の cup 積の次数付き可換性。
