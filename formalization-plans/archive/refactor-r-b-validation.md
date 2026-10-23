# R-B 検証記録

## R24（2-5）

- 基準：main `c6692be81`（checkpoint からの差は計画文書のみ）。
- `lake build SerrePositivity.InfinityCategories.Stable SerrePositivity.InfinityCategories.Derived SerrePositivity.InfinityCategories.DGNerve`：成功（11,358 jobs）。
- `lake env lean scripts/audit_infinity_stable.lean`：Stable axiom audit passed: 23219 declarations in 2792 modules.
- `lake env lean -DmaxRecDepth=20000 scripts/audit_derived_infinity.lean`：D2 axiom audit passed: 22111 declarations in 2523 modules.
- `lake env lean scripts/audit_derived_gluing.lean`：D2 gluing axiom audit passed: 6513 declarations in 701 modules.
- `lake env lean scripts/audit_dg_nerve.lean`：All existing #check, #print axioms and final quasicategory examples passed (process exit 0).
- Derived 監査の通常実行は巨大な expected 配列のコード生成で既定の再帰深度上限に到達した。監査本体は変更せず、実行オプションで上限を上げて成功。
- SemifreeLimits の本文は旧所在とバイト一致（SHA-256：`50443a68f10aaf888b78d7de74cc0a173bf311d0d4f68372bef1e733744679cb`）。宣言名・型・証明を保持。
- DGNerve の全ソース・集約から Derived への直接 import はゼロ。
- main への唯一のファイル変更：個別許可された未追跡 `Derived/DGKernelDerivedMapInvertible.lean` を削除。既存 `DGKernelDerivedQuasiIsoMapInvertible.lean` と非コメントトークンが一致することを確認した（docstring のみ異なる）。
- 詳細ログ：`/tmp/r-b-r24-build.log`、`/tmp/r-b-r24-audit-{stable,derived,gluing,dgnerve}.log`。
