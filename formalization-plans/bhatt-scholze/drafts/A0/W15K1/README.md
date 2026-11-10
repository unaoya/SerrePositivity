# BS-W15 停止点 1 の監査

K1 の証明は本体へ移した。`AuditK1.lean` は対象ビルド後に共有ロックの下で `lake env lean` に渡す監査案。公開 65 宣言について `#print axioms` と `#print sorries` を実行する。入口とリポジトリの監査への登録は調整役が行う。
