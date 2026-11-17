# D-22：完全な冪等完備化射の双積像

## 引き継ぎ
- 現在地：D-22 完了。新規2葉は 57b4a57a4 に保存済み。Stable 集約・全体監査・指定型・禁止 import 閉包の検査も成功。
- 残り：なし。公開名の報告後、ユーザー指定に従って停止。
- 所有：Stable/RetractComplementCofiber・IdempotentCompletionDensity の新規葉、Stable 集約・監査への接続、本計画。
- 読み取り専用：F2/Idempotent/Completion と Core の充満忠実性。SConstruction を import しない。
- 既知の問題：なし。新規 sorry・公理・引用・ModelCategory 仮定なし。推移的 import に SConstruction なし。
- 本工程の完了後はユーザー指定に従って公開名を報告して停止する。

## 三段目
1. [x] Hom 完全性から補射影の cofiber の二つの分裂射を作り、交差成分を除いて双積同型を得る。
2. [x] 完備化射の全対象 retract と h の充満忠実性により補射影を始域へ戻す。
3. [x] 完全性で始域の三角形を写し、指定された d ⊕ Σd の本質像への所属を公開する。
4. [x] 自分の集約の終端後に監査を実行し、型・import 閉包を検査、限定コミットして報告。

## 構成
- 一般補題は前三角圏で成立し、補対象の選択や八面体公理を使わない。
- 補射影 q = 1 − r ≫ i の三角形から、cofiber → d と Σd → cofiber を Hom 完全性で取り、双積の四つの合成式と全体恒等式を示す。
- 主入口の仮定は指定型どおり、C・D の quasicategory 性と安定性、f の完全性と IsIdempotentCompletion のみ。
- 比較する関手は元の `(hoFunctor.map f).toFunctor` のまま保持する。

## 主要宣言
- `retractComplementCofiber_biprodShift`
- `IsExactFunctor.biprod_shift_mem_essentialImage_of_idempotentCompletion`
