# IF-W2c 停止点 1′

静的草案、ビルド・適用 0。§5（main `8e95eff88`）を反映。**全体適用は保留**。再検査に使った [対象 JSON](w2c-combined-plan.json) と [判定記録](w2c-stop1-prime.json)。

| 模擬 | 直接禁止辺 | W2a/W2b 禁止 | affected core | 循環 |
| --- | ---: | ---: | ---: | ---: |
| 作業前 | 18 | 150 | 2,531 | 0 |
| 停止点 1 の草案 | 1 | 106 | 2,366 | 0 |
| A・A′（今回） | 0 | 74 | 1,723 | 0 |
| A・A′ ＋ 群 B の分割案 | 0 | 74 | 1,730 | 0 |
| 比較用に群 B を全て丸ごと移す場合 | 415 | 2,290 | 1,926 | 0 |

**A・A′。** SpectrumPoint は一点に関する 3 宣言を中核に残し、spectrumPoint と補助証明を KST へ split。HotA の入口 10 モジュール・13 辺を調べ、モデル側 8 ファイルを split。HA の禁止モジュールは 90 → 66。CosliceTwistedHomEquivalence はモデル側の定理を使い、ModelBridge に上げると SourceInitial・RightRepresentableTwistedArrowEquivalence・TwistedHomFunctorMap の各宣言が中核利用者として残る。これが 0 へ進むための停止条件。 [入口・経路・宣言](w2c-section5-ha.md)

**B。** 混在 367 本の丸ごとの配置は Stable 144、StablePresentable 56、Derived 167。KST に残す 211 本と R56b 一般補助 10 本（全て Derived）を別扱いにした。丸ごとの案は、KST に残る定数の実参照から禁止辺を生む。分割案では混在 367 本のうち 177 本を丸ごと移し、92 本から一般宣言を切り出し、98 本を保留。R52 は split 0。例えば VerdierFractionComparison の private fraction_ho_localization は現在の source と共に保留。 [候補ごとの根拠](w2c-b-inventory.json)・[段 G への一覧](w2c-stage-g-input.json)。

**静的検査。** 分割案の dry-run は 325 move・594 ファイル、終了 0、applied=false。116 split を snapshot で検査。validator は承認済み 26 指標のうち 14 件で exit 1。新規の増加指標 0、enforce W2b の 3 条件は PASS。基準・例外の変更 0。 [26 指標の経路表](w2c-section5-ratchet.md)。

**下流と実施順。** 逆閉包 11,152 本・129 根、既往の W2a-2 基準で約 1.85 時間。群 B を指定順に進める場合、後の群の支え 26 本について先行取り込み、または import の段階的切替が必要。内訳と利用元を判定記録に収録。§3.1 は承認待ち、下流・verify は 2a・2b 後の合図待ち。
