# HA の方向で CAlg(D(R)) を作る場合の不足項目

照合範囲は §2.0–2.1、§3.1–3.2、§4.1.7、§4.5.4。番号は HA 2017-09-18 版による。

| HA | 新しく必要な宣言 | 現在使える部品と適用範囲 |
| --- | --- | --- |
| 2.0.0.2–.7、2.1.1.10 | 有限基点付き集合の圏とその nerve、active・inert の分解、Segal 条件を持つ ∞ オペラッド、余デカルト射による対称モノイダル ∞ 圏 | Mathlib の `typeToPointed` は基点を付ける。SerrePositivity の余デカルト・ファイブレーションと底変換を使える。Fin∗ の射や operadic Segal 条件が必要。 |
| 2.1.1.23、2.1.2.7、2.1.3.1 | 色付き単体オペラッドの作用素圏と operadic nerve、inert 保存写像、指定した底上の `Alg`・`CAlg` | Mathlib の `SimplicialNerve` と SerrePositivity の `relativeFunctorSpace` はそれぞれ nerve と底上の関手空間を与える。§2.1.3.7 の `cocartesianRelativeFunctorSpace` は余デカルト辺を保つ関手の充満部分複体を与える。作用素圏と inert 保存による代数の部分圏が必要。 |
| 4.1.7.4、4.1.7.6 | テンソルと両立する ∞ 局所化の普遍性、D(R) に入る対称モノイダル構造 | モデル圏の hammock 局所化と `tensor_isCofibrant` が使える。Mathlib の `LocalizedMonoidal` は通常圏の局所化を扱う。モノイダル ∞ 圏としての比較が必要。 |
| 3.1.3.5、3.1.3.13（§3.1.1–3.1.2 が前提） | operadic 余極限、operadic 左 Kan 拡張、代数の制限の左随伴、演算空間を添字とする対称冪と自由性の判定 | 準圏の相対余極限・相対左 Kan 拡張と、dg の `freeAlgebraAdjunction`・`schurFunctor` がある。dg 版は厳密な代数と余不変量を扱う。active コンマ圏上の普遍性とホモトピー対称冪が必要。 |
| 3.2.2.5–.6、3.2.3.1、3.2.3.5 | CAlg の極限の存在と計算、色ごとの同値反映、sifted 余極限の存在と検出、presentability | 点ごとの準圏の極限・余極限や導来 ∞ 圏の presentability を使える。dg の `forget_createsLimitsOfSize`、`forget_reflectsIsomorphisms`、`forget_createsSiftedColimitsOfShape` は通常圏の忘却を扱う。局所化後の CAlg の忘却への比較が必要。 |
| 3.2.4.1–.4、3.2.4.7–.8 | 代数を表す ∞ オペラッド、点ごとのテンソル、CAlg のテンソルが余積となる定理 | 相対関手空間・指定辺による充満部分複体・ファイバー評価を使える。Mathlib の `CommMon.trivial` は通常圏で単位上の始対象を与える。段4で追加確認した `CommAlgCat.binaryCofanIsColimit`・`coe_tensorObj`・`isInitialSelf` は通常の可換R代数でtensorが余積、Rが始対象となる直接の特殊例（3.2.4.7はpartial/special）。導来∞圏のCAlgの余積とテンソルの比較は必要。 |
| 4.5.4.2、4.5.4.6–.7（厳密可換代数との比較を選ぶ場合） | Σₙ の射影モデルでの power cofibration、厳密可換代数への右移送、厳密可換代数の局所化から CAlg への標準写像と同値性 | 二項押し出し積、モノイド公理のセル条件、射影図式のモデル構造、結合 dg 代数の右移送がある。freely powered 条件と厳密可換代数の比較が必要。 |

既存の Barratt–Eccles 模型と比較する経路について、調整役の検討メモは Hinich の比較を候補に挙げている。その経路では Barratt–Eccles の admissibility・Σ-cofibrancy と、∞ 側のモナド性（根拠番号は設計側で再確認が必要）を別途確認する。§4.5.4.7 は freely powered な模型で厳密可換代数を比較する。§2.1.4 の preoperad のモデル構造は、検討メモの最小経路では省ける。

段4での番号の訂正：HA 6.2.2.14 はモナド性の定理ではなく、局所Cartesianなfibrationの相対安定化に関する系である。`St(p)` の局所Cartesian性、Ω∞の辺保存、遷移のderivativeの三結論を持ち、現状none。上のモナド性の根拠として以前この番号を記したのは誤りだった。6.2.2.16(3)はSpへの持ち上げでmonadicityを保つ系だが、一般のCAlgの忘却のモナド性とは別の主張である。
