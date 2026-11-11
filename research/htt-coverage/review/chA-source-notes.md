# 付録 A の原典に関する注意

2017-04-09 版（SHA-256 は `../toc.md`）。下記は PDF の画像でも確認した。原文を別の主張に読み替えて一致件数を増やさず、`chA.csv` の理由に従って判定した。頁は印刷頁。

| 番号 | 頁 | 原文と照合上の扱い |
| --- | ---: | --- |
| A.1.5.11 | 806 | 結論で `X′→X` を作る一方、続く compact 性の文は `X` を主語にする。`X′` に読み替えた小対象補題とは数えず、指定 S-tree の再構成と比較がないため none。 |
| A.2.9.10 | 836 | matching object を colimit と呼び、非同型の incoming direct arrows を使う。A.2.9.7 の matching の limit と同じ式ではない。latching へ読み替えず none。 |
| A.2.9.19 | 841 | (WF) の直前では fibration の iff とするが、(WF) 自体は相対 matching map が trivial fibration となる条件。通常の trivial-fibration の定理へ読み替えず、その assertion を一致部分から除外。自然数次数が全単射の Reedy 構造について (C)(F)(W)(WC) を与える成分だけを partial/component とした。 |
| A.3.5.10 | 895 | 表示式は `colim χ ≃ C[W⁻¹]` だが、続く主語は局所化前の `C`。局所化後の圏に読み替えず、指定された enriched filtered localization と模型の比較もないため none。 |
| A.3.7.7 | 912 | 同値の iff の後で挙げる only-if/if の方向名は、引用された A.3.1.12 から直接得られる向きと逆になる。方向名を補正して使わず、一般の二模型の基礎準圏の比較と simplicial Quillen 同値の鎖の両方が未供給のため none。 |

A.2.7.4 と、SSet を補助模型とする partial 行では、`SerrePositivity/InfinityCategories/ModelBridge/Inputs/KanQuillen.lean` の `kanQuillenModel` も読んだ。これは `kanQuillen_model_exists` の `sorry` による文献入力を選ぶ局所的な定義で、証明済みの具体的 instance として数えていない。positive の証拠に載せた宣言自体は、明示した抽象模型の仮定の下で追加公理なしに検査を通った。
