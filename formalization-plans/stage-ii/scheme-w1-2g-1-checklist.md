# SC-W1 2g-1：主項目の ID 台帳

2026-11-14。main の lane-goals-2026-11-14.md の進捗表示に合わせ、既に報告した型と段 0 の未完の出口へ安定した ID を付ける。ID は宣言数でなく主たる構成・定理の項目に付ける。既存構成の法則・係数移送・合成・貼り合わせ・証明分割は数えず、型は実装記録へ記す。初期の経路に対する独立した追加項目は A01・A02 と、境界調査で特定した未実装の候補 C01 の三つとして区別する。G0 の完了済みの準備はこの 2g-1（G1・G2）の台帳と別計上。

一覧：済み 7／全体 12（うち追加 3）

| ID | 型・出口 | 状態 | 追加 |
| --- | --- | --- | --- |
| A01 | exists_valuation_specialization_diagram：任意の特殊化を同じ剰余体の付値部分環で実現する | 済、b0b7c9234 | 追加 |
| A02 | IsSchemeVCover.liftsSpecializations：付値判定から特殊化の鎖の同時持ち上げ | 済、b0b7c9234 | 追加 |
| A03 | exists_admissible_flat_strictTransformπ_finiteType_affineBase：Noether アフィン基底上、稠密正則主開で平坦な有限型射の平坦化中心 | 済、今回の対象と入口で検証 | |
| A04 | strictTransformπ_surjective_of_vCover：Noether 基底上の有限型 v 被覆の狭義変換の全射性 | 済、今回の対象と入口で検証 | |
| A05 | exists_fppf_blowup_refinement_vCover_affineNoetherianReduced：被約 Noether アフィン基底の fppf–blowup 細分 | 済、今回の対象と入口で検証 | |
| A06 | exists_fppf_proper_refinement_vCover_affineNoetherian：任意の Noether アフィン基底の fppf–proper 細分 | 済、今回の対象と入口で検証 | |
| A07 | Rydh 3.10 の affine 版：任意の affine 基底、有限表示の v 被覆の fppf–proper 細分 | 未完 | |
| C01 | 被約環の単射整拡大で、拡大環の極小素イデアルの集合を準コンパクトにする供給 | 済、C01.1〜C01.3 の対象と入口ビルドで検証 | 追加 |
| B01 | 有限表示の固有射の、有限型 F_p 上のモデルと実際の pullback 比較 | 未完 | |
| B02 | 固有性・全射性・有限個の細分の射と可換式を同じ有限段へ降ろす | 未完 | |
| B03 | Lemma 2.12 の affine v 被覆の有限型 F_p の被覆モデルの図式 | 未完 | |
| B04 | 被覆モデルの filtered 余極限、affine conerve の面・退化・増大写像との整合性 | 未完 | |

各主項目の詳しい仮定・結論と、補助法則・分割の型は scheme-w1-2g-1-report.md と実際のソースに記録する。A07 は A06 だけで完了扱いにしない。B01 の有限表示対象のモデルを単なる射の因子化で代用しない。B02 では基底への写像の忠実平坦性を仮定しない。新しい独立な構成・定理、まとまりの外、外枠に届くときは台帳を勝手に小さく作り替えず報告する。

2026-11-14 の境界調査：C01 は必要性を特定した追加候補として全体・追加に計上した。着手の承認や完了を意味しない。新しい独立構成に当たるため、この線の Lean を止め、2h の段 0 を紙で記録した。

2026-11-14 の再開：main の scheme-w1.md の追記で C01 の着手が承認された。BS17 §2 の事前照合により条件 (b) を選び、C01 の子 ID と見込みを scheme-w1-2g-bs17-reduction.md に記録して再開。前の追加判断待ちの記録はこれで更新する。
