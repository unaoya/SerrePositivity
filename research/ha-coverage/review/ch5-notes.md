# 第5章・序章の照合

原典は2017-09-18版。main `7bf1c5fbb` のソースを照合した。
段4の1,062項目のうち序章3件・第5章500件を完了した。残る第6章・付録A・Bの後で全体の `summary.md` を作る。

| 範囲 | own | mathlib | partial | none | unsure | 合計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0.0.0 | 0 | 1 | 1 | 1 | 0 | 3 |
| 5.1 | 0 | 0 | 2 | 61 | 0 | 63 |
| 5.2 | 3 | 0 | 13 | 158 | 0 | 174 |
| 5.3 | 0 | 0 | 5 | 76 | 0 | 81 |
| 5.4 | 0 | 1 | 6 | 81 | 0 | 88 |
| 5.5 | 0 | 2 | 9 | 83 | 0 | 94 |

第5章はown 3・mathlib 3・partial 35・none 459・unsure 0。序章はmathlib 1・partial 1・none 1。
全partial 36件を末尾追記の四分類で見直した。none 460件は引用・設計引用・同節と隣節・本体とMathlibを個別に検索し、近いソースの型との違いを記録した。§4の3′は使っていない。
対応する66宣言の型と公理、99ソースのSHA256を検証し、追加公理はない。ビルド整理券は常に1枚、保持は580秒上限。

- **twisted arrow**：HAの `[n]⋆[n]ᵒᵖ`・right fibration と、本体のKerodon規約 `[n]ᵒᵖ⋆[n]`・left fibration をopで比較した。恒等射の場合の一方向の普遍性を、全同値射の両側のiffに拡張していない。
- **bar・認識定理**：要素圏のBK bar、DK two-sided bar、厳密単体的モノイドのBMは存在する。増大Eₖ代数のBarの普遍性とは区別した。群的厳密単体的モノイドのM→ΩBMの局所化同型を、全Eₖ・全∞トポスの関手圏同値とは数えない。
- **中心・presentability**：通常の代数中心、Drinfeld中心のbraiding、accessibleな通常圏の大きなcompact生成基数は部分対応。Eₖ中心の普遍性・PrLのtensor・全加群で同時に使える基数の結論は未対応。
- **通常の可換代数**：Mathlibの `CommAlgCat.binaryCofanIsColimit` は可換R代数のtensorが余積という直接の特殊例を与える（5.3.3.7）。同じ発見により3.2.4.7もnoneからpartial/specialに訂正する。導来∞圏のCAlgのtensor・余積の比較は残る。
- **5.3.3.30の印刷**：PDFとraw抽出のどちらもψの後の述語が欠ける。直後の証明と5.3.3.31がψの同値性を明記するため、その主張として照合し、行のreasonにも欠落を記録した。
- **多様体・単位化**：局所同相の厳密微分による十分条件、compact→Hausdorffの同相判定、連続写像のcurryが部分対応。通常の非単位代数のR⊕Aによる単位化は対応するが、A∞のquasi-unitの全coherenceとは区別した。可換環のAway局所化の普遍性は可換な試験対象に限定した。
- **Ran・層・Verdier**：非空有限部分集合の集合、Vietoris有限部分集合のpreconnected性、通常のcover descentとcosheafのHom条件が部分対応。HAのRan位相との比較、hyperdescent、factorization homology、compact-support Verdier双対は未対応。KSTのSupportedVerdierはVerdier商であり、ここでのVerdier双対ではない。
- **compact support・交換**：compact supportを持つ連続写像は自明束のsectionの0単体の場合。S¹でのcompact support除去は全自由ループ空間・Hochschild比較ではない。5.5.6.17は空間値・filtered添字のKan pullback比較に限定し、任意sifted・任意∞トポスの結論を主張しない。
- **Kerodon**：宣言と検収済み表の照合でこの段の追加は8項目（全体13→21）。後半では5.5.3.12のfilteredなcoslice射影が9.1.4.16に対応する。一般補題を共有するだけの番号は加えていない。

BSの検収結果は維持する：7.1.3.18は界面で埋め込みのみ、7.2.2.10はD20のホモロジーによる定義を使うため、これらを理由とするBS側の追加作業はない。
