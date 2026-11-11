# 第6章の照合

2017-09-18版、全356件。ソースはmain `7bf1c5fbb`と同一（専用枝の後続コミットはresearch/ha-coverageのみ）。

| 範囲 | own | mathlib | partial | none | unsure | 合計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 6.1 | 0 | 0 | 18 | 114 | 0 | 132 |
| 6.2 | 0 | 0 | 1 | 136 | 0 | 137 |
| 6.3 | 0 | 0 | 4 | 83 | 0 | 87 |

計：partial 23・none 333・unsure 0。partial 23件を依頼文末尾の四分類で見直した。noneは全行に個別の検索記録を保存し、§4の3′は使っていない。

- **直接の部分対応**：powersetと二次元のpullback/pushout、懸垂による一次切除の十分条件、空間のfiltered余極限関手の全有限極限保存、Indのfiltered余極限、安定圏の双対性・懸垂比較、通常のČech EG、hCの加法性と有限双積、通常表現のnormの左右不変性、通常随伴の(余)極限保存、単体圏と同値関係のposet。
- **Taylor解析の不足**：全高次cubeの切除条件、n-excisive反射Pnと塔、Red/cored・cross-effect、homogeneous関手圏、対称multilinear関手による分類、derivative/differentialの全Map普遍性、相対安定化St(p)、coderivativeのchain ruleは未対応。既存のexact functor、coherent fiber/cofiberの族、通常のtensorや群作用は部品としてreasonに記し、これらだけから全反射が得られるとは判定しない。
- **norm/Tate**：MathlibのTate複体は群表現の鎖・余鎖をnormでつなぐ。一般stable ∞圏のホモトピー軌道から固定点へのnormとの比較はない。6.1.6.11は通常の双積の行列だけでは指定normとの同定が得られないため、見直しでnoneに下げた。6.1.6.12は独立した条件(3)の通常の双積での可逆性だけ、6.1.6.23は本文第二段落の和の左右不変性だけ。
- **番号の訂正**：6.2.2.14は局所Cartesianな相対安定化の系でありBarr–Beckではない。2017年版の∞-categorical Barr–Beckは4.7.3.5（既存の照合は通常圏版のみpartial）。E∞印は元の15件を維持し4.7.3.5にも追加した。Hinichの原論文が用いた版の番号対応は未確認。
- **予想とheuristic**：6.3.0.7・6.3.0.13は原典でもConjecture。6.3.0.6・6.3.0.10などの精密な定式化を省いた説明や文献項目も、証明済み定理の不足とは区別してreasonに記した。noneの件数をそのまま未証明の定理数と解釈しない。

全対応候補の型と公理はkernelで確認し、追加公理はない。保持時間580秒上限、--wait 3600、待つ整理券は1枚ずつとした。
