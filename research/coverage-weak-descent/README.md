# 弱い Coverage の空間値降下（探索の記録）

**問い。** 小さい通常の圏の弱い Coverage で、基本生成篩ごとに降下する空間値前層は生成 Grothendieck 位相の層になるか。弱い引き戻し公理は実引き戻しに入る基本細分を与える。論点は実引き戻し全体での降下。HTT §6.2.2 は Grothendieck 位相を扱う。[HTT §6.2.2](https://www.math.ias.edu/~lurie/papers/HTT.pdf)・[Gratzer の公開質問](https://mathoverflow.net/questions/515360/generalizing-a-lemma-about-covers-from-1-to-infty-topoi)

**保存先。** ローカル枝 `explore/coverage-weak-descent` の HEAD は `c35ec3618165d8f5a30a4b99cd42364b51d02e7a`。区切りは `04551724d`。詳しい経過は保存枝の `formalization-plans/stage-ii/report-bs-infinity-a1-stage0.md` にある。

**確認できたこと。** 共変表現可能な係数で極限性を検出し、基本生成篩の二項交叉降下を空間値へ帰着した。稠密な部分篩への指定右 Kan 比較は各頂点で左逆を持ち、比較の可逆性は、指定余単位を持ち上げる一つの大域射の存在と同値。底変換は、篩への制限を交叉篩への右 Kan 延長として、元の余単位と局所の輸送錐を保って計算する。

**残る入力。** 空間値の二項交叉降下、または同じ余単位を保つ大域射の構成。点ごとの左逆を大域の射として貼る整合性が要る。DHI のセル貼り合わせでは全境界を同じ被覆で扱う。Glass–Minichiello の議論を今回の弱い公理に適用するには、基本篩だけによる局所化と通常層化の単位による局所化の比較が要る。一般形の証明と反例は確認できていない。[DHI, Theorem A.6 と §A.12](https://arxiv.org/pdf/math/0205027#page=36)・[Glass–Minichiello, Propositions 4.15–4.17](https://arxiv.org/html/2602.11971v1)

**検算。**

- 三点の鎖 \(0<1<2\) で基本族を \(0\to i\) とし、対象 2 の最大篩で \(0\to2\) の主篩を含める。残る二つの表現可能を選んだ基本細分の上だけで貼ると、対象 1 で二点残る。最大篩の値は一点。欠けるのは二つの表現可能の重なりであり、この計算は素朴な押し出し表示を退ける。
- \(n\ge2\) とし、\((n+1)\) 単体の境界の空でない面の順序圏で定値 \(K(\mathbb{Z},n)\) を取る。各値は \((n-1)\) 連結だが、極限は \(\operatorname{Map}(S^n,K(\mathbb{Z},n))\) で成分集合は \(\mathbb{Z}\)。点ごとの連結度だけでは全篩の極限での成分を制御できない。

**一般の補題の候補。** `CoverageRightKanBaseChange.lean` の `isRightKanExtension_of_local_baseChange` と `CoverageRightKanIntersectionLimit.lean` の `rightKan_isLimit_iff_of_fixedConeHomotopy`。指定余単位・錐を保つ法則として検討できる。採否と配置は調整役が refactor ledger で決める。
