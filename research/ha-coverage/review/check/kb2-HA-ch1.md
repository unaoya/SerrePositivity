# KB-W2 HA 第1章

原典の版を目次記載SHA-256と照合したPDFの本文と、現在のソースの宣言の型を読み比べた。kernel実行・Lean変更・ビルド・鍵はなし。

対象245行。旧状態：{'none': 124, 'partial': 121}。新状態：{'none': 170, 'partial': 70, 'own': 5}。partial_kind：{'component': 28, 'direction': 3, 'stronger-hyp': 18, 'special': 21}。

既存own・mathlibなど対象外55行は全フィールド・引用符・改行をそのまま保存。対象行でもstatus/declarations/reason/partial_kind以外は不変。axioms/checkは旧記録であり今回のkernel確認結果ではない。

## 全対象行

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 1.1.0.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：この注記は安定モデル圏と Segal 圏の文献案内。モデル圏から準圏への比較と Segal 圏の模型を探し、安定準圏の定義と比較したが、文献案内に対応する数学的主張はない。 |
| 1.1.0.2 | partial → partial | component | KB-W2型再照合：仮定：前三角 dg 圏（Lean が弱い：体に限らず可換環上でよい）。結論：その dg nerve が安定。体上の加群スペクトルで豊穣化した安定 ∞ 圏から dg 圏を復元する逆向きと豊穣化の比較は得られない（Lean が弱い）。 |
| 1.1.1.2 | partial → partial | direction | HasZeroVertexのchosenZeroVertexは同じ準圏Cの始・終頂点を直接与え、その零頂点の恒等辺を終頂点→始頂点の証人にできる。pointed⇒原文(1)(2)(3)の向き。通常圏の零射の結果だけで逆向きを∞圏へ移したとはしない。 |
| 1.1.1.7 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：安定準圏 X（Lean が強い：HA は点付き性のみで射ごとの余ファイバーが存在する場合を含む）。結論：余ファイバー正方形から底辺への射は自明 Kan fibration で切断を持つ。安定な場合の結論と一致し、余ファイバーが一部しかない場合は扱わない。 |
| 1.1.1.8 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：安定準圏 X（Lean が強い：HA は点付きかつ余ファイバーを持てばよい）。結論：余ファイバー関手を左随伴とし、対象を零頂点からの射へ送る関手を右随伴とする（一致）。 |
| 1.1.1.11 | partial → none |  | sp_isStableはBFスペクトル模型とNativeLoopComparisonを入力する。原文の位相空間による指定Spおよび古典安定ホモトピー圏との同一視をこの型で確認しておらず、別模型の安定性だけを原文のspecialとは数えない。 |
| 1.1.1.12 | partial → partial | special | KB-W2型再照合：仮定：可換環 S と加群圏の導来圏の選択 HasDerivedCategory（Lean が強い：アーベル圏一般でなく加群圏の半自由複体模型）。結論：導来 ∞ 圏は安定で、ホモトピー圏と選んだ通常の導来圏が同値（一致）。 |
| 1.1.1.14 | partial → partial | component | KB-W2型再照合：仮定：準圏 X（HA と一致）。結論：IsStable X は Prop であり構造の選択を追加しない。注記で予告する一般の安定 ∞ 圏の標準的なスペクトル豊穣化は型に含まれない（Lean が弱い）。 |
| 1.1.2.8 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：点付き準圏で指定のループ関手が準圏同値（Lean が強い：HA は両関手が定義されればよい）。結論：懸垂を左随伴、ループを右随伴とする QCatAdjunction（一致）。 |
| 1.1.2.9 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：安定準圏 X（Lean は IsStable で仮定をまとめる。HA は点付き性・余ファイバー・懸垂同値で述べる）。結論：hX の前加法構造と有限双積（一致）。HA の仮定から IsStable への直接の比較宣言は採用した型にない。 |
| 1.1.2.10 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：安定準圏の懸垂正方形（Lean が強い：HA は点付きで余ファイバーを持てばよい）。結論：二つの零角の交換が懸垂上の負の恒等射になり、そこからの射への前合成は符号を反転する（一致する安定な場合）。 |
| 1.1.2.11 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：安定準圏 X（Lean が強い：HA の定義は点付きで余ファイバーがあればよい）。結論：hX で余ファイバー正方形から得た三角形に同型なものの集合（一致）。 |
| 1.1.2.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：HA は安定性未証明の点付き圏でも完全三角形という用語を使うと注記する。前加法性・シフトのみを仮定する比較を探したが、cofiberDistinguishedTriangles は IsStable を必要とし、Mathlib の distTriang は三角形の族を既存の構造として取る。 |
| 1.1.2.14 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：安定準圏 X（Lean は IsStable を要求。HA の表現は点付き性・余ファイバー・懸垂同値）。結論：余ファイバー三角形と整数シフトを使う hX の三角圏構造（一致）。HA の形で仮定を与える入口は型にない。 |
| 1.1.2.15 | partial → partial | direction | KB-W2型再照合：仮定：安定準圏、または点付き準圏と有限極限および指定ループ同値（逆向きは HA の懸垂・余ファイバー条件の双対）。結論：安定性から懸垂同値を得る。逆向きはループ版の安定性判定であり、懸垂版の入力から直接 IsStable を返す型は確認できない（Lean が弱い）。 |
| 1.1.2.17 | partial → partial | special | KB-W2型再照合：仮定：加群の導来 ∞ 圏と二対象（Lean が強い：一般の安定 ∞ 圏でなく可換環上の導来 ∞ 圏）。結論：Ext をシフトしたホモトピー圏の Hom で定め、写像空間のホモトピー群と比較する。一般の写像スペクトルを使う比較は含まれない（Lean が弱い）。 |
| 1.1.3.3 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：安定準圏の充満部分圏でファイバーにも閉じる、または hX の三角閉性（Lean が強い：HA は余ファイバーとシフトのみ）。結論：前者は充満部分圏の安定性、後者はシフト閉性。余ファイバーの逆シフトからファイバー閉性を導く判定は得られない（Lean が弱い）。 |
| 1.1.3.5 | partial → partial | component | KB-W2型再照合：仮定：安定準圏と二対象（HA と一致）。結論：有限積・余積の存在と、零始点の押し出しから hX の双積を作る。∞ 圏の正方形自体から余積→積の標準同値を比較する宣言は採用した型にない（Lean が弱い）。 |
| 1.1.4.1 | partial → partial | direction | KB-W2型再照合：仮定：安定準圏の間の完全関手（HA の完全⇒左・右完全の向きに一致）。結論：任意の有限極限および押し出しを保存する。右完全性を有限余極限全体で述べ、三条件の全方向をまとめた型は未確認（Lean が弱い）。 |
| 1.1.4.2 | partial → partial | special | 原文のhomotopy pullbackを現本体の標準catPullback模型として与える場合、ordinaryPullback_isStableとpullbackFst/pullbackSndは同じ圏の安定性と射影の完全性(1)(2)を直接返す。任意の指定模型への輸送と判定(3)は含まない。 |
| 1.1.4.3 | partial → none |  | 零圏への二射のcatPullbackが安定である型は、原文の指定された直積との比較同型・同値を含まない。直積への輸送を追加せず、pullbackだけを二項積のspecialと数えない。 |
| 1.1.4.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：CatEx の豊穣 nerve と exact cospan の引き戻しの安定性はあるが、CatEx 内の極限錐の普遍性と Cat∞ への包含の極限保存を与えない。引き戻し対象の安定性だけは任意小極限の存在・保存の直接の部分結論ではなく、その構成の材料なので none。 |
| 1.1.4.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：余カルテジアン族の切断の安定性と、指定辺を余カルテシアンに送る切断の安定部分圏を探した。stableFunctorCategory は定数族に相当する関手圏であり、遷移関手つきの切断を分類しない。 |
| 1.1.4.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Ind の安定性と有限極限とのフィルター付き交換を確認したが、いずれも安定 ∞ 圏と完全関手の図式の Cat∞ における余極限および完全性の保存を表す型ではない。 |
| 1.2.1.4 | partial → own |  | 同じhCのTStructureを取り、fullSubcomplexOnVerticesにt.le nおよびt.ge nをhCの頂点へ代入すれば、原文のt構造と二つの全部分準圏の定義全体を直接表す。専用のまとめた名称は不要。 |
| 1.2.1.5 | partial → none |  | 通常三角圏hCの切断とHom集合の普遍因子化は、原文のC自身の写像空間同値による局所化・∞随伴を直接返さない。hCへの射影は対象・結論を変えるのでspecial/componentと数えない。 |
| 1.2.1.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常圏では Reflective の包含が右随伴になる。両側の t 切断への所属判定と合わせて確認したが、安定 ∞ 圏の t 構造から全ての極限・余極限に対する閉性を返す型は確認できなかった。 |
| 1.2.1.7 | partial → none |  | 通常三角圏hCの切断とHom集合の普遍因子化は、原文のC自身の写像空間同値による局所化・∞随伴を直接返さない。hCへの射影は対象・結論を変えるのでspecial/componentと数えない。 |
| 1.2.1.8 | partial → none |  | 通常三角圏hCの切断関手に関する所属判定・自然同型は、原文のCの∞切断関手と同じものへの比較を持たない。hCへの射影を対象の特殊化として数えない。 |
| 1.2.1.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：HA は写像空間の切断性と t 構造の切断の違いを注意する。SSet.truncation は単体次元を制限し、TStructure.truncGE はホモトピー圏の t 切断。安定 ∞ 圏の写像空間の切断性と両者の関係を与える型は確認できなかった。 |
| 1.2.1.10 | partial → none |  | 通常三角圏hCの切断関手に関する所属判定・自然同型は、原文のCの∞切断関手と同じものへの比較を持たない。hCへの射影を対象の特殊化として数えない。 |
| 1.2.1.11 | partial → partial | component | t.heartの頂点述語を同じCのfullSubcomplexOnVerticesへ入れれば、原文のC≥0∩C≤0という同じ全部分準圏の構成成分を直接与える。πnという∞関手の構成は含まない。 |
| 1.2.1.12 | partial → none |  | AbelianSubcategory.abelianは通常三角圏内の部分圏の型。moduleHeartVertex_discは指定加群頂点の離散コホモロジー条件であり、原文の二つの心対象間の写像空間の正次数消滅とは異なる結論。C♥のnerve比較も型にない。 |
| 1.2.1.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：BBD と HA の添字の違いは TStructure.isGE_shift_iff と isLE_shift_iff の型で追える。HA が述べる添字規約間の翻訳と C♥ の同定をまとめて表す宣言は確認できなかった。 |
| 1.2.1.14 | partial → partial | stronger-hyp | 同じ辺集合SにIsStronglySaturatedEdgeSetOfShapesも与えると、そのfieldsは同じ準圏の可逆辺包含・2-of-3・pushout安定性という原文の準飽和条件を直接返す。小arrow余極限閉性を加えない全定義と最小閉包は含まない。 |
| 1.2.1.15 | partial → partial | special | C0を同じhCのt構造のt.le nの頂点で張る全部分準圏に限ると、cofiberTriangle_memとisLE₂は同じfiber/cofiber列の中項の所属を直接返す。任意のC0の定義全体と局所化の準飽和性の付記は含まない。 |
| 1.2.1.16 | partial → none |  | 通常三角圏のt構造の切断と拡大閉性は、原文の指定∞局所化Lの像と同じものであるという比較を持たない。従って(5)⇒(3)の直接の型とは数えない。 |
| 1.2.1.17 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：上下の切断関手と安定圏のループの塔を調べた。切断で定める塔のホモトピー極限に対し、安定性と t 構造、および元の圏からの完全関手を構成する型は確認できなかった。 |
| 1.2.1.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：TStructure.plus と minus は有界対象の述語を表す。左完備化の関手に制限して有界部分圏の同値を示す型を探したが、切断塔との比較は確認できなかった。 |
| 1.2.1.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：切断が零になる条件と可算積・塔の極限を調べた。t 構造が分離的である条件と左完備性を結び付ける型は確認できなかった。 |
| 1.2.1.20 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：反対圏の安定性と、通常圏の上下の t 切断を確認した。余極限で定める右完備化または左完備化との双対比較の型は確認できなかった。 |
| 1.2.2.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Mathlib はアーベル圏のスペクトル対象から系列を作る。通常のフィルター付き鎖複体の系列を HA の安定 ∞ 圏の構成に同定する比較を調べたが、この注記の特例を結ぶ型は確認できなかった。 |
| 1.2.2.2 | partial → partial | special | KB-W2型再照合：仮定：点付き準圏と有限全順序 [n]（Lean が強い：HA の I は任意の全順序）。結論：Ar の対角を零にし、順序付き三点の所定の正方形に押し出しを要求し、その充満部分複体を作る（有限の場合は一致）。 |
| 1.2.2.3 | partial → partial | component | KB-W2型再照合：仮定：安定準圏の一つの余ファイバー列（HA の隣接区間から作る列に適用可能）。結論：hC で余ファイバーから懸垂への境界射。すべての区間の境界をシフトでつないだ鎖複体と二乗零性は型に含まれない（Lean が弱い）。 |
| 1.2.2.4 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：有限全順序 [n] と安定準圏 C（Lean が強い：HA は任意の全順序と点付きかつ押し出しがあればよい）。結論：gapped 図式から始点を固定した第一行の関手圏への制限が準圏同値（有限安定な場合は一致）。 |
| 1.2.2.5 | partial → partial | component | KB-W2型再照合：仮定：点付き準圏の gapped 構成（HA の構成に対応）。結論：各 [n] の S 構成の core と、その双単体集合の対角を与える。注記の A∞ 環の加群から得る通常の K 理論との比較はこれらの型にない（Lean が弱い）。 |
| 1.2.2.6 | partial → none |  | 通常アーベル圏のSpectralObjectからの頁と微分の型は、原文の指定X∈Gap(Z,C)のπ-imageから作る同じ頁との比較を持たない。別のスペクトル対象の入力があるだけをstronger-hypと数えない。 |
| 1.2.2.7 | partial → none |  | 通常アーベル圏のSpectralObjectからの頁と微分の型は、原文の指定X∈Gap(Z,C)のπ-imageから作る同じ頁との比較を持たない。別のスペクトル対象の入力があるだけをstronger-hypと数えない。 |
| 1.2.2.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の SpectralObject の第一頁の区間ホモロジーとの同型と境界の計算はある。しかし HA の Gap(Z,C) から得る区間鎖複体に πq を適用した複体との同定はなく、異なる入力の第一頁の計算だけではこの比較を直接与えない。 |
| 1.2.2.9 | partial → partial | component | KB-W2型再照合：仮定：安定準圏と添字の nerve、またはアーベル圏のスペクトル対象。結論：N(Z) を始域とするフィルター付き対象の関手圏を取れ、別途スペクトル対象の系列はある。フィルター付き対象からその入力を作る接続が確認できなかった（Lean が弱い）。 |
| 1.2.2.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：有限 [n] の gapped 延長の頂点 fiber の可縮性はあるが、HA の整数全体に添字付けた X の延長の可縮性と、それから作るスペクトル系列の選択独立性はない。有限区間への制限だけでは整数添字の主張の特殊例にならず、延長・比較の議論が必要。 |
| 1.2.2.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：加群の導来 ∞ 圏のホモトピー圏との同値はある。整数添字のフィルター付き図式のホモトピー圏を、古典的フィルター付き鎖複体の導来圏に同定する比較を探したが確認できなかった。 |
| 1.2.2.12 | partial → partial | component | KB-W2型再照合：仮定：準圏の N(ℕ) 図式または通常圏（HA と同じ形状を取れる）。結論：各図式の余極限の存在および 1 圏で形状の全図式に対する存在を表せる。t 構造の余連結側が列の余極限で閉じるという両立条件は型にない（Lean が弱い）。 |
| 1.2.2.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：アーベル圏で列の余極限の完全性を仮定する型と、導来圏の加群ハートの埋め込みを読んだ。任意の安定 ∞ 圏の t 構造との両立からハートの余極限や πₙ の保存、完全性を導く型は確認できなかった。 |
| 1.2.2.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Mathlib のスペクトル系列の頁と次頁同型を確認し、有界フィルトレーションの場合の収束定理も探した。安定 ∞ 圏の列の余極限の π と E∞ 頁を比較する型は確認できなかった。 |
| 1.2.3.4 | partial → partial | component | KB-W2型再照合：仮定：アーベル圏の複体、下側の切断を与える形状の埋め込み（HA の非負鎖次数は非正余鎖次数）。結論：切断は境界次数で cycles を取り、内部の次数を保つ。包含の右随伴としての同定は採用した型にない（Lean が弱い）。 |
| 1.2.3.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：単体の自由鎖複体と、自然数次数の Γ を確認した。単体的アーベル群で、標準単体を境界で割ったものと一つの次数に集中した複体の Γ を比較する型は確認できなかった。 |
| 1.2.3.7 | partial → partial | component | KB-W2型再照合：仮定：冪等完備な前加法圏と有限余積（HA の同値を主張する場合に一致）。結論：Γ を逆に持つ鎖複体と単体的対象の圏同値。冪等完備性を外した場合の Γ₀ の充満忠実性は採用した型にない（Lean が弱い）。 |
| 1.2.3.8 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：前加法圏の単体的対象（Lean が強い：半単体的対象の面写像に加えて退化写像がある）。結論：微分が面写像の交代和である鎖複体（一致）。 |
| 1.2.3.10 | partial → partial | component | KB-W2型再照合：仮定：単体集合と係数（HA の ℤ を取れる。own の正規化は小さい単体集合）。結論：自由加群の交代面写像複体と、own の退化を消去した正規化複体がある。HA の Moore 正規化と退化商の比較を採用した型は明示しない（Lean が弱い）。 |
| 1.2.3.14 | partial → partial | special | A•をdg圏のDold–Kan写像単体的加群の underlying simplicial setに限れば、doldKanHomSpaceKanは原文の同じ単体集合のKan性という成分を直接返す。任意の単体的アーベル群のπnと正規化ホモロジーの比較全体はこの型には含まない。 |
| 1.2.3.16 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：Γ₀ から得た単体的対象、またはアーベル圏の単体的対象（Lean が強い：HA の任意の冪等完備加法圏の単体的対象を一つの型で扱わない）。結論：退化成分に沿う分裂と非正規化から正規化への比較。一般の冪等完備加法圏での退化商との同定は型にない（Lean が弱い）。 |
| 1.2.3.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Set 値の freeDegeneracies と augmentation はあるが Set は HA の加法的冪等完備圏ではない。加法圏値の左 Kan 拡張と C∗(A)→N∗(F(A)) の同型、および augmentation の擬同型性への比較がなく、集合値の類似構成だけでは直接対応しない。 |
| 1.2.3.19 | partial → partial | special | KB-W2型再照合：仮定：前加法的なモノイダル圏（Lean が強い：任意の多重加法関手でなく二変数テンソルに限る）。結論：左と右の各変数で零射・和を保ち、テンソルが別々に加法的（一致する特例）。 |
| 1.2.3.20 | partial → partial | special | KB-W2型再照合：仮定：前加法的なモノイダル圏（Lean が強い：一般の多重加法関手ではなく二変数テンソル）。結論：固定した対象による左右のテンソル関手が加法的で、Hom 上の写像は各変数で加法的（テンソルの場合の部分と一致。Lean が弱い：任意の多重加法関手と Hom のテンソル積を経由する写像を一括して構成しない）。 |
| 1.2.3.21 | partial → partial | special | KB-W2型再照合：仮定：整数加群の非負鎖複体二つ（Lean が強い：一般の多重加法関手ではなく二変数テンソル）。結論：全次数の直和と符号付き微分によるテンソル複体、および鎖写像への作用（この特殊例の構成と一致。Lean が弱い：任意の多重加法関手への一括拡張は含まれない）。 |
| 1.2.3.22 | partial → partial | special | KB-W2型再照合：仮定：二つの整数加群値単体的対象（Lean が強い：一般の n 変数の多重加法関手でなくテンソルの場合）。結論：前面と後面を取り全次数の分割について加える Alexander–Whitney 写像（二変数の場合は一致）。 |
| 1.2.3.23 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：二変数 AW の awFront と awBack は前後の異なる面を選ぶが、それだけでは順序交換した AW との不一致を述べない。順序依存性を示す比較または反例の宣言は確認できず、非対称な定義を依存性の証明と数えない。 |
| 1.2.3.24 | partial → partial | special | KB-W2型再照合：仮定：整数加群の単体的対象二つとそれぞれの射（Lean が強い：二変数テンソルに特化）。結論：正規化・非正規化の Alexander–Whitney 写像が各射について可換（二変数の場合は一致）。 |
| 1.2.3.25 | partial → none |  | awData_assocはdg写像の線形データ上のAW合成の結合性。原文の任意の多重加法関手の合成に沿うCh(H)の比較とAW自然変換の合成式の同じ射へ同定する型がなく、結合性だけをspecialと数えない。 |
| 1.2.3.26 | partial → partial | component | KB-W2型再照合：仮定：整数加群のテンソル（Lean が強い：一般の冪等完備な加法的モノイダル圏ではない）。結論：正規化と非正規化それぞれのテンソル比較射。一般の両関手の oplax monoidal 構造を返す型は含まれない（Lean が弱い）。 |
| 1.2.3.27 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：整数加群のテンソルと二変数の Alexander–Whitney はある。有限自由アーベル群の圏から任意の加法圏への作用と、反復した作用との可換図式の型を調べたが確認できなかった。 |
| 1.2.3.28 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：正規化 AW と shuffle の合成の一方を恒等と結ぶ normalizedEZHomotopy はある。しかし逆順の合成も恒等と結ぶ比較、または指定 AW の全ホモロジーでの可逆性を与えず、片側の homotopy retraction だけでは HA の擬同型性を直接得られない。 |
| 1.2.4.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Mathlib の Dold–Kan は単体的対象と非負鎖複体の通常圏の同値。安定 ∞ 圏に値を取る場合の、単体的対象と自然数で添字付けたフィルター付き対象の関手 ∞ 圏を比べる宣言は確認できなかった。 |
| 1.2.4.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：単体集合の骨格の列とその通常圏での余極限はある。値域が安定 ∞ 圏である単体的図式に対し、骨格ごとの幾何学的実現を対応するフィルトレーションと同定する型は確認できなかった。 |
| 1.2.4.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：前加法圏に値を取る通常の正規化関手を調べたが、安定 ∞ 圏に値を取る単体的対象の latching 射と骨格フィルトレーションの境界から得られる二つの hC の複体を同定する型は確認できなかった。 |
| 1.2.4.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：SpectralObject の第一頁の計算と normalizedMooreComplex は個別にあるが、HA の単体対象の skeletal filtration から得る第一頁・微分を πq X• の正規化複体と同定する比較はない。二つの部品が存在するだけではこの同定を与えない。 |
| 1.2.4.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：スペクトル系列の頁の零性判定はある。連結な単体的対象の実現について、第一象限と頁の安定、実現のホモトピーへの収束を同時に導く型は確認できなかった。 |
| 1.2.4.6 | partial → partial | stronger-hyp | hCだけでなく明示されたuniverse lift後のホモトピー圏の冪等完備性も入力すれば、idempotentComplete_of_ulift_ho_completeは同じCの冪等完備性を直接返す。lift前のhCの入力からの比較と逆向きはこの引用だけでは含まない。 |
| 1.2.4.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：冪等完備化の安定性と通常の Dold–Kan の余積分解を読んだ。安定 ∞ 圏に値を取る単体的図式の各項をフィルトレーションのシフトした余ファイバーで分解する宣言は確認できなかった。 |
| 1.2.4.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：CoherentIdempotent.endomorphism_idem は coherent 図式から hC の冪等射を得る向き。安定性を用いて hC の任意の冪等射から逆向きの coherent 図式を構成する型は確認できなかった。 |
| 1.2.4.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：集合値で退化を自由に付加する模型とアーベル圏の系列の第 1 頁を確認した。安定 ∞ 圏の半単体的図式から余極限とスペクトル系列を得る比較を探したが確認できなかった。 |
| 1.2.4.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：加群ハートの埋め込みと交代面写像複体を読んだ。左完備な t 構造でハートの半単体的対象を実現し、そのホモトピー群を非正規化ホモロジーで計算する型は確認できなかった。 |
| 1.2.4.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：鎖複体のアシクリック性および半単体的図式の実現の特例を探した。πq によるアシクリック分解から左完備な ∞ 圏での実現の存在と各ホモトピー対象の計算を得る型は確認できなかった。 |
| 1.2.4.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：非負次数への切断と、鎖複体における分解を調べた。左右両完備な t 構造のもとで非負のホモトピー対象の分解から半単体的実現を構成する型は確認できなかった。 |
| 1.2.4.13 | partial → partial | special | KB-W2型再照合：仮定：安定準圏と 2 次元正方形（Lean が強い：任意の n 立方体ではない）。結論：正方形が引き戻しであることと押し出しであることは同値（n=2 の場合に一致）。 |
| 1.2.4.14 | partial → none |  | cofiberPushoutComparisonIsoは二つの余ファイバー頂点間のある同型を返す。原文が指定する同じ誘導射αの可逆性とこの同型を同定する型は引用に含まれず、ある同型の存在だけをαのiffの片方向とは数えない。 |
| 1.2.4.15 | partial → none |  | cofiberが左随伴なので全矢図式の既存余極限を保存する型は候補だが、原文の指定したK▷×Δ1のαがcolimit diagramであることと、同じ矢準圏の余極限性との比較を引用で確認していない。関手の保存性だけをこのiffのdirectionと数えない。 |
| 1.2.4.16 | partial → partial | special | S=∅に限れば、Yは0≤y1≤…≤yn≤1という非空凸部分集合であり、Convex.contractibleSpaceへ同じYの凸性・非空性を入力すると原文の可縮性を直接得る。一般の指定点を含む集合との同相は含まない。 |
| 1.2.4.17 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：comma 圏の弱可縮性を仮定する一般の Quillen A 判定はあるが、HA の切断単射単体圏からの指定包含についてその仮定を示す宣言はない。一般判定だけでは指定包含の cofinality を直接与えない。 |
| 1.2.4.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：安定圏のシフトと切断単体集合の骨格を確認した。最高次数以外が零の切断単体的図式の余極限を最高項の n 重懸垂と同定する宣言は確認できなかった。 |
| 1.2.4.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：左・右 Kan 拡張の判定と安定 ∞ 圏の押し出し・引き戻しの同値を調べた。最高次数と増大次数をそれぞれ切り落とす二つの制限に対し、この同じ F の Kan 拡張条件を比較する型は確認できなかった。 |
| 1.3.0.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：導来圏の構成と Verdier 局所化の型を確認した。ここでの HA の主張は Verdier の学位論文への歴史的帰属と文献案内で、構成定理に対応する主張を含まない。 |
| 1.3.1.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：DGCategory と SimplexData.rhs は Leibniz 則と二項合成まで。高次積を入力する A∞ 圏およびそれに対応する nerve の方程式を探したが、該当する宣言は確認できなかった。 |
| 1.3.1.9 | partial → partial | component | KB-W2型再照合：仮定：dg 圏とその閉次数 0 の基礎圏（HA と一致）。結論：基礎圏の nerve から dg nerve に入り、高次の成分は零で、辺は元の閉零射に対応する。高次の成分が零である全単体を一意に復元する像の逆向きは型にない（Lean が弱い）。 |
| 1.3.1.11 | partial → partial | component | 同じdg圏のH⁰圏とhNdgの比較equivalenceは、原文の構成する比較関手およびそのHom全単射と本質的全射性の成分を直接与える。対象を厳密に同一にした通常圏の同型という全体の型は含まない。 |
| 1.3.1.13 | partial → partial | component | KB-W2型再照合：仮定：dg 圏 C（HA の CΔ の構成と一致。Lean は任意の可換環を許す）。結論：基礎圏を単体的に豊穣化し、Hom を切断した Hom 複体の Dold–Kan 模型と比較し、合成を Alexander–Whitney 写像で与える。任意の鎖複体に対する合成関手そのものの lax monoidal 構造は型に含まれない（Lean が弱い）。 |
| 1.3.1.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：dg QuasiEquivalence は Hom の擬同型と H⁰ の本質的全射を定義する。しかしそれを弱同値類として実現する dg 圏全体の combinatorial ModelCategory の存在、factorization と指定 fibration はない。弱同値候補の述語はモデル構造の存在の部分証明ではない。 |
| 1.3.1.20 | partial → none |  | dgNerve_map_isQCatEquivalence_of_quasiEquivalenceは準同値の保存であり、原文の右Quillen条件を構成する右随伴・fibration保存・trivial fibration保存のどれも直接返さない。その帰結・証明の材料だけをcomponentと数えない。 |
| 1.3.2.2 | partial → partial | special | KB-W2型再照合：仮定：可換環上の dg 圏または加群複体（Lean が強い：任意の加法圏ではない）。結論：dg nerve の辺を閉次数 0 射と同定し、h の Hom を H⁰ と比べ、具体的な鎖写像を辺に対応させる（加群複体で一致）。 |
| 1.3.2.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：pinchedHom のホモトピー群と Hom 複体のコホモロジーの比較はあるが、HA のシフトした Y への鎖ホモトピー類との同定を含まない。pinched モデル・次数と shifted Hom をつなぐ比較が必要であり、コホモロジー群への別の同型だけでは直接対応しない。 |
| 1.3.2.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常のエピに対する Projective と、PΣ の sifted 余極限保存を調べた。アーベル圏の nerve 内で両方の射影性を同定する宣言は確認できなかった。 |
| 1.3.2.6 | partial → partial | component | KB-W2型再照合：仮定：零射を持つ圏の整数次数 cochain 複体（Lean が弱い：有限双積と加法性は不要）。結論：項が十分低い cochain 次数で零となる複体の充満部分圏（Lean が弱い：HA の二方向のうち次数反転後の一方を与える）。 |
| 1.3.2.7 | partial → none |  | 通常の導来圏の有界部分圏とK-injectiveの型は、原文の射影/入射複体のdg nerveとしての同じ導来∞圏の構成への比較を持たない。通常圏へ降ろした別対象をspecialと数えない。 |
| 1.3.2.8 | partial → none |  | 通常の導来圏の有界部分圏とK-injectiveの型は、原文の射影/入射複体のdg nerveとしての同じ導来∞圏の構成への比較を持たない。通常圏へ降ろした別対象をspecialと数えない。 |
| 1.3.2.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：半自由加群複体による非有界導来 ∞ 圏の h と非有界通常導来圏の同値はある。一方 HA は有界な射影複体から作る D⁻ の h の記述であり、通常の DerivedCategory.Minus の定義だけでは同値をその有界模型へ制限しない。非有界の類似比較を partial と数えない。 |
| 1.3.2.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：derivedInfinityCategory_isStable は半自由複体による局所化後の導来 ∞ 圏の安定性である。HA の主張は局所化前の全複体の dg nerve Ndg(Ch(A)) であり、準同型を反転した対象は異なる。導来圏の安定性だけから全複体の dg nerve の安定性は直接得られない。 |
| 1.3.2.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：正規化 Moore 複体と複体の射影 fibration を確認した。単体アーベル群の一般の射について、正次数の正規化成分が全射であることと underlying Kan fibration を結ぶ型は確認できなかった。 |
| 1.3.2.12 | partial → partial | special | KB-W2型再照合：仮定：可換環上の dg 圏から作る特定の単体加群（Lean が強い：任意の単体アーベル群を入力しない）。結論：対応する Hom 単体集合が Kan（一致する特別な場合）。 |
| 1.3.2.13 | partial → partial | special | Aを可換環R上の加群圏とし、その複体のdg圏を入力すると、doldKanSimplicialCategoryは原文の同じCh(A)∆という構成成分を直接与える。指定fの各Hom全射からのKan fibration性という後半は含まない。 |
| 1.3.2.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：dg 圏の Dold–Kan 豊穣 Hom が Kan であることと、複体側の正規化テンソルから誘導する射の fibration を確認した。次数ごとの前合成の全射性を仮定する単体 Hom 射の判定は見つからなかった。 |
| 1.3.2.15 | partial → partial | component | KB-W2型再照合：仮定：モノ f と入射対象 J（Lean が弱い：アーベル性は不要。HA の (b) を各次数に適用）。結論：任意の射から J への f に沿う延長と因数分解の等式（Lean が弱い：複体に対する全次数の記述と (a) の分裂の場合は型に含まれない）。 |
| 1.3.2.16 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：mapping cone による standardCofiberSquare/fullCofiberSquare の dg nerve での押し出し性はある。しかし HA の次数ごとに split な通常の押し出し正方形をその標準正方形と比較していない。指定された通常押し出しを豊穣 homotopy pushout に送る結論には別の比較が必要。 |
| 1.3.2.17 | partial → partial | special | Aを可換環上の加群圏としgを零写像に限ると、standardCofiberSquare_isPushoutは同じmapping coneのdg nerve内のcofiber性を直接返す。E(1)テンソルによる通常押し出しとの同一視は含まない。 |
| 1.3.2.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：半自由複体の非有界導来 ∞ 圏の安定性はあるが、HA の有界射影模型 D⁻ の安定性ではない。有界部分圏の定義だけではその零・fiber/cofiber への閉性を与えず、非有界圏の安定性から部分圏の安定性は直接従わない。 |
| 1.3.2.19 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：アーベル圏の通常の導来圏、心の dg nerve 側は可換環の加群（Lean が強い：心の比較は加群の場合）。結論：通常の導来圏の標準 t 構造と加群の場合の心の充満忠実性・離散頂点の像の特徴付け（Lean が弱い：一般の有界導来 ∞ 圏の t 構造と心の nerve 同値は一体として与えない）。 |
| 1.3.2.20 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の有界射影複体の K-projective 性と局所化 Hom の全単射はあるが、指定準同型 Q→Q′ による Hom 複体の後合成の擬同型性はこれらの型にない。DG module の homotopically projective 始域からの後合成の擬同型性もあるが、HA の任意の加法圏の複体をその DG module 模型に同定し有界射影仮定を移す比較はなく、部品として記録する。 |
| 1.3.2.21 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：可換環上の半自由 dg nerve、二つ目は心の加群から来る頂点（Lean が強い：非負次数の射影複体と非正ホモロジーの複体を一般に入力しない）。結論：π₀ と Ext⁰ の同定及び加群から来る心の Hom の同定（Lean が弱い：この仮定での写像空間の離散性を与えない）。 |
| 1.3.2.22 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の Dold–Kan 同値は非負複体の通常圏と単体的対象の通常圏を結ぶ。HA の左辺は射影複体を鎖ホモトピーで捉えた connective 導来 ∞ 圏であり、右辺も豊穣 nerve である。通常圏の同値だけではこれらの写像空間と指定圏の同値を直接与えない。 |
| 1.3.2.23 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の Dold–Kan 同値と、別の dg nerve/coherent nerve 比較はある。しかし HA の豊穣 DK 関手そのものの各 Hom 上の弱ホモトピー同値を与えていない。二つの独立な同値はこの豊穣関手の弱同値性の証明ではない。 |
| 1.3.2.24 | partial → partial | component | KB-W2型再照合：仮定：圏 C（Lean が弱い：加法性は不要）。結論：冪等完備化への通常の充満忠実埋め込み（Lean が弱い：Dold–Kan から従う非負複体と単体対象の間の ∞ 圏の埋め込みはこの型にない）。 |
| 1.3.3.1 | partial → partial | component | 同じ∞完全関手Fが誘導するhC→hC′の関手にLeftTExact/RightTExactを適用すると、そのn=0のfieldは原文の同じt-structureの半分の頂点を送るという条件を直接返す。∞完全性の条件をこの通常関手のclassだけで得たとはしない。 |
| 1.3.3.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：アーベル圏上で射影分解を用いて左導来を作る型と、PΣ の Yoneda 制限の普遍性を確認した。左完備な安定標的で右 t 完全関手を心の右完全関手で分類する型は見つからなかった。 |
| 1.3.3.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の DerivedCategory.Minus の定義は有界部分圏を与えるだけで、HA の t 構造の左完備性や、それに基づく普遍性による D⁻ の特徴付けを与えない。有界部分圏の存在を完備性・普遍性の部分結論と数えない。 |
| 1.3.3.4 | partial → none |  | leftDerivedToHomotopyCategoryの標的は通常の複体のホモトピー圏で、原文の指定D−(A)→D−(B)の∞拡張とは異なる。H0の比較だけでも同じ延長の存在にならない。 |
| 1.3.3.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：D(ℤ) を含む加群の導来模型と Ω スペクトルの模型を確認した。アーベル群の複体を一般化 Eilenberg–Mac Lane スペクトルへ送る ∞ 関手は確認できなかった。 |
| 1.3.3.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：t 完全性の通常圏での型と H₀ で元の右完全関手を回復する型を確認した。左 t 完全性・心の保存・心での完全性の三条件の同値は見つからなかった。 |
| 1.3.3.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常導来圏の射影対象からの正次数 Ext の消滅はある。しかし任意の左完備 stable C への拡張 F の構成、その充満忠実性と Ext 消滅条件の同値、または有界本質像を与えない。特定の通常導来圏で条件に似た消滅だけでは、この F の結論に直接対応しない。 |
| 1.3.3.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：PΣ の sifted 連続関手の Yoneda 制限同値と有限余積保存の判定はある。しかし HA の connective D⁻ の幾何学的実現を保つ関手圏との比較がなく、filtered 余極限まで課す PΣ の別の普遍性だけから指定制限関手の同値は直接得られない。 |
| 1.3.3.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：射影分解の持ち上げとその鎖ホモトピー、PΣ に対する制限同値を確認した。通常の圏で射影対象に制限し、余等化子から右完全拡張を逆構成する同値は見つからなかった。 |
| 1.3.3.10 | partial → partial | stronger-hyp | KB-W2型再照合：仮定：小余積と幾何学的実現（Lean が強い：HA は有限余積で足りる）。結論：小余極限の存在と保存（Lean が強い：有限の場合を含む。Lean が弱い：n 圏での逆向きはこの型にない）。 |
| 1.3.3.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の三角圏で t 完全性の型と、準圏の余積・幾何学的実現による余極限保存を確認した。connective 部分圏への制限同値および左完備性からその実現を構成する型は見つからなかった。 |
| 1.3.3.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：PΣ では射影対象を代入できる Yoneda 制限を確認した。一般の左完備安定圏に対して右 t 完全な導来関手を connective 値の有限余積保存関手と比較する宣言は見つからなかった。 |
| 1.3.3.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の Ind 圏の定義はあるが、HA の射影対象上の加法的前層の圏 A-hat を Ind(A) と同定せず、そのアーベル性・十分な射影対象も与えない。結論に現れる別の圏の構成だけは対応と数えない。 |
| 1.3.3.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：PΣ の構成と制限同値、通常の Ind 圏を確認した。A の Ind 圏の connective 有界導来 ∞ 圏を PΣ と同定する型は確認できなかった。 |
| 1.3.3.15 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の Ind 圏への Yoneda 埋め込みと D⁻ の有界性を確認した。導来 ∞ 圏に持ち上げた埋め込みの像を全ホモロジーで特徴づける型は見つからなかった。 |
| 1.3.3.16 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：通常のアーベル導来圏の有界側（Lean が弱い：十分な射影対象を仮定しない）。結論：標準 t 構造に関する有界性で充満部分圏を定める（Lean が弱い：∞ 圏の切断塔に関する左完備性は型にない）。 |
| 1.3.3.17 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：PΣ の各対象を sifted 余極限で表す宣言はあるが、HA の D⁻ の像に限定した幾何学的実現による最小閉包を与えない。sifted 余極限には filtered 余極限も含まれ、閉包の形と対象範囲の異なる表示は直接の部分結論にならない。 |
| 1.3.4.2 | partial → partial | special | KB-W2型再照合：仮定：単体集合と全辺、又は W を反転する与えられた関手（Lean が強い：任意の W で仮定なしの存在ではない）。結論：全辺の局所化、及び任意の W の小さい反転因数分解（Lean が弱い：後者は普遍性を要求しない）。 |
| 1.3.4.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の非有界 DerivedCategory.Q の局所化と dg 加群の半自由置換の局所化はある。しかし HA の有界な通常複体の nerve の局所化を、有界射影 dg nerve D⁻ に比較する宣言はない。非有界対象での別の局所化だけでは指定された有界同値を直接与えない。 |
| 1.3.4.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：closedNerveInclusion と一般の isLocalization_of_deformation はあるが、この包含について円柱閉性から変形データを構成し、鎖ホモトピー同値を反転する普遍性を得る宣言はない。一般判定に未構成のデータを入力する必要があり、包含の存在だけでは局所化の結論にならない。 |
| 1.3.4.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：非有界 dg 加群の半自由置換は準同型を反転し局所化を与える。しかし HA の有界射影複体の包含の右随伴、準同型との iff、および有界圏の局所化を構成しない。非有界の反射・置換を別の有界部分圏の右随伴と同一視しない。 |
| 1.3.4.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：hammock による局所化の普遍性と、単体豊穣圏の coherent nerve を確認した。指定 W に円柱の収縮が含まれるとき、通常の nerve から coherent nerve への標識弱同値を判定する型は見つからなかった。 |
| 1.3.4.8 | partial → none |  | hammock局所化・cf coherent nerve・representable homotopy limitの候補はあるが、原文の指定された局所化射/図式の模型との比較を引用型に含まない。別の標的・別の判定をstronger-hypとして数えない。仮定：モデル圏のcofibrant-fibrant 対象と関手的分解・フレーム（Lean が強い：任意の区間対象を持つ局所 Kan な単体圏を扱わない）。結論：弱同値を反転する hammock nerve の局所化（Lean が弱い：単体豊穣圏自身の coherent nerve との比較はこの型にない）。 |
| 1.3.4.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：standardAW による dg Hom の合成はあるが、HA の警告の内容である全複体の豊穣が simplicial tensor を持たないという比較の不成立・反例はない。AW の構成はその失敗を証明せず、修正した局所化の証明も直接与えない。 |
| 1.3.4.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：sifted な図式の点ごとの余極限と、単体豊穣圏の coherent nerve の Hom 比較を確認した。対象を固定した単体圏の homotopy colimit を各 Hom の homotopy colimit で検出する型は見つからなかった。 |
| 1.3.4.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：単体豊穣関手圏と coherent nerve の単体の記述を確認した。各次数で通常の圏を作る C• と join の右随伴による T•C の図式を与える宣言は確認できなかった。 |
| 1.3.4.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：準圏で各頂点下の coslice が弱可縮である型を確認した。任意の単体集合 X について Δ[m] 下の translation と X の m 単体の離散集合の比較同値は見つからなかった。 |
| 1.3.4.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：coherent な余錐の余極限判定を確認した。Δ[n] との join の右随伴からなる translation 図式が X を実現する比較は、Kan な X に限定しても見つからなかった。 |
| 1.3.4.14 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：幾何学的実現と単体豊穣圏の関手圏を確認した。各次数の通常圏 Cₙ から作る単体図式 T•C について、弱同値と元の C の実現を結ぶ型は見つからなかった。 |
| 1.3.4.15 | partial → own |  | modelCofibrantRelativeCategoryは同じモデル圏のcofibrant対象と弱同値を与える。weakNerveEdgesとIsLocalizationを同じFへ適用すれば原文のunderlying ∞-categoryの定義全体になる。存在定理のための関手的分解・フレームをこの定義に追加する必要はない。 |
| 1.3.4.16 | partial → partial | component | KB-W2型再照合：仮定：モデル圏の関手的分解と指定フレーム（Lean が強い：明示的な hammock 模型とフレームを選ぶ）。結論：全圏・cofibrant 圏・cf 圏の局所化を、置換の比較を使って構成する（Lean が弱い：fibrant だけの部分圏はこの型に含まれない）。 |
| 1.3.4.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：QuillenCfCollage は二つの単体モデル圏の cf 対象間の豊穣 Quillen 随伴から作る。HA の M は単一モデル圏の cofibrant 対象を下段、cf 対象を上段とし、下段 Hom は離散である。対象と下段 Hom が異なり、cf/cf の類似対応圏だけでは指定構成の特殊例にならない。 |
| 1.3.4.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：cf/cf Quillen collage の射影の余デカルト性と選んだ左持ち上げ辺の余デカルト性はある。しかし HA の cofibrant/cf・離散下段 Hom の M とは異なり、指定された全横断辺が余デカルト iff 弱同値という判定もない。異なる対応圏上の類似結果を対応と数えない。 |
| 1.3.4.20 | partial → none |  | hammock局所化・cf coherent nerve・representable homotopy limitの候補はあるが、原文の指定された局所化射/図式の模型との比較を引用型に含まない。別の標的・別の判定をstronger-hypとして数えない。仮定：モデル圏の関手的分解と指定フレーム（Lean が強い：HA の単体モデル圏と構成された θ をそのまま入力しない）。結論：cofibrant 及び cf の通常の nerve の弱同値による局所化を hammock で得る（Lean が弱い：θ の標的である cf の豊穣 coherent nerve との指定比較がこの型にない）。 |
| 1.3.4.21 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：左 Quillen 関手が cofibrant 対象間の弱同値を保つ Brown の補題と、単体モデル間の導来随伴を確認した。Quillen 同値から標識 nerve の弱同値を得る型は見つからなかった。 |
| 1.3.4.22 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：モデル圏の hammock による局所化と、一般の可到達余完備準圏の presentability を確認した。組合せ的モデルの局所化に presentability を適用する橋渡しは見つからなかった。 |
| 1.3.4.23 | partial → none |  | hammock局所化・cf coherent nerve・representable homotopy limitの候補はあるが、原文の指定された局所化射/図式の模型との比較を引用型に含まない。別の標的・別の判定をstronger-hypとして数えない。仮定：局所 Kan な単体圏の厳密図式と通常の錐（Lean が強い：一般の組合せ的モデル圏の局所化との同定を仮定に含めない）。結論：coherent nerve での極限性を各対象からの representable homotopy limit 比較で判定（Lean が弱い：モデル圏の homotopy limit からの比較を型に含まない）。 |
| 1.3.4.24 | partial → none |  | hammock局所化・cf coherent nerve・representable homotopy limitの候補はあるが、原文の指定された局所化射/図式の模型との比較を引用型に含まない。別の標的・別の判定をstronger-hypとして数えない。仮定：局所 Kan な単体圏の厳密図式と通常の余錐（Lean が強い：一般の組合せ的モデル圏の局所化を扱わない）。結論：coherent nerve の余極限性を各対象への Hom の homotopy limit 比較で判定（Lean が弱い：モデル圏の homotopy colimit と同定しない）。 |
| 1.3.4.25 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：単体豊穣圏からの厳密関手の nerve と、局所化に沿う相対関手の比較を確認した。射影・入射モデル構造の図式圏を局所化して ∞ 関手圏と同定する型は見つからなかった。 |
| 1.3.4.26 | partial → none |  | hammock局所化・cf coherent nerve・representable homotopy limitの候補はあるが、原文の指定された局所化射/図式の模型との比較を引用型に含まない。別の標的・別の判定をstronger-hypとして数えない。仮定：二つの単体モデル圏と豊穣の随伴・pushout-product・関手的置換（Lean が強い：一般の組合せ的モデル圏間の左 Quillen 関手より限定。モデル圏 instance が必要）。結論：cf nerve 間に誘導される左導来関手が左随伴（Lean が弱い：全ての組合せ的模型の局所化との同定は型にない）。 |
| 1.3.4.27 | partial → none |  | hammock局所化・cf coherent nerve・representable homotopy limitの候補はあるが、原文の指定された局所化射/図式の模型との比較を引用型に含まない。別の標的・別の判定をstronger-hypとして数えない。仮定：単体モデル圏間の豊穣 Quillen 随伴に関手的置換を与える（Lean が強い：一般の組合せ的モデル圏を直接扱わず、モデル圏 instance が必要）。結論：右導来関手と随伴の存在、および通常の置換から作った関手との比較（制限した模型で一致）。 |
| 1.3.5.1 | partial → none |  | IsGrothendieckAbelianは生成対象とAB5による通常圏の定義。原文のpresentabilityとmonoのfiltered余極限閉性の同じ条件へ比較する宣言を確認していない。別の公理系のfieldsだけをcomponentと数えない。 |
| 1.3.5.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Mathlib の Grothendieck アーベル圏の定義と十分な入射対象の定理を確認した。この注は Grothendieck による歴史的導入と文献を述べる。 |
| 1.3.5.3 | partial → none |  | 有界cochain複体のscoped ModelCategory/IsFibrantは原文の無界Ch(A)のモデルと同じ対象・述語ではない。無界側のK-injective性や試験族の直交性だけも、同じモデル構造の存在・各項入射性という結論を直接返さない。 |
| 1.3.5.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：dg 圏の Dold–Kan 豊穣と AW 合成はあるが、HA が述べる simplicial tensor の比較が一般には同型でないこと、または injective 模型が simplicial model category でないことの反例・判定はない。豊穣の構成だけではその不成立を直接証明しない。 |
| 1.3.5.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Grothendieck 圏の複体の filtered 余極限の完全性と通常の準同型の定義を確認した。準同型そのものの filtered 余極限閉性を主張する宣言は確認できなかった。 |
| 1.3.5.6 | partial → none |  | 有界cochain複体のscoped ModelCategory/IsFibrantは原文の無界Ch(A)のモデルと同じ対象・述語ではない。無界側のK-injective性や試験族の直交性だけも、同じモデル構造の存在・各項入射性という結論を直接返さない。 |
| 1.3.5.8 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：可換環の加群。通常の圏との比較には HasDerivedCategory（Lean が強い：一般の Grothendieck アーベル圏を扱わない）。結論：半自由複体の dg nerve とその h の通常の導来圏との同値（Lean が弱い：injective 模型の dg nerve と準圏での比較がない）。 |
| 1.3.5.9 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：可換環上の半自由複体（Lean が強い：任意の Grothendieck 圏と fibrant 複体ではない）。結論：対応する導来 ∞ 圏が安定（加群模型で一致）。 |
| 1.3.5.10 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：十分な入射を持つアーベル圏の有界 cochain 複体と通常の導来圏（Lean が弱い：Grothendieck 性は不要）。結論：有界な入射複体と有界モデルの fibrant 対象の通常の圏同値及び通常の D⁺ の包含（Lean が弱い：HA の無界な dg nerve への充満包含は型にない）。 |
| 1.3.5.11 | partial → partial | stronger-hyp | 同じfibrant複体QにK-injective性も追加すればeq_δ_of_cocycleは同じHom(M,Q)の全次数のcycleがboundaryであると直接返し、原文のacyclic性を得る。無界のモデルinstanceやfibrantだけからの比較は含まない。 |
| 1.3.5.12 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：K-injective 標的への acyclic 始域からの cocycle の消滅と通常局所化 Hom の全単射はある。しかし HA の自明余ファイブレーションに沿う前合成の Hom 複体の擬同型性を述べず、cone や各次数 Hom をつなぐ別の議論が必要。消滅の部品を指定射の擬同型性とは数えない。 |
| 1.3.5.13 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：通常の Grothendieck 圏のホモトピー圏、または可換環上の dg 加群（Lean が強い：準圏側は後者のみ）。結論：K-injective 置換の単位が準同型であり、dg 加群では半自由置換が局所化（Lean が弱い：一般の Grothendieck 圏で fibrant 複体の dg nerve が反射部分圏である型はない）。 |
| 1.3.5.14 | partial → partial | stronger-hyp | 同じ二つのfibrant複体にK-injective性も追加するとquasiIso_iffは、原文後半の同じ準同型fが鎖ホモトピー同値であるという結論を直接返す。前半の任意始域のHom前合成は含まない。 |
| 1.3.5.15 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の閉零圏から dg nerve への包含と dg nerve からの半自由局所化は個別にあるが、合成が通常の nerve の準同型局所化であるという普遍性と injective 模型への比較はない。包含の存在と後半の局所化だけでは合成の局所化を直接得られない。 |
| 1.3.5.16 | partial → none |  | 通常の導来圏のt-structureにおける消滅条件は候補だが、原文の指定したdg nerveの部分準圏と無界入射模型内の共通部分そのものを与える型ではない。 |
| 1.3.5.17 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：十分な入射対象を持ち、通常の意味で項が有界な cochain 複体（Lean が強い：HA の入力はホモロジーが有界な fibrant 複体）。結論：各項入射な有界複体への準同型が存在（Lean が弱い：t 切断の上で元の対象から ∞ 圏同値となる比較はない）。 |
| 1.3.5.18 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：アーベル圏の通常の導来圏（Lean が弱い：Grothendieck 性は不要）。結論：通常の導来圏の標準 t 構造（Lean が弱い：全複体の dg nerve 上で injective 側を指定する HA の t 構造を与えない）。 |
| 1.3.5.19 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：可換環の加群の半自由模型（Lean が強い：任意の Grothendieck 圏と connective・coconnective の任意の対ではない）。結論：心の加群の Hom の同定と離散対象の像の特徴付け（Lean が弱い：指定した対の写像空間の同値は型にない）。 |
| 1.3.5.20 | none → own |  | 同じt-structureのC≤0の頂点述語PへIsKappaColimitClosed ℵ0を適用すると、同じC内の全小filtered余極限に対する閉性という原文の両立条件を直接表す。固定宇宙のsmall条件を保持し、通常圏のt切断で代用しない。 |
| 1.3.5.21 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：可換環の加群の導来 ∞ 圏、t 構造はアーベル圏の通常の導来圏（Lean が強い：∞ 圏側は加群の場合）。結論：加群の導来 ∞ 圏の presentability と、通常の導来圏の標準 t 構造（Lean が弱い：∞ 圏の t 構造の可到達性・右完備性・filtered 余極限との両立はない）。 |
| 1.3.5.22 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：通常の導来圏の t 構造と加群の導来 ∞ 圏の presentability を確認した。Grothendieck アーベル圏で左完備性が失敗する反例の形式化は見つからなかった。 |
| 1.3.5.23 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：加群の導来模型で心の包含を、通常の圏で Grothendieck 性を確認した。filtered 余極限と両立する任意の accessible t 構造の心について Grothendieck 性と D⁺ からの t 完全な拡張を結ぶ型は見つからなかった。 |
| 1.3.5.24 | partial → none |  | 通常の導来圏または加群の半自由dg nerveの型は、原文で指定する有界射影模型・無界入射模型の同じ導来∞圏との比較を持たない。模型や対象を変えた結果だけをspecial/componentと数えない。仮定：通常のアーベル導来圏、∞ 圏側の比較は可換環上の加群（Lean が強い：一般の Grothendieck アーベル圏の二つの模型を扱わない）。結論：通常の圏で有界側の充満部分圏の包含、及び半自由模型の h の比較（Lean が弱い：射影模型から injective 模型への充満忠実性と指定された本質像は型にない）。 |
| 1.4.1.1 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：suspensionFunctorOfFiniteColimits は懸垂を構成し、hasBinaryBiproducts_ho は stable な場合の双積を与える。しかし HA の ΣX の余群構造・fold 射と Hom 上の π1 群構造との一致は含まれない。懸垂や双積の存在はその余群構造を与えるための材料にとどまる。 |
| 1.4.1.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：反射部分圏の表現可能性の移送を確認したが、既に局所な表現対象を仮定する。コンパクトな余群生成族と余積・弱押し出し条件から表現対象を構成する Brown の型は見つからなかった。 |
| 1.4.1.3 | partial → partial | component | KB-W2型再照合：仮定：安定準圏（Lean が弱い：presentable 性は不要）。結論：ホモトピー圏の前加法性と双積があり、原典冒頭の加法性に対応する（Lean が弱い：各対象の余群構造と compactly generated な場合の Brown の全仮定の確認は含まれない）。 |
| 1.4.1.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：点付き空間の coslice と有限空間のコンパクト生成候補を確認した。連結点付き空間を余群対象で生成し Brown の仮定を確かめる宣言は見つからなかった。 |
| 1.4.1.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：点付き空間の準圏と既存の表現対象を移送する定理を調べた。古典的な空間の Brown 表現定理への特殊化は確認できなかった。 |
| 1.4.1.6 | partial → partial | special | Cを安定準圏とし、各HnがhCop上のAb値ホモロジー関手のunderlying Set関手として与えられる場合、cofiberTriangle_memとIsHomological.exactは同じcofiber列に対する条件(2)のkernel-image完全性を直接返す。次数族全体・δと小余積保存の条件(1)は含まない。 |
| 1.4.1.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：安定ホモトピー圏の加法構造を確認した。一般の点付き準圏で二重 suspension を可換余群として構成し、コホモロジー理論の各値に自然なアーベル群構造を入れる型は見つからなかった。 |
| 1.4.1.8 | partial → partial | component | cofiberConnectingToSuspensionは原文最初の同じcofiber列のC″→ΣC′という境界射の構成を直接与える。Hnとδnから長完全列全体を組み立てる型は含まない。 |
| 1.4.1.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：前三角圏のホモロジー関手の完全性と、表現対象を移送する定理を確認した。任意のコホモロジー理論が Brown の余積・弱押し出し条件を満たすという型は確認できなかった。 |
| 1.4.1.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：コンパクト生成の安定 Ind と、表現対象を既に持つ場合の移送を確認した。コホモロジー理論の各次数に Brown を適用して表現対象を返す型は見つからなかった。 |
| 1.4.1.11 | partial → none |  | Kan列からのBF Ω-spectrumの構成は、原文の同じコホモロジー理論のδnと表現対象からSp(C)の極限へ入る構成への比較を持たない。別のスペクトル模型の構造だけをstronger-hypと数えない。 |
| 1.4.2.1 | partial → own |  | 同じFに∀R, IsPushoutSquare R→IsPullbackSquare(R≫F)を課し、指定終頂点*にIsTerminalVertex(F(*))を課せばexcisive/reducedの定義そのもの。functorVertexEquivとfullSubcomplexOnVerticesへその二条件・論理積を代入すれば三つの指定全部分準圏も直接構成できる。 |
| 1.4.2.2 | partial → partial | special | KB-W2型再照合：仮定：両準圏が安定（Lean が強い：HA は始域のみ又は標的のみが安定な場合も述べる）。結論：完全関手が押し出し・引き戻しを保ち、零と fiber 列の保存から完全性が従う（Lean が弱い：片側だけが安定な場合を含めた左・右完全性との同値はこの型に含まれない）。 |
| 1.4.2.3 | partial → partial | special | Kを有限形状に限りDに全有限極限も要求するとhasFiniteLimits_functorCategoryは原文最初の同じFun(C,D)のK極限存在を直接返す。切除的・縮約関手の部分準圏の閉性は含まない。 |
| 1.4.2.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：反射部分圏の presentability は局所化が既に与えられたときの型。切除性や縮約性の局所化を生成する射の集合と、その可到達な反射は確認できなかった。 |
| 1.4.2.5 | partial → partial | component | 同じSpaceの矢準圏にfullSubcomplexOnVerticesを使い、始点のIsTerminalVertexを頂点条件に入れれば原文のS*の構成を直接与える。固定一点のcosliceという別模型への比較ではなく、その指定全部分圏を用いる。Sfinとそのpointed部分は含まない。 |
| 1.4.2.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：有限単体集合の空間模型がコンパクトであることと、PΣ の sifted 余極限による普遍性を確認した。有限余極限完備な空間の部分圏からの右完全関手を一点評価で分類する宣言は見つからなかった。 |
| 1.4.2.7 | partial → none |  | 有限単体集合のKan置換またはBF Ω-spectrumの型は、原文の有限余極限生成で定めたSfinとそれを始域に持つExc*模型との比較を含まない。同じ対象と同定せず別模型の結果をspecialと数えない。 |
| 1.4.2.8 | partial → none |  | 有限単体集合のKan置換またはBF Ω-spectrumの型は、原文の有限余極限生成で定めたSfinとそれを始域に持つExc*模型との比較を含まない。同じ対象と同定せず別模型の結果をspecialと数えない。 |
| 1.4.2.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：関手圏の有限極限を点ごとに計算する結果と、点付き空間の Ω スペクトル模型を確認した。関手圏に値を取るスペクトルを curry してスペクトル値関手と同定する型は確認できなかった。 |
| 1.4.2.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：有限極限を持つ標的への関手圏全体の有限極限と、安定圏間の完全関手の充満部分圏は確認した。一般の標的で縮約切除関手の部分圏が零対象と有限極限を持つ宣言は見つからなかった。 |
| 1.4.2.11 | partial → partial | component | KB-W2型再照合：仮定：点付き準圏に有限極限と loop 図式の切断を取り、その loop が同値（第3項では Lean が弱い：有限余極限は不要。第1・2項では Lean が強い：完全忠実性だけの条件に対して loop 同値を要求）。結論：安定性、および引き戻しなら押し出し（Lean が弱い：完全忠実な suspension または loop だけからの二方向をこの型は与えない）。 |
| 1.4.2.12 | partial → partial | component | KB-W2型再照合：仮定：四角形の関手族とその右上・左下・右下の極限錐を選ぶ（HA と一致：有限極限は選択された錐を与える）。結論：元の左上頂点から引き戻しへの比較辺とその関手族（Lean が弱い：零角の場合の F(X)→ΩF(ΣX) との同定はこの型に含まれない）。 |
| 1.4.2.13 | partial → partial | stronger-hyp | 原文の縮約関手Fに、全suspension正方形の像がpullbackであるという入力も追加するとsends_pushouts_to_pullbacks_of_suspensionSquaresは同じFのexcisive性を直接返す。指定ηXの可逆性だけからこの追加入力を得たとはしない。 |
| 1.4.2.14 | partial → partial | component | 同じ完全関手FのIsExactFunctor.preservesZeroは原文の右辺(1)の零対象保存を直接返す。指定された標準比較ΣF(X)→FΣ(X)の可逆性と全iffはこの引用だけでは含まない。 |
| 1.4.2.15 | partial → none |  | 拡張格子の比較辺とその合成式は候補だが、原文の同じ押出τ・縮約Fからの指定ηW,ητ,ΩFΣWを持つθへの同定を引用型に含まない。格子の別の面の比較だけを構成成分と数えない。 |
| 1.4.2.16 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：切除性を suspension 面で検出する定理は一つの関手の像を判定する。縮約切除関手全体の安定性を示す型は、完全関手の部分圏や具体的な Ω スペクトルの場合も含めて確認できなかった。 |
| 1.4.2.17 | partial → none |  | 有限単体集合のKan置換またはBF Ω-spectrumの型は、原文の有限余極限生成で定めたSfinとそれを始域に持つExc*模型との比較を含まない。同じ対象と同定せず別模型の結果をspecialと数えない。 |
| 1.4.2.18 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：空間の pointed coslice と Ω スペクトルの具体模型を確認した。一般の C について点を忘れる写像を Sp に移して同値とする宣言は見つからなかった。 |
| 1.4.2.19 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：点付き空間を coslice で表す構成と cofiber を取る図式を確認した。基点付加への前合成と cofiber 構成が切除関手の二部分圏を互いに逆にする型は見つからなかった。 |
| 1.4.2.20 | partial → none |  | BF Ω-spectrumの模型・通常圏での評価・レベル群は、原文の指定したExc*模型のSp(C)、Snでの∞評価、または安定群との同じ対象・射の比較を持たない。別模型についての型だけをspecial/componentと数えない。 |
| 1.4.2.21 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：loop 自己同値による安定性の判定は C 内部のもの。スペクトルのレベル 0 の評価を確認したが、その評価が Sp(C) と C の同値になることによる判定は見つからなかった。 |
| 1.4.2.22 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：具体的なスペクトルのレベル評価と、切除性の判定を確認した。レベル評価との後合成で縮約切除関手を一意に持ち上げる型は見つからなかった。 |
| 1.4.2.23 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：安定圏間の完全関手の充満部分圏は構成されている。安定始域から一般の標的への左完全関手を Ω∞ に沿って持ち上げ、その関手圏を同値とする型は見つからなかった。 |
| 1.4.2.24 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：点付き Kan 列の OmegaCondition と OmegaSpectrum への変換はあるが、HA の評価 Ω∞ を備えた Sp(C) と loop 塔のホモトピー極限との圏同値を与えない。厳密な列の型の変換だけでは塔の homotopy limit の普遍性を直接証明しない。 |
| 1.4.2.25 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：具体的 OmegaSpectrum の列が OmegaCondition を満たす宣言はある。しかし任意 C の点付き対象 C∗ の塔と、縮約切除関手としての Sp(C) のホモトピー極限比較はない。列の条件を満たすことだけはこの圏の同定の部分証明ではない。 |
| 1.4.2.26 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：前層の反射部分圏の presentability と Bousfield 局所対象の構成を確認した。始対象から終対象への一射で零対象における被約性を課し、その前層圏の普遍性と点付き性を合わせて与える型は見つからなかった。 |
| 1.4.2.27 | partial → partial | component | KB-W2型再照合：仮定：点付き準圏に有限極限と選択 loop を置く場合、または既に安定な場合（HA と一致する方向別の仮定）。結論：loop 同値から安定性、安定性から互いに逆な suspension と loop、loop 同値から対応する suspension 同値（Lean が弱い：有限余極限と suspension 同値だけを入力する安定性の逆方向はこれらの型に現れない）。 |
| 1.4.3.1 | partial → none |  | BF Ω-spectrumの模型・通常圏での評価・レベル群は、原文の指定したExc*模型のSp(C)、Snでの∞評価、または安定群との同じ対象・射の比較を持たない。別模型についての型だけをspecial/componentと数えない。 |
| 1.4.3.2 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：Ω スペクトルの coherent nerve と対称スペクトルの安定局所対象を調べた。両模型を介して hSp を古典的な安定ホモトピー圏と同定する型は確認できなかった。 |
| 1.4.3.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：レベルのホモトピー群と suspension 面からの切除判定を確認した。有限空間対 X/X′ の評価から相対ホモロジー理論と Mayer–Vietoris を構成する宣言は確認できなかった。 |
| 1.4.3.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：具体的な Ω スペクトルのレベル評価と加群の導来圏の t 構造を確認した。一般の presentable C の Sp(C) で Ω∞ が終対象となる部分圏から accessible t 構造を作る型は見つからなかった。 |
| 1.4.3.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：対称スペクトルの自由対象から作る局所化生成射を確認した。Σ∞₊ の像の拡大・余極限閉包が connective 部分であることを示す型は確認できなかった。 |
| 1.4.3.6 | partial → none |  | BF Ω-spectrumの模型・通常圏での評価・レベル群は、原文の指定したExc*模型のSp(C)、Snでの∞評価、または安定群との同じ対象・射の比較を持たない。別模型についての型だけをspecial/componentと数えない。 |
| 1.4.3.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：小さい安定圏の Ind がコンパクト生成される場合を調べた。一般のコンパクト生成 C から Sp(C) のコンパクト生成を移す型は、Ω スペクトルの具体模型でも確認できなかった。 |
| 1.4.3.8 | partial → none |  | BF Ω-spectrumの模型・通常圏での評価・レベル群は、原文の指定したExc*模型のSp(C)、Snでの∞評価、または安定群との同じ対象・射の比較を持たない。別模型についての型だけをspecial/componentと数えない。 |
| 1.4.3.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：PΣ の sifted 余極限の点ごとの計算と Ω スペクトルのレベル評価を確認した。connective スペクトルから空間への Ω∞ の sifted 余極限保存は見つからなかった。 |
| 1.4.4.1 | partial → partial | stronger-hyp | 原文(2)の同じFに全有限図式の保存余極限HasPreservedColimitも追加すれば、preservesSmallColimits_of_coproducts_finiteは小余積保存⇒同じFの全小余極限保存を直接返す。安定性・exactだけからこの追加入力を供給したとはせず、(1)(3)と全iffは含まない。 |
| 1.4.4.2 | partial → partial | component | 同じpresentableなCの全小余極限存在からHasSmallColimits.hasSmallCoproductsは原文右辺(1)の同じCの小余積存在を直接返す。hCの局所小性と単一κ-compact生成対象という残る条件、逆向きは含まない。 |
| 1.4.4.3 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：安定 Ind の κ コンパクト生成とホモトピー圏の三角構造を確認した。コンパクト生成をホモトピー圏だけの条件と同定する型は見つからなかった。 |
| 1.4.4.4 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：presentable 圏の随伴関手判定と具体的な Ω スペクトルのレベル評価を確認した。一般の Sp(C) の presentability、Σ∞₊⊣Ω∞ および後合成による左随伴の検出は見つからなかった。 |
| 1.4.4.5 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：具体的な Ω スペクトルと PΣ への余極限保存延長の普遍性を確認した。一般の Σ∞₊ に沿う前合成が安定な標的への余極限保存関手を分類する型は見つからなかった。 |
| 1.4.4.6 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：対称スペクトルの自由対象と具体的な Ω スペクトルを調べた。球スペクトルでの評価が安定 presentable 圏への余極限保存関手を分類する宣言は確認できなかった。 |
| 1.4.4.7 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：反射部分圏の局所化の普遍性と、すでに安定な両端の間での有限極限保存を確認した。左完全な reflector から標的の安定性を導く逆向きまで含む型は見つからなかった。 |
| 1.4.4.8 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：レベル評価の型と準圏の一般の充満忠実性の計算を確認した。完全なスペクトル値関手でレベル 0 の評価から充満忠実性を引き上げる型は見つからなかった。 |
| 1.4.4.9 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：presentable 圏の反射 Ind 模型と stable Ind への完全 Yoneda 埋め込みはある。しかし任意の presentable stable C を stable D からの左完全な可到達局所化として表す宣言、またはスペクトル値前層からの指定表示はない。一般の反射性と安定な Ind の構成を別々に持つだけではこの同値条件を直接与えない。 |
| 1.4.4.10 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：前層による presentability の反射模型はある。HA のこの箇所は Giraud と Gabriel–Popescu との類比や文献を述べ、追加の比較同値を主張しない。 |
| 1.4.4.11 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：辺の強飽和閉包内の固定始域圏が presentable になる型を確認した。対象を余極限と拡大で閉じた部分圏の presentability と、そこから t 構造を構成する型は見つからなかった。 |
| 1.4.4.12 | none → own |  | t.ge 0の頂点述語で張る同じC≥0をfullSubcomplexOnVerticesで取り、そのIsPresentableを課せば、原文のaccessibleなt-structureの定義全体に一致する。接続説明の小生成族からの存在定理まではこの定義の対応に含めない。 |
| 1.4.4.13 | none → none |  | KB-W2再検索（現本体・ロックMathlib、KL-W1/B3/B3′/OE-W1移動後を含む）：可到達な反射の像の presentability と通常の t 切断の存在を確認した。二つの切断関手の可到達性と両側部分圏の可到達性・presentability の六条件を比較する型は見つからなかった。 |

## 読取りと再検索

原文・候補の型・現在の引用番号索引・小節ごとの現本体とロックMathlibの再検索はgit外の章別証拠。OE-W1 module-mapと宣言索引を使って移動後の名前・所在・行を確認した。ArchiveとBS draftsの宣言は正の根拠にしない。検索の全ヒットを形式検証したという意味ではない。
