> **11-05 追記（調整役）**：本書は枝 `math/g2`（b60279c26）から写した。その枝の WIP 3 本（`F2/Tensor/SetSectionsUnstraightening`・`SetSectionsLimitNaturality`・`SetSectionsSieveNaturality`）は**ビルドが通らない**（`SetSectionsUnstraightening` の証明引数 hx・hy の推論、`cases` の失敗）ので main には入れていない。段階 II の ∞ 供給レーンが `math/g2` から再開する（main を取り込んでから）。

# IF-G2 G8n：証明済みの部分と未解決の自然性

作業枝：`math/g2`。先行分：`f2b665682`。main `9f59541d3` を `ef6e30e20` で取り込み済み（衝突なし）。
状態：**G8n の四角形は未完。指定錐版の制限射・篩包含の二辺・別版の同値を先行取り込み用として切り出す。**
S4 の自然性による証明は、この区切りだけでは閉じない。

## 実装済み

新規ファイルは `SerrePositivity/InfinityCategories/F2/Tensor/SetSectionsNaturality.lean`。
G1 の既存定義は変更していない。

- `SetWeight.sectionsMap φ F cX hcX cY hcY`：指定錐を受け取り、
  `SSet.Edge cY.vertex cX.vertex` を返す。`φ.mapElements` に沿って `cY` を制限し、
  `cX` の終対象性から得た錐の辺を頂点へ写す。
- `sectionsConeMap_homMk_unique`：錐の圏でこの普遍辺のホモトピー類が一意。
- `sectionsMapOfHasLimit`：存在証明から選んだ錐を上記の API へ渡す版。
- `spaceDiagramEdge`、`tensorWeightEdge`：集合値自然変換の canonical Kan 図式の辺と、
  それにテンソルを後合成した辺。
- `sieveSectionsMap S F cS hcS cU hcU` と `sieveTensorEdge S hE M`：
  `S.functorInclusion : S.functor ⟶ yoneda.obj U` への特殊化。
  **この二辺の G8 四角形が可換という特殊化は未証明。**
- `elementsToReplacement_naturality`、`elementsWeighted_naturality`：
  要素の圏から weighted nerve までの比較の自然性。
- `tensorSpaceFunctor_diagramHom_weight_naturality`：G8 の最初の随伴比較の自然性。

## G8 の別版

`tensorSpaceFunctor_setWeightHomNatural P hE M F c hc` は、既存 G8 と同じ型の
`QCatEquivalence` として構成・検証した。入出力は

```text
Map(P ⋙ tensorSpaceFunctor hE M, F) ≃ Map(M, c.vertex)
```

で、指定錐とその極限性を受け取る。
内部では `sectionsEquivalenceNatural` と `elementsComparisonNatural` を使う。
後者は、集合の定値単体的集合とその反転との標準同型を挟み、
`smallReversedWeightedKanUnstraighteningComparison` の実射へ合成する。
底上の同値の存在から、正規化条件なしに比較を選び直す経路を避けた。

使い分け：既存 `tensorSpaceFunctor_setWeightHom` は変更せず、これまでの
点ごとの同値として使用できる。別版は今回の指定比較を用いる同値。
**名前の `Natural` に対応する、要求された自然性定理はまだ収録していない。**
BS は点ごとの同値をこの別版へ差し替えられるが、自然性を使う箇所は引き続き未解決。
①の証明に合わせて別版の内部比較を定義し直すことは、ユーザーから承認済み。
指定錐を受け取る入出力の型は維持し、内部定義の展開に依存した利用は避ける。

## 既存版との一致

2026-11-05 のユーザー指示により、一致の証明は対象から外す。
BS は別版に差し替える方針。既存版の deprecated 化は後の区切りの候補であり、
今回は既存宣言への属性追加も行っていない。

既存 `smallLeftUnstraighteningComparisonOfFunctorIso η` は、指定同型 η との対応を
選択条件に含めず底上の同値を選ぶ。この仕様だけから、指定比較との一致は導けない。
これは両者の不一致を証明したという意味ではない。

## 残る証明

要求された `tensorSpaceFunctor_setWeightHom_naturality` は未定義。
`eφ := tensorWeightEdge hE M φ`、`rφ := sectionsMap φ F cX hcX cY hcY`、
`ηX, ηY := tensorSpaceFunctor_setWeightHomNatural ...` として

```text
[pre(eφ) ≫ ηX.hom] = [ηY.hom ≫ post(rφ)]  in Ho(𝒮_{u+1})
```

を閉じるには、次の二つの接続が残る。

1. `sectionsEquivalenceNatural` の前合成を、`φ.mapElements` に沿う
   unstraightening の切断の制限へ移す四角形。
   weighted nerve までの厳密な自然性は実装済みだが、指定した比較の全写像空間での
   自然性との接続、および pullback sections の表示変更を閉じていない。
2. その切断制限を、`coherentDiagramSectionsCone` から指定極限錐へ移す比較と
   `spaceUniverseValueEquivalence`・`covariantRepresentableValueEquivalence` を通して、
   `PinchedInterval.postcompose M [rφ]` と同定する四角形。

これらを仮定として追加した定理や、未証明の公理・`sorry` は置いていない。

## 続行方針（2026-11-05 の助言を反映）

1. 比較を `φ.mapElements` に関して関手的に構成し、①を図式の制限と比較の自然性に
   帰着させる。必要なら新規ファイル内の別版の内部比較を定義し直す。
2. ②では二つの実射を直接比較せず、切断制限が同じ錐の脚と可換であることを示す。
   その錐の圏で指定極限錐の終対象性を用い、普遍辺との一致を得る。
   既存の `sectionsConeMap_homMk_unique` が一意性の接続点になる。
   最終的には写像空間全体でのホモトピーを通じて Ho(𝒮) の等式にする必要があり、
   頂点ごとのホモトピー類の一致だけでは完了としない。

見込み：四角形の完成にはさらに1日以上かかる可能性がある。完了日時は未確定。
先行部分と四角形の証明を別の区切りで渡す。

## 検証

- 新規モジュールと F2 入口の小さなビルド：成功（入口ビルドの依存グラフは
  6,665 ジョブ、全ビルドは実施していない）。
- F2 入口と監査に通常の import を追加。23 宣言を #check に登録し、新規モジュールの
  全宣言について標準公理以外への依存と新規公理宣言を検出する監査を追加。
- 監査：**2026-11-05、main 取り込み後に F2 監査を単独実行して PASS**。
  新規モジュール由来の生成宣言を含む63宣言を検査し、依存は標準公理のみ。
  初回の追加監査カウンタの型推論エラーは `count : Nat` に修正済み。
- G1 の既存宣言は変更なし。新規ソースに `sorry`・新規公理なし。

## BS の回答による優先順位の変更（2026-11-05）

先に篩包含 `S.functorInclusion` の場合の四角形を証明する。
任意の篩 S、任意の前層 F、指定された極限錐 cS・cU を使い、
位相・被覆条件・層条件は加えない。縦の二辺はともに
`tensorSpaceFunctor_setWeightHomNatural`。
一般の φ は S8-5 用に後回しとする。
表現可能前層の要素の圏の始対象 `(U, 𝟙)` から評価錐を明示し、
篩の要素への制限と指定極限錐への普遍射を比較する。
四角形完成後に先行分と一緒に main へ入れる方針。

## 篩包含版の作業中の補助（未検証、取り込み対象外）

次の新規3ファイルに証明のテキストを保存した。入口・監査にはまだ登録していない。
**先行分の監査 PASS は、この3ファイルの検証を意味しない。**

- `SetSectionsSieveNaturality.lean`：`(U, 𝟙)` からの評価錐とその篩への制限。
  `sieveEvaluationTriangle` は評価から指定極限への二経路を錐の圏の終対象性で比較し、
  元の `sieveSectionsMap` を三角形の辺として使う。
  `sieveEvaluation_postcomposeIso` はその三角形を任意の M からの全写像空間へ移す。
  これは G8 の縦の同値との照合前の補助であり、要求された四角形ではない。
- `SetSectionsLimitNaturality.lean`：`limitVertexIso_hom_eq_coneEdge` は標準の極限頂点同型を
  錐の普遍辺へ戻す。`limitConeMapIsoOfConeFamilyIso` は錐の族の同型を極限への射の族へ
  反映する。後者には明示的な錐の族の同型の入力があり、自然性の証明済み部分には数えない。
- `SetSectionsUnstraightening.lean`：指定辺の前合成の三角形の族を使い、
  `unstraighteningPrecompositionIso` と `unstraighteningPinchedPrecompositionIso` で
  unstraightening の実際の相対合成と比較する。
  `relativePreIso` は底上の射の相対写像空間内の同型を全写像空間の前合成へ移す補助。

残る接続を具体的に書くと、`φ := S.functorInclusion` に対し、
大きい宇宙へ移した `elementsComparisonNatural S.functor` の後に
`spaceDiagramEdge φ` の unstraightening 像を続けた射と、
`elementsMap φ` の後に `elementsComparisonNatural (yoneda.obj U)` を続けた射を、
**底を固定した相対写像空間の中で**同型にする必要がある。
その同型は `relativePreIso` により全パラメータの比較へ移せる。
さらに、得た切断制限と G8 別版の後段（指定極限・宇宙変更・表現可能値の比較）との
照合が残る。頂点ごとの一致だけで四角形を閉じたとは扱わない。

検証状況：最初の結合プローブで極限比較の表示に関する型エラー2件と
プローブ内の universe 重複が出たためテキストを修正した。その後の追加を含む再検証は
他レーンのビルドと verify のため未実行。`sorry`・`admit`・新規公理は置いていない。
F-2 前の作業保存用に先行分と分けて WIP コミットとする。


## IF-G2-finish 段 1：WIP 3 本の検証と登録（2026-11-05）

**停止点 1。段 2・3 には進んでいない。G8 の篩包含の四角形は引き続き未証明。**
上記の「未検証、取り込み対象外」は過去の checkpoint の記録であり、以下の検証で更新する。

- `math/g2` に main `5a1cea068` を `23552b71d` で取り込み（衝突なし）。
- `SetSectionsUnstraightening`：`intervalMappingPostOfEq` の端点等式を明示し、
  存在する三角形の族を `Classical.choose` で取り出し、面の等式を `congrArg` で直接移す。
- `SetSectionsSieveNaturality`：`Nonempty` な合成構造の取り出しを `Classical.choice` に修正。
- `SetSectionsLimitNaturality`：ソース無変更でビルド成功。
- F-2 改名表と照合し、3 本に旧完全修飾名の参照なし。3 本のビルドで deprecated 警告なし。
- 3 本を `F2.lean` と `scripts/audit_infinity_f2.lean` の通常の import に登録。
  全 33 個の明示宣言を `#check` に登録し、生成宣言を含むモジュール別監査を追加。
- 検証：対象 3 本および直接の入口 F2 の小さなビルド PASS。F2 監査を単独実行して PASS。
  新規 3 本の監査件数は `SetSectionsUnstraightening` 23・`SetSectionsLimitNaturality` 13・`SetSectionsSieveNaturality` 33（計 69 宣言）。`sorryAx`・新規公理宣言・標準 3 公理以外の依存は 0。
  許す標準公理は `propext`・`Classical.choice`・`Quot.sound`。
- ビルド開始前のプロセス確認と共有鍵取得を実施。全ビルド・verify・下流全ビルドは実施していない。
  依存グラフの数千ジョブの表示は既存成果物の利用を含み、実際に再コンパイルしたのは対象モジュールと入口だけ。
- G1・既存 G2 宣言の本文・型・名前は無変更。新しい引用・`sorry`・`admit`・公理宣言なし。

### 今回登録した宣言（すべて `SerrePositivity.InfinityCategories.SetWeight`）

`SetSectionsUnstraightening.lean`：

- `kanEnrichedDiagramHomInterval_ordinary`：全豊穣 Hom の区間比較を通常の射で評価すると、その同じ射の実現を得る。
- `relativePreHom`：底上の射を、相対写像空間の前合成へ写す全パラメータの作用。
- `relativePreHom_vertex`：全パラメータの前合成は、指定した底上の射で元の前合成を回収する。
- `relativePreIso`：相対写像空間内の比較同型から、前合成の全写像空間上の同型を得る。
- `parameterizedDiagram_face`：関手の三角形の族の評価は、三角形の面への制限と厳密に可換。
- `unstraighteningPrecompositionIso`：指定辺による前合成を unstraightening へ写すと、その辺の像との相対合成になる。
- `unstraighteningPinchedPrecompositionIso`：同じ比較を G8 が使う pinched 写像空間へ戻す。

`SetSectionsLimitNaturality.lean`：

- `limitVertexIso_hom_eq_coneEdge`：極限頂点の標準同型の順射は、錐の圏で指定した任意の普遍辺の射影の類。
- `limitConeEndpointComparison`：極限への写像の族を、両端固定の錐の族へ写す比較。
- `limitConeEndpointComparison_isQCatEquivalence`：指定錐の極限性により、錐の族への比較は全写像空間の同値となる。
- `limitConeMapIsoOfConeFamilyIso`：錐の族として同型な二つの写像の族は、極限への写像の族として同型。
- `limitConeMap_homMk_eq_of_coneFamilyIso`：錐の族の同型から、空間のホモトピー圏での写像の等式を得る。
- `sectionsConeFamilyRestriction`：要素の圏に沿う制限を、頂点と図式を固定した錐の族へ移す。
- `sectionsConeFamilyRestriction_fromSections`：切断の制限と錐の族への比較は、全パラメータで厳密に可換。

`SetSectionsSieveNaturality.lean`：

- `representableProjectionCone`：表現可能前層の要素の圏の始対象から射影への明示的な錐。
- `representableProjectionCone_vertex`：この錐の頂点は底の U そのもの。
- `representableEvaluationCone`：任意の前層 F の U での値から、表現可能前層の要素の図式へ向かう錐。
- `representableEvaluationCone_vertex`：評価錐の頂点は F(U)。
- `sieveEvaluationCone`：F(U) の評価錐を篩の要素へ制限する。
- `sieveEvaluationCone_vertex`：篩への制限後も頂点は F(U)。
- `representableEvaluationConeMap`：明示的な評価錐から、指定された表現可能側の極限錐への普遍辺。
- `sieveEvaluationConeMap`：篩へ制限した評価錐から、指定された篩側の極限錐への普遍辺。
- `sieveConeRestriction`：篩の要素への制限を、錐の圏全体の射として使う。
- `sieveConeRestriction_cone`：錐の圏の制限は、先行 API の指定錐の制限に一致する。
- `sieveConeRestriction_projection`：錐の圏での制限は頂点への射影を厳密に保つ。
- `sieveRestrictConeEdge`：錐の比較辺を、同じ篩の要素へ制限する。
- `sieveEvaluationConeMap_factor`：評価錐から篩側の極限への普遍辺は、表現可能側の極限を経由しても同じ類。
- `sieveEvaluationConeMap_postcomposeIso`：上の錐の普遍辺の一意性を、任意の M からの全写像空間へ移す。
- `representableEvaluationMap`：表現可能側の評価 F(U) から指定極限への普遍射。
- `sieveEvaluationMap`：篩へ制限した評価 F(U) から指定極限への普遍射。
- `sieveSectionsMap_edge`：始点の頂点表示を正規化しても、切断制限の元の一次単体は変わらない。
- `sieveEvaluationTriangle`：F(U) からの二つの普遍射と、指定された sieveSectionsMap の可換三角形。
- `sieveEvaluation_postcomposeIso`：評価からの二経路は、指定された切断制限の後合成を含む全写像空間で同型。

### 残る数学的な一歩

段 2 は、切断制限と G8 別版の後段（`coherentDiagramSectionsCone` から指定極限錐への比較、
`spaceUniverseValueEquivalence`、`covariantRepresentableValueEquivalence`）との照合。
今回の `sieveEvaluation_postcomposeIso` は評価錐側の全写像空間の比較であり、この照合そのものではない。
`limitConeMapIsoOfConeFamilyIso` に渡す明示的な錐の族の同型を構成する必要がある。
段 3 は、篩包含に沿う `elementsComparisonNatural` の自然性を底を固定した相対写像空間内で示し、
`relativePreIso` と段 2 の比較を合わせて G8 の四角形を閉じる。
頂点ごとの一致だけで完成と扱わない。


## IF-G2-finish 段 2 の途中：評価側の Ho 等式（2026-11-05）

**②は未完。停止点 2 の完成報告ではなく、証明済み補助の途中保存。main は動かさず、取り込みは Claude が行う。**

追加：`SetSectionsSieveHomotopy.lean` の
`SetWeight.sieveEvaluation_postcompose_homMk_eq`。
任意の篩・前層・M・指定極限錐について、全写像空間の射として
`[post(representableEvaluationMap) ≫ post(sieveSectionsMap)] = [post(sieveEvaluationMap)]`
を `Ho(SpaceInfinity)` で示す。始域は `Map(M,F(U))`、終域は `Map(M,cS.vertex)`。
証明は段 1 の `sieveEvaluation_postcomposeIso` を
`coherentKanEdge_homMk_eq_of_functorIso` に渡す。
頂点ごとの等式ではないが、段 1 の全族同型の直接の帰結であり、G8 との新しい照合を証明したものではない。

検証：新規モジュールと直接の入口 F2 の小さなビルド PASS、F2 単独監査 PASS。
入口と監査の通常 import に登録し、明示宣言とモジュールの全生成宣言を監査。
新規モジュールの監査は 1 宣言、sorry・新規公理 0、標準 3 公理のみ。全ビルドなし。

残る接続をソース上で確認した：

- `sectionsConeFamilyRestriction_fromSections` は切断の制限と共通の固定端点模型の比較の等式。
- `limitConeMap_homMk_eq_of_coneFamilyIso` は、その模型内の**全族の同型を入力に要求**する。
- `limitConeEndpointComparison` は `fixedApexConeHomComparison` を経由し、
  `rightFibrationMappingSection` で選択した切断を使う。
  `RightFibrationHomComparison.lean` の仕様はこの選択の終点に関する自然性を主張していない。
- `representableEvaluationConeMap` と段 1 の評価三角形だけでは、上記の選択された比較射と
  G8 の `coherentDiagramSectionsCone`・値の比較を結ぶ全族の同型はまだ得られていない。

次に必要なのは、錐の辺に沿う `rightFibrationHomComparison` の全族の比較を
共通の自明 Kan fibration の span 上で構成し、固定端点模型へ移すこと。
それを切断制限の厳密な自然性と合成し、さらに G8 の既存の値の比較との一致を示す。
必要な同型を仮定として追加した「②」は置いていない。未完の Lean 宣言も置いていない。
