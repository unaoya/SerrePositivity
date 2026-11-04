# IF-G2 G8n：証明済みの部分と未解決の自然性

作業枝：`math/g2`。基点：`74b8bdd0b`（W2c・B4・G1 を含む main）。
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
- 監査：初回実行で追加監査のカウンタの型推論エラーを検出し、`count : Nat` に修正。
  修正後の再実行は他の `lake build` が動いているため待機中。**監査 PASS は未確認。**
- G1 の既存宣言は変更なし。新規ソースに `sorry`・新規公理なし。
