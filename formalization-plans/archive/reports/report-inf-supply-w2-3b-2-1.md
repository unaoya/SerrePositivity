# IS-W2 の報告（report-inf-supply-w2.md） — 3b-2 前半（G10 の着手〜中間停止）（§22〜§72、2026-11-12〜11-13）

元の報告：[report-inf-supply-w2.md](../../stage-ii/inf-supply-b/report-inf-supply-w2.md)

## 22. 3b-2（G10）の着手：積全複体・標準脚・離散成分（2026-11-12 夜）

### 22.1 範囲と基準

指示書 §9 と停止点1の検収を受け、main `997fc2dfe`（登録 `cfa0e8324` と §9 を含む）を fast-forward で取り込んだ。3b-2 を開始する。§21末尾の「段2は未着手」は停止点1時点の記録であり、本節から更新する。

G10 は、一般の余単体的複体の積 Tot と D(A) の指定極限錐を、図式の射・全パラメーター・指定錐の族まで照合し、離散加群版をその制限として返す範囲を保つ。見込み 5,000–7,200 行、上限 8,400 行。途中の規模報告は止まらずに行う。保守的に当初の段0の上端の半分（1,600行）でも一度実測を知らせる。3b-4 の点つき Kan Tot は K の再開へ移り、このレーンでは作らない。3b-3 の分担を先取りしない。

### 22.2 最初の部品

新規10本、638行（全て3b-2に算入、共通への付け替えなし）。既存の宣言は変更していない。

| 部分 | 本数 | 行数 | 今回の内容 |
| --- | ---: | ---: | --- |
| 一般の積 total | 3 | 243 | `ProductTotal`、`ProductTotalZeroRow`、`ProductTotalFirstRow`。反対圏上の直和 total により全関手を構成。指定射影・lift・射の判定・自然性・全微分の二項公式・各対角線の積錐の普遍性。零行への鎖写像と第一行の射影による指定零ホモトピー。 |
| 余単体的複体 | 5 | 265 | `ProductTotal`、`ProductComponents`、`ProductCone`、`StandardZeroLeg`、`StandardCofaceHomotopy`。交代余面複体を整数へ零延長して適用。全次数 q の積を元の n≥0 の成分 Xⁿ[q−n] で提示し、射の自然性を証明。零次の標準脚は自然変換、二つの余面の後の脚は同じ第一行の射影でホモトピック。 |
| 離散入力の成分 | 2 | 130 | `SingleComponent`、`DiscreteComponents`。一つだけ非零の成分を持つ積の同型。加群を内部次数零へ関手的に埋め込み、負の全次数の零性と、非負全次数 n の元の余単体加群への自然同型。 |

直和全複体の無限和を積へ置き換える推測は使わない。両方向を反対圏へ移した直和 total の射影・普遍性を使用する。全微分は横微分と `(-1)^a` 倍の縦微分の二項で、無限和や積の完全性の仮定はない。全ての縦次数は非有界のまま。

`componentπ X n q` は次数ごとの射であり、Xⁿ への鎖写像と称していない。鎖写像として証明したのは零次の `standardZeroLeg`。二つの余面の両立は `standardCofaceHomotopy` が与える。高次の join 錐全体は未構成である。

離散加群の `discreteTotalDegreeNatIso` は各次数の通常の自然同型まで。交代余面複体との**複体の自然同型**、D(A) への全関手の比較やホモロジー比較が閉じた、とはしていない。

### 22.3 次の接続

1. 離散入力の成分同型を全微分と照合して、零延長された交代余面複体との複体の自然同型へまとめる。
2. 半自由試験対象からの Hom と積 total の交換、end 側の重みの比較・正規化を作る。3b-1 の coend/co-Yoneda の添字・符号・非有界性の計算は使うが、coend の定理をそのまま end に適用しない。
3. 同じ標準脚と高次成分を持つ生の dg nerve の指定錐を作り、写像空間の極限判定に接続する。既存の `Project.DerivedCategories.dgNerve_isLimitCone_iff_homTargetPointedRestriction` が同じ実錐を保持する入口となる。
4. 既存の `Project.DerivedCategories.dgModuleResolvedInfinity_isLimitCone_of_raw` により、生の指定極限錐から半自由出力へ移す経路を確認した。これは入力の Small 性や生の出力の射影性を要求しない。積 total 自体を射影的・半自由と仮定しない。全関手と指定錐の族の輸送は引き続き証明が必要。

見込みはまだ §21.3 の 5,000–7,200 行から変更しない。638行は最初の線形部品で、native 錐や全パラメーターの比較の実測をまだ得ていないため、これだけから下方修正しない。停止点2ではない。

### 22.4 検証・登録待ち

コード：`97dfd772b`（積 total の2本）、`59872193d`（成分・積錐の2本）、`7802069ad`（標準脚・余面ホモトピー・離散成分の6本）。

新規10本すべての鍵付き対象ビルド成功（2,290 jobs）。`--wait 3600` の整理券は一枚にまとめ、鍵の中はビルド・監査だけとした。待ち中に個別検査を通した離散成分2本も、開始前の同じ対象ビルドの束へ含めた。初めの8本の実測は508行（途中のチャットの509行は数え違い）、最終10本は638行。

一時監査 `/private/tmp/AuditISW2G10Ten.lean`：**156宣言、標準三公理のみ**（各モジュール 42, 13, 14, 7, 22, 13, 8, 10, 8, 19）。`sorry`・独自公理0。個別検査も成功。ビルドの警告は空白・行長の style linter のみ。ログ `/private/tmp/isw2-g10-build-3.log`、終了コード0。鍵は解放済み。

基準 `997fc2dfe` からの Lean 差分は新規10本のみ。既存の数学宣言・drafts・入口・正式監査は変更していない。ルートビルドは実行していない。今回の束は着手の途中報告であり、停止点2や規模上限による中断ではない。

登録対象（停止点2で調整役が判断）：

```text
SerrePositivity.HomologicalAlgebra.ProductTotal
SerrePositivity.HomologicalAlgebra.ProductTotalZeroRow
SerrePositivity.HomologicalAlgebra.ProductTotalFirstRow
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductTotal
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductComponents
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductCone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardZeroLeg
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardCofaceHomotopy
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SingleComponent
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteComponents
```


## 23. 3b-2 続き：離散入力の複体比較と指定射影（2026-11-12 夜）

### 23.1 今回閉じた比較

§22.3 の 1（離散入力の次数同型を微分と照合して、零延長された交代余面複体との自然同型へまとめる）を進めた。最終状態の追加は6本・433行、3b-2累計は16本・1,071行。§21.3 の完成見込み 5,000–7,200 行、上限 8,400 行は変更しない。保守的な途中報告点 1,600 行にはまだ達していない。

- `HomologicalAlgebra.ProductTotalSingleRow`（122行）：任意の非有界整数複体を縦次数零に置いた二重複体について、同じ `(q,0)` 射影を使う `singleRowDegreeIso`、微分との可換性、射への自然性を証明し、`singleRowNatIso` にまとめた。積の完全性を要求しない。
- `HomologicalAlgebra.MapExtendComplex`（30行）と `MapExtendComponents`（47行）：既存の `SerrePositivity.mapExtendIso`・`mapExtendIso_naturality` を自然同型として束ね、元の次数での前向き・逆向きの成分公式を証明した。最初に書いた交換の重複証明は取り除いた。変更したのはこのレーンで今回追加した未取り込みファイルだけで、既存 `HomologicalAlgebra/MapExtend.lean` は変更していない。
- `CosimplicialTotalization.DiscreteComplexComparison`（47行）：既存の加法的関手と交代余面複体の交換、上記の零延長との交換、一行二重複体の比較を合成し、`discreteTotalCochainNatIso : discreteTotalFunctor A ≅ discreteCochainFunctor A` を構成した。対象ごとの同型ではなく、余単体加群の図式の射と微分を含む複体の自然同型。
- `CosimplicialTotalization.DiscreteComparisonComponents`（103行）：同じ比較射の非負行を計算し、`discreteTotalCochainNatIso_hom_f_degreeIso` で、元の交代余面複体の零延長同型を後合成すると前回の `discreteTotalDegreeIso` **そのもの**になることを証明した。比較同型を選び直して済ませていない。

鍵待ち中に次の Hom 比較にも着手し、`CosimplicialTotalization.HomTotalComponents`（84行）を追加した。`homTotalComponentsEquiv` は次数 p の `Homogeneous P (Tot X) p` と `∀ n, Homogeneous P (Xⁿ) (p−n)` の線形同値。元の積射影を使う `homTotalComponent` と、`componentLift` を使う `homTotalLift` を作り、両方向の往復と成分による射の判定を証明した。試験対象・入力とも非有界のまま。Hom 微分との可換性・全関手の自然性を証明済みとはしていない。

比較先 `discreteCochainFunctor` は、`alternatingCofaceMapComplex (ModuleCat A)` と `ComplexShape.embeddingUpNat.extendFunctor (ModuleCat A)` の合成。既存の E∞ 界面や BS の `cosimplicialCochains` の宣言は変更していない。

### 23.2 native 極限へ残るもの

今回の結果は線形の複体比較であり、G10 の停止点2ではない。特に次は未完了である。

1. 半自由試験対象 P からの `homComplex A P (Tot X)` と `Tot (homComplex A P X)` の全関手比較。各次数の線形同値は今回の `homTotalComponentsEquiv` で得たが、微分・射の自然性と指定脚との両立を証明する必要がある。通常の複体の極限を保つというだけでは Tot の比較にならない。
2. 正規化・非正規化と end 側の重みの比較、同じ高次成分を持つ生の dg nerve の join 錐、その極限性。
3. 既存の `dgModuleResolvedInfinity_isLimitCone_of_raw` による半自由出力・D(A) への輸送と、**全パラメーターの指定錐の族**。G10 ではこれを3b-3へ移さない。
4. その D(A) 側の比較から、脚・標準射と両立するホモロジー比較と入口 `cosimplicialModule_limitCone` を返すこと。

次の Hom 比較で使う実名は `DifferentialGraded.homComplex`（Mathlib `CochainComplex.linearHomComplex`）、`Homogeneous`（`Cochain`）、`tensorRightHomAdjunction`。`HomLimits.homComplex_limit_ext` は指定された**通常の複体極限**への判定なので、積 Tot の極限性を先取りする入口には使わない。§21.4 の符号と非有界な成分計算を再利用する。

### 23.3 検証と登録待ち

コードコミットは `00538db81` と `471058022`。後者で、今回作った零延長比較を既存 `MapExtend` の再利用に整理し、指定成分の等式と Hom の次数付き線形同値を追加した。

最終の**全16本の鍵付き対象ビルド成功**（2,298 jobs）。`--wait 3600`、一回1,700秒の上限、整理券は同時に一枚。最初の束は15本で開始したため、Hom の1本を加えた検証はその終了・鍵解放を確認した後に一枚で並び直した。最終ログ `/private/tmp/isw2-g10-build-6.log`、終了コード0。鍵は解放済み。

一時監査 `/private/tmp/AuditISW2G10Sixteen.lean`：**232宣言、標準三公理のみ**（42, 13, 14, 7, 22, 13, 8, 10, 8, 19, 26, 2, 12, 3, 10, 23）。`sorry`・独自公理0。個別検査も成功。style／flexible tactic の linter メッセージ以外の検査上の問題はない。

基準 `997fc2dfe` からの Lean 差分は新規16本のみ。既存の数学宣言・drafts・入口・正式監査は変更していない。ルートビルドは実行していない。取り込みや承認を求める停止点ではなく、G10 の停止点2には未到達。

今回の追加登録対象（先の10本に加える）：

```text
SerrePositivity.HomologicalAlgebra.ProductTotalSingleRow
SerrePositivity.HomologicalAlgebra.MapExtendComplex
SerrePositivity.HomologicalAlgebra.MapExtendComponents
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteComplexComparison
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteComparisonComponents
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalComponents
```

## 24. 3b-2 続行：Hom 成分の微分・両変数自然性

### 24.1 今回の部品

追加6本・332行、3b-2累計22本・1,403行。完成見込み5,000–7,200行、上限8,400行は据え置く。保守的な途中報告点1,600行には未到達。既存の数学宣言・drafts・入口・正式監査は変更していない。

- `HomologicalAlgebra.ProductTotalHomDifferential`（54行）：一般の非有界二重複体の同じ積射影から `homRowComponent` を定義し、Hom 微分の行成分を横微分と `(-1)^a` 倍の行内 Hom 微分の和に分けた。試験複体の前合成項の符号は `a+(p+1−a)=p+1` で一致する。有界性・積の完全性を仮定しない。
- `CosimplicialTotalization.HomTotalDifferential`（72行）：上の式を指定 `rowIso` で移し、前回の `homTotalComponent` 自体について `homTotalComponent_differential` を証明。第0行の横項の消滅も証明した。
- `CosimplicialTotalization.HomTotalHorizontal`（54行）：全ての非負行の `rowDifferential` と、正の行の横項を元の交代余面微分の後合成で表す `homTotalHorizontalTerm_succ_v`。零延長の射を選び直していない。
- `CosimplicialTotalization.HomTotalNaturality`（55行）：指定成分の評価公式、入力図式の射についての後合成の自然性、試験対象の射についての前合成の自然性。
- `HomologicalAlgebra.ComplexHomAdditive`（29行）：既存の `DifferentialGraded.homFunctor` に加法性の instance を供給。既存の関手の定義は変更していない。
- `CosimplicialTotalization.HomDoubleComplexComparison`（68行）：加法的関手と交代余面・零延長の既存の交換を合成し、`homDoubleComplexIso` とその積全複体への像 `homDiagramTotalIso` を作った。いずれも入力図式の射を含む自然同型。前向き射の行成分が `rowIso` とその Hom 像の合成であることも証明した。

最後の自然同型は **Tot(Hom(P,X)) と、元の二重複体の各行に Hom(P,−) を適用した積 Tot の比較**である。`Hom(P,Tot X)` からの複体同型が完成したという主張ではない。今回はそのための微分・自然性・標的の交換を揃えた。

### 24.2 残りの順序

1. 元の二重複体の行射影を使い、`Hom(P,Tot X)` から行 Hom の積 Tot への複体の同型を構成する。今回の微分公式を閉性に、前回の次数付き線形同値を逆射に使う。今回の `homDiagramTotalIso` と合わせ、指定射影・射を保つ Hom–Tot の全関手比較へまとめる。
2. 正規化・重み付き end との比較、同じ高次成分を持つ dg nerve の join 錐とその極限性。
3. `dgModuleResolvedInfinity_isLimitCone_of_raw` による D(A) への輸送と全パラメーターの指定錐の族、元の加群版入口とホモロジー比較。

§23.2 の未完了項目は保持する。G10 の停止点2には未到達。

### 24.3 検証と登録待ち

コードコミット `391dbede1`。6本とも個別検査は成功。新規6本の**鍵付き対象ビルド成功**（2,295 jobs）、一時監査は**累計22本・292宣言、標準三公理のみ**。今回の6本の宣言数は21, 1, 13, 7, 7, 11。`sorry`・独自公理0。

整理券一枚・`--wait 3600`・一回1,700秒の上限で実行し、終了コード0を確認。ログ `/private/tmp/isw2-g10-build-7.log`、監査 `/private/tmp/AuditISW2G10TwentyTwo.lean`。鍵待ち中に追加した最後の1本も対象ビルドと監査に含まれたことを確認した。鍵は解放済み。style／flexible tactic の linter メッセージのみで、検査上のエラーはない。

基準 `997fc2dfe` からの Lean 差分は新規22本のみ。ルートビルドは実行していない。停止点2の検収・取り込みを求める報告ではない。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.ProductTotalHomDifferential
SerrePositivity.HomologicalAlgebra.ComplexHomAdditive
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalDifferential
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalHorizontal
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalNaturality
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomDoubleComplexComparison
```

## 25. 3b-2 続行：非有界 Hom–Tot の複体自然同型

### 25.1 早めの途中報告と実測

保守的な途中報告点1,600行に達したので、停止せず実測と残りを記録する。今回7本・465行を追加し、3b-2累計は29本・1,868行。完成見込み5,000–7,200行、上限8,400行は据え置く。この見込みとの差分として残りは約3,100–5,300行。半分の正式な基準を改定後の見込みに取る場合にも、ここでは早めに報告しておく。

§24.2 の1の中心である Hom–Tot の複体自然同型を閉じた。今回の一般補題は内部次数・横次数・試験対象のいずれにも有界性を課さない。積の完全性や試験対象の射影性も仮定しない。

- `HomologicalAlgebra.ProductTotalHomMap`（88行）：全次数等式を持つ `homRowLinear`、指定射影を保つ `homTotalDegreeMap`、前回の符号公式による微分可換性、鎖写像 `homTotalMap`。
- `HomologicalAlgebra.ProductTotalHomIso`（93行）：行 Hom の積の元を元の Tot への射へ戻す `homTotalDegreeInverse`。同じ射影で両逆を証明し、`homTotalDegreeEquiv` と複体同型 `homTotalIso` を構成。`homTotalIso_hom` により前向き射は `homTotalMap` そのもの。
- `HomologicalAlgebra.ProductTotalHomNaturality`（49行）：二重複体の射に関する `homTotalMap_naturality`、および `ProductTotal.functor ⋙ homFunctor P` と `homFunctor P` を行に適用した積 Tot の全関手の自然同型。
- `CosimplicialTotalization.HomTotalComparison`（90行）：一般比較と前回の `homDiagramTotalIso` を合成し、`productTotalFunctor A ⋙ homFunctor P ≅ homDiagramFunctor P ⋙ productTotalFunctor A` を構成。`homTotalNatIso_hom_component` で前向き射の各成分が前回の `homTotalComponent` **そのもの**であることを証明した。

鍵待ち中にさらに2本を追加した。

- `HomologicalAlgebra.ComplexHomPrecompose`（38行）：前合成と後合成の可換性、既存の Hom 関手間の `homPrecomposeNatTrans`。
- `HomologicalAlgebra.ProductTotalHomPrecompose`（53行）：一般の二重複体について、比較鎖写像と試験対象の前合成の可換性、およびそれを全関手上の自然変換の等式とする `homTotalNatIso_precompose`。

さらに `CosimplicialTotalization.HomTotalParameters`（54行）で、試験対象の前合成を全余単体図式へ適用する `homDiagramPrecompose` と、余単体版の `homTotalNatIso_precompose` を証明した。§24 の成分公式と今回の指定成分の等式で全関手上の自然変換の等式へ戻している。これで一般二重複体版・余単体版のどちらも、入力図式の射と試験対象の射の双方について同じ比較射を追跡できる。

### 25.2 残りと見積もり

次は正規化・重み付き end との比較と、同じ高次成分を持つ dg nerve の join 錐。今回は通常の複体圏の自然同型であり、native 極限性はまだ証明していない。`dgNerve_isLimitCone_iff_homTargetPointedRestriction` に入れるには実際の指定錐とその Hom 試験の比較が必要で、通常の複体の極限保存で代用しない。その後に半自由出力・D(A) への輸送、全パラメーターの指定錐の族、加群版入口を残す。

次工程で再確認した入口は `Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/BousfieldKan.lean` の `bousfieldKanHolimFunctor`・`bousfieldKanEvaluation` と、同節 `CoherentConeNativeComparison.lean` の指定錐からの native 切断比較。後者は docstring にもあるとおり BK の比較 q′ との一致を含まない。従って Hom–Tot 同型だけからその一致を推論せず、重み付き end と指定成分を照合する工程を残す。

残りの主な規模のリスクは、射列で添字づけた錐の高次成分と、余単体次数で添字づけた Tot 成分を結ぶ部分にある。3b-1 と同様に、既存の指定錐・Hom 判定を再利用し、存在だけの別の頂点への置き換えを避ける。G10 の停止点2には未到達。

### 25.3 検証と登録待ち

先の6本は鍵付き対象ビルド成功（2,298 jobs）、累計28本360宣言・標準三公理のみの監査を通過し、`08f80bda6` にコミット済み。最後の `HomTotalParameters` も個別検査は成功。先の検証の終了・鍵解放を確認してから、同じ `--wait 3600`・一回1,700秒の上限で最後の1本と累計29本の監査に並び直した。最後の対象ビルドも成功（2,299 jobs）、累計29本の一時監査は **364宣言、標準三公理のみ**。最後の1本は `54a7630b0` にコミットした。今回7本の宣言数は23, 19, 8, 12, 3, 3, 4。`sorry`・独自公理0。

ログは `/private/tmp/isw2-g10-build-9.log` と `/private/tmp/isw2-g10-build-10.log`、最終監査は `/private/tmp/AuditISW2G10TwentyNine.lean`。両方とも終了コード0を確認し、鍵は解放済み。整理券は常に一枚。新規ファイルの style longLine の警告、および依存ファイルの既存 linter メッセージ以外に検査上の問題はない。

基準 `997fc2dfe` からの Lean 差分は新規29本だけ。既存の数学宣言・drafts・入口・正式監査は変更していない。ルートビルドは実行していない。停止点2の検収・取り込みを求める報告ではない。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.ProductTotalHomMap
SerrePositivity.HomologicalAlgebra.ProductTotalHomIso
SerrePositivity.HomologicalAlgebra.ProductTotalHomNaturality
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalComparison
SerrePositivity.HomologicalAlgebra.ComplexHomPrecompose
SerrePositivity.HomologicalAlgebra.ProductTotalHomPrecompose
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalParameters
```


## 26. 3b-2 続行：積全複体への横ホモトピーの移送

### 26.1 検証済みの区切り

新規6本・325行を追加し、累計35本・2,193行。コードコミット `6036adcba`。
`ProductTotalHorizontalComponents` と `ProductTotalHorizontalHomotopy` で、指定積射影による横ホモトピーの成分とその方程式を証明した。縦微分の二項は隣接横次数の符号で相殺する。`CochainProductTotalizationHomotopy` は横の非負余鎖次数を整数へ零延長し、同じ二射と鎖ホモトピー同値を積全複体へ移す。内部次数の有界性・積の完全性・収束の仮定はない。

`ComplexOppositeHomotopy` は添字を保ち形を反転する反対化へ指定ホモトピーを移す。重みの鎖複体に反変な線形 end を適用する準備であり、次数の符号を反転する余鎖複体の反対化とは区別する。`FreePresheafLinearHom` は自由前層の線形 Yoneda 評価と重みの射への自然性、`FunctorComplexExchange` は複体値図式から図式値複体への逆向きの交換関手と両比較同型。

6本の鍵付き対象ビルド成功（1,545 jobs）。累計35本の一時監査は **427宣言、標準三公理のみ**。`sorry`・独自公理0。`--wait 3600`、整理券一枚、一回1,700秒の上限で実行し、終了コード0と鍵の解放を確認した。ログ `/private/tmp/isw2-g10-build-11.log`、監査 `/private/tmp/AuditISW2G10ThirtyFive.lean`。既存の数学宣言・drafts・入口・正式監査は変更していない。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.FreePresheafLinearHom
SerrePositivity.HomologicalAlgebra.FunctorComplexExchange
SerrePositivity.HomologicalAlgebra.ProductTotalHorizontalComponents
SerrePositivity.HomologicalAlgebra.ProductTotalHorizontalHomotopy
SerrePositivity.HomologicalAlgebra.CochainProductTotalizationHomotopy
SerrePositivity.HomologicalAlgebra.ComplexOppositeHomotopy
```

### 26.2 続行中の部分

線形 end の全関手族、標準単体重みから元の余単体図式への自然同型、その鎖分解を積全複体へ移す部分を作業中。これらの未検証分はコミットに含めていない。通常の複体圏の比較だけでは native な指定錐の極限性をまだ得ていない。§25.2 の残り（正規化・BK との指定成分比較・native 錐・D(A) への輸送・全射と指定錐の族）を続ける。停止点2には未到達。見込み5,000–7,200行・上限8,400行は据え置く。

11-12 夜の指示を確認した。停止点2の報告後は承認待ちを挟まず、3b-4 の BE 模型の実現・Tot・U との比較へ進む。3b-3 は③-aの担当。3b-4 の開始時には coherent な図式の厳密化への依存を紙で記し、依存待ちまたは承認を要する判断では境目の紙の作業に移る。点つき Kan 複体の Tot と⑤aの既存ファイルは対象外。


## 27. 3b-2 続行：標準重みと bar 重みの線形 end

### 27.1 比較の内容

§26 の後に新規7本・521行を検証し、累計42本・2,714行。

- `LinearWeightEnd`：線形重み W と複体値図式 X の end の複体。次数 q の元は W から X の次数 q への自然変換である。係数の後合成と重みの前合成を明示し、全関手族と加法性を証明した。対象・二種類の射を名前付きの部品に分けることで、関手構造の不必要な定義展開を避けている。
- `FreeWeightEndEvaluation`・`StandardWeightEnd`：自由単位重みの恒等射の生成元で 1 を評価する複体自然同型。元の余単体図式の全射と全単体作用素に自然。
- `LinearWeightEndTotalization`：鎖複体の重みを反対化して余鎖の end を取り、積全複体へ送る。元の指定鎖ホモトピー・鎖ホモトピー同値を保持する。有界性は不要。
- `AlternatingFaceOpposite`・`StandardWeightTotalComparison`：重みの交代面複体の反対化と交代余面複体を比較し、標準重みの end の積全複体から元の `productTotalFunctor` への同型を構成した。各横次数の前向き射が指定された自由単位重みの評価そのものであることも照合した。
- `BarWeightEndComparison`：3b-1 の `SimplicialRealization.barStandardWeightHomotopyEquiv` を再利用した。元の積 Tot から bar 重みの線形 end の積全複体への鎖ホモトピー同値を得る。前向き射は `barStandardWeightComparison` の前合成そのもの。新しい任意の持ち上げを前向き射には使っていない。

### 27.2 検証

最初の4本は `4e7023038`。鍵付き対象ビルド（1,974 jobs）と累計39本487宣言の監査が成功。次の3本も鍵付き対象ビルド（2,344 jobs）と累計42本 **512宣言、標準三公理のみ**の監査が成功した。個別検査も成功、`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-12.log`・`isw2-g10-build-13.log`、最終監査 `/private/tmp/AuditISW2G10FortyTwo.lean`。双方とも `--wait 3600`・整理券一枚・一回1,700秒の上限で終了コード0。鍵は解放済み。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.LinearWeightEnd
SerrePositivity.HomologicalAlgebra.FreeWeightEndEvaluation
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightEnd
SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalization
SerrePositivity.HomologicalAlgebra.AlternatingFaceOpposite
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalComparison
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BarWeightEndComparison
```

### 27.3 半分での実測と残り

改定後の見込み5,000–7,200行の下端の半分2,500行も超えたので、停止せず実測を更新する。実測2,714行、残りの見込みは約2,300–4,500行、上限8,400行。係数図式の射を重みの全鎖複体上の自然変換として扱う部分を続けている。

今回の bar は既存の `coefficientBarWeight SimplexCategoryᵒᵖ`。その各値は Under の nerve から作られ、BK の `Over` の nerve と同一だとはまだ主張していない。反対圏・正規化・指定錐の成分を照合して Hom 試験の native 切断比較へ移す部分が残る。指定脚・高次単体を持つ join 錐、その極限性、D(A) への輸送、全射と指定錐の族、加群版入口も未完了。通常の複体の鎖ホモトピー同値をもって G10 の完了とはしない。


## 28. 3b-2 続行：指定比較の全射への自然性と Moore 正規化

### 28.1 完了した追加部分

新規4本・225行、コード `7bd6022f7`。累計46本・2,939行。

- `LinearWeightEndTotalParameters`：係数図式の射を、重みの全鎖複体上の自然変換 `linearWeightEndTotalMap` へ移す。係数と反変重みの全関手族 `linearWeightEndTotalFamily` と、指定重み比較の自然性を構成した。
- `StandardWeightTotalNaturality`：§27 の二重複体比較の係数自然性を、同じ積全複体関手で移す。`standardWeightEndTotalNatIso` は元の `productTotalFunctor` への全関手の自然同型で、各対象の射は既存の `standardWeightEndTotalIso` の射。
- `BarWeightEndNaturality`：固定した先頭頂点比較による前合成を、全係数図式上の自然変換 `barWeightEndTotalComparison` にまとめた。各対象での射は §27 の鎖ホモトピー同値の前向き射そのもので、各対象で擬同型。
- `LinearWeightEndNormalization`：既存の Dold–Kan の `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` を再利用し、Moore 包含の前合成による end の積全複体の鎖ホモトピー同値を構成。係数図式の全射への自然性も証明した。内部次数に有界性を課していない。

### 28.2 main 取り込み後の検証

main `3b806b942` を `b51fcd150` で枝へ取り込んだ（競合なし）。夜の進め方と IS-W2 §10 の分担を作業枝へ反映した。自レーンから既存の数学宣言を変更していない。

その後、新規4本を含む **累計46本すべて**の鍵付き対象ビルドが成功（2,383 jobs）。一時監査は **552宣言、標準三公理のみ**。`sorry`・独自公理0、個別検査も成功。ログ `/private/tmp/isw2-g10-build-14.log`、監査 `/private/tmp/AuditISW2G10FortySix.lean`、全対象一覧 `/private/tmp/isw2-g10-fortysix-modules.txt`。`--wait 3600`・整理券一枚・一回1,700秒の上限で終了コード0を確認し、鍵は解放済み。ルートビルドは行っていない。入口と正式監査への登録は調整役へ残す。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalParameters
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalNaturality
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BarWeightEndNaturality
SerrePositivity.HomologicalAlgebra.LinearWeightEndNormalization
```

### 28.3 次の工程

停止点2には未到達。通常の複体上の比較・係数自然性・正規化の計算部品を閉じた段階であり、native な join 錐はまだ構成していない。次は、正規化された線形 bar end の成分を、指定 join 錐の脚と高次単体に照合する。既存の `dgNerve_isLimitCone_iff_homTargetPointedRestriction` と `coherentCone_isLimit_iff_reflectedNativeComparison` は実際の錐を入力に取るので、その入力と切断比較を構成する工程を省略しない。`Under(Δᵒᵖ)` と BK の `Over(Δ)` の反対向きも照合する。

この後に D(A) への輸送・全射と指定錐の族・加群版入口を残す。見込み5,000–7,200行、上限8,400行は据え置き。夜の指示どおり承認待ちは挟まず続行し、停止点2に達したら報告をコミットして3b-4へ進む。


## 29. 3b-2 続行：反対 under と BK over の重みの照合

### 29.1 閉じた比較

新規6本・335行、コード `164e9d61d`。累計52本・3,274行。

- `UnderOppositeOverNerve`：既存の `Under.opEquivOpOver` の厳密な逆関手を nerve に移し、底の全射に自然な同型を構成した。さらに既存の `nerveOppositeIso` と合成し、二重反対圏から戻した `underNerveWeight Jᵒᵖ` が **`bousfieldKanWeight J ⋙ SSet.opFunctor`** と同型であることを示した。over 重みそのものとは区別している。
- `AlternatingReverseSigns`：Fin.rev による交代和の添字替えと、n+1 次元の境界の反転符号 `(-1)^(n+1)` を証明。
- `AlternatingFaceReverse`：次数符号を `ε₀=1`、`εₙ₊₁=(-1)^(n+1) εₙ` として、単体順序反転後の交代面複体から元への同型を構成した。単体的対象の全射に自然で、零次数では恒等射。
- `OverNerveCoefficientWeight`・`DoubleOppositeOverWeight`：重みの各単体の係数余積と二変数の交換を使って線形化し、元の bar 鎖重みと二重反対圏へ移した BK over 鎖重みの符号付き同型を構成した。
- `CosimplicialTotalization.BousfieldKanWeightEndComparison`：元の `productTotalFunctor` から BK over 重みの線形 end の積全複体への自然変換を構成した。各対象での射は、元の bar 比較に上記の鎖同型の前合成を合成した鎖ホモトピー同値の前向き射そのもの。全図式に自然で、各対象で擬同型。

### 29.2 検証と登録待ち

個別検査成功。新規6本の鍵付き対象ビルド成功（2,517 jobs）、累計52本の一時監査は **605宣言、標準三公理のみ**。`sorry`・独自公理0。`--wait 3600`、整理券一枚、一回1,700秒の上限で終了コード0を確認し、鍵は解放済み。ログ `/private/tmp/isw2-g10-build-15.log`、監査 `/private/tmp/AuditISW2G10FiftyTwo.lean`、全対象一覧 `/private/tmp/isw2-g10-fiftytwo-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.UnderOppositeOverNerve
SerrePositivity.HomologicalAlgebra.AlternatingReverseSigns
SerrePositivity.HomologicalAlgebra.AlternatingFaceReverse
SerrePositivity.HomologicalAlgebra.OverNerveCoefficientWeight
SerrePositivity.HomologicalAlgebra.DoubleOppositeOverWeight
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BousfieldKanWeightEndComparison
```

### 29.3 native 錐へ残る接続

§28.3 の under/over の向きの照合は閉じた。残りは、正規化した線形 end と Hom 空間の BK 切断比較を結び、同じ頂点・脚・高次単体の join 錐を構成して極限性を示すこと、その D(A) への輸送と全射・指定錐の族、加群版入口である。今回の擬同型だけを native 錐の極限性とはしていない。

調べた既存の入力は `EInfinity/ComplexLimits/NormalizedChainsHom`、`NormalizedChainsHomNaturality`、`NormalizedHomTargetNaturality`、`NormalizedHomZeroEvaluation`。これらは実正規化鎖と Dold–Kan の Hom 同値、始域・標的の自然性、零次数の指定評価を供給する。既存宣言を再利用する候補として確認しただけで、⑤aのファイルは変更していない。通常の複体の Hom 同値から native な全錐の切断比較への移送は引き続き必要。

見込み5,000–7,200行・上限8,400行は据え置く。停止点2には未到達。承認待ちは挟まず続行する。

## 30. 3b-2 続行：積 end の Hom 成分表示

### 30.1 検証済みの部品

コード `3de36dfc2`、新規6本395行。累計58本3,669行。

- `CochainProductTotalComponents`：任意の非負余鎖二重複体について、零延長の指定行同型と積射影、逆の成分 lift、指定積錐の極限性。元の余単体図式に限らないので、正規化した重みの end にも適用できる。
- `CochainProductTotalLinearComponents`：同じ指定射影による、各全次数と成分加群の積の線形同値。
- `ExtendedChainHomRows`：非負鎖重みを負次数へ零延長したものからの斉次射を、元の鎖次数 n の射の族で線形に表示。正の次数は零対象の一意性で処理。
- `ExtendedChainHomDifferential`：その成分表示で Hom 微分を縦横の二項に展開。零鎖次数では横項が実際の零延長によって消える。
- `WeightEndHomSigns`：成分の符号 `(-1)^(n(q+1)) εₙ` の縦・横の漸化式、平方が1、零鎖次数が1を証明。
- `WeightEndHomComponents`：積 end の各次数から、負次数へ延長した同じ重みからの斉次射への符号付き線形同値。

最後の宣言は次数ごとの同値であり、複体同型や native な錐の極限性を主張するものではない。微分の可換性は次の工程。

### 30.2 検証と登録待ち

個別検査と新規6本の鍵付き対象ビルド成功（2,305 jobs）。累計58本の一時監査は **709宣言、標準三公理のみ**。`sorry`・独自公理0。`--wait 3600`、整理券一枚、一回1,700秒上限で終了コード0。鍵は解放済み。ログ `/private/tmp/isw2-g10-build-16.log`、監査 `/private/tmp/AuditISW2G10FiftyEight.lean`、一覧 `/private/tmp/isw2-g10-fiftyeight-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CochainProductTotalComponents
SerrePositivity.HomologicalAlgebra.CochainProductTotalLinearComponents
SerrePositivity.HomologicalAlgebra.ExtendedChainHomRows
SerrePositivity.HomologicalAlgebra.ExtendedChainHomDifferential
SerrePositivity.HomologicalAlgebra.WeightEndHomSigns
SerrePositivity.HomologicalAlgebra.WeightEndHomComponents
```

### 30.3 残り

停止点2には未到達。積全微分と上記の線形同値の可換性、正規化鎖の Hom と BK 切断比較、指定 join 錐と極限性、D(A) への輸送と全射・指定錐の族を残す。`CochainProductTotalDifferential.lean` は個別検査中の未コミット下書き。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

見込み5,000〜7,200行、上限8,400行は据え置き。夜の指示どおり承認待ちは挟まない。停止点2を閉じた後は、3b-3との依存関係を紙に書いてから3b-4のBE模型へ進む。

## 31. 3b-2 続行：積 end–Hom の複体同型と実正規化 BK 比較

### 31.1 閉じた比較

コード `a91223d7f`（5本317行）・`2069f341e`（1本57行）、今回6本374行。累計64本4,043行。

- `CochainProductTotalDifferential`：任意の非負余鎖二重複体の積全微分を、正の横次数の横項と符号付き縦項、零横次数の縦項で表示。零延長の指定行同型を保持する。
- `ExtendedChainHomRowDifferential`：零延長した鎖重みからの Hom 微分を、同じ全次数の成分の族へ戻した二つの公式。評価先の等式に伴う輸送も明示。
- `WeightEndHomEvaluation`：§30の次数同値の各成分は、元の積射影に指定符号を掛けたもの。零鎖次数の評価は変わらない。
- `WeightEndHomDifferential`：この次数同値が微分と可換であることを証明。縦項は `weightEndHomSign_vertical`、横項は `weightEndHomSign_horizontal` で合わせる。
- `WeightEndHomIso`：同じ次数同値を前向きの射に持つ、非有界積 end と線形 Hom 複体の実際の同型。
- `CosimplicialTotalization.NormalizedBousfieldKanHomComparison`：元の積 Tot → 指定 BK over end → Moore 包含による正規化 end → 上記 Hom 同型を合成した鎖ホモトピー同値。前向き射を明示して同じ射であることを証明し、擬同型も得た。重みは図式圏での実 Moore 正規化であり、通常の π₀ の Hom への置き換えではない。

### 31.2 検証と登録待ち

全6本の個別検査成功。先の5本の鍵付き対象ビルド（2,310 jobs）と累計63本の監査 **754宣言、標準三公理のみ**、最後の1本の鍵付き対象ビルド（2,539 jobs）と累計64本の監査 **766宣言、標準三公理のみ**が成功。`sorry`・独自公理0。各回 `--wait 3600`、整理券一枚、実行上限1,700秒、終了コード0。鍵は解放済み。

ログ `/private/tmp/isw2-g10-build-17.log`・`/private/tmp/isw2-g10-build-18.log`。最終監査 `/private/tmp/AuditISW2G10SixtyFour.lean`、一覧 `/private/tmp/isw2-g10-sixtyfour-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CochainProductTotalDifferential
SerrePositivity.HomologicalAlgebra.ExtendedChainHomRowDifferential
SerrePositivity.HomologicalAlgebra.WeightEndHomEvaluation
SerrePositivity.HomologicalAlgebra.WeightEndHomDifferential
SerrePositivity.HomologicalAlgebra.WeightEndHomIso
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanHomComparison
```

### 31.3 native 錐への残り

停止点2には未到達。§30で残した end–Hom の微分可換性と複体同型は閉じた。残りは、実正規化鎖から Dold–Kan Hom 空間への比較、指定 join 錐の構成とその制限写像の同値性、D(A) への輸送、全射・指定錐の族と加群版入口。

既存の `Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/GeneralHomHolimComparison` は、任意の小圏について `weightedCoherentConeSectionsComparison_homotopyEquivalence` と `reflectedHomHolimConeComparison_homotopyEquivalence` を供給する。離散・cospan・tower に限定した旧入口から一般化し直す必要はない。ただしここでの係数は反転した豊穣 Hom なので、今回の線形 BK 重みから移すときに反転と Dold–Kan の比較を明示し、元の指定錐の脚・高次単体と照合する必要がある。`dgNerve_isLimitCone_iff_homTargetPointedRestriction` と `coherentCone_isLimit_iff_reflectedNativeComparison` が要求する実際の join 錐を、この複体比較だけで代用しない。

見込み5,000〜7,200行、上限8,400行は据え置き。既存宣言・⑤aのファイル・入口・公式監査は変更していない。夜の指示どおり承認待ちは挟まず続行する。

## 32. 3b-2 続行：図式圏の Dold–Kan Hom と指定 BK 錐入力

### 32.1 検証済みの進捗

コード `81b5d243d`（8本505行）・`471857f6e`（2本102行）。今回10本607行、累計74本4,650行。

- `NegativeExtendTruncationHom`・`NegativeExtendTruncationNaturality`・`NegativeExtendTruncationTarget`：任意のアーベル圏で、負次数への零延長からの射と smart 切断への射を、同じ包含を使って同定。始域の全鎖射・標的の全複体射への自然性を証明した。既存の加群圏に固定された宣言は変更していない。
- `NormalizedWeightHom`：上記と Dold–Kan 随伴を合成し、図式圏で実 Moore 正規化した重みからの複体射を、元の単体的重みから Γ(truncLE′ H) への射と同定。重み・係数の両自然性を持つ。
- `CopowerUnitHom`・`CopowerUnitHomDiagram`・`CopowerUnitHomBifunctor`：指定余積包含の1で評価する同値を、集合、全図式、全二変数図式へ順に持ち上げた。小さい集合は ULift し、単体方向と添字圏方向の全作用素を保つ。
- `NormalizedLinearWeightHom`：実正規化線形重みからの複体射を、線形化前の集合的重みから Dold–Kan の集合値単体図式への自然変換へ移す同値。単なる次数ごとの写像の族ではない。
- `CosimplicialTotalization.NormalizedBousfieldKanConeRepresentative`：Hom–Tot 比較と正規化 BK 比較で元の Tot への射の零次閉元を移し、実複体射へ戻した。特に元の Tot の恒等射から、頂点を元の Tot とする指定錐の複体代表を構成。
- `CosimplicialTotalization.NormalizedBousfieldKanSetCone`：同じ二重反対圏上の集合的 over 重みを固定し、その線形化が既存の係数重みそのものであることを `rfl` で証明。指定錐代表を、両方向の全作用素を持つ集合的な単体写像へ移した。

最後の宣言は native な join 錐へ渡す入力であり、join 錐やその極限性の宣言ではない。頂点の選び直しはしていない。

### 32.2 検証と登録待ち

全10本の個別検査成功。鍵付き対象ビルドは、8本（1,800 jobs）、錐の複体代表（2,553 jobs）、集合的錐入力（2,577 jobs）が成功。累計監査は順に72本846宣言・73本855宣言・74本 **865宣言、標準三公理のみ**。`sorry`・独自公理0。各回 `--wait 3600`、整理券一枚、一回1,700秒上限、終了コード0。鍵は解放済み。

ログ `/private/tmp/isw2-g10-build-19.log`〜`/private/tmp/isw2-g10-build-21.log`。最終監査 `/private/tmp/AuditISW2G10SeventyFour.lean`、一覧 `/private/tmp/isw2-g10-seventyfour-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationHom
SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationNaturality
SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationTarget
SerrePositivity.HomologicalAlgebra.NormalizedWeightHom
SerrePositivity.HomologicalAlgebra.CopowerUnitHom
SerrePositivity.HomologicalAlgebra.CopowerUnitHomDiagram
SerrePositivity.HomologicalAlgebra.CopowerUnitHomBifunctor
SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightHom
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanConeRepresentative
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanSetCone
```

### 32.3 実測と残りの再見積もり

停止点2には未到達。指定錐を作るための恒等射からの複体代表と集合的入力はできた。一方、図式圏で取った smart 切断・Γ を対象ごとの dg Hom 空間へ照合する部分は、§31時点の一般の Hom 同値とは別工程であることを確認した。既存の加群版だけをそのまま図式版として使わない。

| 残り | 見込み（行） |
| --- | ---: |
| 図式圏の切断・Dold–Kan と対象ごとの Hom 空間の照合、指定評価 | 450〜650 |
| 全 Hom パラメータの BK 切断比較、反転係数と native 制限比較の同定 | 900〜1,300 |
| 指定 join 錐の構成、脚・高次成分の照合、D(A) への輸送 | 500〜850 |
| 全射・指定錐の族、加群版入口、検証の調整 | 400〜650 |

残り2,250〜3,450行、完成見込み **約6,900〜8,100行**（従来5,000〜7,200行から更新）。上限 **8,400行**、現在の残枠3,750行。現時点では上限内の見込みなので承認待ちは挟まない。超えそうになれば、夜の指示どおり検証済みを保存し、その線の Lean を止めて3b-3/3b-4の境目の紙の作業へ移る。

一般の切断比較には§31.3の `GeneralHomHolimComparison` を使う。実際の join 錐への戻しには `CoherentConeSectionSpace.fixedVertexConeSpaceEquiv` / `CoherentConeSections.cosliceSectionCone` が既存だが、必要な指定脚と高次単体の照合はまだ証明していない。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

## 33. 3b-2 続行：点ごとの切断・Γ と指定 BK 錐入力

### 33.1 検証済みの進捗

コード `1d4aefcd3`（7本346行）・`a98934a6a`（3本110行）。今回10本456行、累計84本5,106行。

- `DoldKanGammaMap`・`DoldKanGammaMapNaturality`・`DoldKanGammaDiagram`：Γ の指定余積比較を、単体方向・鎖射・加法関手の自然変換について証明し、図式圏の Γ と各点の Γ を全関手の自然同型で比較した。
- `NegativeExtendTruncationAdjunction`・`FunctorComplexExchangeEquivalence`・`PointwiseExtendComplex`：既存の延長–切断 Hom 同値を随伴へ、成分交換を圏同値へまとめ、零延長を点ごとの評価と交換する全自然同型を構成した。
- `PointwiseTruncationAdjunction`：上の指定零延長比較を左随伴側で移し、右随伴の一意性から切断の比較を得た。比較と余単位の可換性も証明し、任意に選んだ同型で代用していない。
- `PointwiseTruncation`・`PointwiseTruncationGamma`：成分交換の単位・余単位と指定 mate を合成し、図式圏の smart 切断と Γ を点ごとの切断・Γ に結ぶ全関手同型を構成した。
- `PointwiseBousfieldKanSetCone`：§32 の指定 BK 錐入力を同じ頂点のまま、各点の Hom 複体から取った単体集合の全図式へ輸送した。これはまだ native な join 錐ではない。

### 33.2 検証と登録待ち

鍵付き対象ビルド2回（1,629 jobs、2,588 jobs）、累計監査81本915宣言、84本 **935宣言、標準三公理のみ**。両回終了コード0、`sorry`・独自公理0。`--wait 3600`、一枚の整理券、一回1,700秒上限。鍵は解放済み。

ログ `/private/tmp/isw2-g10-build-22.log`・`/private/tmp/isw2-g10-build-23.log`。最終監査 `/private/tmp/AuditISW2G10EightyFour.lean`、一覧 `/private/tmp/isw2-g10-eightyfour-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.DoldKanGammaMap
SerrePositivity.HomologicalAlgebra.DoldKanGammaMapNaturality
SerrePositivity.HomologicalAlgebra.DoldKanGammaDiagram
SerrePositivity.HomologicalAlgebra.FunctorComplexExchangeEquivalence
SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationAdjunction
SerrePositivity.HomologicalAlgebra.PointwiseExtendComplex
SerrePositivity.HomologicalAlgebra.PointwiseTruncationAdjunction
SerrePositivity.HomologicalAlgebra.PointwiseTruncation
SerrePositivity.HomologicalAlgebra.PointwiseTruncationGamma
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.PointwiseBousfieldKanSetCone
```

### 33.3 残り

停止点2には未到達。次は反転した豊穣 Hom を使う既存 native 比較との照合。既存 `AlternatingFaceReverse` の指定符号同型を Moore 包含・射影と合成すれば、反転重みの実正規化を元の正規化へ鎖ホモトピー同値で戻せる。これを指定錐代表に前合成し、単体順序を再反転する経路で進める。反転を恒等射とは扱わない。

その後、指定脚・高次単体の照合、実 join 錐と極限性、D(A) への輸送、全射・指定錐の族が残る。完成見込み約6,900〜8,100行、上限8,400行は据え置き。残枠3,294行。既存宣言・⑤aのファイル・入口・公式監査は変更していない。夜の指示どおり承認待ちは挟まず続行する。

## 34. 3b-2 続行：反転 Hom への指定錐入力

コード `27e0437b2`、新規3本133行。累計87本5,239行。

- `NormalizedMooreReverse`：反転した単体的対象の Moore 正規化から元の正規化へ、指定包含・交代面反転符号同型・指定正規化射影を合成した鎖ホモトピー同値を構成。前向き射を全自然変換として固定し、同じ射である等式を証明した。
- `ReflectedBousfieldKanSetCone`：上の射の負次数延長を指定錐代表に前合成し、反転した BK 重み上の集合的錐入力を得た。
- `ReflectedPointwiseBousfieldKanCone`：点ごとの切断・Γ へ移し、二度の反転を解く指定同型を使い、元の BK 重みから反転 Hom 図式への全自然変換を構成した。

個別検査、鍵付き対象ビルド2,591 jobs、累計87本 **956宣言、標準三公理のみ**の一時監査が成功。`sorry`・独自公理0、終了コード0。`--wait 3600`、一枚の整理券、一回1,700秒上限。ログ `/private/tmp/isw2-g10-build-24.log`、監査 `/private/tmp/AuditISW2G10EightySeven.lean`、一覧 `/private/tmp/isw2-g10-eightyseven-modules.txt`。鍵は解放済み。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.NormalizedMooreReverse
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBousfieldKanSetCone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedPointwiseBousfieldKanCone
```

停止点2には未到達。今回の反転 Hom は Mathlib Γ で書いた点ごとの Hom なので、既存 `doldKanSimplicialHomIso` の逆向きと全図式射への自然性を通じて、`reflectedHomHolimConeComparison` の豊穣 Hom に照合する必要がある。そこから実 join 錐を取り、指定脚・高次単体と制限比較の同定、極限性、D(A) への輸送、全射・指定錐の族を閉じる。反転重み上の射の構成だけを native 錐の極限性とは数えない。

完成見込み約6,900〜8,100行、上限8,400行は据え置き、残枠3,161行。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

## 35. 3b-2 続行：実豊穣 Hom と元の Tot の native coherent 錐

### 35.1 検証済みの進捗

コード `0df2624c7`（3本149行）・`1299dd4e4`（3本138行）。今回6本287行、累計93本5,526行。

- `DiagramComparison.DoldKanClosedPostcomposition`：⑤a の既存 `EInfinity.ComplexLimits.standardDoldKanModuleIso_chainMap` を再利用。標準成分の全単体で鎖写像の作用と同じ閉射の豊穣後合成を照合し、指定 Γ 同型の後合成自然性を証明した。⑤a の既存ファイルは変更していない。
- `DiagramComparison.ComplexDoldKanHomDiagram`：元の複体の Γ Hom と、閉複体射圏の実豊穣 Hom を全関手の自然同型で結んだ。
- `EnrichedBousfieldKanCone`：指定錐入力を元の実反転豊穣 Hom の全図式へ輸送。遷移射を便宜的に定義し直していない。
- `SmallBousfieldKanWeight`：AsSmall で持ち上げた over の射列を元の射列へ戻す全自然変換を構成。係数環の宇宙を0に制限しない。
- `ReflectedWeightedNativeCone`：任意の指定 BK 自然変換を重み付き end の零単体にし、既存の `reflectedHomHolimConeComparison` と `fixedVertexConeSpaceEquiv` で実 join 錐を構成。左端の指定頂点の等式と、元の切断点への往復等式を証明した。
- `NativeCoherentCone`：上記を今回の入力へ適用し、元の積 Tot を頂点とする実 native coherent join 錐を構成。頂点の厳密な等式 `nativeCoherentCone_vertexMap` を証明した。極限性はまだ証明していない。

### 35.2 検証と登録待ち

再利用する既存対象の依存ビルド2回（5,934 jobs、4,260 jobs）、新規対象ビルド2回（6,034 jobs、6,045 jobs）が成功。新規対象の累計監査は90本988宣言、93本 **1,009宣言、標準三公理のみ**。`sorry`・独自公理0、各回終了コード0。鍵は `--wait 3600`、一枚の整理券、一回1,700秒上限、現在解放済み。

依存ログ `/private/tmp/isw2-g10-dependencies-25.log`・`/private/tmp/isw2-g10-dependencies-26.log`、対象ログ `/private/tmp/isw2-g10-build-27.log`・`/private/tmp/isw2-g10-build-28.log`。最終監査 `/private/tmp/AuditISW2G10NinetyThree.lean`、一覧 `/private/tmp/isw2-g10-ninetythree-modules.txt`。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DoldKanClosedPostcomposition
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDoldKanHomDiagram
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBousfieldKanCone
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallBousfieldKanWeight
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedWeightedNativeCone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeCoherentCone
```

### 35.3 残り

停止点2には未到達。実 join 錐と元の頂点は得られた。残りは標準脚・高次成分の照合、全 Hom パラメータの比較と native 制限への同定、極限性、D(A) への輸送、全射・指定錐の族。

`GeneralHomHolimComparison` の比較同値だけでは、元の Tot からの Hom 比較が同値であることにはならない。既存の鎖ホモトピー同値を単体的な全パラメータ比較へ接続し、その射が今回構成した錐からの制限であることを示す必要がある。⑤a の `NormalizedTensorHomBifunctor.normalizedTensorHomDoldKanIso`（正確な宣言は `SerrePositivity.EInfinity.ComplexLimits.normalizedTensorHomDoldKanIso`）が全パラメータ Hom の再利用候補。通常の導来極限の Hom 同値だけで native 極限性を代用しない。

完成見込み約6,900〜8,100行、上限8,400行を現時点では据え置く。残枠2,874行。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

## 36. 3b-2 続行：零次数評価・dg 錐・全 Hom パラメータ

コード `f6cc52ea3`、新規3本138行。累計96本5,664行。

- `NormalizedMooreReverseEvaluation`：指定 Moore 反転比較を非正規化複体の包含後に計算する式を証明。零次数では元の評価を厳密に保つ。標準脚の照合に使う部品であり、native 錐の脚との最終等式はまだ閉じていない。
- `NativeDGCone`：指定 coherent 錐全体を既存 `coherentComparison` で後合成し、同じ strict 図式の実 dg nerve の join 錐を構成。coherent 錐と dg 錐の両方について、頂点が元の積 Tot である等式を証明。
- `ReflectedWeightedHomComparison`：指定 BK 入力に任意の反転豊穣 Hom 単体を前合成する全パラメータ族を構成。既存の豊穣合成と閉射への自然性を使い、全添字射について自然な族を重み付き end への実射にまとめた。点や通常 Hom だけの比較ではない。同値性と native 制限への一致は別の残課題。

個別検査、鍵付き対象ビルド6,048 jobs、累計96本 **1,021宣言、標準三公理のみ**の一時監査が成功。`sorry`・独自公理0、終了コード0。`--wait 3600`、一枚の整理券、一回1,700秒上限。鍵は解放済み。ログ `/private/tmp/isw2-g10-build-29.log`、監査 `/private/tmp/AuditISW2G10NinetySix.lean`、一覧 `/private/tmp/isw2-g10-ninetysix-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.NormalizedMooreReverseEvaluation
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDGCone
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedWeightedHomComparison
```

停止点2には未到達。現在の中心課題は、今回の全豊穣 Hom 比較を既存の非有界 Hom–Tot/BK 鎖比較へ照合し、同値性を証明すること。さらに元の錐に対する native 制限との一致（または頂点評価を保つ族による比較）を証明する。Γ の零単体での Hom 同値だけでは全単体の同値性の代わりにならない。標準脚の最終等式、D(A) への輸送、全射・指定錐の族も残る。

完成見込み約6,900〜8,100行、上限8,400行は据え置き、残枠2,736行。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

## 37. 3b-2：指定 Γ 比較の検証と、規模による中間停止

### 37.1 検証済み

コード `2e23f92a7`、新規2本122行。累計 **98本5,786行**。

- `DiagramComparison.TruncatedDoldKanQuasiIso`：実 pinched Hom と Γ の既存の自然比較を使い、非有界複体の指定した擬同型の smart 切断・Γ 像が単体的ホモトピー同値になることを証明した。単位 Hom の指定同型を通すので、別の射に取り替えていない。
- `CosimplicialTotalization.NormalizedBousfieldKanHomSpace`：元の Hom–Tot/BK 比較を鎖ホモトピー同値として保持し、その同じ Γ 像の単体的ホモトピー同値性を証明した。標的は正規化 BK Hom 複体の Γ であり、重み付き切断空間との同定はまだない。

個別検査と鍵付き対象ビルド **4,355 jobs**、累計98本 **1,041宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。鍵は `--wait 3600`、一枚の整理券、一回1,700秒上限、解放済み。ログ `/private/tmp/isw2-g10-build-31.log`、監査 `/private/tmp/AuditISW2G10NinetyEight.lean`、一覧 `/private/tmp/isw2-g10-ninetyeight-modules.txt`。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.TruncatedDoldKanQuasiIso
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanHomSpace
```

既存宣言・⑤aのファイル・入口・公式監査は変更していない。

### 37.2 残る全単体比較と短縮経路の検討

Γ の零単体の随伴同値を全単体へ拡張する際、二つの始域を区別する必要がある。重み W、単体 Δ[n]、係数 Hom 図式 H に対して、切断空間側は `N_A(W × Δ[n])` から H への図式射、Γ Hom 側は `N_A(W) ⊗ N_A(Δ[n])` から H への図式射として現れる。正規化・負次数延長・宇宙持ち上げを含む指定比較と、その n・図式添字への自然性が必要になる。型が似ていることや零単体の一致では同値性を閉じられない。

確認した再利用候補：

1. `EInfinity.ComplexLimits.normalizedTensorHomDoldKanIso` は実テンソル Hom と Γ Hom の全二変数同型を供給する。ただし `N(W × Δ[n])` と正規化テンソルの比較はこの宣言の結論ではない。
2. Kerodon 配置の `DifferentialGradedCategories.normalizedEZHomotopy` と `KST.ProExcision.NormalizedEZHomotopyNaturality` は具体的 AW・shuffle とその自然なホモトピーを供給する。確認した型は `SimplicialObject (ModuleCat ℤ)`。一般 A の自由線形化に移し、今回の Moore 正規化・負次数延長・全パラメータの比較へ接続する仕事が残る。一般 A の鎖写像としては `EInfinity.Shuffle` が再利用候補だが、必要なホモトピー全体への直接適用はまだ確認できていない。
3. `HomotopicalAlgebra.Diagram.WeightedFrameHomNaturality` には全関手の Hom 同型がある。しかし確認した関連フレームの普遍性は模型構造とその比較の仮定を持つ。IS-W2 が禁止する `[ModelCategory SSet]` を追加する近道にはしない。
4. 既存 `coherentCone_isLimit_of_family_lifts` は native 錐を作り直さずに使える。必要なのは指定した全 Hom 族の持ち上げ・頂点評価の等式・制限の同値性。今回の Γ 比較だけでこの三条件が済んだとはしない。`reflectedWeightedHomComparison` の豊穣合成と同じ射になる照合が残る。

従来の完成見込み6,900〜8,100行は、(1) の全二変数同型から切断空間への接続と (4) の指定制限への照合を軽く数えすぎていた。確認済み API に基づく暫定的な残量は次のとおり。下限も完成の保証ではない。

| 未実装のまとまり | 追加見込み |
| --- | ---: |
| 正規化テンソル／積重みの比較、一般 A と全単体への自然性、同じ Γ 比較との照合 | 1,000〜1,600行 |
| 指定豊穣 Hom 合成・native 切断への持ち上げと頂点評価、極限性 | 600〜900行 |
| 標準脚の最終等式、D(A) への輸送 | 400〜700行 |
| 全図式射・指定錐の族・離散加群版入口 | 500〜900行 |
| 残り合計 | **2,500〜4,100行** |

完成見込み **8,286〜9,886行（約8,300〜9,900行）**、現在の上限 **8,400行**、残枠2,614行。上端が上限を超えるため、検証済みを上記コミットへ保存し、**3b-2 の Lean を中間停止する**。これは停止点2ではない。範囲・型を弱めず、上限を独自に引き上げない。夜の指示に従い、承認待ちで紙の作業まで止めず、次節の境目の整理へ移った。

## 38. 夜の代わりの作業：3b-3 と3b-4の境目

以下は型案と依存の整理であり、Lean の宣言や証明の完了報告ではない。3b-3 は③-a、BE 固有の3b-4は③-b。点つき Kan Tot は作らず、⑤aの既存ファイルも変更しない。

### 38.1 ③-a から使う入力

J は Δ・Δᵒᵖ の二つだけに固定する。略記 `I_J = nerve J`、`DA = derivedInfinityCategory A` とする。

| 入力の型案 | 必要な強さ／使用箇所 |
| --- | --- |
| `eval_A,J : StrictDiagramInfinity_A J → Fun(I_J, DA)` とその QCat 同値 | strict 複体図式の objectwise 擬同型による局所化からの実評価。BE 図式を忘却した strict 複体図式を、任意の coherent な D(A) 図式へ比較する段階 |
| `nerve (J ⥤ Complex A)` 上の実評価との全関手同型 | 忘却した元の図式の射・全単体を保持する。対象ごとに選んだ同値だけでは U との比較の正方形にならない |
| 図式の FunctorIso に沿う指定 join 錐／余錐の輸送と往復比較 | 同じ頂点・脚・高次単体を持つ錐の族の輸送。極限性／余極限性の保存と図式射への自然性まで |
| 3b-1から移した実現の全パラメータ比較 | strict な複体図式の実現関手と native な実現錐の族の比較。BE 実現の U 像を全関手として識別する最後の段階 |

G10 の指定 Tot 錐・全図式射の比較は引き続き3b-2の責任。3b-3 の評価同値の証明を G10 だけに依存させる循環は作らない。

### 38.2 BE 側の別の不足を D(A) の厳密化で隠さない

`Fun(I_J, DA)` の厳密化から、`Fun(I_J, CAlg_A)` の厳密化は自動的には出ない。忘却した図式を厳密化しても、BE 作用や coherent な代数射をその持ち上げに回復できたことにはならない。

したがって3b-4の段取りを次のように分ける。

1. **strict BE 図式での模型計算**：`J ⥤ (BarrattEccles.operad A).Algebra` の実現・Tot を置換と指定錐つきで扱う。これは加群値の3b-3を待たず検討できる。既存 `BarrattEccles.Diagram.projectiveModelCategory`・`weakEquivalence_iff` は図式の置換と弱同値判定に使うが、projective 全対象 fibrant を理由に通常 lim を導来 lim と同定しない。
2. **strict 図式の U 比較**：既存 `algebraCAlgSource_underlyingDerivedIso` を実際の `cAlgForgetDerived` との接続に使う。置換前の台の図式と同じ全自然変換を保つ。実現では U が右 Quillen であることだけから保存を結論しない。
3. **任意の coherent BE 図式への拡張**：BE 図式の局所化から `Fun(I_J, CAlg_A)` への比較、または同じ役割を果たす一般定理の BE 模型への適用が別途必要。③-aの加群版の結論だけで済ませない。一般定理が供給されたときの BE 固有の仮定の確認は③-b側とする案。新たな BE 厳密化そのものの範囲・規模が必要なら、実装前に調整役へ判断事項として残す。

3 の入力がない所に来たら、対象ごとの strict 表示の存在を仮定に足して先へ進まない。任意の coherent BE 図式の主張を strict 図式に黙って狭めない。

### 38.3 提案する比較の形と受け渡し

以下の名前は説明用の仮名で、既存宣言名ではない。

- `RealizeBE` と `TotBE` はそれぞれ strict 図式の局所化上の全関手。忘却との比較は `FunctorIso (RealizeBE ≫ U) (U_Diagram ≫ RealizeDA)`、`FunctorIso (TotBE ≫ U) (U_Diagram ≫ TotDA)` の形にする。
- それぞれに指定 join 余錐／錐の族を持たせ、比較同型の成分だけでなく、各脚・高次単体の U 像との両立を渡す。全単体が必要な点は今回の G10 の残課題と同じであり、零単体の Hom 同型で代用しない。
- 3b-3 による図式同型と錐輸送を使う場所は、strict BE 図式の台の模型計算が済んだ後。BE 側の coherent 図式の比較が得られた場合にのみ、その両方向の輸送へ拡張する。
- `EInfinityTheory.ofCosimplicial_forget` へ渡す制限は、余単体環代数を離散 BE 代数へ送った図式に固定する。`nerveMap (cosimplicialCochains A) ≫ strictToD A` との既存の型を保つ。
- `ofCosimplicial_cone` は上と同じ頂点の `TotalizationCone` を返す。別の極限対象を選んで `HasLimit` だけ返す形にしない。制限・係数変更の自然性は⑤aの既存の欄に合わせ、こちらで欄の型を変更しない。

### 38.4 置き場所・再利用・再開順

新規の BE 固有補助は `EInfinity/BarrattEccles/` の新規ファイル（仮案 `DiagramRealizationComparison`、`DiagramTotalizationComparison`、`DiagramForgetConeComparison`）。一般の図式局所化比較は③-aの `Project/DerivedCategories/DiagramComparison/` と役割を分け、一般の native 錐輸送は Kerodon の該当節へ置く。⑤aの `CAlgUnderlyingDerivedComparison`・frame・忘却関手の既存ファイルは読み取りと import の対象だけにする。

再利用候補は `HomotopyWeight` の実現とフレーム比較、`CAlgUnderlyingDerivedComparison` の実 U への全自然同型、3b-1の指定実現余錐、完成後の G10 の指定 Tot 錐。⑤aの報告§21.5にあるとおり、通常の sifted colim の創出や右 Quillen 性だけで導来実現の保存を済ませない。`forget_preservesSifted` を入力にしてその実現部分を証明する循環も作らない。

再開時はまず G10 の規模の判断を反映し、上記§37.2の全単体比較を閉じる。停止点2の後、strict BE 図式の計算を進める。③-aの3b-3の入力が揃うまでは境目を保ち、BE 値の厳密化の不足を加群版の供給済み欄へ押し込まない。今回の紙の整理のためのビルドは不要。鍵は取得していない。

## 39. 中間停止中の紙の確認：EZ の係数変更を短縮する候補

main の IS-W2 §10 までを再確認した。G10 の上限8,400行を変更する追記はまだないため、§37の Lean の中間停止を維持する。前ターンは検証済みコードと境界の報告を保存した進捗であり、鍵待ちではない。

§37.2の一般 A への移送について、再開時に先に試す短縮候補を具体化した。

- Mathlib `Algebra/Homology/Homotopy.lean` の `Functor.mapHomotopy`・`Functor.mapHomotopyEquiv` は加法的関手で実鎖ホモトピーを運ぶ。従って ℤ 上の EZ のホモトピーを `ModuleCat.extendScalars (Int.castRingHom A)` で運ぶ部分に、A の ℤ 上の平坦性を追加する必要はない。擬同型の底変換一般を使う議論とは区別する。
- 本体 `HomologicalAlgebra/CochainTensor/BaseChange.lean` の `cochainTensorBaseChangeIso` と `map_ι_cochainTensorBaseChangeXIso` は、整数コチェイン複体でのテンソルの実底変換同型と各余積成分の式を持つ。負次数延長後のテンソル部分を一から作り直さない候補になる。
- Moore 正規化と底変換の交換は、一般の核の保存を要求する形にしない。Moore 包含・射影と `PInfty` による分裂を加法的関手で運び、A 上の指定された分裂と比較する案を優先する。その後、自由線形化の底変換同型を全単体・全重み添字について照合する。ここはまだ Lean 未検証。
- 残る核心は、得られた射が今回の `normalizedBousfieldKanHomSpaceComparison` と `reflectedWeightedHomComparison` を結ぶ同じ射であること。n ごとの鎖ホモトピー同値だけでは単体的 Hom 比較の同値性を証明したことにならない。n の面・退化への自然性、ホモトピーを全パラメータへ移す比較、native な頂点評価との一致を残件として保つ。

この候補は一般 A の部分の再実装を減らし得るが、上記の未検証の接続を零行とは数えない。§37の完成見込みを下げて Lean を再開するだけの根拠にはまだならない。型・範囲・⑤aのファイルは変更していない。今回は読取りと文書のみで、ビルド・鍵の取得は行っていない。

## 40. 11-13承認後の再開：指定 Moore 分裂の加法関手による移送

ユーザー承認により3b-2の上限を **10,000行**へ変更し、§37の中間停止を解除して Lean を再開した。残りは§37.2の四つのまとまりに限定する。小さな同定補題の追加許容は3本まで、四つの外の新しいまとまりが必要になれば検証済みを保存して停止する。累計約7,900行で止まらずに実測・残量を報告する。型・範囲の弱化、`[ModelCategory SSet]` の追加、⑤aの既存ファイルの変更は行わない。停止点2の後に3b-4のBE部分へ進む。

コード `d18645332`、新規 `SerrePositivity.HomologicalAlgebra.NormalizedMooreMap`（107行）。累計 **99本5,893行**。

§39の短縮候補を先に実装した。Mathlib の `map_PInfty_f` と交代面複体の指定自然同型を使い、加法関手で移した Moore 分裂と、移した単体的対象の元の Moore 分裂の間に自然同型 `normalizedMooreMapNatIso` を構成した。前向き射は移した包含・交代面比較・指定射影の合成、逆射も指定された分裂の合成。包含との等式と全単体的対象の射への自然性を証明した。核の保存・平坦性は要求していない。これは第一のまとまり（正規化テンソル／積重み比較の係数変更）の内部であり、別のまとまりを追加したものではない。

個別検査、鍵付き対象ビルド **1,330 jobs**、累計99本 **1,056宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-32.log`、監査 `/private/tmp/AuditISW2G10NinetyNine.lean`、登録待ち一覧 `/private/tmp/isw2-g10-ninetynine-modules.txt`。鍵は `--wait 3600`、一枚、一回1,700秒上限、解放済み。入口・公式監査は変更していない。

次は、この同じ自然同型を使って係数拡大で運んだ EZ ホモトピーの始域・終域を照合する。テンソル側では既存 `cochainTensorBaseChangeIso` を再利用する。今回だけで一般AのEZ比較や全単体の重み付き切断比較が完了したとは数えない。停止点2は未完。現在の残枠は4,107行。

## 41. 3b-2 続行：既存 EZ ホモトピーの加法関手による移送

コード `1b07886d0`、新規 `SerrePositivity.HomologicalAlgebra.NormalizedEZMap`（91行）。累計 **100本5,984行**。

第一のまとまりの内部で、§39の `Functor.mapHomotopy` を使う候補を実装した。整数係数の指定 `normalizedEZHomotopy` を加法関手で運び、§40の Moore 比較同型で前後合成して、移した単体的対象の元の Moore 正規化上のホモトピーへ戻した。`mappedNormalizedAlexanderWhitney`・`mappedNormalizedShuffle` は指定された AW・shuffle の像と同じ Moore 同型から構成し、両入力の全単体的射への自然性を証明した。係数拡大は加法関手の特殊例として適用でき、平坦性を要求しない。

結論は AW の後に shuffle を合成した射と恒等の鎖ホモトピーである。この一方の合成のホモトピーだけから、全単体の切断比較が同値と結論していない。テンソル側は移した元の整数テンソルを明示的に保持している。一般 A の正規化テンソルへの同定、積重みの自由線形化との同定、指定豊穣合成への照合は残る。

既存依存の鍵付きビルド **1,846 jobs**、個別検査、新規対象の鍵付きビルド **1,848 jobs**、累計100本 **1,067宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-33.log`・`/private/tmp/isw2-g10-build-34.log`、監査 `/private/tmp/AuditISW2G10Hundred.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundred-modules.txt`。共有鍵は `--wait 3600`、整理券は同時に一枚、各回1,700秒上限。現在解放済み。

次の接続には既存 `mapExtendNatIso`・`NegativeTensor.comparison`・`cochainTensorBaseChangeIso` を使う。今回、新しいまとまり・追加仮定・⑤aの既存ファイルの変更はない。停止点2は未完。10,000行までの残枠4,016行、約7,900行での非停止の中間報告の条件を保持する。

## 42. 3b-2 続行：負次数テンソルと係数拡大の指定比較

コード `90f5fcfe9`、新規 `SerrePositivity.HomologicalAlgebra.NegativeTensorBaseChange`（39行）。累計 **101本6,023行**。

第一のまとまりの内部で、既存 `mapExtendIso`・`NegativeTensor.comparison`・`cochainTensorBaseChangeIso` をそのまま合成した。`negativeTensorBaseChangeIso` は、係数拡大した自然数鎖テンソルを負次数へ延長した複体から、係数拡大した二因子の負次数延長のテンソルへの指定同型。平坦性・有界性を要求せず、コチェインの既存の符号を保持する。

既存依存の鍵付き対象ビルド **1,962 jobs**、個別検査、新規対象の鍵付きビルド **1,965 jobs**、累計101本 **1,088宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-35.log`・`/private/tmp/isw2-g10-build-36.log`、監査 `/private/tmp/AuditISW2G10HundredOne.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredone-modules.txt`。共有鍵は `--wait 3600`、整理券は一枚、各回1,700秒上限、解放済み。

宇宙の接続を確認した。Mathlib の ModuleCat のモノイダル構造と既存 `cochainTensorBaseChangeIso` は環・加群を同じ宇宙に置く。一方、KST の `chainIntegerTensor` は任意の宇宙の整数加群のための明示的テンソルであり、今回の同型に直接代入できたとはしていない。この差には既存 `Project.DerivedCategories.DGIntegerCoefficientTensor` の `integerCoefficientTensorIso`・`integerCoefficientTensorComparison_naturality`、`simplicialRingIntegerModuleEquivalence` を再利用できる。持ち上げた整数環 `ULift ℤ` への移送を鎖テンソルまで結び、その後に今回の底変換同型を適用する。対象宇宙を0に制限しない。

この接続と、全図式射についての比較の照合はまだ未完。今回、全単体の切断比較や native 極限性を証明済みとは数えない。指定の四まとまりの外への追加、既存宣言・⑤aのファイル・入口・公式監査の変更はない。停止点2は未完、残枠3,977行。約7,900行での中間報告の条件を保持する。

## 43. 3b-2 続行：任意の宇宙の整数鎖テンソルと底変換の接続

コード `ee4e5a1f3`、新規2本247行。累計 **103本6,270行**。

- `DiagramComparison.IntegerCoefficientTensorDegrees`（93行）：既存の `integerCoefficientTensorIso` と余積比較を合成し、元の整数鎖テンソルの全次数を同宇宙の整数係数環のテンソルへ比較した。各二重次数の包含の公式と、元の二つの鎖写像への自然性を証明した。
- `DiagramComparison.IntegerCoefficientTensorDifferential`（154行）：次数が一致しない場合の零包含、第一・第二の部分微分、全微分を照合し、`integerCoefficientChainTensorIso` とその鎖写像への自然性を証明した。さらに `integerNegativeTensorBaseChangeIso` で、同宇宙の整数係数環から A への底変換を§42の比較に接続した。元の `chainIntegerTensor` を使い、宇宙を0に縮めない。

依存対象ビルド **2,126 jobs**、次数比較の対象ビルド **2,127 jobs**、複体同型の対象ビルド **2,211 jobs**と個別検査が成功。累計一時監査は102本1,107宣言、最終103本 **1,132宣言・標準三公理のみ**、いずれも終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-37.log`・`/private/tmp/isw2-g10-build-38.log`・`/private/tmp/isw2-g10-build-39.log`。最終監査 `/private/tmp/AuditISW2G10HundredThree.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthree-modules.txt`。鍵は `--wait 3600`、同時に一枚、各回1,700秒上限、解放済み。ビルドには長い行のスタイル警告があるがエラーはない。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientTensorDegrees
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientTensorDifferential
```

第一のまとまりの内部の接続であり、新しいまとまりではない。§41の移送した EZ ホモトピーを今回のテンソル同型で挟み、負次数の比較へ移す段と、自由線形化した積重みとの同定・全単体への照合が続く。今回だけで重み付き切断の同値性を証明済みとは数えない。指定の残り三まとまりも保持する。既存宣言・⑤aのファイル・入口・公式監査は変更していない。停止点2は未完、上限10,000行まで残枠3,730行。約7,900行での非停止の中間報告を保持する。

## 44. 3b-2 続行：一般 A の元の自由積鎖へ EZ ホモトピーを接続

コード `9f0e3070c`、新規3本234行。累計 **106本6,504行**。

- `DiagramComparison.NegativeEZCoefficient`（83行）：§43の整数テンソル底変換と指定 Moore 同型を合成。一般係数の負次数正規化テンソルへの指定 AW、その逆向きの shuffle、AW の後の shuffle を恒等へ結ぶ元のホモトピーを構成した。
- `DiagramComparison.IntegerCoefficientFree`（72行）：任意の宇宙の整数自由化の指定生成元による随伴を構成し、同宇宙の整数係数移送・係数拡大の随伴を合成。元の `ModuleCat.free A` との全自然同型を得た。指定単位の保存と、その生成元の像が元の A 自由加群の標準生成元である評価式を証明した。
- `DiagramComparison.FreeProductEZ`（79行）：既存 `linearizedTensorIso` と上記自由化比較を Moore 正規化・負次数延長へ送った。元の A 自由化した X×Y の正規化鎖から、X・Y の正規化鎖のテンソルへの AW と、その逆向きの shuffle を構成し、この積の複体上で AW→shuffle と恒等の鎖ホモトピーを証明した。

新規対象の鍵付きビルド **2,239 jobs**・**2,240 jobs**、個別検査が成功。累計一時監査は105本1,172宣言、最終106本 **1,195宣言・標準三公理のみ**、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-40.log`・`/private/tmp/isw2-g10-build-41.log`。最終監査 `/private/tmp/AuditISW2G10HundredSix.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredsix-modules.txt`。鍵は `--wait 3600`、整理券は同時に一枚、各回1,700秒上限、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficient
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientFree
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductEZ
```

いずれも第一のまとまりの内部。今回の鎖ホモトピーは一方の合成についてのもの。逆順の合成、最終 AW・shuffle の全単体パラメータへの自然性、既存の単位余積による BK 線形化との同定、Γ Hom／重み付き切断比較への照合を完了済みとは数えない。後続の指定 native 制限・極限性、標準脚・D(A) 輸送、全射・錐の族も残る。範囲・型の弱化、⑤aのファイル・既存宣言・入口・公式監査の変更はない。停止点2は未完、残枠3,496行。約7,900行で実測と残りを再見積もりする。

## 45. 3b-2 続行：指定係数 EZ 写像の全単体的射への自然性

コード `5ff48b6fd`、新規4本236行。累計 **110本6,740行**。

- `HomologicalAlgebra.CochainTensorBaseChangeNaturality`（43行）：既存 `cochainTensorBaseChangeIso` の両因子の鎖写像への自然性を標準余積包含で証明した。
- `HomologicalAlgebra.NegativeTensorBaseChangeNaturality`（54行）：零延長の自然同型、既存負次数テンソル比較、上記底変換の自然性を合成し、同じ `negativeTensorBaseChangeIso` の自然性を証明した。
- `DiagramComparison.CoefficientTensorNaturality`（73行）：整数係数移送と、最後に元の Moore 正規化へ戻す同型を含む自然性を証明した。
- `DiagramComparison.NegativeEZCoefficientNaturality`（66行）：同じ負次数 AW・shuffle の両入力について、任意の二つの単体的射への自然性を証明した。別の自然な写像を定義し直して置換していない。

全て第一のまとまりの「自然性・照合」の内部。四まとまりの外に新しいまとまりや補助的な主題を追加していない。合成の elaboration が200,000 heartbeatsに達した箇所は、比較の引数を明示して段階を分けて解消し、制限値は増やしていない。

依存対象の鍵付きビルド **1,964 jobs**、個別検査、新規対象の鍵付きビルド **2,242 jobs**、累計110本 **1,204宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-42.log`・`/private/tmp/isw2-g10-build-43.log`、最終監査 `/private/tmp/AuditISW2G10HundredTen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredten-modules.txt`。鍵は `--wait 3600`、整理券は同時に一枚、各回1,700秒上限、解放済み。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CochainTensorBaseChangeNaturality
SerrePositivity.HomologicalAlgebra.NegativeTensorBaseChangeNaturality
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientTensorNaturality
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficientNaturality
```

次は自由積鎖への最後の輸送に自然性を通し、元の重み付き切断比較と照合する。逆順の合成や全単体空間の同値性を今回の自然性だけで結論していない。指定 native 制限・極限性、標準脚・D(A) 輸送、全図式射・錐の族も保持する。既存宣言・⑤aのファイル・入口・公式監査は変更していない。停止点2は未完、残枠3,260行。約7,900行での非停止の中間報告の条件を保持する。

## 46. 3b-2 続行：元の自由積鎖上の指定 AW・shuffle の自然性

コード `12db1050c`、新規1本125行。累計 **111本6,865行**。

`DiagramComparison.FreeProductComparisonNaturality` で、指定自由化同型・積の係数同型・その二因子テンソルの自然性を証明した。その同じ同型で輸送した `freeProductAlexanderWhitney` と `freeProductShuffle` が、任意の二つの単体的集合の射に自然であることを証明した。元の自由正規化鎖の射を明記し、別の比較写像への取り替えはしていない。第一のまとまりの「自然性・照合」の内部である。

個別検査、鍵付き対象ビルド **2,246 jobs**、累計111本 **1,219宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-44.log`、監査 `/private/tmp/AuditISW2G10HundredEleven.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredeleven-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductComparisonNaturality
```

逆順の EZ 合成、BK 線形化で使う単位加群の余積との同定、全単体パラメータの Hom／重み付き切断比較との照合は残る。指定 native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族も完了済みとは数えない。既存宣言・⑤aのファイル・入口・公式監査は変更していない。停止点2は未完、残枠3,135行。約7,900行で実測と残りの見込みを報告する。

## 47. 3b-2 続行：指定余積と自由線形重みの同定

コード `e02b135b5`、新規2本137行。累計 **113本7,002行**。

- `HomologicalAlgebra.CopowerUnitFree`（83行）：小さい添字集合 S の単位加群の指定余積と `ModuleCat.free A (ULift S)` の同型を構成した。両方向の指定生成元の像、逆射との合成、全添字写像への自然性を証明した。係数の宇宙は任意のまま。
- `HomologicalAlgebra.NormalizedLinearWeightFree`（54行）：同じ自然同型を図式圏と単体方向へ運び、既存 `linearizedSimplicialWeight` と自由線形化の比較を得た。重みの全自然変換への自然性、および同じ Moore 正規化・負次数延長による複体の同型を構成した。

第一のまとまりの既存線形化との照合であり、四まとまりの外の主題を追加していない。図式圏の正規化と点ごとの自由積比較の最終照合や、全単体 Hom／切断比較の同値性まで済んだとは数えない。

個別検査と鍵付き対象ビルド **1,835 jobs**、累計113本 **1,239宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-45.log`、監査 `/private/tmp/AuditISW2G10HundredThirteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CopowerUnitFree
SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightFree
```

次の確認候補：実際の全単体比較の第二因子は標準単体である。既存 `EInfinity.ComplexLimits.normalizedSimplexChainContraction`・`normalizedSimplexTensorContraction` を使い、指定 AW と増大写像の両立から必要な同値を得られるか確認する。この候補は未証明であり、一方の EZ ホモトピーだけで結論したものではない。⑤aの既存ファイルには変更を加えない。

指定 native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,998行。約7,900行で実測と残量を報告する。

## 48. 標準単体の収縮による短縮候補の検査

§47末尾の候補を、既存の型と個別 Lean 検査で確認した。`freeNegativeChains (SSet.uliftFunctor.obj Δ[n])` は既存 `BarrattEccles.normalizedFunctor` の値と定義的に一致する。`normalizedSimplexCochainContraction` と `normalizedSimplexTensorContraction` はそのまま適用でき、順方向も `(𝟙 K ⊗ augmentation) ≫ ρ_K` と定義的に一致する。依存対象の鍵付きビルド **2,395 jobs** が成功し、個別検査も終了コード0。ログ `/private/tmp/isw2-g10-dependencies-46.log`・`/private/tmp/isw2-free-simplex-contraction-2.log`。鍵は解放済み。

ただし、これで第一のまとまりの全単体比較を閉じることはできない。各 n での鎖ホモトピー同値は、各 n の鎖写像の集合の全単射ではない。また、重みの図式方向の end を取る比較には、その方向で両立するホモトピーが要る。頂点を選んだ収縮を n ごとに適用しただけでは、必要な全単体の切断空間の比較や、その指定豊穣合成との一致は得られない。これらの橋を省略して同値性を主張しない。

今回の試作は既存定義の包み直しだけで、上記の不足を解消しないため、本体には残さない。個別検査を通した試作は `/private/tmp/isw2-free-simplex-contraction-tested.lean` に保存した。新規登録対象なし、累計 **113本7,002行**のまま。次は、正規化 shuffle→AW の合成の直接の照合を検討する。既存の `normalizedEZHomotopy` が供給する逆順（AW→shuffle）のホモトピーと取り違えない。停止点2は未完であり、四つのまとまり・10,000行上限・約7,900行での中間報告の条件は維持する。

## 49. 3b-2 続行：shuffle→AW の異なる二重次数の成分の消滅

コード `d9f60a395`、新規1本67行。累計 **114本7,069行**。

`DiagramComparison.ShuffleCutNormalization` で、既存格子路の両因子を AW で切断した写像がともに単射なら、切断点が元の第一次数 p に一致することを次元の不等式から証明した。切断点が異なる場合は少なくとも一因子が非単射になる。Mathlib の `degeneracy_comp_PInfty` と元の Moore 分裂を使って、その作用素と実 Moore 射影との合成が零であること、したがって正規化された実整数テンソル成分が零であることを証明した。第一のまとまりの合成の照合に属する。

個別検査、鍵付き対象ビルド **1,846 jobs**、累計114本 **1,245宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-47.log`、監査 `/private/tmp/AuditISW2G10HundredFourteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfourteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutNormalization
```

これは異なる切断点の成分の消滅であり、対角成分や正規化 shuffle→AW 全体の恒等式まで完了したものではない。対角では非退化の格子路の一意性・符号の確認、対角側の Moore 射影を挟む合成との照合が残る。全単体 Hom／切断比較、指定 native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族も保持する。停止点2は未完、残枠2,931行。約7,900行で実測と残量を報告する。

## 50. 3b-2 続行：対角に残る格子路の一意性と符号

コード `213ae49a6`、新規1本76行。累計 **115本7,145行**。

`DiagramComparison.ShuffleCutDiagonal` で、最初の p 本を水平にした格子路 `initialShuffle` を定義した。対角の前半の切断が単射なら自己単射は恒等なので、終点の値と濃度から格子路がこれに一致することを証明した。また、この格子路の逆転数が零、shuffle 符号が +1 であることを証明した。第一のまとまりの対角成分の照合に属する。

個別検査、鍵付き対象ビルド **1,847 jobs**、累計115本 **1,255宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-48.log`、監査 `/private/tmp/AuditISW2G10HundredFifteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfifteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutDiagonal
```

残るのは指定格子路の両切断の恒等式、全成分の合成と途中の Moore 射影の照合である。正規化 shuffle→AW 全体の恒等式、全単体 Hom／切断比較、native 極限性などを完了済みとは数えない。停止点2は未完、残枠2,855行。約7,900行で実測と残量を報告する。

11-13 昼の B3 凍結予告を受領した。検証済みを上記コードと本報告に保存する。18時の確定連絡で凍結となれば、その後は枝へのコミットを控え、翌朝の main 取り込み・改名表の追従を一括レーンの B4 手順に従って行う。現時点で凍結の確定や改名の先行適用はしていない。

## 51. 3b-2 続行：指定格子路の両切断の恒等式

コード `b16fcbc8a`、新規1本88行。累計 **116本7,233行**。

`DiagramComparison.ShuffleCutValues` で、指定格子路の水平部分の初期 x ステップ、垂直部分の初期 x ステップの濃度を、それぞれ Fin x への明示的な全単射から計算した。この計算により、`awFront ≫ initialShuffle.left` と `awBack ≫ initialShuffle.right` が、それぞれの単体の恒等射であることを証明した。第一のまとまりの対角成分の照合である。

個別検査、鍵付き対象ビルド **1,848 jobs**、累計116本 **1,267宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-49.log`、監査 `/private/tmp/AuditISW2G10HundredSixteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredsixteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券で順番待ちし、取得後は1,700秒上限でビルド・監査の間だけ使用、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutValues
```

次は、有限和の非対角消滅・対角の一意性・符号・両切断の恒等式を同じ成分の合成へまとめる。正規化 shuffle と AW の間に挟まる対角側の Moore 射影の照合も必要であり、成分の計算だけで最終合成の恒等式が済んだとは数えない。全単体 Hom／切断比較、native 極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,767行。約7,900行で実測と残量を報告する。凍結予告は受領済みだが、今回のコミット時点では確定連絡は未受領。

## 52. 3b-2 続行：実 shuffle 成分と正規化切断の合成

コード `22a357334`、新規1本73行。累計 **117本7,306行**。

`DiagramComparison.ShuffleCutSum` で、対角切断の符号付き和を唯一の初期水平格子路へ簡約し、二因子の元の Moore 射影になる式を証明した。さらに、これを既存の `shuffleBidegree` と実際の切断写像との合成に結び、対角の合成は二因子の射影、非対角の合成は零となる式を証明した。第一のまとまりの成分の合成の照合である。

個別検査、鍵付き対象ビルド **1,849 jobs**、累計117本 **1,277宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-50.log`、監査 `/private/tmp/AuditISW2G10HundredSeventeen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredseventeen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutSum
```

次は切断点の和と標準余積包含を介して全テンソルへの式へまとめる。また、正規化 shuffle と AW の間に挟まる対角側の Moore 射影の照合が残る。この段階の成分の式から、正規化合成全体や全単体切断空間の同値性が済んだとは数えない。native 極限性、標準脚・D(A) 輸送、全図式射・指定錐の族も残る。停止点2は未完、残枠2,694行。約7,900行で実測と残量を報告する。

## 53. 3b-2 続行：指定正規化 EZ の両方向の鎖ホモトピー同値

コード `8a91a1d27`、新規1本105行。累計 **118本7,411行**。

`DiagramComparison.ShuffleAWProjected` で、標準包含と AW の有限和を使い、元の鎖写像について `shuffle ≫ alexanderWhitney ≫ 二因子のMoore射影 = 二因子のMoore射影` を証明した。正規化した逆順合成に挟まる対角側の Moore 射影は、既存 `homotopyPInftyToId` で恒等へ結び、その後はこの等式と元の Moore 分裂を使った。これにより `normalizedShuffleAWHomotopy`、さらに既存の順方向のホモトピーと合わせた `normalizedSpecifiedEZEquiv` を構成した。hom・inv は既存の `normalizedAlexanderWhitney`・`normalizedShuffle` そのものである。

第一のまとまりの整数係数での逆順合成の不足が閉じた。射影を厳密に消すための追加の組合せ論は不要だった。一般 A への移送は既存 `Functor.mapHomotopy`、Moore 比較、係数テンソル比較で進める。ホモトピーの図式方向の両立や、全単体の指定切断比較への接続まで今回済んだとは数えない。

個別検査、鍵付き対象ビルド **1,872 jobs**、累計118本 **1,288宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-51.log`、監査 `/private/tmp/AuditISW2G10HundredEighteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredeighteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleAWProjected
```

全単体 Hom／切断比較、native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,589行。約7,900行で実測と残量を報告する。型の弱化、模型構造の追加、⑤aの既存ファイルの変更はない。

## 54. 3b-2 続行：一般係数の指定自由積 EZ 同値

コード `6bfbd68d8`、新規1本66行。累計 **119本7,477行**。

`DiagramComparison.CoefficientEZEquivalence` で、§53の逆順ホモトピーを `Functor.mapHomotopy` により任意の加法関手へ移した。同じ Moore 比較、負次数延長、係数テンソル同型、最後の自由化同型を使い、既存 `freeProductAlexanderWhitney`・`freeProductShuffle` を hom・inv とする `freeProductEZEquiv` を構成した。任意の可換環 A で、積の A 自由正規化鎖と二因子の正規化鎖のテンソルの間の両方向の鎖ホモトピー同値であり、平坦性は要求しない。第一のまとまりの一般係数への移送である。

個別検査、鍵付き対象ビルド **2,246 jobs**、累計119本 **1,319宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-52.log`、監査 `/private/tmp/AuditISW2G10HundredNineteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundrednineteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientEZEquivalence
```

次はホモトピーの図式方向の両立と、元の全単体 Hom／切断比較への接続である。既存 KST の `ChainHomotopySquare` と `MooreHomotopyNaturality.moorePInftyHomotopy_naturality` が逆順ホモトピーの自然性にも使えることを確認したが、その自然性の証明は今回完了済みとは数えない。native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族も残る。停止点2は未完、残枠2,523行。約7,900行で実測と残量を報告する。

## 55. 3b-2 続行：指定逆順 EZ ホモトピーの自然性

コード `1934ab94f`、新規1本79行。累計 **120本7,556行**。

`DiagramComparison.ShuffleAWHomotopyNaturality` で、Moore 収縮への前合成（包含・shuffle）と後合成（AW・射影）の自然性を証明した。既存 KST の Moore 収縮の自然性と `ChainHomotopySquare` の合成則を完全修飾で参照し、実際の `normalizedShuffleAWHomotopy` の両入力の任意の射への自然性を、各次数のホモトピー成分の等式として証明した。第一のまとまりの図式方向の両立である。

最終合成の自動推論が200,000 heartbeatsに達した箇所は、射と中間の四角形を明示して分割し解消した。制限値は変更していない。

依存対象の鍵付きビルド **1,852 jobs**、個別検査、新規対象の鍵付きビルド **1,879 jobs**、累計120本 **1,322宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-53.log`・`/private/tmp/isw2-g10-build-54.log`、監査 `/private/tmp/AuditISW2G10HundredTwenty.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwenty-modules.txt`。鍵は `--wait 3600`、一枚の整理券、各回1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleAWHomotopyNaturality
```

次はこの自然性を一般係数・負次数延長へ運び、図式の重みの比較へつなぐ。全単体 Hom／切断比較、native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,444行。約7,900行で実測と残量を報告する。

## 56. 3b-2 続行：図式圏の指定整数 EZ 鎖ホモトピー同値

コード `9b1857680`、新規2本135行。累計 **122本7,691行**。

- `HomologicalAlgebra.PointwiseChainHomotopy`（56行）：各点の指定鎖ホモトピーと次数を一つ上げる成分の自然性から、図式圏の鎖ホモトピーを構成した。各点の成分は元のものと定義的に一致する。
- `DiagramComparison.DiagramIntegerEZ`（79行）：任意の添字圏について、積を正規化した側・二因子の正規化テンソル側の複体値図式と、指定 AW・shuffle の全図式射を構成した。既存の順方向および§55の逆方向の自然性を使い、元の成分交換関手を通して、図式圏における両方向の鎖ホモトピー同値 `integerEZDiagramEquiv` を構成した。

第一のまとまりの図式方向の両立を実装した。点ごとの同値の存在だけで図式の end での同値を結論したものではない。一般係数の元の正規化模型・積重みへの同定と、全単体 Hom／切断比較への接続は残る。

個別検査、鍵付き対象ビルド **1,888 jobs**、累計122本 **1,346宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-55.log`、監査 `/private/tmp/AuditISW2G10HundredTwentyTwo.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentytwo-modules.txt`。鍵は `--wait 3600`、一枚の整理券で順番待ちし、取得後は1,700秒上限でビルド・監査の間だけ使用、解放済み。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.PointwiseChainHomotopy
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramIntegerEZ
```

native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,309行。約7,900行で実測と残量を報告する。

## 57. 3b-2 続行：一般係数の元の正規化テンソル図式への輸送

コード `7f567da87`、新規2本142行。累計 **124本7,833行**。

- `DiagramComparison.DiagramCoefficientEZ`（74行）：図式圏の同値を加法的係数変更へ運び、積側を既存 Moore 全自然同型で係数変更後の元の正規化へ戻した。指定ホモトピーの負次数延長も構成した。
- `DiagramComparison.NegativeEZTargetDiagram`（68行）：元の一般係数の負次数正規化テンソルの図式を構成し、既存係数テンソル同型の全自然性を適用した。図式交換と延長の指定同型を使い、標的をこの図式に戻した同値を構成した。

第一のまとまりの一般係数・全図式への輸送である。積重みの自由化との最終同定、指定 AW・shuffle の各点との照合、全単体 Hom／切断比較への接続を完了済みとは数えない。

個別検査、鍵付き対象ビルド **2,263 jobs**、累計124本 **1,393宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-56.log`、監査 `/private/tmp/AuditISW2G10HundredTwentyFour.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentyfour-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramCoefficientEZ
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZTargetDiagram
```

### 57.1 約7,900行の非停止の中間報告

11-13のユーザー指示3に基づく報告。実測 **7,833行**、上限10,000行まで **2,167行**。§37時点の5,786行から2,047行を追加した。追加は第一のまとまりの、一般係数・宇宙・正規化テンソル・両方向の指定 EZ ホモトピー・その図式化に使った。§37で第一のまとまり全体を1,000〜1,600行とした見込みは、この部分だけで超過している。

| 残る承認済みのまとまり | 今回の暫定追加見込み | 現状 |
| --- | ---: | --- |
| 正規化テンソル／積重み、全単体比較と照合の残り | 600〜1,000行 | 両方向の自然な EZ 同値は図式圏まで構成済み。自由化・元の Hom 比較・全単体作用素との最終接続が残る |
| 指定豊穣 Hom 合成・native 制限・極限性 | 600〜900行 | 指定 native 錐と比較族は既存。今回の比較がその制限と同じ射である照合が残る |
| 標準脚の最終等式と D(A) 輸送 | 400〜700行 | 元の脚と raw 錐は既存。極限性確定後の最終照合・輸送が残る |
| 全図式射・指定錐の族・離散加群版入口 | 500〜900行 | strict Tot 側の成分は既存。最終の錐の族と入口が残る |
| 合計 | **2,100〜3,500行** | 完成見込み **9,933〜11,333行** |

下限でも余裕は67行しかなく、10,000行内に収まる保証はない。この報告を停止点2や上限変更の承認とはしない。最新の指示3のとおり、この中間報告自体では承認待ちにせず、既存の全自然同型・指定錐を使う短い接続を優先する。四つの外のまとまりを追加せず、型・範囲の弱化も行わない。10,000行の上限を独自に延長せず、超える変更や範囲外のまとまりが必要になったところで、検証済みを保存して停止する。停止点2は未完。

## 58. 3b-2 続行：元の自由積図式への輸送と延長比較の自然性

コード `b5eb19199`、新規2本118行。累計 **126本7,951行**。

- `DiagramComparison.FreeProductDiagramEZ`（65行）：任意の単体的集合の二図式について、積側とテンソル側の自由化の全自然同型を構成した。§57の図式圏の比較を両側から運び、元の A 自由正規化鎖による積図式とテンソル図式の鎖ホモトピー同値を構成した。
- `DiagramComparison.DiagramExtendNaturality`（53行）：既存 `negativeDiagramExchangeIso` を同じ成分を持つ全自然同型へまとめ、任意の複体値図式射との可換式を証明した。

順方向の各点が元の指定 AW と一致する式は、`rfl` だけでは閉じないことを個別検査で確認した。図式交換・零延長の比較を通るため、後者の自然性を使って照合する。この未証明の等式は本体に残しておらず、試作は `/private/tmp/isw2-free-product-diagram-component-draft.lean` に保存した。今回の同値構成を、この最終成分等式まで済んだものとして数えない。いずれも第一のまとまりの同定・自然性の内部である。

個別検査、鍵付き対象ビルド **2,269 jobs**・**2,264 jobs**、一時監査125本1,415宣言、最終累計126本 **1,426宣言・標準三公理のみ**が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-57.log`・`/private/tmp/isw2-g10-build-58.log`、最終監査 `/private/tmp/AuditISW2G10HundredTwentySix.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentysix-modules.txt`。鍵は `--wait 3600`、同時に一枚の整理券、各回1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramEZ
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramExtendNaturality
```

約7,900行の中間報告の実測を **7,951行、残枠2,049行**に更新する。残る四まとまりと上限内完了のリスクは§57.1のとおり。全単体 Hom／切断比較、native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は未完であり、停止点2にはまだ達していない。

## 59. 3b-2 続行：図式 EZ の二射と指定 AW・shuffle の同定

コード `0d3c7567d`、新規2本113行。累計 **128本8,064行**。

- `DiagramComparison.CoefficientDiagramMaps`（45行）：係数 AW・shuffle の全図式射を構成し、既存係数図式同値の hom・inv との等式を証明した。
- `DiagramComparison.FreeProductDiagramMaps`（68行）：元の自由積図式の指定 AW・shuffle を構成し、自由積図式同値の両方向と同定した。図式交換・零延長比較の自然性で中間同型を相殺する。§58で残した照合を、各点だけでなく全図式射の等式として閉じた。

第一のまとまりの同定・自然性の内部。全単体 Hom 比較や native 極限性を、今回の等式だけから結論してはいない。

鍵付き対象ビルド **2,272 jobs**、累計128本 **1,457宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-59.log`、監査 `/private/tmp/AuditISW2G10HundredTwentyEight.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentyeight-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientDiagramMaps
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramMaps
```

残枠 **1,936行**。全単体 Hom／切断比較、native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残り、停止点2は未完。次のパラメータ方向の自然性は個別検査中であり、このコミットには含めない。B3凍結の予告に従い検証済みだけを保存した。凍結確定後は枝へのコミットを控える。

## 60. 3b-2 続行：重み・単体パラメータ方向の自然性

コード `ef2e57fce`、新規 `DiagramComparison.FreeProductDiagramNaturality` 1本53行。累計 **129本8,117行**。元の自由負次数鎖を図式の自然変換へ作用させ、指定 AW・shuffle が二つの図式の任意の自然変換と可換であることを証明した。第一のまとまりの自然性の内部であり、標準単体の作用素を代入できる形である。

個別検査、鍵付き対象ビルド **2,273 jobs**、累計129本 **1,464宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-60.log`、監査 `/private/tmp/AuditISW2G10HundredTwentyNine.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentynine-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramNaturality
```

残枠 **1,883行**。積重みとテンソル側の余単体的な族、および指定二射を `FreeProductFrames.lean` に下書き中（未コミット）。鎖ホモトピー同値から全単体 Hom 空間への接続、指定豊穣合成・native 極限性、脚・D(A)・錐の族は引き続き未完。停止点2ではない。

## 61. 3b-2 続行：積重み・テンソルの余単体図式と指定二射

コード `d825603b7`、新規 `DiagramComparison.FreeProductFrames` 1本67行。累計 **130本8,184行**。

元の自由負次数鎖の図式関手を使い、任意の余単体的パラメータ P に対して、積を正規化する族と正規化後のテンソルの族を構成した。§60の自然性を使い、指定 AW・shuffle を全余単体作用素と可換な自然変換にした。標準単体を代入する前の全パラメータ形である。第一のまとまりの全単体比較の内部。

個別検査、鍵付き対象ビルド **2,274 jobs**、累計130本 **1,483宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-61.log`、監査 `/private/tmp/AuditISW2G10HundredThirty.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirty-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrames
```

残枠 **1,816行**。同じ二射からの全単体 Hom 比較 `FreeProductHomComparison.lean`（42行）は個別検査済み、対象ビルド・監査待ちであり、このコミットには含めない。標準単体の代入後、テンソル側を既存の Dold–Kan Hom と、積側を重み付き切断空間と同定し、指定射のホモトピー同値性を証明することが残る。次数ごとの鎖ホモトピー同値だけから空間の同値性を結論しない。native 極限性等も未完であり、停止点2には達していない。

## 62. 3b-2 続行：指定二射から全単体 Hom 比較へ

コード `8da07570f`、新規 `DiagramComparison.FreeProductHomComparison` 1本42行。累計 **131本8,226行**。

§61の余単体 AW・shuffle に既存の `cosimplicialHomMap` を適用し、両方向の実際の単体的 Hom 射を構成した。標的の全図式射にも自然であり、全次数の作用が指定図式 AW・shuffle の前合成そのものである等式を保持する。第一のまとまりの指定比較射の構成。空間としての同値性はまだ証明していない。

個別検査、鍵付き対象ビルド **2,276 jobs**、累計131本 **1,488宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-62.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyOne.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtyone-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductHomComparison
```

残枠 **1,774行**。`StandardSimplexParameter.lean`（51行）では、持ち上げた標準単体の自由鎖と既存 `normalizedFunctor` の定数図式の全自然同型、およびテンソル族への輸送を個別検査済み。対象ビルド・監査待ちなので未コミット。

次の接続で必要なのは、図式圏の `linearHomComplex` の Γ とテンソル族からの Hom の同定である。点ごとの既存 `tensorHomEquiv` の始域・標的自然性を使い、添字方向の自然性条件を保持して組み立てる。積側を重み付き切断空間に同定する部分、指定射の空間の同値性、豊穣合成・native 極限性、脚・D(A)・錐の族も未完。これらを省略して停止点2としない。

## 63. 3b-2 続行：元の標準単体パラメータとの同定

コード `2d63e090d`、新規 `DiagramComparison.StandardSimplexParameter` 1本51行。累計 **132本8,277行**。

小さい標準単体を宇宙持ち上げした定数図式の自由鎖と、既存 `EInfinity.BarrattEccles.normalizedFunctor` の定数図式を全余単体的に同定した。同じ自然同型をテンソル族へ移した。既存の正規化関手を参照するだけで、⑤aのファイルや模型の構造を変更していない。第一のまとまりのパラメータの同定。

個別検査、鍵付き対象ビルド **2,275 jobs**、累計132本 **1,503宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-63.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyTwo.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtytwo-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardSimplexParameter
```

残枠 **1,723行**。図式テンソルからの射を自然性条件つきの Hom 射の族へ転置する証明を `DiagramTensorHom.lean` で進めている（未コミット）。図式 Hom 複体との同定、指定比較の空間としての同値性、native 極限性と後続の三まとまりは未完。停止点2ではない。

## 64. 3b-2 続行：自然性条件を保つ図式テンソル–Hom 同値

コード `fb60abd72`、新規 `DiagramComparison.DiagramTensorHom` 1本64行。累計 **133本8,341行**。

図式のテンソルからの射を、各点の Hom 複体への射の族と同定した。族の型には、添字の任意の射について前合成と後合成が一致する条件を含める。既存 `tensorHomEquiv` の始域・標的自然性から両方向を構成し、逆写像の法則とパラメータ複体の全射への自然性を証明した。第一のまとまりの図式 Hom の同定の内部。

個別検査、鍵付き対象ビルド **2,065 jobs**、累計133本 **1,520宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-64.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyThree.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtythree-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorHom
```

残枠 **1,659行**。`DiagramHomCochains.lean` の各次数の評価・組み立て・微分との可換性は個別検査済み。`DiagramHomFamilyLift.lean` で上の族を図式 Hom 複体への鎖写像にする証明を検査中。いずれもまだ未コミット。指定全単体比較の同値性、native 極限性と残る段階は未完であり、停止点2ではない。

## 65. 3b-2 続行：図式 Hom 複体への組み立て

コード `48e70aba5`、新規2本112行。累計 **135本8,453行**。

- `DiagramComparison.DiagramHomCochains`（50行）：図式 cochain の各点での評価、自然性条件つきの族からの組み立て、評価と微分の可換性、各点による外延性を証明した。
- `DiagramComparison.DiagramHomFamilyLift`（62行）：§64の Hom 射の族を、元の図式圏の `linearHomComplex` への鎖写像にした。線形性と微分可換性を各点の元の射から導いた。

第一のまとまりの図式 Hom 同定の内部。小さい添字圏を対象とし、必要な Δ・Δᵒᵖ を含む。指定射の同値性や native 極限性をこれだけで結論しない。

個別検査、鍵付き対象ビルド **2,070 jobs**、累計135本 **1,536宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-65.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyFive.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtyfive-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomCochains
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyLift
```

残枠 **1,547行**。`DiagramHomFamilyEquiv.lean`（111行）の各点への評価による逆写像・両合成の法則・図式テンソル–Hom 同値・パラメータ前合成への自然性は個別検査済み、対象ビルド・監査待ち（未コミット）。次に標準単体を代入して既存 `normalizedSimplexHomEquiv` と合成できる。積重み側との同定、空間の同値性、native 極限性、脚・D(A) 輸送、全図式射・指定錐の族は未完。停止点2ではない。

## 66. 3b-2 続行：元の図式 Hom への同値とパラメータ自然性

コード `20b09a216`、新規 `DiagramComparison.DiagramHomFamilyEquiv` 1本111行。累計 **136本8,564行**。

図式 Hom 複体への射を各点に評価する逆写像を構成し、§65の組み立てとの両合成が恒等であることを証明した。§64の転置と合成して、図式テンソルからの射と元の図式 `linearHomComplex` への射を同定し、パラメータ複体の全射による前合成との可換式も証明した。第一のまとまりの図式 Hom の同定の内部。

個別検査、鍵付き対象ビルド **2,071 jobs**、累計136本 **1,557宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-66.log`、監査 `/private/tmp/AuditISW2G10HundredThirtySix.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtysix-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyEquiv
```

残枠 **1,436行**。`DiagramTensorDoldKan.lean` で標準単体を代入した全単体同型を検査中。元の自由テンソル族への輸送の型推論が制限に達したため、中間 Hom 同型を指定前合成で明示している。制限値は変更していない。積重み側との同定、空間の同値性、native 極限性と後続の要件は未完で、停止点2ではない。

## 67. 3b-2 続行：図式テンソル Hom と実 Dold–Kan 空間

コード `4daa43593`、新規 `DiagramComparison.DiagramTensorDoldKan` 1本79行。累計 **137本8,643行**。

§66に正規化標準単体を代入し、既存 `normalizedSimplexHomEquiv` と合成して、図式テンソル Hom と元の図式 `linearHomComplex` の実 Dold–Kan 空間との全単体同型を構成した。単体作用素との可換性も証明した。§63の指定同型を前合成して、元の自由テンソル族の Hom へ戻す同型も構成した。第一のまとまりのテンソル側の接続。

上記コミットの個別検査、鍵付き対象ビルド **2,564 jobs**、累計137本 **1,572宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-67.log`、監査 `/private/tmp/AuditISW2G10HundredThirtySeven.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtyseven-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorDoldKan
```

残枠 **1,357行**。`FreeChainsAdjunction.lean` で自由加群・Dold–Kan・負次数延長の随伴の合成と図式への持ち上げを個別検査済み（未コミット）。積側は既存の重み付き切断の随伴と合成する。

その接続は持ち上げた添字圏 `AsSmall` も使うため、本枝の新設 `DiagramHomCochains`・`DiagramHomFamilyLift`・`DiagramHomFamilyEquiv`・`DiagramTensorDoldKan` の四本について、添字 `J : Type v` と係数 `A : Type (max u v)` を許す一般化を検査中。`v = 0` で従来の小さい添字圏を含む。main に該当四本が存在しないことを確認済みで、既存の main の宣言・入口・⑤aのファイルは変更しない。この未コミットの一般化を上記監査が検証したとは数えず、再ビルド・再監査する。停止点2は未完。

## 68. 3b-2 続行：自由鎖の随伴と持ち上げ添字への対応

コード `052a11093`、新規 `DiagramComparison.FreeChainsAdjunction` 1本42行。累計 **138本8,685行**。§67で予告した本枝新設四本の宇宙一般化は行数差0。

自由加群・Dold–Kan・負次数延長の既存随伴を合成し、元の自由負次数鎖と実 Dold–Kan 関手の随伴、および図式全体への持ち上げを構成した。四本の一般化は `J : Type v`、`A : Type (max u v)` に変更し、従来の `v = 0` と持ち上げ添字の双方を含む。既存 main の宣言は変更していない。

個別検査、一般化した四本と直接の importer を含む鍵付き対象ビルド **2,570 jobs**、累計138本 **1,579宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-68.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyEight.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtyeight-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeChainsAdjunction
```

残枠 **1,315行**。`ProductSectionsHom.lean`（51行）は、この随伴と既存の重み付き切断の随伴を合成して、積重みの Hom と元の切断空間を全単体で同定する。個別検査済みで対象ビルド・監査待ち、未コミット。`NormalizedWeightSectionMap.lean` で両端の同型の間に指定 AW・shuffle を置く射を検査中。空間の同値性や native 極限性を、射を構成しただけで完了とは数えない。停止点2は未完。

## 69. 3b-2 続行：積重み Hom と重み付き切断の全単体同型

コード `007702bd5`、新規 `DiagramComparison.ProductSectionsHom` 1本51行。累計 **139本8,736行**。

持ち上げ標準単体の全自然同型と Yoneda 同型を使い、自由鎖の随伴と既存の重み付き切断の随伴を合成した。積重みの自由鎖からの全単体 Hom を、同じ重み・同じ実 Γ 図式の重み付き切断空間に同定した。第一のまとまりの積側の接続。

個別検査、鍵付き対象ビルド **2,632 jobs**、累計139本 **1,584宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-69.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyNine.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtynine-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductSectionsHom
```

残枠 **1,264行**。`NormalizedWeightSectionMap.lean` の指定 AW・shuffle による両方向の実単体的射は個別検査済み、対象ビルド・監査待ち。

同値性には、自然な鎖ホモトピーを余単体 Hom の実単体的ホモトピーへ移す接続がなお必要。一般の余単体図式について点ごとの鎖ホモトピーだけで結論してはいけない。直接の経路として、積重みの第二パラメータのグラフを指定 AW に送り、パラメータ鎖への余作用を作る部分を `ProductParameterCoaction.lean` で検査中。余作用の単位則、区間によるホモトピー評価、両端点との等式はこれからで、同値性を証明済みとはしない。既存のモデル圏の frame 比較も確認したが、必要な frame 条件を証明せず適用したり `[ModelCategory SSet]` を追加したりはしない。native 極限性と後続も未完。停止点2ではない。

## 70. 3b-2 続行：指定正規化重み比較の両方向の射

コード `2fc8b73dc`、新規 `DiagramComparison.NormalizedWeightSectionMap` 1本43行。累計 **140本8,779行**。

§67と§69の全単体同型の間に、元の AW・shuffle による指定前合成を置き、図式 Hom 複体の実 Dold–Kan 空間と重み付き切断空間の間の両方向の実単体的射を構成した。逆射の法則やホモトピー同値性を、この構成だけで主張してはいない。

個別検査、鍵付き対象ビルド **2,640 jobs**、累計140本 **1,588宣言・標準三公理のみ**の一時監査が成功。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-70.log`、監査 `/private/tmp/AuditISW2G10HundredForty.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredforty-modules.txt`。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionMap
```

## 71. 3b-2 続行：積パラメータの指定余作用と凍結前の保存

コード `a09e4c437`、新規 `DiagramComparison.ProductParameterCoaction` 1本55行。累計 **141本8,834行**、上限10,000行まで **1,166行**。

積の第二射影のグラフを自由負次数鎖へ送り、指定 AW と合成してパラメータ鎖への余作用を構成した。重みとパラメータの全図式射に対する自然性を証明した。§37.2の第一のまとまりの内部で、余作用の単位則や鎖ホモトピーから実単体的ホモトピーへの輸送はまだ含まない。

個別検査、鍵付き対象ビルド **2,275 jobs**、累計141本 **1,604宣言・標準三公理のみ**の一時監査の成功をログで確認した。対応するビルド・監査のプロセスは終了している。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-71.log`、監査 `/private/tmp/AuditISW2G10HundredFortyOne.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortyone-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductParameterCoaction
```

検証済みの Lean は上記まで枝にコミット済み。11-13昼の凍結予告を受領した。確定連絡後は夜の枝へのコミットを控え、翌朝の main 取り込みと改名追従は配布される手順に従う。現時点で凍結確定の連絡は未受領。

停止点2は未完。残るのは、指定全単体比較のホモトピー同値性と指定豊穣 Hom 合成との照合、native 切断・極限性、標準脚と D(A) 輸送、全図式射・指定錐の族・離散加群入口。残枠は小さく、既存の自然な鎖ホモトピーを点ごとに適用しただけで全単体空間の同値性とする短縮はできない。範囲・型は維持し、上限を超えそうな場合は追加実装前に報告する。

## 72. 3b-2：残工程の再点検と上限による中間停止

11-13、§71の保存後に実ソースと既存の極限判定の型を再点検した。登録待ち141本の一覧を現在の作業木の各ファイルに解決して行数を再集計し、**8,834行**を確認した。検証済みコードは `a09e4c437` まで、報告は `e1c96bafc` まで。未コミットの Lean はない。以下は紙の検討であり、新しいビルド・監査の実施を主張しない。

### 72.1 短縮候補の検査

1. `NormalizedBousfieldKanHomSpace.normalizedBousfieldKanHomSpaceComparison_equivalence` は元の Hom–Tot 比較の Γ 像の同値性を既に証明する。ただし終域は正規化 BK Hom 複体の Γ であり、重み付き切断空間ではない。`NormalizedWeightSectionMap` の両方向の射はこの次の接続で、両合成の単体的ホモトピーはまだない。鎖の段階の自然な EZ ホモトピーを得たことと、余単体 Hom 空間でのホモトピーを得たことを混同しない。
2. 直接の経路では `ProductParameterCoaction` の余作用を使い、単位則、区間の評価、両端点の式、全単体への自然性を証明する必要がある。現ファイルの結論はグラフ・余作用・自然性までで、これらの残項を含まない。一般 A の EZ の移送そのものは既存の加法的移送・底変換同型・分裂で済んでおり、作り直さない。
3. `ModelCategoryComparison.frameHomMap_homotopyEquivalence` は別の候補だが、実際の二つの frame の Reedy cofibrancy、両 frame の構造射の弱同値性、比較の各点の弱同値性、標的の fibrancy を要求する。確認した型は `[ModelCategory C]` を持つ一般定理であり、新しい `[ModelCategory SSet]` を足す必要があるという意味ではない。しかし今回の図式圏と frame に対する必要条件の証明が自動的に供給されるわけではなく、現時点では短い完成経路を確認できていない。
4. `coherentCone_isLimit_of_family_lifts` の型を再確認した。必要なのは各試験対象での実切断への族 `a`、頂点評価が `coherentCosliceFiberComparison` そのものになる式 `ha`、同じ族の制限が同値である証明 `he`。`EnrichedBousfieldKanCone` の自然変換と空間間の抽象的な同値だけではこの三入力を満たさない。指定豊穣合成との照合を省けない。
5. `dgModuleResolvedInfinity_isLimitCone_of_raw` は raw の実極限性を仮定として D(A) 側へ運べる。この定理を再利用して輸送自体を作り直す必要はないが、raw 極限性の入力と、元の頂点・標準脚の同定は別途必要。全図式射・指定錐の族・離散加群入口も3b-2の責任として残す。

### 72.2 残量と停止理由

§37.2の四つのまとまりを維持した再見積もり。これは実装量の予測であり、数学的な下限でも完成の保証でもない。第二〜第四のまとまりは、既存の錐・輸送定理を再利用する前提の従来見込みを維持する。第一は一般 A の移送と両端の Hom 同定が済んだ分を除いた。

| 残るまとまり | 今あるもの／残る結論 | 追加見込み |
| --- | --- | ---: |
| 正規化テンソル／積重み | 両端の全単体同型・AW/shuffle の射・自然な鎖ホモトピーはある。実単体的ホモトピーと指定比較の最終照合が残る | 400〜700行 |
| 指定豊穣 Hom と native 極限性 | 指定錐と豊穣 Hom 図式はある。上記 `a`・`ha`・`he` と同じ制限の照合が残る | 600〜900行 |
| 標準脚と D(A) 輸送 | 既存の輸送定理を使う。元の標準脚の最終式と入力の接続が残る | 400〜700行 |
| 全図式射・指定錐の族・離散加群入口 | 点ごとの完成から全射・同じ錐の族への組み立てと入口が残る | 500〜900行 |
| 合計 | | **1,900〜3,200行** |

完成見込みは **10,734〜12,034行**、承認済み上限は **10,000行**、残枠は **1,166行**。上限を超えそうなときは検証済みを保存して止めるという条件に達したため、**3b-2 の追加 Lean はここで中間停止する**。上限を使い切るための補助宣言追加は行わない。新しい第五のまとまりを要求しているのではなく、承認済み四まとまりの残量が枠を超える見込みである。

これは停止点2ではない。範囲・型を弱めず、全図式射を3b-3に移さず、⑤aのファイルを変更せず、上限を独自に変更しない。検証済み部分はすべて保存済みで、凍結前の取り込みに利用できる。再開には、この残工程と規模について調整が必要。

### 72.3 代わりの紙の作業：3b-4への受け渡しの現状

§38の境目は維持する。今回完成した自由鎖・正規化・全単体 Hom の部品は加群の比較であり、BE 作用を持つ Tot を構成したものではない。3b-4の U 比較に渡すものは、G10 が完成した際の同じ頂点・脚・高次単体を持つ指定 Tot 錐の族である。現状の `normalizedWeightSectionMap` を代用品として渡さない。

再開後は上表の順でG10を閉じ、停止点2の検証後に§38.2の1・2（strict BE 模型と実 U の比較）へ進む。③-aの3b-3が必要なのは coherent な図式へ拡張する際の評価同値と錐の輸送である。加群値の評価同値から BE 値の厳密化を無条件に推論しない。この紙の整理では鍵を取得せず、BE の新規 Lean も開始していない。

