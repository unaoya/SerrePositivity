# IS-W2 の報告（report-inf-supply-w2.md） — 3b-4 後半（R03d・R03h・B4′）（§236〜§305、2026-11-15〜11-16）

元の報告：[report-inf-supply-w2.md](../../stage-ii/inf-supply-b/report-inf-supply-w2.md)

## 236. §20の承認による再開：同じnative fiber射と同じcorrected pairing（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

ユーザーはIS-W2 §20として外枠22,000行を承認した。/goalの範囲と型は維持し、Tot側R03d・R02〜R05とR11/R12のTot部分を先に閉じて停止点3b-4a、その後は止める指示がなければ実現側へ進む。§19の中間定理の枠も維持する。判断待ちを解いてLeanを再開した。

最初の検査単位は§235のとおり。元のstrictBETotJointSourceNativeFiberMapに、同じnative Hom入力によるvertexFiberPullbackIsoの順射を合成する。包含後の等式は、既存のvertexFiberPullbackIso_hom_ι、元のfiberLiftの包含後の等式、元のnative Hom写像の第一射影の等式を順に合成する。これにより元の同じcorrected pairingへの制限を回収する。既存のpullback・fiber・合成則の照合であり、追加の数学項目としては数えない。native fiber射の弱同値性はこの段では主張しない。

### 236.1 型（既存構成の合成則、共通入力 `(A : Type u) [CommRing A]`）

#### StrictDiagramTotJointSourceNativeFiberPairing（66行）

```lean
def strictBETotJointSourceNativeTwistedFiberMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
      vertexFiber (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P))

theorem strictBETotJointSourceNativeFiberMap_ι (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceNativeFiberMap A P ≫
      vertexFiberι (strictBETotJointNativeHomProjection A) (nerveVertex P) =
        simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
          strictBETotJointSourceNativeHomMap A

theorem strictBETotJointSourceNativeTwistedFiberMap_ι (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceNativeTwistedFiberMap A P ≫
      vertexFiberι (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P)) =
      simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceCorrectedPairing A
```

## 237. 同じfiber制限による指定pathの保持（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

元のstrictBETotJointSourceCorrectedPairingIsoそのものを同じfiber包含へ前合成する。その射影は、元の指定されたstrictBETotJointSourcePairingBasePathIsoと厳密な射影等式の同じ合成を、同じfiber包含へ前合成したものに等しい。既存functorIso_precomp_postcompと元の全同型の射影等式だけによる全同型の合成則であり、新しい数学の項目を増やさない。native fiber射の弱同値性やR03dの最終等式が済んだとは扱わない。

### 237.1 型（共通入力 `(A : Type u) [CommRing A]`）

#### StrictDiagramTotJointSourceNativeFiberPath（56行）

```lean
def strictBETotJointSourceFiberPairingIso (P : strictBETotJointHomIndex A) :
    FunctorIso
      (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceCorrectedPairing A)
      (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceNativePairing A)

theorem strictBETotJointSourceFiberPairingIso_postcomp (P : strictBETotJointHomIndex A) :
    (strictBETotJointSourceFiberPairingIso A P).postcomp
      (twistedArrowProjection (CAlg_R A)) =
      FunctorIso.precomp (eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          strictBETotJointSourcePairingBasePathIso A)
            (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P)
```

## 238. 再開の最初の検査単位の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03d・R02・R03は引き続き未完了。

§236・§237の二本を検証した。元のnative fiber射へ同じvertexFiberPullbackIsoを合成し、包含後に同じ元のcorrected pairingへの制限を厳密に回収する。さらに、そのcorrected pairingと元のpairingの同じ全同型を同じfiber包含へ制限し、射影が元の指定pathをそのまま制限したものと全同型として等しいことを確認した。native fiber射自身の弱同値性、同じ延長の全同値性、固定始域の元の全FunctorIsoへの最終正規化はまだ残る。

検査経過：最初の個別検査では単体記法のscopeとfiberLiftの包含後の簡約を直した。二度目の等式ではpullback.sndと元のnative射影の定義展開を明示した。最終個別検査9358は終了0。313の対象ビルドは12,228 jobsで成功したが、一時監査の先頭で私がimportをmoduleより前に置いて構文エラーを起こした。314ではその先頭を修正し既存交換則の依存も生成したが、合成同型へのprecompの型推論が失敗した。FunctorIso.precompを明示した最終個別検査64620は終了0。

最終315：鍵付き対象ビルド12,233 jobs、小監査180本・1,291宣言、標準三公理のみ。実ハンドル90235・終了0、鍵返却済み。コマンドはwith_build_lock.sh --class impl --wait 3600と1700秒のguardを使用し、一度に一枚の整理券のみ。rootビルドや公式監査の登録は行っていない。既存依存を含む対象ビルドである。名前空間の長いopen行についてstyle警告はあるが、エラーはない。

今回122行（66行・56行）、累計180本・11,686行／承認済み外枠22,000行、残り10,314行。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainを変更していない。追加する数学の一覧項目は増やさず、既存のfiber・pullback・全同型の合成則として型を§236・§237に記載した。

登録候補（調整役の取り込み時用、今回はこちらで登録しない）：

- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiberPairing
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiberPath

次は§234.3・§235のとおり、同じnative fiber射を元の固定始域のroof比較と照合し、その実射自身の弱同値性へ接続する。Tot側の停止点3b-4aはまだ未到達であり、この検収を停止点の完成とはしない。

## 239. R03dの次の接続：同じfiber包含の通常圏での表示（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

前ターンは§236〜§238を検証して1c8716f15へ保存した進捗。今回も§238の次から続ける。mainにIS-W2 §20の追記は入ったが、この確認時点では57705f223はmainの祖先ではないので、取り込み完了後のmergeはまだ行わない（ユーザーはmerge前の続行を承認済み）。

元のroofは固定始域の実際のHom単体のラベルで定義される。§238のfiber包含をこの通常圏のラベルに照合するため、元のGrothendieck表示を経由するfiber包含が通常のGrothendieck.ιと同じnerve射であることを示す。元のweighted nerve同型の逆を別の逆で置き換えず、同じ順射を合成して確認する。既存構成の単位・係数表示の法則であり、数学的な一覧項目は増やさない。見込み80〜180行。共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

```lean
theorem grothWeightedNerveForward_fiberInclusion (i : I) :
    nerveMap (Grothendieck.ι F i) ≫ grothWeightedNerveForward F =
      weightedNerveConstantLift (F ⋙ nerveFunctor) i

theorem grothendieckFiberInclusion_eq_nerveMap (i : I) :
    grothendieckFiberInclusion F i = nerveMap (Grothendieck.ι F i)
```

この照合だけでnative fiber射自身の弱同値性は結論しない。元の通常の要素圏とroofの反対要素圏の規約、同じcorrected pairingの指定path、固定始域の元の全Hom比較の合成順序を、引き続き追跡する。

## 240. 元のfiber包含から元のsource-frameのラベルへ（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

§239の順射のprefix計算は個別検査90750で終了0。その同じ順射を合成して元の逆を消去し、grothendieckFiberInclusionが通常のGrothendieck.ιのnerveと厳密に等しいことを示した。これを元の全要素圏へ移すと、同じsimplicialElementsFiberInclusionは同じ通常の要素圏の包含のnerveとなる。通常の包含を元のsource-frameのdownへ合成し、同じ底・単体次数と元のHom単体のラベルを厳密に回収する。元のnative pairingへの制限も同じ通常の包含のnerveを通る。

全て、元のfiber包含・係数表示・合成則の照合であり、新しい数学の一覧項目は増やさない。通常の要素圏をroofの反対要素圏と同一視しておらず、弱同値性やR03dの全同型の正規化を完了と数えない。一般版は116行（見込み80〜180行、上端との差−64行）、BEの係数表示の特殊化は62行。一般版の完成形の個別検査31293は終了0。BEの合成検査と対象ビルド・監査は別途以下へ記録する。

### 240.1 型

一般版の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。Gは同じI上のSSet値の図式。BE版は `(A : Type u) [CommRing A]`。Gを使う宣言には未使用のFは入らない。

#### SimplicialElementsFiberInclusion（116行）

```lean
theorem grothWeightedNerveForward_fiberInclusion (i : I) :
    nerveMap (Grothendieck.ι F i) ≫ grothWeightedNerveForward F =
      weightedNerveConstantLift (F ⋙ nerveFunctor) i

theorem grothendieckFiberInclusion_eq_nerveMap (i : I) :
    grothendieckFiberInclusion F i = nerveMap (Grothendieck.ι F i)

def simplicialElementsFiberFunctor (G : I ⥤ SSet.{u}) (i : I) :
    (simplicialElementsCatDiagram G).obj i ⥤ SimplicialTotalElements G

theorem simplicialElementsFiberInclusion_eq_nerveMap (G : I ⥤ SSet.{u}) (i : I) :
    simplicialElementsFiberInclusion G i = nerveMap (simplicialElementsFiberFunctor G i)

theorem simplicialElementsFiberFunctor_obj (G : I ⥤ SSet.{u}) (i : I)
    (s : (simplicialElementsCatDiagram G).obj i) :
    ((simplicialElementsFiberFunctor G i).obj s).obj = (i, s.obj)

theorem simplicialElementsFiberFunctor_value (G : I ⥤ SSet.{u}) (i : I)
    (s : (simplicialElementsCatDiagram G).obj i) :
    ((simplicialElementsFiberFunctor G i).obj s).val = s.val
```

#### StrictDiagramTotJointSourceFiberElements（62行）

```lean
def strictBETotJointSourceFiberElements (P : strictBETotJointHomIndex A) :
    (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P ⥤
      FrameHom.SourceFrameArrowElements (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A))

theorem strictBETotJointSourceFiberElements_parameters (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    ((strictBETotJointSourceFiberElements A P).obj s).obj = (AsSmall.down.obj P, s.obj)

theorem strictBETotJointSourceFiberElements_value (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    FrameHom.sourceFrameArrowValue (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A))
      ((strictBETotJointSourceFiberElements A P).obj s) = s.val.down

theorem strictBETotJointSourceFiberPairing_eq (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
      strictBETotJointSourceNativePairing A =
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      strictBETotJointSourceNativePairing A
```

## 241. 対象ビルドの順番待ち中の照合：roofの余終性の入力範囲（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

316の対象ビルドと小監査を、一枚の整理券で--class impl --wait 3600により待機中。一般版の個別検査は通過したが、一時的な結合検査ではBE側の全importを先に読み込んだ文脈でprefix証明が200,000 heartbeatsに達した。計算上限は上げず、実際のモジュール分割で一般版を先にビルドしてからBEの特殊化を検査する。結合検査の失敗を対象ビルドの成功と扱わない。最終結果は次の検収欄へ記す。

待機中に既存のroof側のAPIを確認した。CofibrantSourceFrameRightKanCofinalityのcofibrantSourceFrameRawRoofMap_isLeftCofinalは、X・YともCofibrantAlgebra Aであり、cofibrantAlgebraRelativeCategoryのhammockを使う。ModelBifibrantFrameRightKanCofinalityのmodelBifibrantSourceFrameRawRoofMap_isLeftCofinalは、X・YともBifibrantObjectであり、modelBifibrantRelativeCategoryのhammockを使う。今回の元の右置換RYを、そのままこれらの入力に読み替えることはできない。元のnative Homの入力と全局所化の比較を保ち、必要な係数移送と端点同型を明示する必要がある。

またcosliceTwistedHomMap_isQCatEquivalenceは任意のquasicategoryの同じ端点での同値で、cosliceTwistedHomMap_ιは元のcosliceからtwisted-arrowへの包含後の等式を与える。ただし今回のroof評価のpinched Homとcoslice fiberの規約を合わせる工程が残る。この同値を引用するだけで§238の実射自身が弱同値になったとはしない。今回のラベル回収と、元のroofとの正規化を接続してから判定する。

## 242. 元のfiber包含とラベルの対象ビルド検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

316が終了した。同じ整理券で共有鍵を待ち、対象ビルド12,230 jobs成功、小監査182本・1,303宣言、標準三公理のみ。実ハンドル88366・終了0、鍵返却済み。一般版とBE特殊化を実際の二モジュールに分けたビルドで通し、一時結合ファイルのtimeoutを解消した。計算上限は変更していない。

今回178行、累計182本・11,864行／外枠22,000行。一般版116行とBE版62行。sorry・独自公理0。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。R03dのnative fiber射自身の弱同値性はまだ未完了。

登録候補：SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberInclusion、およびSerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceFiberElements。

この検収直後に調整役からtensorFrameHomIso_pointの集約時の重複を通知された。316の小監査は両定義を同時importする検査ではなかったため、これを検出できていない。次の修正ではmainの既存の定義と同時にimportし、宣言名の突合も行う。316の成功を集約での重複不存在の根拠としては使わない。

## 243. 集約時の重複定理の修正と宣言名の突合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

調整役から通知されたtensorFrameHomIso_pointの重複を修正した。TensorConeUnitPointでの宣言を削除し、FrameConeClassesの既存lemmaを再公開する互換入口だけを残した。StrictDiagramTotUniversalProbePointComparisonはFrameConeClassesを直接importし、既存lemmaの暗黙引数Yを呼び出し側で明示する。既存FrameConeClasses側は変更していない。互換入口には宣言がないので、小監査ではこのモジュールの宣言数0を明示的に要求し、補題の実際の定義元がFrameConeClassesであることも検査する。

宣言名の突合は、自分のIS-W2のモジュール一覧と枝で追加したLeanファイル548本（1,728個の名前付き宣言）を対象に、main 7e03e17a7 のEInfinity配下3,749本・13,399個の名前付き宣言と行った。namespace・section・endを追跡し、コメントを除いてdef・lemma・theorem・abbrev等と名前付きinstanceを走査し、同じ完全名が異なるファイルにあるものを検出した。同一ファイルでmainと共通の宣言は重複と数えない。この修正後の対main EInfinityの衝突は0件。

自分のファイル同士にも同じ走査を行い、HAのnormalizedMooreReverse_zero_inclusionをもう1件検出した。NormalizedMooreReverseZeroとNormalizedMooreReverseEvaluationに同じ完全名・同じ型の定理があった。Zero側をEvaluationの再公開だけの互換入口にし、既存Evaluation側は変更しない。直接importerのNormalizedMooreReverseExtendZeroも対象ビルドに含める。修正後の自分の新規ファイル同士の衝突は0件。HAの補題の定義元がNormalizedMooreReverseEvaluationであり、Zero側の宣言数が0であることも小監査で検査する。走査結果は/private/tmp/isw2-declaration-collision-scan.jsonと/private/tmp/isw2-declaration-collision-scan-after-fix.jsonに保存した。

これは名前付き宣言をテキスト走査する確認であり、全importの同時ビルドやLeanの生成する内部名の検査とは区別する。小監査には既存の定義元を明示的にimportして、通知された二つの名前について実際の同時importと定義元も検証する。既存の公式入口・監査、⑤a、mainは変更しない。

317の対象ビルド・小監査は--class impl --wait 3600で同じ整理券のまま待機する。待機中でpayloadのzshがまだ起動していないことをpsで確認してから、追加で見つかったHAの直接importerも同じジョブへまとめた。追加の整理券や鍵の取り直しは行っていない。結果が通るまではこの修正コードをコミットしない。

## 244. R03dの係数移送の下書き：元の固定標的roofの反対圏へ（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。この下書きは対象ビルド前なので検証済みの行数・モジュール数には加えない。

重複修正の対象ビルドを待つ間に、既存のULiftHom.equiv、宇宙持ち上げのelementsEquivalence、固定標的のelementsCostructuredEquivalence.rightOpを合成した。元の通常の要素圏は固定標的のroofの反対圏に移る。次数・元の実射のラベル・単体作用素を、同じ関手の厳密な式で回収する。既存の同値と係数移送の合成則であり、数学的な一覧項目を増やさない。見込み80〜150行。元のnative fiber射の弱同値性はまだ結論しない。

UniverseLiftElementsのoleanが未生成だったので、その既存ソースを一時検査へ含めた。別モジュールの宇宙変数vの再宣言が一時結合ファイルだけで重なったため、その一時ファイルの宣言を整理した。最終個別検査37848は終了0。対象ビルドと小監査は、優先する重複修正を検収した後に行う。このLean下書きは重複修正のコミットに含めない。

### 244.1 型

共通入力は `{C : Type u} [Category.{v} C] (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)`。

#### LiftedSourceFrameFiberRoof（53行）

```lean
def liftedSourceFrameFiberRoofEquivalence (P : liftedSourceFrameIndex (C := C)) :
    (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P ≌
      (CostructuredArrow (Q.obj (AsSmall.down.obj P).1.unop)
        (R.obj (AsSmall.down.obj P).2))ᵒᵖ

theorem liftedSourceFrameFiberRoofEquivalence_degree (P : liftedSourceFrameIndex (C := C))
    (s : (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P) :
    (((liftedSourceFrameFiberRoofEquivalence Q R P).functor.obj s).unop).left =
      s.obj.unop

theorem liftedSourceFrameFiberRoofEquivalence_value (P : liftedSourceFrameIndex (C := C))
    (s : (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P) :
    (((liftedSourceFrameFiberRoofEquivalence Q R P).functor.obj s).unop).hom =
      s.val.down

theorem liftedSourceFrameFiberRoofEquivalence_operator (P : liftedSourceFrameIndex (C := C))
    {s t : (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P}
    (f : s ⟶ t) :
    (((liftedSourceFrameFiberRoofEquivalence Q R P).functor.map f).unop).left =
      f.down.hom.unop
```

## 245. 同じroofのラベルと元のnative pairingのラベルを照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

§244の同じ既存同値の合成をBEの同じ全パラメータへ特殊化した。同じroofの射のラベルが、元のstrictBETotJointSourceFiberElementsを経由してnative pairingへ渡したsourceFrameArrowValueと厳密に等しい。次数も同じ元のHom単体の次数である。既存の係数移送・同値の合成則の照合として型を記録し、数学的な一覧項目を増やさない。一般版と合わせた一時個別検査81098は終了0。元のnative fiber射自身の弱同値性はなお未完了。

優先する重複修正の318はまだ鍵の順番待ちで、psによりpayload未起動を確認した。同じジョブへこの二本の対象と小監査を追加した（整理券の追加・取り直しなし）。対象ビルドと監査が通るまでは、この二本もコミットしない。重複修正とこの係数移送は別コミットにする。追加の宣言名はgit grepでもmainのEInfinity配下に存在しないことを確認した。

### 245.1 型（共通入力 `(A : Type u) [CommRing A]`）

#### StrictDiagramTotJointSourceFiberRoof（58行）

```lean
def strictBETotJointSourceFiberRoofEquivalence (P : strictBETotJointHomIndex A) :
    (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P ≌
      (CostructuredArrow ((strictBETotJointSourceFrame A).obj (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))ᵒᵖ

theorem strictBETotJointSourceFiberRoofEquivalence_degree (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    (((strictBETotJointSourceFiberRoofEquivalence A P).functor.obj s).unop).left =
      s.obj.unop

theorem strictBETotJointSourceFiberRoofEquivalence_pairingValue
    (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    (((strictBETotJointSourceFiberRoofEquivalence A P).functor.obj s).unop).hom =
      FrameHom.sourceFrameArrowValue (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A))
        ((strictBETotJointSourceFiberElements A P).obj s)
```

## 246. 調整役への重複修正の検収報告（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

依頼されたtensorFrameHomIso_pointの重複を削除した。TensorConeUnitPointはFrameConeClassesを再公開する宣言0の互換入口になり、StrictDiagramTotUniversalProbePointComparisonは既存lemmaを直接使う。Kᵒᵖ・重み・frame・元の比較射と暗黙のYを明示して既存lemmaを取り、その成分表示をIso.app_homで合わせた。既存FrameConeClassesは変更していない。途中の317ではYだけを明示した呼び出しでSmallCategoryの推論に失敗し、引数を明示した後は成分表示の差も修正した。最終個別検査7586は終了0。

同名宣言の追加の確認で見つけたHAのnormalizedMooreReverse_zero_inclusionも同様に修正した。NormalizedMooreReverseZeroはNormalizedMooreReverseEvaluationを再公開する宣言0の互換入口となり、既存Evaluation側の証明を使う。直接importerのNormalizedMooreReverseExtendZeroも対象ビルドに含めた。一時結合検査48967は終了0。既存補題の型と内容は維持し、G10の完了項目を弱めていない。

最終の全宣言名走査はmain 7f52c5cd1を対象とし、検査時点の自分の549本・1,732個の名前と、main EInfinityの3,745本・13,373個の名前を照合して、異なるファイル間の衝突0件。その後に追加したBEのroof特殊化の3宣言もgit grepでmainに存在しないことを確認した。自分の550本・1,735個の名前の最終の内部照合も衝突0件。これらはテキストによる名前付き宣言の確認であり、生成される内部名を含むrootの全ビルドとは区別する。

318の最終結果：鍵付き対象ビルド12,245 jobs成功、小監査188モジュール・1,318宣言、標準三公理のみ。実ハンドル88868・終了0、鍵返却済み。--class impl --wait 3600、1700秒guardで同じ一枚の整理券を使った。待機中に個別検査を通過したR03dの二本も同じ対象と監査へまとめた。BEの自分の184本は1,311宣言、残りは既存FrameConeClassesとHAの既存・直接importerの4本である。

小監査は二つの互換入口の宣言数が0であることに加え、tensorFrameHomIso_pointの定義元がFrameConeClasses、normalizedMooreReverse_zero_inclusionの定義元がNormalizedMooreReverseEvaluationであることを明示的に要求して成功した。従って旧い重複宣言の定義元を取り違えた結果を成功としていない。sorry・独自公理0、計算上限の変更なし。既存の定義元二本・公式入口・公式監査・mainは変更していない。

修正対象（この修正のコミットに含む）：

- SerrePositivity/EInfinity/HomotopyWeight/TensorConeUnitPoint.lean
- SerrePositivity/EInfinity/BarrattEccles/StrictDiagramTotUniversalProbePointComparison.lean
- SerrePositivity/HomologicalAlgebra/NormalizedMooreReverseZero.lean

rootとEInfinity集約の全ビルドは実行していない。取り込みの再検収を調整役にお願いする。二つの互換入口は登録済み・登録予定の経路を維持するが、自身の宣言数は0となる。R03dで追加した二本は次節の別コミットとして記録する。

## 247. 同じfiberから元のroofへの係数移送を保存（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03d・R02・R03は未完了。

重複修正は専用コミットe0c5190ecに保存した。その修正と別に、§244・§245の二本を同じ318の対象ビルドと小監査で検収して保存する。一般版53行、BE版58行、計111行。一般版は見込み80〜150行に対して53行（上端との差−97行）。既存の三つの同値の合成で元の通常のfiber要素圏を元の固定標的roofの反対圏へ移し、元の次数・実射ラベル・単体作用素を保持した。同じroofの射のラベルは、元のnative pairingへ渡したsourceFrameArrowValueに厳密に等しい。

検証は§246に記載した318（対象ビルド12,245 jobs、188モジュール1,318宣言、標準三公理のみ、実ハンドル88868・終了0）による。個別検査37848・81098も終了0。BEの自分のモジュール一覧は184本・1,311宣言で、TensorConeUnitPointは既存補題の再公開のみのため自身の宣言0を含む。検証済みの累計は11,953行／外枠22,000行。sorry・独自公理0、計算上限変更なし、[ModelCategory SSet]なし、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainの変更なし。

今回の登録候補：

- SerrePositivity.EInfinity.FrameHom.LiftedSourceFrameFiberRoof
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceFiberRoof

57705f223以後の検証済み新規ファイルは上記二本に加え、§238のStrictDiagramTotJointSourceNativeFiberPairing・StrictDiagramTotJointSourceNativeFiberPath、§242のSimplicialElementsFiberInclusion・StrictDiagramTotJointSourceFiberElementsの計6本。各節の完全なモジュール名を使って登録できる。こちらで公式入口・監査には登録していない。

次は同じ元のfiberの反対要素圏を既存resolutionLeftRoofColimitMapへ送る。この既存の実射の弱同値性には右置換のfibrancyと指定right frame・第一分解が使える（FibrantSourceReducedFirst）。その後に§238の同じnative fiber射と指定pathを、この同じroofの全族の比較へ照合する。ラベルが一致するだけで実射の弱同値性や全FunctorIsoの正規化が済んだとはしない。Tot側の停止点3b-4aは引き続き未到達。

## 248. 元の反対要素圏を同じ実left-roof比較へ移す（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

§247の次の検査単位。元の持ち上げたHomの要素圏の反対nerveから、元のsourceFrameElementsFamilyの入力nerveへ、同じULiftの上下だけを使う厳密な同型を取る。その順射を元のresolutionLeftRoofColimitMapに合成する。標的のfibrancy・指定right frame・第一分解は既存の弱同値定理と同じ入力として明示し、その実射の弱同値性を同じ係数同型で移す。新しい弱同値の仮定や[ModelCategory SSet]を置かない。

既存の係数移送と既存の実射の弱同値定理を同じ同型で前合成する法則であり、新しい数学的な一覧項目は増やさない。二本合わせて見込み100〜200行。元のnative fiber射自体の弱同値性をまだ結論していない。元のsame corrected pairingとこの基準roof比較の照合が残る。

### 248.1 型

第一のファイルの共通入力は `(K : SSet.{v})`、wは指定された宇宙の持ち上げ。第二のファイルは `{C : Type u} [Category.{v} C] [ModelCategory C] {X : C} (q : CofibrantResolution (C := C) simplex X) (Y : C)`。弱同値定理のYのfibrancy、r、cofを全て明示している。

#### ElementsOppositeUniverseIso（63行）

```lean
def elementsOppositeUniverseIndex :
    (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ ⥤
      ULiftHom.{max w v} K.Elementsᵒᵖ

def elementsOppositeUniverseIndexInverse :
    ULiftHom.{max w v} K.Elementsᵒᵖ ⥤
      (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ

def elementsOppositeUniverseNerveIso :
    nerve (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ ≅
      nerve (ULiftHom.{max w v} K.Elementsᵒᵖ)
```

#### LiftedResolutionLeftRoof（43行）

```lean
def liftedResolutionLeftRoofColimitMap :
    nerve (ULiftHom.{max u v}
      ((SSet.uliftFunctor.{max u v,v}).obj ((cosimplicialHom q.obj).obj Y)).Elements)ᵒᵖ ⟶
      SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (weakEquivalences C) X Y

theorem liftedResolutionLeftRoofColimitMap_isWeakHomotopyEquivalence [IsFibrant Y]
    (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C)
      (trivialFibrations C)) :
    IsWeakHomotopyEquivalence (liftedResolutionLeftRoofColimitMap q Y)
```

## 249. 同じBEの反対fiberから元の実roof比較への弱同値（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

厳密な係数同型は最終個別検査46841で終了0。元の実left-roof比較とその弱同値性の係数移送は、一時結合検査10774で終了0。nerveMapの既存の補助入口は対象宇宙を共有する圏の関手を要求するため、今回の同じ上下の関手を全射列へ直接合成して、異なる対象宇宙のnerve間の同じ実写像を定義した。両往復の厳密な等式も各射列で確認した。計算上限は変更しない。

その元の実射をBEの同じ全パラメータPへ特殊化する。元のsource frameはmodelSourceFrameFamilyを同じframedLimitProbeへ適用したもの、標的は同じrightFrameReplacement。元の右置換のfibrancyとrightFrameFamily・mappingCofibrantFactorizationを、既存の弱同値定理の入力へそのまま使う。新しいfibrancyや弱同値性を仮定として追加しない。既存の係数移送・特殊化の法則として型を記録し、数学的な一覧項目は増やさない。特殊化の見込み80〜150行。

これは元のnormal fiberの反対要素圏から同じhammock余極限への基準射についての弱同値性である。元のnative fiber射とこの基準射が同じ比較を表すこと、元の指定pathを保った正規化、固定始域の元の全FunctorIsoとの一致は引き続き残る。R03dを完了とは数えない。

### 249.1 型（共通入力 `(A : Type u) [CommRing A]`）

#### StrictDiagramTotJointSourceRoofComparison（59行）

```lean
def strictBETotJointSourceRoofComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)

theorem strictBETotJointSourceRoofComparison_isWeakHomotopyEquivalence
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofComparison A P)
```

## 250. 同じ反対fiberから元の実roof比較への弱同値の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

§248の厳密な同型は最終個別検査46841・終了0、元の実roof比較への係数移送と弱同値性は10774・終了0、BEへの特殊化は21507・終了0。319の鍵付き対象ビルド12,236 jobsと小監査191モジュール・1,336宣言が成功し、標準三公理のみ。実ハンドル16462・終了0、鍵返却済み。--class impl --wait 3600と1700秒guardを使った。二つの互換入口の宣言数0と既存補題の正しい定義元を確認する条件も引き続き検査した。

今回三本165行。一般の厳密な同型63行、既存のroof比較への移送43行、BEへの特殊化59行。§248の二本は見込み100〜200行に対して106行（上端との差−94行）、§249の特殊化は見込み80〜150行に対して59行（上端との差−91行）。検証済みは187本・12,118行／外枠22,000行。自分の187本の宣言数は1,329で、互換入口TensorConeUnitPointの宣言0を含む。小監査全体には既存定義元とHAの直接importer等の4本も加えている。

元のnative fiberの反対要素圏から、同じsource frame・右置換・第一分解を使う元のhammock余極限への実射を回収し、その実射が弱同値であることを既存定理から移した。native fiber射の弱同値性や、元の固定始域の全FunctorIsoへの正規化を完了とはしていない。既存の係数移送の法則として数学的な一覧の項目数は変えない。sorry・独自公理0、計算上限変更なし、[ModelCategory SSet]なし、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainの変更なし。

登録候補：

- SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ElementsOppositeUniverseIso
- SerrePositivity.EInfinity.FrameHom.LiftedResolutionLeftRoof
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofComparison

次の照合では、normal要素圏のnerveから出る元のnative fiber射そのものをopFunctorで反対向きに写し、nerveOppositeIsoで§249の同じ反対要素圏の始域へ合わせる。この係数移送の元の写像を追跡した上で、元の指定pathと同じroofの全族との照合に進む。opによる表示の変更だけで弱同値性が証明されたとはしない。

## 251. 元のnative fiber射そのものの反対表示と弱同値性の反映（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

§250の基準roof射と始域の向きを合わせるため、元のstrictBETotJointSourceNativeTwistedFiberMapそのものをopFunctorで写し、元のnerveOppositeIsoの逆を前合成する。同じnerve反転を戻すと元の実射のop反転を厳密に回収する。この表示を別の同値の存在へ変更しない。

op反転による弱同値保存の既存定理を二度使い、同じop自己同値の単位の自然性と弱同値の消去則で元の射の弱同値性へ戻す。始域・終域のKan性を新しい入力にしない。その反映則と同じnerve反転同型により、反対表示の弱同値性は元のtwisted fiber射の弱同値性と同値となる。さらに元のvertexFiberPullbackIsoの弱同値性を消去し、元のpullbackのnative fiber射自身との同値に戻す。

既存のop保存則・自己同値の単位・pullbackのfiber同型による係数移送の法則であり、新しい数学的な一覧項目は増やさない。二本で見込み100〜180行。反対表示を定義しただけで弱同値と主張せず、§249の同じ基準roof比較との指定pathを保つ照合は引き続き残る。

### 251.1 型

一般版は任意の `{X Y : SSet.{u}} (f : X ⟶ Y)`。BE版の共通入力は `(A : Type u) [CommRing A]`。

#### OppositeWeakHomotopyReflection（36行）

```lean
theorem opposite_map_isWeakHomotopyEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsWeakHomotopyEquivalence (SSet.opFunctor.map f) ↔ IsWeakHomotopyEquivalence f
```

#### StrictDiagramTotJointSourceNativeOppositeFiber（84行）

```lean
def strictBETotJointSourceNativeOppositeFiberMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      (vertexFiber (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P))).op

theorem strictBETotJointSourceNativeOppositeFiberMap_recover (P : strictBETotJointHomIndex A) :
    (nerveOppositeIso
      (C := (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)).hom ≫
        strictBETotJointSourceNativeOppositeFiberMap A P =
      SSet.opFunctor.map (strictBETotJointSourceNativeTwistedFiberMap A P)

theorem strictBETotJointSourceNativeOppositeFiberMap_weak_iff (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceNativeOppositeFiberMap A P) ↔
      IsWeakHomotopyEquivalence (strictBETotJointSourceNativeTwistedFiberMap A P)

theorem strictBETotJointSourceNativeOppositeFiberMap_weak_iff_original
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceNativeOppositeFiberMap A P) ↔
      IsWeakHomotopyEquivalence (strictBETotJointSourceNativeFiberMap A P)
```

## 252. 元のnative fiber射の反対表示と弱同値性の同値を検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

§251の最終個別検査42295は終了0。op自己同値の単位の成分はIso.app_homで表示を合わせ、その自然性を元のfとopFunctor.mapの二重適用の等式として明記して既存保存則を反映した。元のnative fiberの反対表示と元のtwisted fiber射の弱同値性の同値、さらに同じvertexFiberPullbackIsoを消去して元のpullbackのnative fiber射自身との同値まで示した。

320の鍵付き対象ビルド12,230 jobs成功、小監査193モジュール・1,344宣言、標準三公理のみ。実ハンドル1058・終了0、鍵返却済み。--class impl --wait 3600と1700秒guardを使った。二つの互換入口の宣言数0と既存補題の定義元の検査も維持した。新しい宣言名はgit grepでmainのSerrePositivity全体に存在しないことを確認した。

今回二本120行（一般版36行、BE版84行）、見込み100〜180行に対し上端との差−60行。検証済み189本・12,238行／外枠22,000行。自分の宣言数は1,337で、互換入口の宣言0を含む。小監査全体には既存定義元とHAの直接importer等4本を加えている。既存のop・自己同値の単位・pullbackのfiber同型による係数移送の法則として、数学的な一覧項目は増やさない。

sorry・独自公理0、計算上限変更なし、[ModelCategory SSet]なし、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainの変更なし。今回の同値は実射の弱同値性を別の射の存在へ弱めていない。反対表示の射自体が弱同値であることを結論するには、§250の同じ実roof比較との指定pathを保つ照合がなお必要である。

登録候補：

- SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.OppositeWeakHomotopyReflection
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeOppositeFiber

次に使う既存のAPIはKanHammockHomPinchedMap_weakとKanHammockHomPinchedMap_app_valで、元のEx∞ hammock Homから同じ局所化頂点のpinched Homへの実射と、その全単体の値を保持している。元の同じ局所化比較・端点の指定pathを追跡し、§250の実roof射と今回のnative射の反対表示を全単体・全族として照合する。零単体の回収やπ₀だけの一致ではR03dの全同型の正規化が済んだとはしない。Tot側の停止点3b-4aはまだ未到達。

## 253. 同じroofから同じ局所化頂点のpinched Homへの比較（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

元のstrictBETotJointSourceRoofComparisonを、元のAsSmallComparison.colimitIso、同じEx∞単位、元のkanHammockHomPinchedMapへ合成した。元の全モデル相対圏modelRelativeCategoryを使い、cofibrant/bifibrant相対圏へ置き換えていない。この実射の弱同値性は既存の三つの比較の弱同値性を合成して得る。また元の全標的比較asSmallKanHammockHomFamilyMapの同じ成分を使った構成と厳密に等しいことを、元のEx∞単位の自然性で示した。

全単体の値の既存式をBEへ直接展開するとwhnfの200,000 heartbeatsに達したため、上限を変更せず、一般の相対圏で同じ値と同じ全パラメータの式に名前を付けて分割した。最終個別検査1450は終了0。これは証明・elaborationの分割であり、元の全次数・全単体の主張を保持する。二本合わせて見込み150〜260行。既存比較・係数移送・Ex∞単位・同じ評価式の前合成則なので、数学的な一覧項目は増やさない。

### 253.1 名前付き評価式の意味

C・X・Y・T・fは下記の型の通り。名前付き命題の定義は次の全次数・全単体の等式そのものである。

```lean
def KanHammockPinchedValueFormula {T : SSet.{u}}
    (f : T ⟶ exInfinity.obj (colimitGraph C.weakEquivalences X Y)) : Prop :=
  ∀ {n : ℕ} (s : T _⦋n⦌),
    (((f ≫ kanHammockHomPinchedMap C X Y).app (Opposite.op ⦋n⦌)) s).val =
      kanHammockPinchedSimplexValue C X Y (f.app (Opposite.op ⦋n⦌) s)
```

BEではfに同じstrictBETotJointSourceRoofKanComparisonを代入する。native fiber射との同一視はまだ残る。

### 253.2 型

一般版の共通入力は `(C : RelativeCategory.{u}) (X Y : C.category)`。BE版は `(A : Type u) [CommRing A]`。

#### KanHammockPinchedSimplexValue（49行）

```lean
def kanHammockPinchedSimplexValue {n : ℕ}
    (s : (exInfinity.obj (colimitGraph C.weakEquivalences X Y)) _⦋n⦌) :
    (kanHammockNerve C) _⦋n + 1⦌

theorem kanHammockHomPinchedMap_value {n : ℕ}
    (s : (exInfinity.obj (colimitGraph C.weakEquivalences X Y)) _⦋n⦌) :
    ((kanHammockHomPinchedMap C X Y).app (Opposite.op ⦋n⦌) s).val =
      kanHammockPinchedSimplexValue C X Y s

def KanHammockPinchedValueFormula {T : SSet.{u}}
    (f : T ⟶ exInfinity.obj (colimitGraph C.weakEquivalences X Y)) : Prop

theorem kanHammockHomPinchedMap_value_family {T : SSet.{u}}
    (f : T ⟶ exInfinity.obj (colimitGraph C.weakEquivalences X Y)) :
    KanHammockPinchedValueFormula C X Y f
```

#### StrictDiagramTotJointSourceRoofPinched（116行）

```lean
abbrev strictBETotJointRoofSourceObject (P : strictBETotJointHomIndex A) :
    (modelRelativeCategory (operad A).Algebra).category

abbrev strictBETotJointRoofTargetObject (P : strictBETotJointHomIndex A) :
    (modelRelativeCategory (operad A).Algebra).category

def strictBETotJointSourceRoofKanComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      exInfinity.obj
        (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
          (modelRelativeCategory (operad A).Algebra).weakEquivalences
          (strictBETotJointRoofSourceObject A P) (strictBETotJointRoofTargetObject A P))

theorem strictBETotJointSourceRoofKanComparison_weak (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofKanComparison A P)

theorem strictBETotJointSourceRoofKanComparison_unit (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofComparison A P ≫ exInfinityUnit.app _ ≫
      (FrameHom.asSmallKanHammockHomFamilyMap (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)).app
          (strictBETotJointRoofTargetObject A P) =
      strictBETotJointSourceRoofKanComparison A P

def strictBETotJointSourceRoofPinchedComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (operad A).Algebra)).app (Opposite.op ⦋0⦌)
            (nerveVertex (strictBETotJointRoofSourceObject A P)))
        ((SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (operad A).Algebra)).app (Opposite.op ⦋0⦌)
            (nerveVertex (strictBETotJointRoofTargetObject A P)))

theorem strictBETotJointSourceRoofPinchedComparison_weak (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofPinchedComparison A P)

theorem strictBETotJointSourceRoofPinchedComparison_app_val (P : strictBETotJointHomIndex A) :
    SimplicialLocalization.KanHammockPinchedValueFormula
      (modelRelativeCategory (operad A).Algebra)
      (strictBETotJointRoofSourceObject A P) (strictBETotJointRoofTargetObject A P)
      (strictBETotJointSourceRoofKanComparison A P)
```

## 254. 同じ局所化頂点のpinched Homへの基準射の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

§253の最終個別検査1450は終了0。321の鍵付き対象ビルド12,238 jobs、小監査195モジュール・1,363宣言が成功し、標準三公理のみ。実ハンドル73896・終了0、鍵返却済み。--class impl --wait 3600・1700秒guardを使った。新しい宣言名はmainのSerrePositivity全体にないことをgit grepで確認した。二つの互換入口の宣言0と既存補題の定義元の検査も維持している。

今回二本165行（一般の全単体の値の分割49行、BEの基準射116行）。見込み150〜260行に対し上端との差−95行。検証済み191本・12,403行／外枠22,000行。自分の宣言数は1,356で、互換入口の宣言0を含む。監査全体には既存定義元・HAの直接importer等4本も含む。

元の実roof比較から同じ全モデル相対圏のKan hammock Hom・同じ局所化頂点のpinched Homへの実射と、その弱同値性、元の全標的AsSmall比較と同じEx∞単位の厳密な三角形を保存した。全次数・全単体の値の式は名前付き命題の定義でそのまま保持し、elaborationの分割によって計算上限を上げずに検査した。sorry・独自公理0、[ModelCategory SSet]なし、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainの変更なし。既存の合成・係数移送・証明の分割として一覧の項目数は増やさない。

登録候補：

- SerrePositivity.EInfinity.SimplicialLocalization.KanHammockPinchedSimplexValue
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofPinched

次は既存CoherentLocalizationComparison.pinchedEquivalenceを、元のstrictBETotRightFrameCoherentComparisonの同じ第二成分に適用し、同じ指定二胞体の両端の共役として元のCAlg源へ輸送する。probe始域と右置換標的を元のnative fiberの両端へ合わせること、元のnative射と基準roof射との全単体での照合、R03dの元の固定始域の全FunctorIsoへの正規化はなお残る。

## 255. 同じ指定局所化比較と端点同型によるroof基準射の輸送（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

既存のCoherentLocalizationComparison.pinchedEquivalenceを元のstrictBETotRightFrameCoherentComparisonの同じ第二成分に適用する。比較関手と指定二胞体の両端成分への分解は既存の厳密な等式から得る。さらに元のprobe比較と元の全標的右置換単位を使い、基準roof射の両端を元のモデル源の頂点へ合わせる。新しい比較同値や指定経路は選び直さない。既存の合成・係数移送の法則として項目数は増やさない。二本183行。対象ビルド・監査はこれから実行し、成功前にコードをコミットしない。

これは弱同値である基準射の端点を揃える段であり、元のnative fiber射そのものの弱同値性はまだ主張しない。同じnative射との全単体の照合と元の固定始域の全FunctorIsoへの正規化が残る。

共通入力は `(A : Type u) [CommRing A]`。型は以下のとおり。

#### StrictDiagramTotJointSourceRoofNativePinched（84行）

```lean
def strictBETotJointRoofLocalizationComparison (P : strictBETotJointHomIndex A) :
    FrameHom.CoherentLocalizationComparison
      (SimplicialLocalization.hammockLocalizationNerveMap
        (modelRelativeCategory (operad A).Algebra)) (strictBETotModelSource A)

def strictBETotJointSourceRoofNativePinchedComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (strictBETotJointRoofSourceObject A P)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (strictBETotJointRoofTargetObject A P)))

theorem strictBETotJointSourceRoofNativePinchedComparison_weak (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofNativePinchedComparison A P)

theorem strictBETotJointSourceRoofNativePinchedComparison_normalization
    (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofNativePinchedComparison A P =
      strictBETotJointSourceRoofPinchedComparison A P ≫
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap
          (strictBETotJointRoofLocalizationComparison A P).equivalence.hom _ _ ≫
        (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointEquivalence
          ((strictBETotJointRoofLocalizationComparison A P).triangle.toNatIso.app
            (HomotopyCategory.mk (nerveVertex (strictBETotJointRoofSourceObject A P))))
          ((strictBETotJointRoofLocalizationComparison A P).triangle.toNatIso.app
            (HomotopyCategory.mk (nerveVertex (strictBETotJointRoofTargetObject A P))))).hom
```

#### StrictDiagramTotJointSourceRoofEndpointTransport（99行）

```lean
def strictBETotJointRoofProbeEndpointIso (P : strictBETotJointHomIndex A) :
    VertexIso
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointRoofSourceObject A P)))
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))

theorem strictBETotJointRoofTargetReplacement_vertex (P : strictBETotJointHomIndex A) :
    ((nerveMap (strictBETotTargetReplacement A) ≫ strictBETotModelSource A).app
      (Opposite.op ⦋0⦌)) (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)) =
      (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointRoofTargetObject A P))

def strictBETotJointRoofTargetEndpointUnitIso (P : strictBETotJointHomIndex A) :
    VertexIso
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointRoofTargetObject A P)))

def strictBETotJointSourceRoofNormalizedPinchedComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))

theorem strictBETotJointSourceRoofNormalizedPinchedComparison_weak
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofNormalizedPinchedComparison A P)
```

## 256. 同じ指定比較と端点輸送の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

322の鍵付き対象ビルド12,241 jobsと小監査197モジュール・1,391宣言が成功し、標準三公理のみ。実ハンドル80601・終了0、鍵返却済み。--class impl --wait 3600、1700秒guardを使用。二つの互換入口の宣言0と既存補題の定義元の検査を維持した。二本の新規宣言名はmain EInfinityとのgit grepで重複なし。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainを変更していない。

今回二本183行。検証済み193本・12,586行／外枠22,000行、自分の宣言は1,384。監査には既存定義元等の4モジュールも含む。既存の合成・係数移送の法則で項目数は増やさない。

登録候補：

- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofNativePinched
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofEndpointTransport

元のnative fiber射との全単体の比較と、その実射の弱同値性はなお残る。次は元のnative Hom入力の頂点を元のモデル源の二頂点と厳密に合わせ、twisted-arrow fiberの比較の両端を明示する。

## 257. 同じnative入力の端点と既存twisted・pinched比較の単位則（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

元の固定始域則を零単体へ評価して、元のnative Hom入力が元の二つのCAlg源の頂点の対であることを示す。nerveMapの頂点、直積の射影則、零次の定値則を型を分けて適用する。一般のtwisted Homからpinched Homへの比較は、既存のcoslice比較の同じ指定逆とcosliceの右写像空間比較の合成とする。反転したtwisted Homは同じedgewise二射影の同じ指定逆で戻す。元のcoslice・edgewise比較との二つの単位三角形は全FunctorIsoとして保持する。既存比較の合成・単位・係数移送の法則であり、新しい数学の項目は足さない。見込み二本150〜220行。対象ビルド・監査の前にはコードをコミットしない。

既存RoofPrefixFamilyTriangle.native_family_eq_roof_arrowは一般の同じ宇宙の相対圏で、全roof族の区間評価を同じaugmentationの逆と評価の合成と同定する。両端のbifibrancyを追加せず使える。この全族則を、同じfiber要素圏へ運んだroof族に適用し、元の補正pairingが保存する同じ底のpathと合わせるのが次の接続点。いまの二本だけから元のnative射の弱同値性は結論しない。

BEの共通入力は `(A : Type u) [CommRing A]`。一般版は `{C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌)`。

#### StrictDiagramTotJointHomInputVertex（73行）

```lean
theorem strictBETotJointNativeHomInput_vertex (P : strictBETotJointHomIndex A) :
    (strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P) =
      (SSet.opObjEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (AsSmall.down.obj P).1.unop)),
       (algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (AsSmall.down.obj P).2))

theorem strictBETotJointNativeHomInput_model_vertex (P : strictBETotJointHomIndex A) :
    (strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P) =
      (SSet.opObjEquiv.symm ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject
          (operad A).Algebra (AsSmall.down.obj P).1.unop))),
       (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject
          (operad A).Algebra (AsSmall.down.obj P).2)))
```

#### TwistedHomPinchedComparison（73行）

```lean
def twistedArrowHomPinchedEquivalence :
    QCatEquivalence (twistedArrowHomSpace x y) (Basic.pinchedHom x y)

def twistedArrowHomOppositePinchedEquivalence :
    QCatEquivalence (twistedArrowHomSpace x y).op (Basic.pinchedHom x y)

theorem twistedArrowHomOppositePinchedEquivalence_hom :
    (twistedArrowHomOppositePinchedEquivalence x y).hom =
      (isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
      edgewiseRight (twistedArrowHomSpace x y) ≫
      (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
      (cosliceFiberRightMappingEquivalence x y).hom

def twistedArrowHomPinchedEquivalence_coslice :
    FunctorIso (cosliceTwistedHomMap x y ≫ (twistedArrowHomPinchedEquivalence x y).hom)
      (cosliceFiberRightMappingEquivalence x y).hom

def twistedArrowHomOppositePinchedEquivalence_edgewise :
    FunctorIso
      (edgewiseLeft (twistedArrowHomSpace x y) ≫
        (twistedArrowHomOppositePinchedEquivalence x y).hom)
      (edgewiseRight (twistedArrowHomSpace x y) ≫
        (twistedArrowHomPinchedEquivalence x y).hom)
```

## 258. 元のnative実射を元のroofと同じpinched Homへ運ぶ（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

§257の端点の等式で元のnative twisted fiberの反転を元の両端のtwisted Homに合わせ、§257の一般比較を合成する。その同値に元のstrictBETotJointSourceNativeOppositeFiberMapを合成した実射を定義する。新しい弱同値性の前提を置かず、この実射の弱同値性と元のstrictBETotJointSourceNativeFiberMapの弱同値性が同値であることを、既存の反転則と比較の弱同値性の消去則で示す。見込み80〜130行に対し81行の下書き。既存の合成・係数移送・消去則の分割で、項目数は増やさない。

個別の一時結合検査26130は終了0。対象ビルド・小監査はまだなのでコミットしない。323は端点のモデル源表示に既存BEのモデル構造をlocal instanceで明示する前のソースを読み、失敗した。固有名のlocal instanceを追加し、元のジョブの終了を確認して324を一枚の整理券で実行中。計算上限は変更していない。

共通入力は `(A : Type u) [CommRing A]`。

#### StrictDiagramTotJointSourceNativePinched（81行）

```lean
def strictBETotJointNativeFiberPinchedEquivalence (P : strictBETotJointHomIndex A) :
    QCatEquivalence
      (vertexFiber (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P))).op
      (Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))))

def strictBETotJointSourceNativePinchedMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))

theorem strictBETotJointSourceNativePinchedMap_weak_iff_original
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceNativePinchedMap A P) ↔
      IsWeakHomotopyEquivalence (strictBETotJointSourceNativeFiberMap A P)
```

この実射とstrictBETotJointSourceRoofNormalizedPinchedComparisonは同じ始域・標的を持つ。残る中核は、元の補正pairingの指定された底のpathと、元のroof全族のaugmentationを、全パラメータの区間評価で照合すること。既存intervalFamilyHom_eq_imp_homotopyは任意のパラメータに対してこの全評価の等式からホモトピーを与えるので、π₀のみへの弱化を避けられる。現時点ではその等式を示していない。

## 259. 元のnative射を同じpinched標的へ運ぶ既存則の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

324の対象ビルド10,628 jobs・小監査199モジュール1,409宣言が成功（実ハンドル31286・終了0）。325は元のnative実射の対象ビルド12,248 jobs・小監査200モジュール1,418宣言が成功（実ハンドル30857・終了0）。いずれも標準三公理のみ、鍵返却済み。--class impl --wait 3600、1700秒guardで各一枚の整理券を使い、前のジョブの終了を確認して次へ進めた。既存補題の定義元と二つの互換入口の宣言0の検査も維持。今回の全新規宣言名についてmain SerrePositivity全体とのgit grepで重複がないことを確認した。

今回三本229行（端点75、一般比較と全単位三角形73、同じnative実射81）。前二本の見込み150〜220行に対し148行、第三の見込み80〜130行に対し81行。検証済み196本・12,815行／外枠22,000行、自分の宣言は1,411。sorry・独自公理0、計算上限変更なし、[ModelCategory SSet]なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainを変更していない。

登録候補：

- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointHomInputVertex
- SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomPinchedComparison
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativePinched

元の実射と基準roof射の始域・標的が揃い、元の実射の弱同値性を厳密に反映する比較まで検証した。両実射の全族の同定自体は未証明であり、R03d・3b-4aの完了とはしない。次の最小の主張は、両実射を区間写像空間へ送ったintervalFamilyHomの等式。既存RoofPrefixFamilyTriangleの全roof族の式と、元の補正pairingの同じ底のpathとの照合が必要である。

## 260. R03dの同じ実射の全族照合をR03hとして追加（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03hは未完了。

§19の「同じまとまり・一つの見込み1,500行以下」の枠により、元のnative実射と元のroof基準射の全族の照合をR03hとして追加する。新しいまとまりではなくR03dの元のfiber射自身の弱同値性と固定始域の全比較の正規化に必要な中間の定理。⑤aの欄の型を変えない。型を弱めず、追加の弱同値性・充填性を前提にしない。

型（共通入力 `(A : Type u) [CommRing A]`、`intervalFamilyHom`はKerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories、`pinchedHomToIntervalMappingSpace`はKerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces）：

```lean
theorem strictBETotJointSourceNativePinchedMap_interval_family
    (P : strictBETotJointHomIndex A) :
    intervalFamilyHom
      (strictBETotJointSourceNativePinchedMap A P ≫
        pinchedHomToIntervalMappingSpace _ _) =
    intervalFamilyHom
      (strictBETotJointSourceRoofNormalizedPinchedComparison A P ≫
        pinchedHomToIntervalMappingSpace _ _)
```

この全称命題を/private/tmp/isw2-nativepinched-family-type.leanで#checkし、実ハンドル67282・終了0。これは型の検査であり証明ではない。Lean本体に未証明の宣言・sorryを置いていない。

見込み850〜1,400行。内訳：元のfiber要素圏のroof族をRoofPrefixの同じ族へ運ぶ係数・自然性の照合250〜400行、元の補正pairingを同じcoslice・edgewise比較で区間評価し、保存された底のpathを使う全族の照合300〜600行、同じ局所化三角形・probe・右置換単位での共役と既存roof全族則の合成150〜250行、まとめ150行以内。未確定の中心は二番目であり、1,500行を超える新しい中間定理やまとまりの外のものが要ると分かった場合は、§19どおり検証済みを保存して報告する。

使用する既存の入口：RoofPrefixFamilyTriangle.native_family_eq_roof_arrow（一般の同じ宇宙の相対圏での全roof族）、CoherentLocalizationComparison.pinchedEquivalence_homとtriangle_naturality、pinchedEndpointEquivalence_family、今回のtwistedArrowHomPinchedEquivalence_cosliceとtwistedArrowHomOppositePinchedEquivalence_edgewise、元のstrictBETotJointSourceFiberPairingIso_postcomp（同じ底のpathの保存）。全族の評価の等式を得た後はintervalFamilyHom_eq_imp_homotopyとpinched・区間比較の弱同値性で、元の実射自身の弱同値性に戻す。以降も元の固定始域の全FunctorIsoへの正規化を省かない。

§255〜256のコードは3693013ba、§257〜259のコードは7edd92b76に保存済み。検証済み196本・12,815行／外枠22,000行。停止点3b-4aの完成報告ではない。

## 261. B4′の取り込み前採取を開始（11-15、途中）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03hは未完了。B4′もまだ完了ではない。

検証済みLeanは670ef9d75までの履歴に保存済み。B4′開始時の作業木はクリーン。基準391b2a0d2から追加・変更されたLean（drafts除外、存在するソース）は197本。原ソースを/private/tmp/isw2-b4prime-20261115/original-sources.tar.gz、一覧を同ディレクトリfiles.json、元HEADとmainの記録をprovenance.jsonへ保存した。元HEADは670ef9d75、開始時mainはb29addabd。公式指示はmainのcitation-attributes.md §15とbulk-b3prime/B4/README.mdを読んだ。

最初の三本と次の八本、計11本のcollectと指定rewrite.pyによるプレビューが成功。確認済みのreview.jsonは全て空、追加import0、現ソースとの差分0本。自分の検証済み196モジュールのパスにはmodule-map.jsonとの一致0。これは残りの短名束縛の確認の代用にはせず、残りも採取する。

残りは8本以下ずつの組で採取・プレビューする単一の実行ハンドル41644へまとめた。各組で--class impl --wait 3600、鍵取得後280秒guard。前の組の終了・鍵返却の後に次の組を一度だけ出し、失敗や保留で停止する。複数の整理券を同時に出さず、同じ採取の時間切れを取り直すループも使わない。現在は第2組を実行中。mainのmerge・プレビュー反映・取り込み後の対象ビルドと小監査はまだ。古い索引を取り込み後のソースへ流用しない。

R03hの並行する紙と一時検査：元のfiber上の同じroof図式・augmentation・評価、同じ全単体の二列図式、元のAsSmall比較を通した実roof比較とRoofPrefix.familyMapの厳密な等式を一時ファイル/private/tmp/isw2-rooffiberprefix.leanで検査し、ハンドル47381・終了0。既存依存RoofPrefixColumnRoofの326対象ビルド7,211 jobsも成功（ハンドル57972・終了0）。新規本体モジュールを追加・コミットした検収ではないため、検証済み196本・12,815行の数は増やさない。B4′の参照採取中の原ソースも変更していない。B4′完了後にこの同じ型の法則を本体で検査し直し、元のnative pairingが保存する指定された底のpathとの全族照合へ戻る。

## 262. B4′採取19本の検収と、取り込み取り消しに由来する削除の事前確認（11-15、途中）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03h・B4′は未完了。

第2組の8本もcollect・プレビュー成功。19／197本が保留0・追加import0・差分0。第2組は待ち込み660.1秒で成功し鍵を返却した。採取そのものの実測は8本で約2分なので、以降は12本以下の約3〜4分の組、280秒guardを維持する形へまとめ直した。178本を15組へ分け、既済19本との重複・漏れがないことを集合で検査した。

切り替え時には、完了した第2組の次の第3組がまだ鍵待ちで、子のpayloadが起動していないことをpsで確認した。待ちのwrapper96924にだけSIGTERMを送り、既存のsignal handler・finallyによる整理券の片付けを経て、旧runner41644が終了143になった。採取の失敗や時間切れではなく、未起動の待ちだけの意図した取り消しである。その終了を確認してから、新しい単一runner38504を起動した。同時に複数の整理券は出していない。新しい進捗は/private/tmp/isw2-b4prime-20261115/progress-12.json、before-rXX・preview-rXXに記録する。新しい実行も各組一回ずつで、保留や失敗で停止する。mainはまだmergeしていない。

作業木を変えないgit merge-treeの事前確認では、共通祖先57705f223からmain側の取り込み取り消しedf81f92eが効くため、検証済みの自分の176本が削除扱いになった。対象一覧は/private/tmp/isw2-b4prime-20261115/merge-preview-absent-own-files.json。重複修正済みのStrictDiagramTotUniversalProbePointComparison・TensorConeUnitPointとモジュール一覧はmodify/delete、報告は内容競合の候補。最終のmergeでは、取り消しの目的だった重複が既に修正されている元の自分のソースを、検査済みプレビューから保持する必要がある。B3′で移動した別の本体ソース全体へ上書きせず、今回の197本と宣言の所有元表・module-mapに従う。公式入口や監査の取り消された登録は勝手に戻さず、調整役への登録候補に残す。mainの独立した変更は保持する。

鍵待ち中の一時検査では、同じ実roof全族の任意の後合成を、元の全augmentationの逆と評価の像へ戻す式まで検査できた（/private/tmp/isw2-rooffibercolumn.lean、199行、ハンドル26704・終了0）。同じ全FunctorIsoの定値族が元の指定成分に一致する法則も、既存の未ビルドの評価補題を一時結合して検査した（/private/tmp/isw2-constantisofamily-combined.lean、ハンドル53401・終了0）。どちらもプロジェクトのソースは変更しておらず、B4′後の本体の対象ビルド・小監査はまだ。検証済み196本・12,815行の数は維持する。

## 263. B4′採取55本と、同じ全augmentationの一時照合（11-15、途中）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03h・B4′は未完了。

B4′は55／197本の参照採取・プレビューが成功。全てreview.jsonは空、追加import0、原ソースとの差分0本。12本の組r00・r01・r02も280秒guardの範囲内で成功した（待ちを含む経過748.5秒・759.6秒・483.6秒）。同じ単一runner38504を継続し、これから第r03組。mainの実際のmergeはまだ行っていない。

取り込み前の全索引とプレビューをまとめる/private/tmp/isw2-b4prime-20261115/assemble-before.pyを準備した。全197本が重複・欠落なく揃い、全captureのsourceが現原ソースと一致することを検査してから、before-allと新しいpreview-allを作る。MERGE_HEADがあるとき、またはmain取り込み後には動かせないガードを置き、旧索引を取り込み後のソースへ流用しない。事前mergeで消える176本については、全てがedf81f92eの削除対象に含まれることもgit diff-treeと照合した。

R03hの一時検査では、同じroof図式・同じ全単体の二列図式・元のroof比較とRoofPrefix全族の一致・任意の後合成の全roof公式に続き、同じfull augmentationが元の全パラメータのaugmentation自身の引き戻しであることまで検査した。最初の全関手の照合は200,000 heartbeatに達したため上限を変えず、対象・射・一般のfiber包含の単体作用素の法則へ分割した。後者の等式輸送はGrothendieck.ιの元のeqToHomを射影して処理し、別の包含や別のpathに替えていない。最終/private/tmp/isw2-roofparameter2.lean（355行、一時入力全体）は実ハンドル3044・終了0。一般のfiber作用素の独立検査36768も終了0。

同じ元のnerveTransformationPostIsoの順射を元の全自然変換のNerveColumn.homへ戻す法則も/private/tmp/isw2-nervepostisocolumn.leanで検査し、実ハンドル80148・終了0。定値族の法則の検査53401も終了0。全て一時ファイルの個別検査で、プロジェクトには追加・変更していない。検証済み196本・12,815行／外枠22,000行の計数は維持。本体モジュールへの配置と対象ビルド・小監査はB4′後に行う。

以下は通過した一時の型（名称は本体反映時に新規宣言名との重複を確認する）。BE側の共通入力は `(A : Type u) [CommRing A]`、canonicalな既存modelCategory AとmappingCofibrantFactorization Aのlocal instanceのみを使う。既存構成の合成・単位・係数移送・証明分割の法則として一覧の項目数は増やさない。元のnative射とroof射の全族の等式、すなわちR03hそのものはなお未証明。

```lean
abbrev strictBETotJointRoofResolution (P : strictBETotJointHomIndex A)

def strictBETotJointSourceRoofFrameDiagram (P : strictBETotJointHomIndex A) :
    ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⥤
      (modelRelativeCategory (operad A).Algebra).category

def strictBETotJointSourceRoofFrameAugmentation (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra
          (framedLimitProbe A (AsSmall.down.obj P).1.unop))

def strictBETotJointSourceRoofFrameEvaluation (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra
          ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))

lemma strictBETotJointSourceRoofFrameAugmentation_weak
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (modelRelativeCategory (operad A).Algebra).weakEquivalences
      ((strictBETotJointSourceRoofFrameAugmentation A P).app s)

lemma strictBETotJointSourceRoofFrameDiagram_weak
    (P : strictBETotJointHomIndex A)
    {s t : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ}
    (f : s ⟶ t) :
    (modelRelativeCategory (operad A).Algebra).weakEquivalences
      ((strictBETotJointSourceRoofFrameDiagram A P).map f)

def strictBETotJointSourceRoofFrameZigzag (P : strictBETotJointHomIndex A)

theorem strictBETotJointSourceRoofFrameZigzag_nerve
    (P : strictBETotJointHomIndex A) :
    (elementsOppositeUniverseNerveIso.{u+1,u}
      ((SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
        (strictBETotJointRoofResolution A P).obj).obj
          ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))).hom ≫
      FrameHom.frameLeftRoofNerveMap (weakEquivalences (operad A).Algebra)
        (strictBETotJointRoofResolution A P).obj
        (strictBETotJointRoofResolution A P).augmentation
        (strictBETotJointRoofResolution A P).augmentation_weakEquivalence
        (fun f => (strictBETotJointRoofResolution A P).homotopicallyConstant f) ≫
      (Hammock.AsSmallComparison.graphIso (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
        LeftRoof.word).hom =
      nerveMap (strictBETotJointSourceRoofFrameZigzag A P)

theorem strictBETotJointSourceRoofKanComparison_prefix
    (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofKanComparison A P =
      SimplicialLocalization.RoofPrefix.familyMap
        (modelRelativeCategory (operad A).Algebra)
        (strictBETotJointSourceRoofFrameDiagram A P)
        (strictBETotJointSourceRoofFrameAugmentation A P)
        (strictBETotJointSourceRoofFrameAugmentation_weak A P)
        (strictBETotJointSourceRoofFrameEvaluation A P)
        (strictBETotJointSourceRoofFrameDiagram_weak A P)

theorem strictBETotJointSourceRoofPinchedComparison_column_roof
    {E : SSet.{u+1}} [Quasicategory E] (P : strictBETotJointHomIndex A)
    (F : SimplicialLocalization.kanHammockNerve
      (modelRelativeCategory (operad A).Algebra) ⟶ E) :
    let R := modelRelativeCategory (operad A).Algebra
    let V := strictBETotJointSourceRoofFrameDiagram A P
    let p := strictBETotJointSourceRoofFrameAugmentation A P
    let hp := strictBETotJointSourceRoofFrameAugmentation_weak A P
    Arrow.mk
      (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom
        ((strictBETotJointSourceRoofPinchedComparison A P ≫
          SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F _ _) ≫
          SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk
      ((FrameHom.NerveColumn.augmentationIso
        (SimplicialLocalization.hammockLocalizationNerveMap R ≫ F) V p
        (SimplicialLocalization.RoofPrefix.postcomp_augmentation_invertible R V p hp F)).inv ≫
        FrameHom.NerveColumn.hom
          (SimplicialLocalization.hammockLocalizationNerveMap R ≫ F)
          (strictBETotJointSourceRoofFrameEvaluation A P))

def strictBETotJointSourceRoofFullAugmentation (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra (AsSmall.down.obj P).1.unop)

theorem strictBETotJointSourceRoofFullAugmentation_app
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (strictBETotJointSourceRoofFullAugmentation A P).app s =
      (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
        ((strictBETotJointRoofResolution A P).augmentation.app s.unop.obj.unop ≫
          framedLimitProbeComparison A (AsSmall.down.obj P).1.unop)

theorem strictBETotJointSourceRoofFullAugmentation_original
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (strictBETotJointSourceRoofFullAugmentation A P).app s =
      (strictBETotJointSourceFrameAugmentation A).app
        ((AsSmall.up : (operad A).Algebra × SimplexCategory ⥤
          strictBETotJointSourceFrameIndex A).obj
            ((AsSmall.down.obj P).1.unop, s.unop.obj.unop))

theorem strictBETotJointSourceRoofFullAugmentation_weak
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (modelRelativeCategory (operad A).Algebra).weakEquivalences
      ((strictBETotJointSourceRoofFullAugmentation A P).app s)

def strictBETotJointRoofParameterIndex (P : strictBETotJointHomIndex A) :
    ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⥤
      strictBETotJointSourceFrameIndex A

theorem strictBETotJointRoofParameterIndex_obj (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (strictBETotJointRoofParameterIndex A P).obj s =
      (AsSmall.up : (operad A).Algebra × SimplexCategory ⥤ strictBETotJointSourceFrameIndex A).obj
        ((AsSmall.down.obj P).1.unop, s.unop.obj.unop)

lemma sameSimplicialElementsFiberFunctor_degree {I : Type u} [SmallCategory I]
    (G : I ⥤ SSet.{u}) (i : I)
    {s t : (simplicialElementsCatDiagram G).obj i} (f : s ⟶ t) :
    ((simplicialElementsFiberFunctor G i).map f).hom.2 = f.down.hom

theorem strictBETotJointRoofParameterIndex_map (P : strictBETotJointHomIndex A)
    {s t : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ}
    (f : s ⟶ t) :
    HEq ((strictBETotJointRoofParameterIndex A P).map f)
      ((AsSmall.up : (operad A).Algebra × SimplexCategory ⥤ strictBETotJointSourceFrameIndex A).map
        ((𝟙 (AsSmall.down.obj P).1.unop, f.unop.down.hom.unop) :
          ((AsSmall.down.obj P).1.unop, s.unop.obj.unop) ⟶
            ((AsSmall.down.obj P).1.unop, t.unop.obj.unop)))

theorem strictBETotJointRoofParameterIndex_evaluation (P : strictBETotJointHomIndex A) :
    strictBETotJointRoofParameterIndex A P ⋙ strictBETotJointSourceFrameEvaluation A =
      strictBETotJointSourceRoofFrameDiagram A P

theorem strictBETotJointRoofParameterIndex_constant (P : strictBETotJointHomIndex A) :
    strictBETotJointRoofParameterIndex A P ⋙ strictBETotJointSourceFrameConstant A =
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra (AsSmall.down.obj P).1.unop)

theorem strictBETotJointRoofParameterIndex_augmentation
    (P : strictBETotJointHomIndex A) :
    HEq (CategoryTheory.Functor.whiskerLeft (strictBETotJointRoofParameterIndex A P)
      (strictBETotJointSourceFrameAugmentation A))
      (strictBETotJointSourceRoofFullAugmentation A P)

private theorem sameFunctor_map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {x y x' y' : C} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (h : HEq f g) : HEq (F.map f) (F.map g)

private theorem sameNatTrans_heq {I C : Type*} [Category I] [Category C]
    {F G F' G' : I ⥤ C} (hF : F = F') (hG : G = G')
    (η : F ⟶ G) (η' : F' ⟶ G')
    (ha : ∀ i, HEq (η.app i) (η'.app i)) : HEq η η'
```

定値族の法則（一般の準圏K・X、任意のT）と元の全augmentation同型の順射の法則：

```lean
lemma sameFunctorIso_constant_family {K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    (T : SSet.{u}) {f g : K ⟶ X} (e : FunctorIso f g) (x : K _⦋0⦌) :
    (constantFunctorCompIso T x f).inv ≫
      (e.precomp (SSet.const x : T ⟶ K)).hom ≫
      (constantFunctorCompIso T x g).hom =
        constantFunctorHomMap T (e.app x).hom

lemma sameNerveTransformationPostIso_column
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F G : I ⥤ C} (η : F ⟶ G) {Q : SSet.{u}} [Quasicategory Q]
    (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    (nerveTransformationPostIso η L hη).hom = NerveColumn.hom L η
```

## 264. B4′採取67本と、元の指定augmentation同型の全制限の一時検査（11-15、途中）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03h・B4′は未完了。

B4′は67／197本のcollect・プレビューが成功し、review.jsonは全て空、追加import0、原ソースとの差分0本。r03は待ちを含め720.4秒で成功した。単一runner38504は第r04組を継続中。mainの実際のmerge、プレビュー反映、取り込み後の対象ビルド・小監査はまだ。取り込み前のソースは変えていない。

R03hの一時検査を、元の指定された全augmentationのFunctorIso自身の制限まで進めた。一般のnerve自然変換の全引き戻しが同じ反転同型を保つこと、全自然変換の表示変更がその同型を保つことを先に示し、元のstrictBETotJointSourceFrameAugmentationIsoを同じroofパラメータへ前合成した値が、同じfull augmentationのNerveColumn.augmentationIsoそのものであることをHEqで示した。対象ごとの同型へ置き換えず、同じ全関手同型の値を保存する。

/private/tmp/isw2-nervecolumnprecomp.leanはハンドル61860・終了0、一般の表示変更を含む/private/tmp/isw2-nervepostisoheq.leanは77461・終了0、BEの全制限を結合した/private/tmp/isw2-roofnativeaug.leanは45906・終了0。同じfiber上の全標的入力が元の同じ標的の定値図式・定値nerve写像であることも/private/tmp/isw2-rooftarget.leanで検査し94919・終了0。これらも一時検査だけで本体には未反映。元のnative射と基準roof射の全族の等式（R03h）と、元の固定始域の全FunctorIsoへの正規化は引き続き残る。検証済み196本・12,815行／外枠22,000行の計数は維持する。

使用する取り込み後の小監査の範囲も確認した。現在のAuditISW2BKCells325.leanは自分のモジュール一覧196本を全て含み、追加の既存4本（FrameConeClasses・NormalizedMooreReverseEvaluation・NormalizedMooreReverseExtendZero・NormalizedMooreReverseZero）と合わせて200本である。二つの互換入口の宣言0と既存補題の定義元の検査を維持する。新しい本体の証明分割を反映する際は、その変更後に改めて対象ビルドと小監査を行う。

追加した一時の型は以下のとおり。既存構成の反転・単位・合成・係数移送の法則と証明分割なので一覧の項目数は増やさない。一般版の共通openはNerveColumn・FunctorIso等の既存の定義元に対応し、BE版の共通入力は `(A : Type u) [CommRing A]` と既存のcanonical model/factorizationのみ。

```lean
lemma sameNerveColumn_whiskerLeft
    {I J C : Type u} [Category.{u} I] [Category.{u} J] [Category.{u} C]
    (R : J ⥤ I) {F G : I ⥤ C} (η : F ⟶ G)
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q) :
    (hoFunctor.map ((MonoidalClosed.pre (nerveMap R)).app Q)).toFunctor.map
      (NerveColumn.hom L η) = NerveColumn.hom L (CategoryTheory.Functor.whiskerLeft R η)

lemma sameNerveTransformationPostIso_precomp
    {I J C : Type u} [Category.{u} I] [Category.{u} J] [Category.{u} C]
    (R : J ⥤ I) {F G : I ⥤ C} (η : F ⟶ G)
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    HEq ((nerveTransformationPostIso η L hη).precomp (nerveMap R))
      (nerveTransformationPostIso (CategoryTheory.Functor.whiskerLeft R η) L
        (fun j => hη (R.obj j)))

lemma sameNerveTransformationPostIso_heq
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F G F' G' : I ⥤ C} (hF : F = F') (hG : G = G')
    (η : F ⟶ G) (η' : F' ⟶ G') (he : HEq η η')
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated)
    (hη' : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η'.app i)).map L).toTruncated) :
    HEq (nerveTransformationPostIso η L hη) (nerveTransformationPostIso η' L hη')

lemma sameNerveTransformationPostIso_augmentation
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    (V : I ⥤ C) {X : C} (p : V ⟶ (CategoryTheory.Functor.const I).obj X)
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)
    (hp : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map L).toTruncated) :
    nerveTransformationPostIso p L hp = NerveColumn.augmentationIso L V p hp

theorem strictBETotJointSourceRoofFullAugmentation_inverted
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    IsInvertibleEdge ((nerve.edgeMk
      ((strictBETotJointSourceRoofFullAugmentation A P).app s)).map
      (strictBETotModelSource A)).toTruncated

theorem strictBETotJointSourceFrameAugmentationIso_roof_restriction
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceFrameAugmentationIso A).precomp
      (nerveMap (strictBETotJointRoofParameterIndex A P)))
      (FrameHom.NerveColumn.augmentationIso (strictBETotModelSource A)
        (strictBETotJointSourceRoofFrameDiagram A P)
        (strictBETotJointSourceRoofFullAugmentation A P)
        (strictBETotJointSourceRoofFullAugmentation_inverted A P))

lemma sameSimplicialElementsFiberFunctor_projection {I : Type u} [SmallCategory I]
    (G : I ⥤ SSet.{u}) (i : I) :
    simplicialElementsFiberFunctor G i ⋙ simplicialTotalElementsProjection G =
      (CategoryTheory.Functor.const _).obj i

theorem strictBETotJointSourceTargetIndex_fiber (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
      strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A =
    (CategoryTheory.Functor.const _).obj ((strictBETotJointHomTargetIndex A).obj P)

theorem strictBETotJointSourceTargetIndex_nerve_fiber
    (P : strictBETotJointHomIndex A) :
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A) =
    SSet.const (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))

```

## 265. B4′ の採取の組の調整と、元の同じ標的置換の全制限則（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 265.1 B4′ の現況

採取・プレビュー済みは 91／197 ファイル、各 review は空。12 本の組の鍵の実保持は直近で約134〜144秒だったため、未開始の r06 の整理券だけを取り下げ、残り106本を最大20本の6組（s00〜s05）にした。一回の実処理は引き続き gtimeout 280秒、待ちは --class impl --wait 3600、一枚だけ。旧 runner の143はこの未開始の取り下げの終了値で、採取や証明の検証失敗ではない。完了済み91本の索引は保持する。現在の runner は run-remaining-20.py、状況は progress-20.json。197本の全採取後に同じ元ソースから最終の preview-all を作り、それから main を取り込む。元の Lean ソースは変更していない。

### 265.2 同じ元の標的置換を、全関手同型として制限する

B4′ の待ち時間に、一時 Lean ファイルだけで次の既存構成の制限・単位の法則を確認した。元の全標的置換の逆を、同じ fiber 上で同じ標的頂点へ引き戻す全 FunctorIso として同定し、その hom を元の頂点成分の逆の定値族へ同定する。点ごとの同型の存在への置き換えはしていない。依存型の書換えは前合成則と HEq の合成に分け、計算上限は変更していない。

個別検査：isw2-rooftargetiso.lean（最終ログ rooftargetiso4、exit 0）、isw2-rooftargetconstant.lean（最終ログ rooftargetconstant2、exit 0）。既存の未ビルドの共通補題のソースを一時的に結合して検査したもので、本体の新規モジュールの対象ビルド・監査ではない。B4′ 完了後に共通の既存モジュールを import し、新規の法則だけを本体に分割して対象ビルドと小監査を行う。

R03h の本体、すなわち同じ corrected pairing の native fiber 射と元の roof の全 interval 族との等式はまだ残る。今回の二法則を R03h の完了とは数えない。

```lean
theorem strictBETotJointSourceTargetReplacementIso_fiber
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceTargetReplacementIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      (((strictBETotTargetReplacementNativeIso A).precomp
        (SSet.const (X := nerve ((simplicialElementsCatDiagram
          (strictBETotJointSourceCoefficients A)).obj P))
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))))).symm

theorem strictBETotTargetReplacementNativeIso_symm_constant_family
    (P : strictBETotJointHomIndex A) :
    (constantFunctorCompIso
      (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
      (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
      (nerveMap (strictBETotTargetReplacement A) ≫ strictBETotModelSource A)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (strictBETotTargetReplacementNativeIso A).symm
        (SSet.const (X := nerve ((simplicialElementsCatDiagram
          (strictBETotJointSourceCoefficients A)).obj P))
            (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))).hom ≫
      (constantFunctorCompIso
        (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
        (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
        (strictBETotModelSource A)).hom =
      constantFunctorHomMap
        (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
        ((strictBETotTargetReplacementNativeIso A).app
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))).inv
```

## 266. B4′ の151本までの照合と、同じ全関手同型の反転・制限則（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 266.1 B4′

現在の採取・プレビュー済みは 151／197。完了した各組の review は空、元のソースとの差分は0。各 compiler capture の source と元ファイルのバイト列も照合した。670ef9d75 以降の枝のコミットに Lean の変更はない。s02 までの採取を終え、同じ runner が s03 の一枚の整理券で継続中（--class impl --wait 3600、実処理280秒）。main の取り込みはまだ行っていない。残りの全採取、同じ原環境での最終プレビューの後に統合する。

取り込み後の検査の準備は、自レーン196本と既存の直接の確認対象4本（FrameConeClasses、NormalizedMooreReverseEvaluation、NormalizedMooreReverseExtendZero、NormalizedMooreReverseZero）の計200本。小監査も同じ200本を対象とし、互換用の二ファイルの宣言数0、および tensorFrameHomIso_point と normalizedMooreReverse_zero_inclusion の元の定義元を確認する。root や公式の監査は変更・実行しない。main 側の revert に由来する自レーンの削除を保持して統合する理由と対象は §262 のとおりで、統合直前に再照合する。

### 266.2 既存の反転と前合成の法則

isw2-opisoprecomp.lean（84行、一時ファイル）を lake env lean で検査し、最終ログ isw2-opisoprecomp13 は exit 0。元の FunctorIso.op の値を、同じ内部 Hom の反転同型による元の像へ端点だけ輸送したものとして同定した。逆射を既存の functorOppositeHomEquiv と合わせ、その既存の前合成則から、同じ全関手同型の反転と制限の両立を HEq で得た。単体ごとの、または点ごとの同型の存在への置き換えではない。

端点の Eq.mp の簡約と同型の共役式を別の小補題に分けた。計算上限は上げていない。以下は既存構成の輸送・前合成の法則とその証明の分割であり、一覧の新しい数学の項目には数えない。B4′ の元のソースには追加しておらず、追従後に本体の新規モジュールへ分けて対象ビルドと小監査を通す。R03h の同じ native 射と roof の全 interval 族の最終等式は未完である。

```lean
private lemma sameEqMp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (b : γ) :
    HEq (Eq.mp h a) b ↔ HEq a b

lemma sameVertexIso_op_inv {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : VertexIso x y) :
    e.op.inv = homotopyCategoryOpHomEquiv x y e.hom

lemma sameFunctorIso_op_heq {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    HEq e.op (VertexIso.map (VertexIso.op e)
      (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom)

lemma sameVertexIso_conjugate_heq {Z : SSet.{u}} {a b a' b' : Z _⦋0⦌}
    (e : VertexIso a b) (ha : a = a') (hb : b = b') :
    HEq ((eqToIso (congrArg HomotopyCategory.mk ha)).symm ≪≫ e ≪≫
        eqToIso (congrArg HomotopyCategory.mk hb)) e

lemma sameFunctorIso_op_conjugate {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    e.op = (eqToIso (congrArg HomotopyCategory.mk
      (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex f))).symm ≪≫
      VertexIso.map (VertexIso.op e)
        (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex g))

lemma sameFunctorIso_op_inv {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    e.op.inv = functorOppositeHomEquiv f g e.hom

lemma sameFunctorIso_precomp_inv {A X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (p : A ⟶ X) :
    (e.precomp p).inv = (SSet.mapHomotopyCategory ((pre p).app Y)).map e.inv

lemma sameFunctorIso_op_precomp {A X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) (p : A ⟶ X) :
    HEq (e.precomp p).op (e.op.precomp (SSet.opFunctor.map p))
```

## 267. B4′ の191本までの確認と、同じnative augmentationのroofへの制限（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 267.1 B4′

採取とプレビューは 191／197。完了分の review は空、プレビューと元ソースのバイト列の差分は0。最後の s05（6本）を同じ一枚の整理券で継続中。実処理の上限280秒、--class impl --wait 3600を維持している。main はまだ取り込んでいない。統合直前の merge-tree も再確認した（main 58d6a0de9）。予覧で欠ける自レーン176本は全て以前の revert edf81f92e の削除であり、二つの修正済みLeanのmodify/delete、一覧JSON、報告の競合も前回と同じ。main の報告への独立した追記は0。B3′の新配置の変更を保持し、この自レーンの検証済みソースを落とさずに統合する。

### 267.2 元のnative側の全同型を同じroofへ合わせる法則

一時ファイル isw2-nerveleftop.lean と isw2-roofopaugmentation.lean を lake env lean で検査した。最終ログ nerveleftop と roofopaugmentation2 はともに exit 0。後者は検査用に既存の定義・以前の検証済み補題を結合した 821 行で、新しいnative側の部分は 118 行。これは本体の対象ビルドや監査の代用ではない。原環境のLeanソースには変更を入れておらず、本体へ分けた後に対象ビルドと小監査を行う。

元のfiberの反変入力を、同じ leftOp パラメータと既存の nerve 反転で表し、元の strictBETotJointSourceAugmentationDomainIso の全値を保持して制限した。§266の反転・前合成の法則と§264の全augmentationの制限則をつなぎ、同じ全 FunctorIso の fiber 制限が、同じroofのaugmentationIsoを反転して同じ入力へ引き戻したものに HEq で一致するところまで確認した。任意に別の同型を選んだり、点ごとの同値で代用していない。

以下は既存構成の反転・制限・端点輸送の法則と証明の分割であり、一覧の新しい数学には数えない。R03h の最終の interval 族の等式、元のnative fiber射自身の弱同値性、R03d は未完である。

```lean
lemma sameNerveLeftOp_input {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ Dᵒᵖ) :
    nerveMap F ≫ (nerveOppositeIso (C := D)).inv =
      (nerveMap (opOp C) ≫ (nerveOppositeIso (C := Cᵒᵖ)).inv) ≫
        SSet.opFunctor.map (nerveMap F.leftOp)

lemma sameFunctorIso_precomp_of_heq {K X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (he : HEq e e') (p : K ⟶ X) : HEq (e.precomp p) (e'.precomp p)

lemma sameFunctorIso_op_of_heq {X Y : SSet.{u}} [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') : HEq e.op e'.op

theorem strictBETotJointSourceAugmentationInput_fiber
    (P : strictBETotJointHomIndex A) :
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      strictBETotJointSourceAugmentationInput A =
    (nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
      (nerveOppositeIso (C := ((simplicialElementsCatDiagram
        (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv) ≫
      SSet.opFunctor.map (nerveMap (strictBETotJointRoofParameterIndex A P))

theorem strictBETotJointSourceAugmentationDomainIso_value :
    HEq (strictBETotJointSourceAugmentationDomainIso A)
      ((strictBETotJointSourceFrameAugmentationIso A).op.precomp
        (strictBETotJointSourceAugmentationInput A))

theorem strictBETotJointSourceAugmentationDomainIso_fiber_value
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceAugmentationDomainIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      ((strictBETotJointSourceFrameAugmentationIso A).op.precomp
        (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
          strictBETotJointSourceAugmentationInput A))

theorem strictBETotJointSourceAugmentationDomainIso_fiber_parameter
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceAugmentationDomainIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      (((strictBETotJointSourceFrameAugmentationIso A).precomp
        (nerveMap (strictBETotJointRoofParameterIndex A P))).op.precomp
          (nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
            (nerveOppositeIso (C := ((simplicialElementsCatDiagram
              (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv))

theorem strictBETotJointSourceAugmentationDomainIso_roof_restriction
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceAugmentationDomainIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      ((FrameHom.NerveColumn.augmentationIso (strictBETotModelSource A)
        (strictBETotJointSourceRoofFrameDiagram A P)
        (strictBETotJointSourceRoofFullAugmentation A P)
        (strictBETotJointSourceRoofFullAugmentation_inverted A P)).op.precomp
          (nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
            (nerveOppositeIso (C := ((simplicialElementsCatDiagram
              (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv))
```

## 268. B4′ 完了：B3′ の追従と重複修正後の統合検証（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 268.1 原環境の採取・プレビュー

基準391b2a0d2より後の自レーンの追加・変更Lean（draftsを除く）197本を、main取り込み前にcompilerで採取した。Leanの元ソースを固定し、各組のcollectは --class impl --wait 3600、実処理は280秒以内、一枚の整理券で順に実行した。元の検証済みコードのHEADは670ef9d75、最終プレビューのHEADは4723dc1ad（この間は報告だけの変更）。採取済みJSONのsourceと実ソースのバイト列を全件照合した。

最後に197本の索引をまとめ、同じ原環境のソースからmainの bulk-b3prime/B4/rewrite.py と namespace-rewrite-map.json・所有元表を使って preview-all を作り直した。結果は保留0、追加import0、書換え0ファイル・0行。openの個別解消を要する保留も0。古い索引で取り込み後のソースを再採取・再書換えする操作は行っていない。証跡は /private/tmp/isw2-b4prime-20261115/ の before-all、preview-all、preview-all-summary.json。

### 268.2 main の統合

main 58d6a0de9 を自レーンへ統合した。統合コミットは **81683a2ab**。以前の57705f223の取り込みを戻したrevert edf81f92eにより、通常のmerge予覧では自レーンの検証済み176本が削除されるため、削除の由来を全件照合して元の検証済みソースを保持した。二つの修正済みLean（StrictDiagramTotUniversalProbePointComparison、TensorConeUnitPoint）のmodify/delete、一覧JSON、報告の計4競合も解消した。main側の報告・一覧への独立した追記は0と確認した。

最終プレビューと統合後の自レーン197本は全件バイト一致。B3′の配置の変更はmainから入り、自レーンの書換えは0ファイル・0行である。登録候補は既存の **formalization-plans/stage-ii/inf-supply-b/is-w2-be-20261114-modules.json（196本）** を使用する。

### 268.3 対象ビルド・小監査・重複照合

共有鍵を --class impl --wait 3600 で一回取り、gtimeout 1700秒の中で200モジュールの対象ビルドと小監査を実行した。200本は自レーン196本に、FrameConeClasses・NormalizedMooreReverseEvaluation・NormalizedMooreReverseExtendZero・NormalizedMooreReverseZeroの既存4本を加えたもの。対象モジュールの一覧は一時ディレクトリの postmerge-targets.json。

- 対象ビルド：成功（依存を含む12,346 jobs）。rootのビルドではない。
- 小監査：/private/tmp/AuditISW2BKCells325.lean、200モジュール・**1,418宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。
- TensorConeUnitPoint・NormalizedMooreReverseZeroは宣言数0。tensorFrameHomIso_pointの定義元はFrameConeClasses、normalizedMooreReverse_zero_inclusionの定義元はNormalizedMooreReverseEvaluationと実環境で確認した。既存の定理を使う修正e0c5190ecを含む状態で成功している。
- 宣言名の照合：自レーンのmanifest群等から562ファイル・1778個の名前を取り、mainのEInfinity/3745ファイル・13373個の名前と照合。異なるファイル間の同名宣言は0、自レーン内部も0。これは名前付きのソース宣言の照合で、上の実環境での監査と分けて記録する。
- 自レーン対象のgit diff --check：通過。

ビルドと監査のログは /private/tmp/isw2-b4prime-20261115/build327.log、統合の検収記録は merge-result.json、重複照合は /private/tmp/isw2-b4prime-20261115/declaration-collision-scan.json。

### 268.4 /goal の続き

B4′は完了。R03hの単位・反転・全augmentation制限の個別検査済みの法則を本体の新規ファイルへ分けて検証し、同じnative fiber射と元のroofの全interval族の照合を続ける。R03dの全関手同型と元の固定始域の同型との照合、3b-4aの残りは未完。点ごとの同値で置き換えず、外枠22,000行と型つき一覧の規則を維持する。

## 269. 同じroof・native augmentationの照合則の本体化と、同じ全変換の射（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 269.1 検収

§263〜267の個別検査済みの法則を本体の新規15モジュールへ分けた。元の同じroofのラベル・全augmentation・標的置換単位を保持したまま、元の全関手同型のfiber制限まで照合する。既存のMapHomotopyCategoryComp・FunctorIsoWhiskerCancellation・FunctorIsoVertexEvaluation等はimportして使い、再定義していない。公開importの不足と名前空間のopenを補い、最終の鍵付き対象ビルド330で確認した。

さらに、既存の全straightening関手で同じ底上の射を写す共通1本と、その値を元のraw/native Homの両変数の全変換にするBE1本を追加した。これはR03dの同じ射の定義の部分であり、元の実射を別の射へ置き換えていない。mの弱同値性を仮定していない。元の単位を保つ延長を後で適用し、可逆性と固定始域の元の指定同型との一致を証明する必要が残る。

コードのコミット：**e879e4d7f**。新規17本（共通6・BE11）、**1,345行・90宣言**。既存のLeanの変更は0。登録候補JSONは is-w2-be-20261114-modules.json の **213本**に更新した。入口と公式監査への登録は調整役の取り込み時の対象。

- 鍵：--class impl --wait 3600、一枚の整理券、実処理gtimeout 1700秒。
- 対象ビルド：新規17本、成功（依存を含む12,266 jobs）。
- 小監査：AuditISW2BKCells330.lean、**217モジュール・1,508宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。二つの互換モジュールの宣言数0と既存定理の定義元の検査も継続して成功。
- 宣言名の照合：main d2354cf40に固定し、自レーン579ファイル・1,829個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build330.log、isw2-validation330.json、isw2-declaration-collision-scan330.json。§268の重複照合の証跡はB4′ディレクトリに固定したコピーへリンクを揃えた。

### 269.2 規模と残り

3b-4の実測は **213モジュール・14,160行・1,501宣言**（小監査の既存確認対象4本はこの実測に含めない）。外枠22,000行まで7,840行。既存構成の単位・反転・制限の法則と証明の分割なので、今回の追加を一覧の新しい数学のIDとしては数えない。

§260のR03hの850〜1,400行という見込みは、前提の法則・照合データだけで15本・1,262行になったため、完成までの総増分の見込みとしては低かった。残る主等式の証明は、同じcorrected pairingの全族を同じroofの全族へ合わせる部分で、見込み450〜850行。前提の実測とこの主等式を合わせるとR03hの一群は1,712〜2,112行程度になる。新しい数学の中間の主張自体が1,500行を超える見込みや、別のまとまりが必要になった場合は§19の条件で報告する。

R03hの最終interval族の等式、同じnative fiber射自身の弱同値性、R03dの全関手同型と元の固定始域の指定同型との一致は未完である。R02・R03・R04・R05、R11・R12のTotの分も引き続き残る。今回の全変換の射を可逆とみなしたり、対象ごとの同値で置き換えたりはしていない。

### 269.3 今回の新しい射の定義の型

以下はR03dの射の定義の分割。§263〜267に記録した法則の型は同じで、今回本体の名前空間へ配置した。privateな端点輸送の補題の型も§263・§266に記録済み。

#### LeftStraighteningDiagramHom

```lean
def leftStraighteningInfinityDiagramHom {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    FunctorHom (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q)
```

#### StrictDiagramTotJointNativeTransformation

```lean
def strictBETotJointSourceNativeTransformation
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom) :
    FunctorHom (strictBETotJointRawHomCoherent A) (strictBETotJointNativeHomCoherent A)
```

### 269.4 新規の登録候補

- `SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIsoWhisker`（120行）
- `SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveLeftOpInput`（31行）
- `SerrePositivity.EInfinity.FrameHom.NerveColumnWhiskering`（102行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofFrame`（108行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofGraph`（76行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofPrefix`（75行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofColumn`（66行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofAugmentation`（75行）
- `SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberFunctorLaws`（41行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofParameter`（136行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofNativeAugmentation`（75行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceTargetFiber`（91行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceOppositeAugmentation`（157行）
- `SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoConstantFamily`（46行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceTargetUnit`（64行）
- `SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHom`（38行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointNativeTransformation`（44行）

## 270. 元の twisted-arrow の三単体の四辺の座標（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 270.1 既存構成の法則の分割

B4′は§268で完了し、§269の検証済み17本も枝に保存済み。/goalの続きとして、元のcorrected pairingの単位を調べるための座標計算を新規1本に分けた。標準三単体の二つの三角形の合成則、既存の同じedgewiseWeightIsoと左右包含・面の式を使う。新しい数学のIDの追加ではなく、既存構成の合成・射影の前提計算である。

同じtwisted-arrowの辺の始点は三単体の内側の辺（1,2）、終点は外側の辺（0,3）。左射影を反転表示から戻すと（0,1）、右射影は（2,3）になる。したがって同じ三単体の合成則を、元のcorrected pairingの代表辺へ適用できる。任意の単体集合についての法則で、[ModelCategory SSet]・Kan性・計算上限の変更はない。

これは元の単位の評価を調べる前提の計算である。R03hの全interval族の等式やR03dの全関手同型はまだ証明していない。個々の頂点での射の等式だけから全変換の一致を結論しない。今後は元の全straightening変換と元の固定始域の同型を、同じ局所化・Yonedaの単位で照合する必要がある。

### 270.2 型

以下は新規ファイルの全13宣言の型。既存の辺・三角形を端点つきで読むdefも含めて記録する。

#### TwistedArrowThreeSimplexCoordinates（183行）

```lean
def twistedSquareStdEdge (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    SSet.Edge (X := (Δ[n] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm i) (stdSimplex.obj₀Equiv.symm j)

def twistedSquareStdTriangle (n : ℕ) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    SSet.Edge.CompStruct (twistedSquareStdEdge n i j hij)
      (twistedSquareStdEdge n j k hjk) (twistedSquareStdEdge n i k (hij.trans hjk))

lemma twistedSquareStd_three_composite :
    HomotopyCategory.homMk (twistedSquareStdEdge.{u} 3 0 1 (by decide)) ≫
      HomotopyCategory.homMk (twistedSquareStdEdge 3 1 2 (by decide)) ≫
        HomotopyCategory.homMk (twistedSquareStdEdge 3 2 3 (by decide)) =
      HomotopyCategory.homMk (twistedSquareStdEdge 3 0 3 (by decide))

lemma twistedSquare_three_composite {C : SSet.{u}} (σ : (Δ[3] : SSet.{u}) ⟶ C) :
    HomotopyCategory.homMk ((twistedSquareStdEdge 3 0 1 (by decide)).map σ) ≫
      HomotopyCategory.homMk ((twistedSquareStdEdge 3 1 2 (by decide)).map σ) ≫
        HomotopyCategory.homMk ((twistedSquareStdEdge 3 2 3 (by decide)).map σ) =
      HomotopyCategory.homMk ((twistedSquareStdEdge 3 0 3 (by decide)).map σ)

lemma twistedSquare_source_order :
    edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (1 : Fin 2)) =
      (stdSimplex.edge 3 1 2 (by decide)).down.toOrderHom

lemma twistedSquare_target_order :
    edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (0 : Fin 2)) =
      (stdSimplex.edge 3 0 3 (by decide)).down.toOrderHom

def twistedSquareThreeSimplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    (Δ[3] : SSet.{u}) ⟶ C

lemma twistedSquare_source_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    (edgewiseWeightIso 0).inv ≫ (TwistedArrow C).δ 1 s =
      stdSimplex.map (stdSimplex.edge 3 1 2 (by decide)).down ≫ twistedSquareThreeSimplex s

lemma twistedSquare_target_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    (edgewiseWeightIso 0).inv ≫ (TwistedArrow C).δ 0 s =
      stdSimplex.map (stdSimplex.edge 3 0 3 (by decide)).down ≫ twistedSquareThreeSimplex s

lemma twistedSquare_left_inclusion :
    (stdSimplex.opIso ⦋1⦌).inv ≫ joinInl (Δ[1] : SSet.{u}).op Δ[1] =
      stdSimplex.map (stdSimplex.edge 3 0 1 (by decide)).down ≫ (edgewiseWeightIso 1).inv

lemma twistedSquare_right_inclusion :
    joinInr (Δ[1] : SSet.{u}).op Δ[1] =
      stdSimplex.map (stdSimplex.edge 3 2 3 (by decide)).down ≫ (edgewiseWeightIso 1).inv

lemma twistedSquare_left_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    SSet.yonedaEquiv.symm (SSet.opObjEquiv ((edgewiseLeft C).app _ s)) =
      stdSimplex.map (stdSimplex.edge 3 0 1 (by decide)).down ≫ twistedSquareThreeSimplex s

lemma twistedSquare_right_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    SSet.yonedaEquiv.symm ((edgewiseRight C).app _ s) =
      stdSimplex.map (stdSimplex.edge 3 2 3 (by decide)).down ≫ twistedSquareThreeSimplex s
```

### 270.3 検証

コードのコミット：**b528ea6a1**。新規1本・183行、型を上に記録した名前付き13宣言（生成された定数を含む実環境26宣言）。既存のLeanの変更は0。

- 鍵：--class impl --wait 3600、一枚の整理券、取得後の処理はgtimeout 1700秒。処理終了とともに返却済み。
- 対象ビルド331：新規1本、成功（依存を含む1,555 jobs）。longLineのスタイル警告のみ。計算上限・linterの設定を上げたり無効にしたりしていない。
- 小監査：AuditISW2BKCells331.lean、218モジュール・**1,534宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。二つの互換モジュールの宣言数0と既存の定理の定義元の検査も成功。
- 宣言名：main d2354cf40に固定し、自レーン580ファイル・1,842個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build331.log、isw2-validation331.json、isw2-declaration-collision-scan331.json。

3b-4の実測は**214モジュール・14,343行・1,527宣言**。外枠22,000行まで7,657行。今回は既存の合成則の分割で、一覧のIDの完了数と追加数は変わらない。登録候補は自レーンのJSONだけに追記し、共通の入口と公式監査は変更していない。

登録候補：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowThreeSimplexCoordinates`。R03h・R03dの未完の範囲は270.1のとおりで、/goalは継続。

## 271. 元の射影の合成則と、元の単位ラベルの pairing の像（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 271.1 既存の構成の法則の分割

§270の座標計算を、実際の左右射影の辺に接続した。twisted-arrowの頂点を同じ重みの逆で元の辺へ戻し、同じ辺の左射影（反転を戻したもの）、始点の辺、右射影の合成は終点の辺になることを証明する。これは任意の単体集合についての既存の合成則で、Kan性や[ModelCategory SSet]を仮定しない。両端の辺の類が可逆で、外側の辺が元の単位の合成なら、内側の辺の類は恒等射になるという相殺則も分けた。

さらに元の全twisted pairingの零単体は元のラベルの実射そのものであることを計算した。その同じ全pairingを元のモデル源へ後合成する値も保持する。BEの元の単位ラベルを全要素圏の同じ次数0の要素として読み、そのnative pairingの像が、元のsource-frame増大写像・probe比較・標的置換単位の同じ合成になることを照合した。新しい単位や逆は選んでいない。

これはR03d/R03hの証明の前提の合成・単位・射影の法則であり、一覧の新しい数学のIDは追加しない。新規3本（共通2・BE1）、312行。各ファイルは200行以下。既存のLeanの変更は0。

### 271.2 型

全17個の名前付きdef/lemmaの型を記録する。BEのlocal instanceは同じmodelCategory AとmappingCofibrantFactorization Aを使う従来の二つ（代数のModelCategoryと、cofibrations/trivialFibrationsの関手的因子分解）で、SSetの模型構造は足さない。

#### TwistedArrowEdgeComposition（170行）

```lean
lemma twistedSquare_composite_of_edge_coordinates {C : SSet.{u}}
    (σ : (Δ[3] : SSet.{u}) ⟶ C)
    {q x y z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x y)
    (r : SSet.Edge y z) (b : SSet.Edge q z)
    (hp : ((twistedSquareStdEdge 3 0 1 (by decide)).map σ).edge = p.edge)
    (ha : ((twistedSquareStdEdge 3 1 2 (by decide)).map σ).edge = a.edge)
    (hr : ((twistedSquareStdEdge 3 2 3 (by decide)).map σ).edge = r.edge)
    (hb : ((twistedSquareStdEdge 3 0 3 (by decide)).map σ).edge = b.edge) :
    HomotopyCategory.homMk p ≫ HomotopyCategory.homMk a ≫
      HomotopyCategory.homMk r = HomotopyCategory.homMk b

lemma twistedSquare_mapped_edge_yoneda {C : SSet.{u}} (σ : (Δ[3] : SSet.{u}) ⟶ C)
    (i j : Fin 4) (h : i ≤ j) :
    SSet.yonedaEquiv.symm (((twistedSquareStdEdge 3 i j h).map σ).edge) =
      stdSimplex.map (stdSimplex.edge.{u} 3 i j h).down ≫ σ

lemma twistedSquare_composite_of_projections {C : SSet.{u}}
    (s : (TwistedArrow C) _⦋1⦌)
    {q x y z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x y)
    (r : SSet.Edge y z) (b : SSet.Edge q z)
    (hp : SSet.opObjEquiv ((edgewiseLeft C).app _ s) = p.edge)
    (ha : (TwistedArrow C).δ 1 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm a.edge)
    (hr : (edgewiseRight C).app _ s = r.edge)
    (hb : (TwistedArrow C).δ 0 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm b.edge) :
    HomotopyCategory.homMk p ≫ HomotopyCategory.homMk a ≫
      HomotopyCategory.homMk r = HomotopyCategory.homMk b

lemma twistedSquare_unit_of_projections {C : SSet.{u}}
    (s : (TwistedArrow C) _⦋1⦌)
    {q x z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x x)
    (r : SSet.Edge x z) (b : SSet.Edge q z)
    [IsIso (HomotopyCategory.homMk p)] [IsIso (HomotopyCategory.homMk r)]
    (hp : SSet.opObjEquiv ((edgewiseLeft C).app _ s) = p.edge)
    (ha : (TwistedArrow C).δ 1 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm a.edge)
    (hr : (edgewiseRight C).app _ s = r.edge)
    (hb : (TwistedArrow C).δ 0 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm b.edge)
    (hu : HomotopyCategory.homMk b = HomotopyCategory.homMk p ≫ HomotopyCategory.homMk r) :
    HomotopyCategory.homMk a = 𝟙 (HomotopyCategory.mk x)

lemma twistedSquare_zero_left_inclusion :
    (stdSimplex.opIso ⦋0⦌).inv ≫ joinInl (Δ[0] : SSet.{u}).op Δ[0] =
      stdSimplex.δ 1 ≫ (edgewiseWeightIso 0).inv

lemma twistedSquare_zero_right_inclusion :
    joinInr (Δ[0] : SSet.{u}).op Δ[0] =
      stdSimplex.δ 0 ≫ (edgewiseWeightIso 0).inv

def twistedArrowVertexEdge {C : SSet.{u}} (a : (TwistedArrow C) _⦋0⦌) :
    SSet.Edge (SSet.opObjEquiv ((edgewiseLeft C).app _ a)) ((edgewiseRight C).app _ a)

lemma twistedArrowVertexEdge_inverse {C : SSet.{u}} (a : (TwistedArrow C) _⦋0⦌) :
    (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm (twistedArrowVertexEdge a).edge = a

lemma twistedArrowEdge_composition {C : SSet.{u}} {a b : (TwistedArrow C) _⦋0⦌}
    (s : SSet.Edge a b) :
    HomotopyCategory.homMk (SSet.Edge.ofTruncated (edgeUnop (s.map (edgewiseLeft C)).toTruncated)) ≫
      HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
        HomotopyCategory.homMk (s.map (edgewiseRight C)) =
      HomotopyCategory.homMk (twistedArrowVertexEdge b)
```

#### TwistedPairingZero（60行）

```lean
lemma twistedPairingSimplex_zero (i : I) :
    twistedPairingSimplex A B h (nerveVertex i) = ComposableArrows.mk₁ (h i)

lemma twistedPairingNerveMap_zero
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) (i : I) :
    (twistedPairingNerveMap A B h hh).app (Opposite.op ⦋0⦌) (nerveVertex i) =
      (edgewiseWeightIso 0).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm (ComposableArrows.mk₁ (h i))

lemma twistedPairingNerveMap_zero_postcomp {D : SSet.{u}} (G : nerve C ⟶ D)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) (i : I) :
    (twistedPairingNerveMap A B h hh ≫ edgewiseSubdivisionMap G).app
      (Opposite.op ⦋0⦌) (nerveVertex i) =
      (edgewiseWeightIso 0).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm (ComposableArrows.mk₁ (h i)) ≫ G
```

#### StrictDiagramTotJointSourceUnitLabel（82行）

```lean
def strictBETotJointUnitIndex (X : (operad A).Algebra) : strictBETotJointHomIndex A

def strictBETotJointSourceUnitLabel (X : (operad A).Algebra) : StrictBETotJointSourceElements A

lemma strictBETotJointSourceNativePairing_vertex (t : StrictBETotJointSourceElements A) :
    (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌)
      (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t) =
      (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm
        (ComposableArrows.mk₁ (SerrePositivity.EInfinity.FrameHom.liftedSourceFrameArrowValue
          (strictBETotJointSourceFrame A) (rightFrameReplacement (rightFrameFamily A)) t)) ≫
            strictBETotModelSource A

lemma strictBETotJointSourceUnitLabel_value (X : (operad A).Algebra) :
    SerrePositivity.EInfinity.FrameHom.liftedSourceFrameArrowValue
      (strictBETotJointSourceFrame A) (rightFrameReplacement (rightFrameFamily A))
      (strictBETotJointSourceUnitLabel A X) =
      (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
        (((strictBETotJointRoofResolution A (strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
          framedLimitProbeComparison A X) ≫
          ((rightFrameUnit (rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌))

lemma strictBETotJointSourceUnitLabel_native_pairing (X : (operad A).Algebra) :
    (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌)
      (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex
        (strictBETotJointSourceUnitLabel A X)) =
      (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm
        (ComposableArrows.mk₁ ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          (((strictBETotJointRoofResolution A (strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
            framedLimitProbeComparison A X) ≫
            ((rightFrameUnit (rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌)))) ≫
              strictBETotModelSource A
```

### 271.3 残る照合と検証

今回の相殺則の仮定を、元のcorrectedPairingIsoの成分の左右射影の式から回収する必要がある。今回のBEの単位ラベルの像は元のoriginal pairingについての式であり、corrected pairingの像が既に恒等射だとみなさない。その後に同じ全straightening変換の単位の像へ接続し、全Yoneda評価による全変換の照合が必要である。頂点ごとの等式を全族の等式として扱わない。

R03hの全interval族の等式、元のnative fiber射自身の弱同値性、R03dの全関手同型と元の固定始域の同型との一致は引き続き未完。今回はこれらの完了を報告する段階ではない。§269の残り450〜850行の見込みには、今回の前提の分割312行も増えた。全族の照合の主証明の検証はまだなく、その見込みで完成を保証しない。外枠22,000行と§19の停止条件を維持する。

コードのコミット：**c9dda3e9d**。新規3本・312行、名前付きdef/lemma17個。実環境の新規3本は15・6・9宣言（生成された定数とlocal instanceを含む）。既存のLeanの変更は0。

- 鍵：--class impl --wait 3600、一枚の整理券、取得後gtimeout 1700秒。検査終了とともに返却済み。
- 対象ビルド333：新規3本、成功（依存を含む12,249 jobs）。332では本体化の際の二つの有限の場合分けへのrflの適用が欠けていたため失敗し、元の個別検査済みの形へ戻して333で成功した。計算上限を変更していない。
- 小監査：AuditISW2BKCells332.lean、**221モジュール・1,563宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。互換二モジュールの宣言数0と、既存の定理の定義元の検査も成功。
- 宣言名の照合：main a4388efc9に固定し、自レーン583ファイル・1,859個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build333.log、isw2-validation333.json、isw2-declaration-collision-scan332.json。

今回までの検証済みの実測は**217モジュール・14,655行・1,556宣言**。外枠22,000行まで7,345行。監査の生成定数を含む実環境の数は単純加算せず、今回のimport後の集計を用いた（既存OppositeFunctorIsoWhiskerは12→11、ソース変更0。公開宣言の追加・変更ではない）。登録候補JSONだけを更新し、共通の入口と公式監査は変更していない。

登録候補は上記三本。今回の検証の後、同じ成分の合成則をホモトピー圏の元の射へ移す分割を続ける。R03h・R03dは未完で、一覧の完了数は増やしていない。

## 272. 同じ corrected pairing の元の成分に対する合成則（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 272.1 同じ射への接続

§271の左右射影の合成則を、twisted-arrowのホモトピー圏の任意の元の射について述べる形にした。元の射の代表辺を取って同じ三単体の計算を適用し、既存のhomotopyOppositeEquivalenceの同じ関手で反変の辺の類へ戻す。結論には選んだ代表辺を残さず、元の射そのものの左右射影と両端の元の辺だけを使う。既存の構成の合成則の証明の分割であり、一覧の新しい数学のIDは追加しない。

BEでは、元のstrictBETotJointSourceCorrectedPairingIsoの同じ全関手同型の成分を代入した。これにより、同じcorrected pairingの頂点の元の辺に、元の成分の左射影と右射影を合成すると、同じoriginal pairingの頂点の元の辺になる。存在だけの成分へ置き換えていない。全要素の任意のtに対する成分の等式であり、tについての全関手の族の一致を証明したものではない。

次に元の成分の二射影を、既存の全augmentation同型と標的の置換単位の同じ成分へ合わせる必要がある。元の単位ラベルのoriginal pairingの像は§271で検証したが、その像と今回の合成則だけで、まだcorrected pairingの単位の像の恒等性を完了したとしない。元の全straightening変換の単位の評価と、全Yoneda評価による全変換の一致も残る。R03hの全interval族の等式とR03dは引き続き未完。

### 272.2 型

新規2本（共通1・BE1）、96行。名前付きdef/lemmaは2個。BEのlocal instanceは元の代数のModelCategoryと関手的因子分解の同じ二つである。既存のLeanの変更は0。

#### TwistedArrowHomComposition（52行）

```lean
lemma twistedArrowHom_composition {C : SSet.{u}} [Quasicategory C]
    {a b : (TwistedArrow C) _⦋0⦌}
    (f : HomotopyCategory.mk a ⟶ HomotopyCategory.mk b) :
    ((homotopyOppositeEquivalence C).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft C)).map f)).unop ≫
        HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
          (SSet.mapHomotopyCategory (edgewiseRight C)).map f =
            HomotopyCategory.homMk (twistedArrowVertexEdge b)
```

#### StrictDiagramTotJointCorrectionComponent（44行）

```lean
theorem strictBETotJointSourceCorrection_component_composition
    (t : StrictBETotJointSourceElements A) :
    let a := (strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
    let b := (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
    let f := ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    ((homotopyOppositeEquivalence (CAlg_R A)).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft (CAlg_R A))).map f)).unop ≫
        HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
          (SSet.mapHomotopyCategory (edgewiseRight (CAlg_R A))).map f =
            HomotopyCategory.homMk (twistedArrowVertexEdge b)
```

### 272.3 検証

コードのコミット：**6d1362deb**。新規2本・96行、公開定理2個。実環境の新規二本は1・3宣言（BEのlocal instance二つを含む）。既存のLeanの変更は0。

- 個別検査は両方とも成功。鍵付き対象ビルド334はBE側の単体表記のscopeが欠けていたため失敗した。open scoped Simplicialを補って個別検査を通し、335で対象ビルドと小監査を成功させた。計算上限の変更はない。
- 鍵：--class impl --wait 3600、一枚の整理券、取得後gtimeout 1700秒。検査終了とともに返却済み。
- 対象ビルド335：新規二本、成功（依存を含む12,226 jobs）。
- 小監査：AuditISW2BKCells334Names.lean、**223モジュール・1,567宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。互換二モジュールの宣言数0と既存定理の定義元の確認も成功。
- §271の一件の数の差を調べるため、同じ鍵の中で元の218モジュールのimportの組も小監査で再検査した。**1,534宣言・標準三公理のみ**と元の数を再現した。OppositeFunctorIsoWhisker由来として列挙される12個と11個の名前の差は、`VertexIso.map.eq_1`という生成補題一件だけだった。手書きの公開宣言の名前の差は0。実測は今回の実環境の数を使う。
- 宣言名の照合：main a4388efc9に固定し、自レーン585ファイル・1,861個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build335.log、isw2-validation335.json、isw2-opposite-name-difference335.json、isw2-declaration-collision-scan335.json。

3b-4の検証済みの実測は**219モジュール・14,751行・1,560宣言**。外枠22,000行まで7,249行。登録候補は272.2の二本を自レーンのJSONへ追記した。共通の入口・公式監査は変更していない。

元の成分の射影を同じ全augmentation・標的単位の成分へ合わせる所から続ける。全interval族の等式と全関手同型の照合はまだなく、R03h・R03dおよび3b-4aを完了とはしていない。

## 273. 元の補正比較の二射影の全同型と、その同じ成分（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 273.1 全同型の指定値の回収

元のfunctorIsoPairの二射影が、元の二つの全関手同型そのものを回収する法則を証明した。それをBEの元の端点比較へ適用し、端点の型の等式を外して同じ組の値へ照合した。元の補正比較の指定pathを射影すると元の全端点比較を回収する既存の厳密な等式を使い、次を全関手同型のHEqとして得た。

- strictBETotJointSourceCorrectedPairingIsoの左射影は、元のstrictBETotJointSourceAugmentationDomainIsoの同じ逆。
- 同じ補正比較の右射影は、元のstrictBETotJointSourceTargetReplacementIsoの同じ逆。

HEqは端点の図式の表示の等式を扱うために使い、値を点ごとに新たに選んでいない。全パラメータの高次単体を持つ元の同型の値の照合である。さらに元の補正前後のpairingの射影の厳密な等式を四つに分け、それを成分評価に使って、元の同じ補正比較の成分を左右へ写した像も、元の全端点比較の逆の同じ成分にHEqで一致させた。

これは既存の構成の合成・射影・端点輸送・成分評価の法則の分割であり、新しい数学の一覧IDは追加しない。新規4本（共通1・BE3）、347行。全ファイル200行以下。既存のLeanの変更は0。[ModelCategory SSet]や計算上限の変更はない。モデルのinstanceはBE代数の元のものだけを使う。

### 273.2 型

公開def/lemma14個の全型と、privateなEq.mpの輸送の法則を記録する。各BEファイルのlocal instanceは元のmodelCategory A、mappingCofibrantFactorization A、および底の(CAlg_R A).op ⊗ CAlg_R Aの既存のquasicategory_tensorの三つで、ファイルごとに異なる名前にしている。

```lean
private lemma jointPairingProjectionEqMpHeq {α β γ : Sort _} (h : α = β) (a : α) (b : γ) :
    HEq (Eq.mp h a) b ↔ HEq a b
```

#### FunctorIsoPairingProjections（55行）

```lean
lemma functorIsoPair_postcomp_fst {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    (functorIsoPair e d).postcomp (fst X Y) = e

lemma functorIsoPair_postcomp_snd {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    (functorIsoPair e d).postcomp (snd X Y) = d
```

#### StrictDiagramTotJointPairingProjectionValues（98行）

```lean
lemma strictBETotJointSourceNativePairingBaseIso_pair_value :
    HEq (strictBETotJointSourceNativePairingBaseIso A)
      (functorIsoPair (strictBETotJointSourceAugmentationDomainIso A)
        (strictBETotJointSourceTargetReplacementIso A))

lemma strictBETotJointSourceNativePairingBaseIso_symm_fst :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (strictBETotJointSourceNativePairingBaseIso A).symm
      (fst (CAlg_R A).op (CAlg_R A)))
      (strictBETotJointSourceAugmentationDomainIso A).symm

lemma strictBETotJointSourceNativePairingBaseIso_symm_snd :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (strictBETotJointSourceNativePairingBaseIso A).symm
      (snd (CAlg_R A).op (CAlg_R A)))
      (strictBETotJointSourceTargetReplacementIso A).symm
```

#### StrictDiagramTotJointCorrectionProjectionValues（120行）

```lean
lemma strictBETotJointSourceCorrectionIso_projection_value {E : SSet.{u+1}}
    (q : (CAlg_R A).op ⊗ CAlg_R A ⟶ E) :
    HEq (((strictBETotJointSourceCorrectedPairingIso A).postcomp
      (twistedArrowProjection (CAlg_R A))).postcomp q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (strictBETotJointSourceNativePairingBaseIso A).symm q)

lemma strictBETotJointSourceCorrectionIso_left_value :
    HEq ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseLeft (CAlg_R A)))
      (strictBETotJointSourceAugmentationDomainIso A).symm

lemma strictBETotJointSourceCorrectionIso_right_value :
    HEq ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseRight (CAlg_R A)))
      (strictBETotJointSourceTargetReplacementIso A).symm

lemma strictBETotJointSourceCorrectedPairing_left :
    strictBETotJointSourceCorrectedPairing A ≫ edgewiseLeft (CAlg_R A) =
      strictBETotJointSourceOriginalNativeDomain A

lemma strictBETotJointSourceNativePairing_left :
    strictBETotJointSourceNativePairing A ≫ edgewiseLeft (CAlg_R A) =
      strictBETotJointSourceNativeDomain A

lemma strictBETotJointSourceCorrectedPairing_right :
    strictBETotJointSourceCorrectedPairing A ≫ edgewiseRight (CAlg_R A) =
      strictBETotJointSourceOriginalNativeCodomain A

lemma strictBETotJointSourceNativePairing_right :
    strictBETotJointSourceNativePairing A ≫ edgewiseRight (CAlg_R A) =
      strictBETotJointSourceNativeCodomain A
```

#### StrictDiagramTotJointCorrectionProjectionComponents（74行）

```lean
lemma strictBETotJointSourceCorrectionIso_left_component (t : StrictBETotJointSourceElements A) :
    HEq (VertexIso.map ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t))
      (edgewiseLeft (CAlg_R A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (strictBETotJointSourceAugmentationDomainIso A).symm (nerveVertex t))

lemma strictBETotJointSourceCorrectionIso_right_component (t : StrictBETotJointSourceElements A) :
    HEq (VertexIso.map ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t))
      (edgewiseRight (CAlg_R A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (strictBETotJointSourceTargetReplacementIso A).symm (nerveVertex t))
```

### 273.3 検収と残り

コードのコミット：**37c38f755**。新規4本・347行。公開def/lemma14個、privateな輸送の法則1個、BEのlocal instance9個。実環境の新規四本は2・7・10・5宣言。既存のLeanの変更は0。

個別検査では全型・証明が通った。既存の端点輸送と成分評価の九モジュールを再利用し、必要な依存の対象ビルド336（1,885 jobs）・337（3,392 jobs）を共有鍵で通した。本体化の338では、一時ファイルで共有していたopenの不足を検出し、新規三ファイルで名前空間を明示した。計算上限は変更していない。

- 鍵：--class impl --wait 3600、一枚の整理券、取得後gtimeout 1700秒。検査終了とともに返却済み。
- 対象ビルド339：新規四本、成功（依存を含む12,244 jobs）。
- 小監査：AuditISW2BKCells338.lean、**227モジュール・1,591宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。互換二モジュールの宣言数0と既存の定理の定義元の確認も成功。
- 宣言名の照合：main a4388efc9に固定し、自レーン589ファイル・1,875個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build339.log、isw2-validation339.json、isw2-declaration-collision-scan339.json。

3b-4の検証済みの実測は**223モジュール・15,098行・1,584宣言**。外枠22,000行まで6,902行。登録候補は273.2の四本を自レーンのJSONへ追記した。共通の入口と公式監査は変更していない。

これで元のcorrected pairingの成分の左右射影が、元の全augmentationと標的単位の同じ成分であることまで接続できた。元の単位ラベルで、それらの成分の像を元の増大写像・probe比較・置換単位の実射の類へ計算する部分が残る。さらに、元の全straightening変換の単位の評価、全Yoneda評価による全変換の一致、R03hの全interval族の等式を閉じる必要がある。成分の一致だけを全族の等式とみなさない。R03h・R03d・3b-4aはまだ完了していない。

## 274. 同じ全同型の反転した逆成分の評価（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 274.1 反転と同じ評価の両立

元のホモトピーHの反転の頂点の辺を元の向きへ戻すと、同じHの元の頂点の辺になることを、恒等辺の反転の既存の式と区間の二頂点の計算で示した。これを元の二胞体の同じホモトピー代表へ適用し、functorOppositeHomEquivで反転してから頂点評価し、元のhomotopyOppositeEquivalenceで戻す作用は、元の頂点評価の反対射になるという等式を得た。始域は任意の単体集合で、標的だけをquasicategoryとする。

さらに元の全関手同型eの反転e.opの逆成分を同じ点で評価し、反転ホモトピー圏から戻すと、元のeの同じ順成分の反対射になることを示した。成分と二胞体評価の橋は、既存のFunctorIso.app_eq_evaluateを直接使うprivateな二行の帰結である。元の同型、反転Hom対応、同じ成分の選択を保持している。新しい数学の一覧IDは追加しない。既存の係数移送・単位・成分評価の法則の分割である。

新規1本・86行、公開lemma3個・private lemma1個。既存のLeanの変更は0。[ModelCategory SSet]・計算上限の変更はない。

### 274.2 型

privateな評価の帰結と、公開三補題の全型を記録する。

```lean
private lemma oppositeEvaluationAppHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) (x : X _⦋0⦌) :
    (e.app x).hom = functorHomEvaluate e.hom x
```

#### OppositeFunctorIsoEvaluation（86行）

```lean
lemma oppositeHomotopyVertexEdge_unop {A D : SSet.{u}} {F G : A ⟶ D}
    (H : SSet.Homotopy F G) (x : A _⦋0⦌) :
    edgeUnop (X := D) (simplicialHomotopyVertexEdge (homotopyOpposite H)
      (SSet.opObjEquiv.symm x)).toTruncated =
        (simplicialHomotopyVertexEdge H x).toTruncated

lemma functorHomEvaluate_opposite {A D : SSet.{u}} [Quasicategory D]
    {F G : A ⟶ D} (α : FunctorHom F G) (x : A _⦋0⦌) :
    (homotopyOppositeEquivalence D).functor.map
      (functorHomEvaluate (functorOppositeHomEquiv F G α) (SSet.opObjEquiv.symm x)) =
        (functorHomEvaluate α x).op

lemma functorIso_op_app_inv {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) (x : X _⦋0⦌) :
    (homotopyOppositeEquivalence Y).functor.map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        e.op (SSet.opObjEquiv.symm x)).inv) = (e.app x).hom.op
```

### 274.3 検証と次の照合

コードのコミット：**166682a6b**。新規1本・86行、公開lemma3個・private lemma1個。既存のLeanの変更は0。

- 全補題の個別検査は成功。成分と二胞体評価の橋は既存のFunctorIso.app_eq_evaluateの直接の二行の帰結へ短縮してから、本体の検査を行った。
- 鍵：--class impl --wait 3600、一枚の整理券、取得後gtimeout 1700秒。検査終了とともに返却済み。
- 対象ビルド340：新規1本、成功（依存を含む2,244 jobs）。
- 小監査：AuditISW2BKCells340.lean、**228モジュール・1,595宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。互換二モジュールの宣言数0と、既存の定理の定義元の確認も成功。
- 新規ファイル由来として実環境で数えた定数は3個。既存OppositeFunctorIsoWhiskerの生成補題を含む数は11→12に戻ったため、今回も単純な加算ではなく現在のimport後の実環境で集計する（§272の同じimport構成による宣言名の照合を参照）。
- 宣言名の照合：main a4388efc9に固定し、自レーン590ファイル・1,878個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build340.log、isw2-validation340.json、isw2-declaration-collision-scan340.json。

3b-4の検証済みの実測は**224モジュール・15,184行・1,588宣言**。外枠22,000行まで6,816行。登録候補は274.2の一ファイルを自レーンのJSONへ追記した。共通の入口と公式監査は変更していない。

次は273の同じ成分の左射影の像へ今回の公式を適用し、元のsource-frame全augmentationの成分の射の類へ戻す。前合成の成分は既存のfunctorIso_app_precomp_heqを使う。入力のnerveの零単体の表示はComposableArrows.ext₀で同じ元のparameterの点へ合わせ、同じnerveTransformationPostIsoの成分はNerveColumn.hom_component_arrowで元の実射の類へ合わせる。元の単位ラベルについて、元の増大写像・probe比較・標的単位の合成との相殺へ進む。

ここまでは成分評価の計算である。R03hの全interval族の等式、元のnative fiber射自身の弱同値性、R03dの全関手同型と元の固定始域の同型の一致、3b-4aは引き続き未完。今回の等式を全パラメータの族の一致の代わりにはしない。

## 275. 元の augmentation と標的単位の同じ成分の実射への照合（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 275.1 元の実射の類の回収

§274の反転評価と、既存の前合成・成分評価の法則を使い、元の反変augmentation同型の逆成分を反転ホモトピー圏から戻した射が、元の増大写像とprobe比較の同じ合成の実射の類になることを、端点込みのArrowの等式で照合した。入力の零単体は、同じnerve反転の式を使って元のparameterの同じ点へ合わせた。元の全augmentationの成分の式は、NerveColumn.hom_component_arrowへ元の同じ全円柱を入れている。

標的についても、元の全弱自然変換の同型の順成分のArrowの式を示し、元の同じ標的置換同型と全実射の標的への引き戻しへ適用した。元の標的比較の逆成分は、元の同じ置換単位の実射の類になる。新たな置換や成分の選択は行っていない。

全要素の任意のtについての元の成分の計算であり、tについての全族の等式を得たとはしていない。これらを元の補正比較の成分の二射影へ代入し、§272の同じ合成則へ接続する所から進む。R03h・R03dは未完。

既存の構成の係数移送・前合成・単位・成分評価の法則の分割で、新しい数学の一覧IDは追加しない。新規2本・221行、公開lemma8個・private lemma1個。各ファイル200行以下。既存のLeanの変更は0。[ModelCategory SSet]・計算上限の変更はない。

### 275.2 型

全公開8補題と、privateな端点輸送の法則の型を記録する。local instanceは各ファイルで元のBE代数のmodelCategory AとmappingCofibrantFactorization Aの二つだけを使い、ファイル間で名前を分けている。

```lean
private lemma jointAugmentationAppInvArrowOfHEq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') (x : X _⦋0⦌) :
    Arrow.mk (e.app x).inv = Arrow.mk (e'.app x).inv
```

#### StrictDiagramTotJointSourceAugmentationPointValues（125行）

```lean
lemma strictBETotJointSourceAugmentationInput_vertex (t : StrictBETotJointSourceElements A) :
    SSet.opObjEquiv ((strictBETotJointSourceAugmentationInput A).app
      (Opposite.op ⦋0⦌) (nerveVertex t)) =
      nerveVertex (((strictBETotJointSourceParameterIndex A).obj t).unop)

lemma strictBETotJointSourceFrameAugmentation_parameter_component (t : StrictBETotJointSourceElements A) :
    (strictBETotJointSourceFrameAugmentation A).app
      (((strictBETotJointSourceParameterIndex A).obj t).unop) =
    (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
      (((strictBETotJointRoofResolution A t.obj.1).augmentation.app t.obj.2.unop) ≫
        framedLimitProbeComparison A (AsSmall.down.obj t.obj.1).1.unop)

lemma strictBETotJointSourceFrameAugmentation_component_arrow (t : StrictBETotJointSourceElements A) :
    Arrow.mk ((strictBETotJointSourceFrameAugmentationIso A).app
      (nerveVertex (((strictBETotJointSourceParameterIndex A).obj t).unop))).hom =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app
          (((strictBETotJointSourceParameterIndex A).obj t).unop))).map
            (strictBETotModelSource A)))

lemma strictBETotJointSourceAugmentationDomainIso_inv_component_arrow (t : StrictBETotJointSourceElements A) :
    Arrow.mk (((homotopyOppositeEquivalence (CAlg_R A)).functor.map
      ((strictBETotJointSourceAugmentationDomainIso A).app (nerveVertex t)).inv).unop) =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app
          (((strictBETotJointSourceParameterIndex A).obj t).unop))).map
            (strictBETotModelSource A)))
```

#### StrictDiagramTotJointSourceTargetPointValues（96行）

```lean
lemma strictBETotModelWeakTransformationIso_component_arrow {J : Type (u+1)} [SmallCategory J]
    {F G : J ⥤ AsSmall.{u+1} (operad A).Algebra} (η : F ⟶ G)
    (hη : ∀ j, weakEquivalences (operad A).Algebra (AsSmall.down.map (η.app j))) (j : J) :
    Arrow.mk ((strictBETotModelWeakTransformationIso A η hη).app (nerveVertex j)).hom =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk (η.app j)).map (strictBETotModelSource A)))

lemma strictBETotTargetReplacementNativeIso_component_arrow (Y : AsSmall.{u+1} (operad A).Algebra) :
    Arrow.mk ((strictBETotTargetReplacementNativeIso A).app (nerveVertex Y)).hom =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((strictBETotTargetReplacementUnit A).app Y)).map (strictBETotModelSource A)))

lemma strictBETotJointSourceTargetReplacementIso_inv_component_arrow (t : StrictBETotJointSourceElements A) :
    Arrow.mk ((strictBETotJointSourceTargetReplacementIso A).app (nerveVertex t)).inv =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((strictBETotTargetReplacementUnit A).app
          ((strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A).obj t))).map
            (strictBETotModelSource A)))

lemma strictBETotJointSourceTargetReplacementUnit_parameter_component (t : StrictBETotJointSourceElements A) :
    (strictBETotTargetReplacementUnit A).app
      ((strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A).obj t) =
    (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
      ((rightFrameReplacementUnit (rightFrameFamily A)).app (AsSmall.down.obj t.obj.1).2)
```

### 275.3 検証

コードのコミット：**fd55d35ec**。新規2本・221行、公開lemma8個・private lemma1個、local instance4個。実環境で新規二本は6・6宣言。既存のLeanの変更は0。

- 個別検査で全型・証明が通った。再利用する既存NerveColumnComponentArrowとFunctorIsoComponentPreの対象ビルド341（5,713 jobs）も共有鍵で成功。
- 鍵：--class impl --wait 3600、一枚の整理券、取得後gtimeout 1700秒。検査終了とともに返却済み。
- 対象ビルド342：新規二本、成功（依存を含む12,284 jobs）。
- 小監査：AuditISW2BKCells342.lean、**230モジュール・1,606宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。互換二モジュールの宣言数0と既存の定理の定義元の確認も成功。
- 宣言名の照合：main a4388efc9に固定し、自レーン592ファイル・1,886個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build342.log、isw2-validation342.json、isw2-declaration-collision-scan342.json。

今回までの検証済みの実測は**226モジュール・15,405行・1,599宣言**。外枠22,000行まで6,595行。生成補題を含む数は今回のimport後の実環境で集計した。登録候補は275.2の二本を自レーンのJSONへ追記した。共通の入口と公式監査は変更していない。

## 276. 元の補正比較の同じ成分の実際の左右像の実射への照合（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 276.1 同じ成分の像を代入する

§273の元の全射影の値の照合を同じ点で読み、§275の同じaugmentationと標的単位の実射の類の計算を代入した。結論に現れるfは、元のstrictBETotJointSourceCorrectedPairingIsoの同じ成分の順射そのものである。元のfを左へ写して反転ホモトピー圏から戻すと、元の増大写像とprobe比較の同じ合成の実射の類になる。右へ写すと、元の標的置換単位の同じ実射の類になる。両方とも端点を保持したArrowの等式で述べる。

存在だけの射へ置き換えず、§272の同じ成分の合成則で実際に使う二つの射を同定した。全要素の任意のtに対する成分の計算であり、tについての全interval族の一致を得たとはしていない。元の単位ラベルで両端を相殺する所へ進む。R03h・R03dは未完。

既存の構成の単位・係数移送・成分評価・合成則の分割で、新しい数学の一覧IDは追加しない。新規1本・99行、公開lemma2個・private lemma1個。既存のLeanの変更は0。計算上限は変更していない。

### 276.2 型

公開二補題とprivateな成分の型の輸送の法則の全型を記録する。local instanceは元のBE代数のmodelCategory AとmappingCofibrantFactorization Aの二つのみ。

```lean
private lemma jointCorrectionAppHomArrowOfHEq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') (x : X _⦋0⦌) :
    Arrow.mk (e.app x).hom = Arrow.mk (e'.app x).hom
```

#### StrictDiagramTotJointCorrectionComponentArrows（99行）

```lean
lemma strictBETotJointSourceCorrection_left_component_arrow (t : StrictBETotJointSourceElements A) :
    let f := ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    Arrow.mk (((homotopyOppositeEquivalence (CAlg_R A)).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft (CAlg_R A))).map f)).unop) =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          ((strictBETotJointRoofResolution A t.obj.1).augmentation.app t.obj.2.unop ≫
            framedLimitProbeComparison A (AsSmall.down.obj t.obj.1).1.unop))).map
              (strictBETotModelSource A)))

lemma strictBETotJointSourceCorrection_right_component_arrow (t : StrictBETotJointSourceElements A) :
    let f := ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    Arrow.mk ((SSet.mapHomotopyCategory (edgewiseRight (CAlg_R A))).map f) =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          ((rightFrameReplacementUnit (rightFrameFamily A)).app (AsSmall.down.obj t.obj.1).2))).map
            (strictBETotModelSource A)))
```

### 276.3 検証

コードのコミット：**cdd6b0af0**。新規1本・99行、公開lemma2個・private lemma1個、local instance2個。実環境で新規一ファイルは4宣言。既存のLeanの変更は0。

- 個別検査で全型・証明が通った。
- 鍵：--class impl --wait 3600、一枚の整理券、取得後gtimeout 1700秒。検査終了とともに返却済み。
- 対象ビルド343：新規一ファイル、成功（依存を含む12,289 jobs）。
- 小監査：AuditISW2BKCells343.lean、**231モジュール・1,610宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。互換二モジュールの宣言数0と既存の定理の定義元の確認も成功。
- 宣言名の照合：main a4388efc9に固定し、自レーン593ファイル・1,888個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build343.log、isw2-validation343.json、isw2-declaration-collision-scan343.json。

3b-4の検証済みの実測は**227モジュール・15,504行・1,603宣言**。外枠22,000行まで6,496行。登録候補は276.2の一ファイルを自レーンのJSONへ追記した。共通の入口と公式監査は変更していない。

## 277. 元の補正単位の辺の類と native 恒等射の照合（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 277.1 同じ単位ラベルの相殺

元のstrictBETotJointSourceUnitLabel A Xを、同じstrictBETotJointSourceCorrectedPairingで送った頂点の辺の類が、元のnative試験対象の恒等射のArrowに一致することを証明した。結論の恒等射は、元のstrictBETotModelSourceでmodelRelativeObject Xを送った同じ頂点上のものである。

証明では元のstrictBETotJointSourceCorrectedPairingIsoの同じ成分の順射fを使う。§272の同じ成分の三辺の合成則へ、§276の同じfの左右射影の元の実射の類の同定を代入する。original pairingの同じ単位ラベルの像は§271の式であり、その像の二射の合成を同じnerveの合成三角形で計算した。f自身は同型の順射なので、左右の射影と反転ホモトピー圏の同じ比較の像も可逆である。この同じ二射を相殺して、中央の元の補正単位の辺の類を元の恒等射へ戻す。標的置換がcofibrantだという仮定や[ModelCategory SSet]を足していない。

端点込みのArrowの等式で述べ、元の同型や射を再選択していない。恒等射に一致するのはホモトピー圏の射の類であり、元の単体集合の一単体が退化辺と厳密に等しいとはしていない。

既存の構成の単位・合成・係数移送の法則の証明の分割として、端点を保持した相殺則、同じ実射のtwisted頂点の辺の式、同じnerveの合成の像の式を分けた。新しい数学の一覧IDは追加しない。新規3本（共通2・BE1）、170行、公開lemma4個。各ファイル200行以下。既存のLeanの変更は0。計算上限は変更していない。

### 277.2 型

四つの公開補題の全型を記録する。BEのlocal instanceは元のmodelCategory AとmappingCofibrantFactorization Aの二つのみである。

#### ArrowMiddleUnit（43行）

```lean
lemma arrow_middle_unit_of_outer_arrow_equalities {D : Type u} [Category.{v} D]
    {q x y z q₀ x₀ z₀ : D} (p : q ⟶ x) (a : x ⟶ y) (r : y ⟶ z) (b : q ⟶ z)
    (p₀ : q₀ ⟶ x₀) (r₀ : x₀ ⟶ z₀) [IsIso p] [IsIso r]
    (hp : Arrow.mk p = Arrow.mk p₀) (hr : Arrow.mk r = Arrow.mk r₀)
    (hb : Arrow.mk b = Arrow.mk (p₀ ≫ r₀)) (h : p ≫ a ≫ r = b) :
    Arrow.mk a = Arrow.mk (𝟙 x₀)
```

#### TwistedArrowVertexEdgeNerve（47行）

```lean
lemma twistedArrowVertexEdge_nerve_arrow {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (F : nerve C ⟶ E) {x y : C} (g : x ⟶ y) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      ((edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm (ComposableArrows.mk₁ g) ≫ F))) =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk g).map F))

lemma mappedNerveEdgeHom_comp {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (F : nerve C ⟶ E) {x y z : C} (g : x ⟶ y) (h : y ⟶ z) :
    HomotopyCategory.homMk ((nerve.edgeMk (g ≫ h)).map F) =
      HomotopyCategory.homMk ((nerve.edgeMk g).map F) ≫
        HomotopyCategory.homMk ((nerve.edgeMk h).map F)
```

#### StrictDiagramTotJointCorrectedUnitArrow（80行）

```lean
lemma strictBETotJointSourceCorrectedPairing_unit_arrow (X : (operad A).Algebra) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      ((strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointSourceUnitLabel A X))))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk ((strictBETotModelSource A).app
        (Opposite.op ⦋0⦌) (nerveVertex (modelRelativeObject (operad A).Algebra X)))))
```

### 277.3 検証

四補題の個別検査は成功。単位ラベルの合成の係数移送は、外側のFunctor.map_compを一回だけ使い、元のsource-frame増大写像とprobe比較の合成のまとまりを保持した。新規三本の対象ビルド344と小監査も成功（--class impl --wait 3600、一枚の整理券、gtimeout 1700秒）。対象ビルドは依存を含む12,292 jobsで成功。小監査は234モジュール・1,616宣言、propext・Classical.choice・Quot.soundのみで、sorryAx・追加公理なし。新規三本170行、公開四補題と局所instance二つ。自レーン累計230本・15,674行（外枠まで6,326行）、実環境の自レーン宣言1,609。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と、自レーン596ファイル・1,892個の名前を照合し、異なるファイル間の重複0、内部も0。git diff --checkも通過。証跡は /private/tmp/isw2-build344.log、isw2-validation344.json、isw2-declaration-collision-scan344.json。共通の入口と公式監査は変更していない。

コードは30887c8aeに保存した。

### 277.4 残る範囲

今回の補正単位の辺の類の等式は、元の全要素の同じ単位ラベルの像についてのもの。次に元のnative fiber点をこの同じラベルへ合わせ、その同じHom空間内の単位点の比較へ戻す必要がある。既存のcosliceFiberVertexIsoOfHomEqとcosliceTwistedHomMapの同じ比較・単位三角形が候補になるが、この移送はまだ検証していない。元の全straightening比較と単位条件を通した単位の評価、全Yoneda評価・局所化の前合成の充満忠実性による全変換の一致も残る。

R03hの全interval族の等式、元のnative fiber射自身の弱同値性、R03dの全関手同型と元の固定始域の同型の一致、および3b-4aはまだ未完。今回の一点の辺の類の等式を、全パラメータの族の一致の代わりにはしない。/goalは元の全範囲のまま継続する。

## 278. 同じnative fiber射の元の単位ラベルへの制限（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 278.1 範囲と型

§277の三本は30887c8aeに保存した。元のnative fiber射に元のpullbackのfiber同型を合成した同じ射を、同じ係数の単位ラベルで評価する。元の包含後の厳密な等式を評価する既存構成の法則と証明の分割であり、新しい数学のIDの追加はない。個別検査 /private/tmp/isw2-native-unit-fiber.lean は終了コード0、出力なし。以下の型を本体へ切り出し、対象ビルドと小監査を行う。

#### StrictDiagramTotJointNativeUnitFiber（84行）

```lean
def strictBETotJointSourceNativeUnitFiberElement (X : (operad A).Algebra) :
    (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj
      (strictBETotJointUnitIndex A X)

lemma strictBETotJointSourceNativeUnitFiberElement_value (X : (operad A).Algebra) :
    (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A)
      (strictBETotJointUnitIndex A X)).obj (strictBETotJointSourceNativeUnitFiberElement A X) =
        strictBETotJointSourceUnitLabel A X

lemma strictBETotJointSourceNativeTwistedFiberMap_unit_value (X : (operad A).Algebra) :
    ((strictBETotJointSourceNativeTwistedFiberMap A (strictBETotJointUnitIndex A X)).app
      (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val =
      (strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointSourceUnitLabel A X))

lemma strictBETotJointSourceNativeTwistedFiberMap_unit_arrow (X : (operad A).Algebra) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      (((strictBETotJointSourceNativeTwistedFiberMap A (strictBETotJointUnitIndex A X)).app
        (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk ((strictBETotModelSource A).app
        (Opposite.op ⦋0⦌) (nerveVertex (modelRelativeObject (operad A).Algebra X)))))
```

### 278.2 検収と残り

対象ビルド345は依存を含む12,293 jobsで成功。--class impl --wait 3600、一枚の整理券、gtimeout 1700秒で対象ビルドと小監査を実行し、終了コード0。小監査は235モジュール・1,622宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。新規一本84行、公開定義一つ・公開補題三つ・局所instance二つ。自レーン累計231本・15,758行（外枠まで6,242行）、自レーン実環境1,615宣言。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と、自レーン597ファイル・1,896個の名前を照合し、異なるファイル間の重複0、内部も0。git diff --check通過。証跡は /private/tmp/isw2-build345.log、isw2-validation345.json、isw2-declaration-collision-scan345.json。コードは413230b6dに保存した。元のnative fiber射そのものについて同じ単位の辺の類を回収する範囲であり、Hom空間の点の同型・全straightening比較の単位評価・全変換の一致はまだ主張しない。R03h・R03d・3b-4aも未完。

## 279. 元の単位条件を満たす同じ全空間の射の単位への接続（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 279.1 型と範囲

§277〜278の結果・型・コミットは4d59e83eaに報告した。既存のstrictBETotJointSourceNativeFiberUnit_mapを同じpullback同型で後合成し、その同じ写像の元の単位点での値を§278へ接続する。既存の単位・合成・係数移送の法則と証明の分割であり、新しい数学のIDの追加はない。

個別検査の一時ファイルでvertexFiberMap・nerveVertexの名前空間が欠け、未知の短名が暗黙の変数として推論されていたため、型推論が既定上限に達した。必要なEquivalence・TheSliceAndJoinConstructionsを明示し、autoImplicit falseで再検査した9回目は終了コード0、出力なし。計算上限は上げていない。元の等式の型を保ち、HEqへの型の変更は採用していない。以下を本体へ分けて対象ビルド346と小監査を行う。

#### StrictDiagramTotJointNativeLiftUnit（95行）

```lean
lemma strictBETotJointSourceNativeLiftUnit_twistedFiberMap
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).left ≫ m =
        strictBETotJointSourceNativeHomMap A) (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P ≫
      vertexFiberMap (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
        (strictBETotJointNativeHomProjection A) m hm (nerveVertex P) ≫
        (vertexFiberPullbackIso (twistedArrowProjection (CAlg_R A))
          (strictBETotJointNativeHomInput A) (nerveVertex P)).hom =
            strictBETotJointSourceNativeTwistedFiberMap A P

lemma strictBETotJointSourceNativeLiftUnit_unit_arrow
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).left ≫ m =
        strictBETotJointSourceNativeHomMap A) (X : (operad A).Algebra) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      (((simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A)
          (strictBETotJointUnitIndex A X) ≫
        vertexFiberMap (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
          (strictBETotJointNativeHomProjection A) m hm (nerveVertex (strictBETotJointUnitIndex A X)) ≫
        (vertexFiberPullbackIso (twistedArrowProjection (CAlg_R A))
          (strictBETotJointNativeHomInput A) (nerveVertex (strictBETotJointUnitIndex A X))).hom).app
          (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk ((strictBETotModelSource A).app
        (Opposite.op ⦋0⦌) (nerveVertex (modelRelativeObject (operad A).Algebra X)))))
```

### 279.2 検収と残り

対象ビルド346は依存を含む12,294 jobsで成功。--class impl --wait 3600、一枚の整理券で順番を待ち、gtimeout 1700秒の中で対象ビルドと小監査を実行した。小監査は236モジュール・1,626宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。新規一本95行、公開二補題・局所instance二つ。自レーン累計232本・15,853行（外枠まで6,147行）、自レーン実環境1,619宣言。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と、自レーン598ファイル・1,898個の名前を照合し、異なるファイル間の重複0、内部も0。git diff --check通過。証跡は /private/tmp/isw2-build346.log、isw2-validation346.json、isw2-declaration-collision-scan346.json。共通の入口・公式監査・⑤aのファイル・既存Leanは変更していない。コードは7d9e0ebb2に保存した。全空間の射には元の底の等式と元の単位条件だけを仮定した。実射自身の弱同値性・全straightening比較の単位の評価・全関手同型の一致はまだ未完であり、今回の単位点の辺の類で代用しない。R03h・R03d・3b-4aは未完のまま。

### 279.3 次の確認箇所

元のnative fiberの単位の辺の類の一致から、同じHom空間の点の同型へ戻す際に、既存のcosliceTwistedHomMapとcosliceFiberVertexToEdgeが同じ辺を表す次の構成の法則を調べた。

```lean
lemma cosliceTwistedHomMap_vertex_edge_arrow {C : SSet.{u}} {x y : C _⦋0⦌}
    (v : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) _⦋0⦌) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      (((cosliceTwistedHomMap x y).app (Opposite.op ⦋0⦌) v).val))) =
      Arrow.mk (HomotopyCategory.homMk (cosliceFiberVertexToEdge v))
```

これは未検証の候補で、本体・manifest・監査・済みの数には入れていない。同じedgewiseWeightIsoの逆とcosliceEdgewiseCollapseの零次元の式を合わせれば足りる見込みだが、一時ファイルの一点の証明でSubsingletonの推論が通らず、未解決のままの大きい証明はkernelの既定上限にも達した。計算上限は上げず、小さい重みの等式と辺の等式に分割する検査用ファイル /private/tmp/isw2-coslice-twisted-unit-split.lean に残した。次はFin 1の座標を明示して小さい補題ごとに検査する。既存のcosliceFiberVertexIsoOfHomEqへ実際の単位点を戻す照合、元のstraightening評価の全自然性による全変換の一致をさらに示す必要があり、今回の結果で全関手同型を得たとはしない。

B4′自体は§268で完了。統合81683a2ab・報告8c7971003、書換え0・保留0を維持し、§277〜279は/goal再開後の追加の検証である。

## 280. 元のcoslice比較が表す同じ辺の零次元の式（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 280.1 範囲と型

前回は元の単位条件と元のnative fiberの単位の辺の類の照合を検証し、81e99bcecまで保存したため、進捗あり。作業木はクリーン、共有鍵も持っていない状態から再開した。§279.3の零次元のcoslice比較の法則を三つの小補題へ分割した。Fin 1の座標はFin.eq_zeroで明示し、同じ逆則は括弧の位置を合わせて適用した。個別検査 /private/tmp/isw2-coslice-twisted-unit-split.lean は終了コード0、出力なし。計算上限・既存の型は変更していない。以下は既存構成の単位・係数移送の法則と証明の分割であり、新しい数学のIDには数えない。

#### CosliceTwistedHomVertexEdge（68行）

```lean
lemma cosliceEdgewiseCollapse_zero :
    cosliceEdgewiseCollapse.{u} ⦋0⦌ =
      (joinIso (stdSimplex.opIso ⦋0⦌) (Iso.refl (Δ[0] : SSet.{u}))).hom

lemma edgewiseWeightIso_zero_inv_comp_cosliceCollapse :
    (edgewiseWeightIso.{u} 0).inv ≫ cosliceEdgewiseCollapse ⦋0⦌ =
      (joinStdSimplexIso 0 0).inv

lemma cosliceTwistedHomMap_vertex_edge_arrow {C : SSet.{u}} {x y : C _⦋0⦌}
    (v : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) _⦋0⦌) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      (((cosliceTwistedHomMap x y).app (Opposite.op ⦋0⦌) v).val))) =
      Arrow.mk (HomotopyCategory.homMk (cosliceFiberVertexToEdge v))
```

### 280.2 検収と残り

新規一本の対象ビルド347と、既存の次の入力cosliceFiberVertexIsoOfHomEqの定義元CosliceFiberHomClassのビルドは成功（依存を含む2,268 jobs）。--class impl --wait 3600、一枚の整理券、gtimeout 1700秒で対象ビルドと小監査を行い、終了コード0。小監査は237モジュール・1,629宣言、標準三公理propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。新規一本68行・公開三補題。自レーン233本・15,921行（外枠まで6,079行）、自レーン実環境1,622宣言。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と自レーン599ファイル・1,901個の名前を照合し、異なるファイル間の重複0、内部も0。git diff --check通過。証跡は /private/tmp/isw2-build347.log、isw2-validation347.json、isw2-declaration-collision-scan347.json。元のnative fiber射の弱同値性、R03hの全interval族、R03dの全関手同型、3b-4aはまだ未完。

## 281. R03d内の点の比較の中間の定理R03i（型と見込み、2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 25（うち追加 13）。

### 281.1 追加する型

指示書§19の枠で、R01〜R03の同じまとまりの中間の定理としてR03iを足す。§277〜279で示した元の単位の辺の類を、元のtwisted-arrowの同じ両端固定のHom空間の点の同型へ戻すために使う。見込みは450〜950行（既存構成の法則・証明の分割・native単位への適用を含む）、1,500行以内。既存のcosliceFiberVertexIsoOfHomEqの判定を、元のcosliceTwistedHomMapの同じ比較と同じ単位三角形で移すもので、⑤aの欄の型には触れない。

```lean
theorem nonempty_twistedArrowHomSpace_vertexIso_of_arrow_eq
    {C : SSet.{u}} [Quasicategory C] {x y : C _⦋0⦌}
    {v w : (twistedArrowHomSpace x y) _⦋0⦌}
    (h : Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v.val)) =
      Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge w.val))) :
    Nonempty (VertexIso v w)
```

### 281.2 証明の順序

1. 元のfiber内の辺を元のtwisted-arrow全空間へ含めると、左右射影は元の底の頂点の恒等射の類になることを、包含後の厳密な定値の等式で示す。
2. 既存のtwistedArrowHom_compositionを同じ辺へ適用し、左右の恒等射を相殺する。これにより同じfiber内のVertexIsoで辺のArrowの類が変わらないことが分かる。
3. 既存のcosliceTwistedHomMap_isQCatEquivalenceの同じ指定逆で元の二点を戻す。元のinvHomIsoの成分と2を使い、§280の辺の式を通して、戻した二つのcoslice点の元の矢印の類を一致させる。
4. 既存のcosliceFiberVertexIsoOfHomEqを使い、その同じ同型を元のcosliceTwistedHomMapで写す。元のinvHomIsoの二つの成分で元の二点へ戻す。

ここまでが同じ点の同型の中間定理であり、それだけでR03dの全関手同型を主張しない。元の全straightening・指定単位・全パラメータの同じ変換への照合、R03hの全interval族、R03d以下の残りは維持する。

### 281.3 分割した法則の型と個別検査

/private/tmp/isw2-fiber-edge-constant.leanの五つの主張は個別検査5で終了コード0、出力なし。最初の四つは元の包含・射影・合成・恒等の法則の分割で、一覧のIDには数えない。最後の一つが上に追加したR03iそのもの。以下の新規四本へ分け、対象ビルド348と小監査で本体を確認する。いずれも200行未満、計算上限は変更していない。

#### VertexFiberEdgeProjectedArrow（40行）

```lean
lemma vertexFiber_edge_projected_arrow {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D)
    {b : B _⦋0⦌} {v w : (vertexFiber p b) _⦋0⦌} (e : SSet.Edge v w) :
    Arrow.mk (HomotopyCategory.homMk ((e.map (vertexFiberι p b)).map (p ≫ g))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (g.app (Opposite.op ⦋0⦌) b)))
```

#### ArrowMiddleIdentity（37行）

```lean
lemma arrow_middle_eq_of_outer_identity_arrows {D : Type u} [Category.{v} D]
    {q x y z x₀ y₀ : D} (p : q ⟶ x) (a : x ⟶ y) (r : y ⟶ z) (b : q ⟶ z)
    (hp : Arrow.mk p = Arrow.mk (𝟙 x₀)) (hr : Arrow.mk r = Arrow.mk (𝟙 y₀))
    (h : p ≫ a ≫ r = b) : Arrow.mk a = Arrow.mk b
```

#### TwistedHomVertexEdgeClasses（70行）

```lean
lemma twistedArrowHomSpace_edge_arrow_eq {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} {v w : (twistedArrowHomSpace x y) _⦋0⦌}
    (e : SSet.Edge v w) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v.val)) =
      Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge w.val))

lemma twistedArrowHomSpace_vertexIso_arrow_eq {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} {v w : (twistedArrowHomSpace x y) _⦋0⦌}
    (e : VertexIso v w) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v.val)) =
      Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge w.val))
```

#### TwistedHomVertexIsoOfArrowEq（55行）

```lean
lemma nonempty_twistedArrowHomSpace_vertexIso_of_arrow_eq {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} {v w : (twistedArrowHomSpace x y) _⦋0⦌}
    (h : Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v.val)) =
      Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge w.val))) :
    Nonempty (VertexIso v w)
```

### 281.4 R03iの検収

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

新規四本202行の対象ビルド349は成功（依存を含む2,683 jobs）。初回348は新規ファイルの補助補題の名前空間が一つ不足して停止し、同じ新規ファイルで明示して再実行した。--class impl --wait 3600、一枚の整理券、gtimeout 1700秒。小監査は241モジュール・1,634宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計237本・16,123行（外枠まで5,877行）、自レーン実環境1,627宣言。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と、自レーン603ファイル・1,906個の名前を照合し、異なるファイル間の重複0、内部も0。名前空間のopenの追記で宣言名は変えていない。git diff --check通過。証跡は /private/tmp/isw2-build349.log、isw2-validation349.json、isw2-declaration-collision-scan349.json。既存のLean・⑤aのファイル・公式入口・公式監査には変更なし。

R03iの追加した型は本体のnonempty_twistedArrowHomSpace_vertexIso_of_arrow_eqとして閉じたため、済みを一つ増やした。今回の四本202行は、R03iの見込み450〜950行のうち一般の判定の部分。§280の68行を含めた関連する前提計算は270行、元のnative単位点への適用はこの次に行う。この二点を同じHom空間で結べる判定は、まだ全パラメータの同じ変換の一致やnative fiber射自身の弱同値性を証明するものではない。R03h・R03d・3b-4aは未完のまま続ける。

## 282. 元のnative単位点と、元の恒等点の同じHom空間での同型（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 282.1 型と範囲

§280の零次元の式はfcf587ecd、R03iと既存の四法則は078318c2bに保存した。次に元のnative fiber射の単位点を、strictBETotJointNativeHomInput_model_vertexの同じ底の等式だけで移し、R03iを適用する。比較先は既存のtwistedArrowSourceIdentityそのものを、既存のtwistedArrowSourceFiberIsoで制限した点であり、別の恒等点を選び直していない。

以下はR03iへの適用と既存の係数移送・制限・単位の法則の分割で、新しい数学のIDは追加しない。個別検査 /private/tmp/isw2-native-unit-points.lean は3回目で終了コード0、出力なし。最初の試みで定義上の一致とした箇所は、元のtwistedArrowSourceFiberIso_ιによる厳密な式へ直した。計算上限は変更していない。

#### TwistedHomIdentityPoint（68行）

```lean
def twistedArrowHomSpaceIdentityPoint {C : SSet.{u}} (x : C _⦋0⦌) :
    (twistedArrowHomSpace x x) _⦋0⦌

lemma twistedArrowHomSpaceIdentityPoint_value {C : SSet.{u}} (x : C _⦋0⦌) :
    (twistedArrowHomSpaceIdentityPoint x).val = SSet.const x

lemma twistedArrowVertexEdge_const_arrow {C : SSet.{u}} (x : C _⦋0⦌) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge (SSet.const x))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk x))

lemma twistedArrowHomSpaceIdentityPoint_arrow {C : SSet.{u}} (x : C _⦋0⦌) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge (twistedArrowHomSpaceIdentityPoint x).val)) =
      Arrow.mk (𝟙 (HomotopyCategory.mk x))
```

#### StrictDiagramTotJointNativeUnitPoint（92行）

```lean
def strictBETotJointNativeUnitFiberIso (X : (operad A).Algebra) :
    vertexFiber (twistedArrowProjection (CAlg_R A))
      ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointUnitIndex A X))) ≅
      twistedArrowHomSpace
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (modelRelativeObject (operad A).Algebra X)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (modelRelativeObject (operad A).Algebra X)))

def strictBETotJointNativeUnitPoint (X : (operad A).Algebra) :
    (twistedArrowHomSpace
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X)))
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X)))) _⦋0⦌

lemma strictBETotJointNativeUnitPoint_value (X : (operad A).Algebra) :
    (strictBETotJointNativeUnitPoint A X).val =
      ((strictBETotJointSourceNativeTwistedFiberMap A (strictBETotJointUnitIndex A X)).app
        (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val

lemma strictBETotJointNativeUnitPoint_identityIso (X : (operad A).Algebra) :
    Nonempty (VertexIso (strictBETotJointNativeUnitPoint A X)
      (twistedArrowHomSpaceIdentityPoint ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X)))))
```

係数移送の値のprivate補題も型を記録する（同じhで場合分けする既存の等式の係数移送）。

```lean
private lemma jointNativeUnitPointTransport_value {E B : SSet.{u}} (p : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') (n : SimplexCategoryᵒᵖ)
    (v : (vertexFiber p b).obj n) :
    ((eqToHom (congrArg (vertexFiber p) h)).app n v).val = v.val
```

### 282.2 検収と残り

新規二本160行の対象ビルド350は成功（依存を含む12,307 jobs）。--class impl --wait 3600、一枚の整理券、gtimeout 1700秒で対象ビルドと小監査を行い、終了コード0。小監査は243モジュール・1,646宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。公開定義三つ・公開補題五つ・private補題一つ・局所instance二つ。自レーン累計239本・16,283行（外枠まで5,717行）、自レーン実環境1,639宣言。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と、自レーン605ファイル・1,914個の名前を照合し、異なるファイル間の重複0、内部も0。git diff --check通過。証跡は /private/tmp/isw2-build350.log、isw2-validation350.json、isw2-declaration-collision-scan350.json。既存Lean・⑤aのファイル・公式入口・公式監査は変更していない。コードは87305debaに保存した。元の単位点の同じHom空間での同型までは本体で検証したが、この同型を元の全straighteningの評価と指定単位を通して全変換の一致へ接続する部分はまだ未完。R03h・R03d・3b-4aは未完のまま。

R03iの見込み450〜950行に対し、一般の判定202行・元のcosliceの零次元の式68行・元のnative単位点への適用160行の実測は計430行（下端より20行少ない）。この範囲の中間定理は閉じた。元の単位条件を満たす全空間の射を同じfiberへ戻す§279の95行は前回の検証済みで、この差分へ重ねて数えていない。

## 283. 同じ全straighteningの射と指定fiber評価の全自然性の照合（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 283.1 型と範囲

§282の同じnative単位点の比較は87305deba、§280〜282の報告は720c1893fに保存した。次に、元のleftStraighteningInfinityDiagramHomと元のleftStraighteningInfinityMapの同じ射の像の端点正規化を照合し、任意の底上の射について元のleftStraighteningInfinityMap_evaluateIsoの自然性を適用する。定義のidと二つのEq.mpの処理を分割し、同じ両端の等式をArrowの式で保持した。自然性は既存のNatIso.naturality_2を使い、元の指定評価同型を選び直していない。

以下は既存構成の係数移送・評価・自然性・合成則と証明の分割で、新しい数学のIDは追加しない。個別検査 /private/tmp/isw2-straightening-map-arrow.lean は9回目で終了コード0、出力なし。既存の型・計算上限は変更していない。新規三本はすべて200行未満。

#### FunctorHomEvaluationArrow（35行）

```lean
lemma functorHomEvaluate_arrow {K X : SSet.{u}} {U V : K ⟶ X}
    (a : FunctorHom U V) (x : K _⦋0⦌) :
    Arrow.mk (functorHomEvaluate a x) =
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := X) x)).toFunctor.map a)
```

#### LeftStraighteningDiagramHomArrow（60行）

```lean
lemma leftStraighteningInfinityDiagramHom_heq {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    HEq (leftStraighteningInfinityDiagramHom p q f hf)
      ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated))

lemma leftStraighteningInfinityDiagramHom_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    Arrow.mk (leftStraighteningInfinityDiagramHom p q f hf) =
      Arrow.mk ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated))
```

#### LeftStraighteningDiagramHomEvaluation（84行）

```lean
lemma leftStraighteningInfinityDiagramHom_evaluate_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b)) =
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b))).toFunctor.map
        ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)))

lemma leftStraighteningInfinityMap_fiberEvaluate_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk ((hoFunctor.map
      (leftStraighteningInfinityMap B ≫ evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b))).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)) =
      Arrow.mk (((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex p)).hom ≫
        (hoFunctor.map (leftFibrationInfinityFiberEvaluation b)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated) ≫
        ((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex q)).inv)

lemma leftStraighteningInfinityDiagramHom_fiber_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b)) =
      Arrow.mk (((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex p)).hom ≫
        (hoFunctor.map (leftFibrationInfinityFiberEvaluation b)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated) ≫
        ((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex q)).inv)
```

privateの係数移送の二補題の型：

```lean
private lemma straighteningHomEqMp_heq_iff {α β : Sort u} (h : α = β) (a : α)
    {γ : Sort _} (b : γ) : HEq (Eq.mp h a) b ↔ HEq a b

private lemma straighteningHomArrow_of_heq {D : Type u} [Category.{v} D]
    {a b a' b' : D} (ha : a = a') (hb : b = b')
    {f : a ⟶ b} {g : a' ⟶ b'} (h : HEq f g) : Arrow.mk f = Arrow.mk g
```

### 283.2 検収と残り

新規三本179行の対象ビルド351は成功（依存を含む3,107 jobs）。--class impl --wait 3600、一枚の整理券、gtimeout 1700秒で順番を待ち、対象ビルドと小監査を実行した。小監査は246モジュール・1,654宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。公開六補題・private二補題。自レーン累計242本・16,462行（外枠まで5,538行）、自レーン実環境1,647宣言。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と自レーン608ファイル・1,920個の名前を照合し、異なるファイル間の重複0、内部も0。git diff --check通過。証跡は /private/tmp/isw2-build351.log、isw2-validation351.json、isw2-declaration-collision-scan351.json。既存のLean・⑤aのファイル・公式入口・公式監査は変更していない。今回の結論は同じ全図式の射の評価について、元の指定評価同型とfiber評価の同じ射の像を結ぶ自然性の式。fiber評価の像を実際のvertexFiberMapへさらに合わせ、元の全native変換の分類同型の成分と指定単位を通す必要がある。これだけで全変換の一致やR03h・R03d・3b-4aを閉じたとはしない。

## 284. 元の全straighteningの射の評価と、同じ実際のfiber射の厳密な等式（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 284.1 型と範囲

§283の同じ全射の評価はf49a6d017に保存した。さらに元のleftFibrationInfinityFiberEvaluationの同じcoherentな辺の像を、実際のvertexFiberMapの同じcoherentな辺へ一致させた。元のleftStraighteningInfinityMap_evaluateIsoの同じ成分を既存の頂点の等式だけで正規化し、同じホモトピー圏の射の厳密な等式を回収する。

以下は既存の豊穣作用・評価・全自然性・係数移送・合成則と証明の分割であり、新しい数学のIDは足さない。個別検査 /private/tmp/isw2-fiber-evaluation-edge.lean は4回目で終了コード0、出力なし。頂点の等式の直接の項がwhnfの既定上限に達した箇所は、既存の評価の法則と元の頂点の等式へ分割し、評価の始域も明記して通した。計算上限・既存の型は変更していない。

#### LeftFibrationFiberEvaluationEdge（61行）

```lean
lemma leftFibrationInfinityFiberEvaluation_edge {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    (leftFibrationInfinityFiberEvaluation b).app (Opposite.op ⦋1⦌)
        (leftFibrationInfinityEdge p q f hf).edge =
      (coherentNerveEdge (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
          leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)).edge

lemma leftFibrationInfinityFiberEvaluation_hom_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk ((hoFunctor.map (leftFibrationInfinityFiberEvaluation b)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)) =
      Arrow.mk (HomotopyCategory.homMk (coherentNerveEdge
        (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
          leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)))
```

#### LeftStraighteningDiagramFiberComparison（55行）

```lean
lemma leftStraighteningInfinityDiagram_fiber_vertex {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    (leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up b) =
      (leftStraighteningInfinityMap B ≫ evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b)).app
        (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p)

def leftStraighteningInfinityDiagram_fiberIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    VertexIso ((leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up b))
      (coherentNerveVertex (leftFibrationFiberObject b (leftFibrationObjectOf p)))
```

#### LeftStraighteningDiagramFiberNaturality（79行）

```lean
lemma leftStraighteningInfinityDiagramHom_actualFiber_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b)) =
      Arrow.mk ((leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv)

lemma leftStraighteningInfinityDiagramHom_actualFiber_value {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b) =
      (leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv
```

privateの同じ合成の係数移送の型：

```lean
private lemma straighteningFiberArrow_conjugation {D : Type u} [Category.{v} D]
    {a b x y x' y' : D} (hx : x = x') (hy : y = y')
    (l : a ⟶ x) (r : y ⟶ b) (f : x ⟶ y) (g : x' ⟶ y')
    (h : Arrow.mk f = Arrow.mk g) :
    Arrow.mk (l ≫ f ≫ r) =
      Arrow.mk ((l ≫ eqToHom hx) ≫ g ≫ (eqToHom hy.symm ≫ r))
```

### 284.2 検収と残り

新規三本195行の対象ビルド352は成功（依存を含む3,111 jobs）。--class impl --wait 3600、一枚の整理券、gtimeout 1700秒。小監査は249モジュール・1,662宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。公開定義一つ・公開補題五つ・private補題一つ。自レーン累計245本・16,657行（外枠まで5,343行）、自レーン実環境1,655宣言。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と、自レーン611ファイル・1,926個の名前を照合し、異なるファイル間の重複0、内部も0。git diff --check通過。証跡は /private/tmp/isw2-build352.log、isw2-validation352.json、isw2-declaration-collision-scan352.json。既存Lean・⑤aのファイル・公式入口・公式監査は変更していない。次は元のstrictBETotJointSourceNativeTransformationの両側の元の分類同型を、この同じ評価の等式へ合成する。その分類同型の指定単位での実際の作用、局所化に沿う全前合成の充満忠実性とYoneda評価を通した全変換の一致はまだ未完。今回の任意の射についての評価の式を、その全変換の一致の代わりにはしない。R03h・R03d・3b-4aは未完のまま続ける。

## 285. 元の二変数native全変換の評価の式と、同じ全射の単位点の像（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 285.1 型と範囲

§284の元の全射の評価と実fiber射の厳密な等式は6f9d939f7に保存した。元のstrictBETotJointSourceNativeTransformationの定義へ、既存のfunctorHomEvaluate_compと同じ全straighteningの評価の等式を代入し、元の両側の分類同型を含む式を得る。さらに元の置換単位を保つ同じ全空間の射について、同じfiber単位・pullback同型・底の等式を通した元の単位点の像が、元の恒等点と同型になることを得た。

前者は任意のmとhmだけを扱う。後者のhuは元のexists_strictBETotJointSourceNativeLiftで保証される元の置換単位の条件そのもので、弱同値性や新しい単位保存条件を前提には足していない。これらは既存の評価・合成・単位・係数移送の法則とR03iの適用の分割であり、新しい数学のIDは追加しない。

個別検査は/private/tmp/isw2-native-transform-eval.leanが初回、/private/tmp/isw2-native-lift-unit-point.leanが2回目で終了コード0、出力なし。後者の初回は一時ファイルでcontinuousLeftFibrationReplacementUnitの名前空間が不足しており、明示して直した。計算上限・既存の型を変えていない。新規二本は200行未満。

#### StrictDiagramTotJointNativeTransformationEvaluation（68行）

```lean
lemma strictBETotJointSourceNativeTransformation_evaluate
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (P : strictBETotJointHomIndex A) :
    let p := (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
    let q := strictBETotJointNativeHomProjection A
    let b := nerveVertex P
    functorHomEvaluate (strictBETotJointSourceNativeTransformation A m hm) (ULift.up b) =
      functorHomEvaluate (strictBETotJointRawSourceElementsClassificationIso A).hom (ULift.up b) ≫
        (leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q m hm b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv ≫
        functorHomEvaluate (strictBETotJointNativeHomClassificationIso A).hom (ULift.up b)
```

#### StrictDiagramTotJointNativeLiftUnitPoint（77行）

```lean
lemma strictBETotJointSourceNativeLiftUnit_identityPoint
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).left ≫ m =
        strictBETotJointSourceNativeHomMap A) (X : (operad A).Algebra) :
    let P := strictBETotJointUnitIndex A X
    Nonempty (VertexIso
      ((strictBETotJointNativeUnitFiberIso A X).hom.app (Opposite.op ⦋0⦌)
        (((simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P ≫
          vertexFiberMap (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
            (strictBETotJointNativeHomProjection A) m hm (nerveVertex P) ≫
          (vertexFiberPullbackIso (twistedArrowProjection (CAlg_R A))
            (strictBETotJointNativeHomInput A) (nerveVertex P)).hom).app (Opposite.op ⦋0⦌)
              (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X)))))
      (twistedArrowHomSpaceIdentityPoint ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X)))))
```

### 285.2 検収と残り

新規二本145行の対象ビルド353は成功（依存を含む12,318 jobs）。--class impl --wait 3600、一枚の整理券、gtimeout 1700秒。小監査は251モジュール・1,669宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。公開二補題・局所instance五つ。自レーン累計247本・16,802行（外枠まで5,198行）、自レーン実環境1,662宣言。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と、自レーン613ファイル・1,928個の名前を照合し、異なるファイル間の重複0、内部も0。git diff --check通過。証跡は /private/tmp/isw2-build353.log、isw2-validation353.json、isw2-declaration-collision-scan353.json。既存のLean・⑤aのファイル・公式入口・公式監査は変更していない。次に残るのは、元のraw側の全分類同型が元のraw単位を同じfiber単位へ送り、元のnative側の全分類同型が同じ実fiberの恒等点へ合うことの、指定された元の成分での照合。さらに局所化に沿う全前合成の充満忠実性と既存のYoneda評価の全同値を使い、全変換の同じ射の一致へ戻す必要がある。R03hの全interval族、R03dの全関手同型と元の固定始域の同型の一致、3b-4aは未完のまま。今回の任意のmに対する式と元のmの単位点の同型を、その全変換の一致の代用にはしない。

## 286. 元の分類同型の順射と、同じ元の全射の像の照合（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 286.1 型と範囲

§285の元のnative全変換の評価と同じ全射の単位点の比較は389a5c352に保存した。raw側の全分類同型に現れるleftClassification_of_precompositionEquivalenceについて、その既存の順射が同じ元の射のleftStraighteningInfinityDiagramHomそのものであることを合わせ、同じ実fiberの評価の式へ接続した。定義が元の辺の類のasIsoを使っていることと、元の二つの頂点の等式を保持する。

以下は既存構成の係数移送・合成・評価の法則と証明の分割であり、新しい数学のIDは追加しない。個別検査 /private/tmp/isw2-classification-forward-hom.lean は2回目で終了コード0（unused simp引数id_eqの警告一件）。新規本体ではその未使用引数だけを外し、対象ビルド354で確かめる。計算上限・既存の型は変えていない。

#### ClassificationTransportHom（84行）

```lean
lemma leftClassification_of_precompositionEquivalence_value {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    HEq (leftClassification_of_precompositionEquivalence p q f hf ef)
      (VertexIso.map (leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p q f hf ef)
        (leftStraighteningInfinityMap B))

lemma leftClassification_of_precompositionEquivalence_hom {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    (leftClassification_of_precompositionEquivalence p q f hf ef).hom =
      leftStraighteningInfinityDiagramHom p q f hf

lemma leftClassification_of_precompositionEquivalence_fiber_value {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f)
    (b : B _⦋0⦌) :
    functorHomEvaluate (leftClassification_of_precompositionEquivalence p q f hf ef).hom (ULift.up b) =
      (leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv
```

privateの係数移送の型：

```lean
private lemma classificationTransportEqMp_heq_iff {α β : Sort u} (h : α = β) (a : α)
    {γ : Sort _} (b : γ) : HEq (Eq.mp h a) b ↔ HEq a b

private lemma classificationTransportIsoHom_heq {D : Type u} [Category.{v} D]
    {a b a' b' : D} (ha : a = a') (hb : b = b')
    (e : a ≅ b) (e' : a' ≅ b') (h : HEq e e') : HEq e.hom e'.hom
```

### 286.2 検収と残り

新規一本84行の対象ビルド354は成功（依存を含む3,117 jobs）。--class impl --wait 3600、一枚の整理券、gtimeout 1700秒。小監査は252モジュール・1,673宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。公開三補題・private二補題。自レーン累計248本・16,886行（外枠まで5,114行）、自レーン実環境1,666宣言。main a4388efc9のEInfinity/3,745ファイル・13,373個の名前と、自レーン614ファイル・1,931個の名前を照合し、異なるファイル間の重複0、内部も0。mainのInfinityCategories/にも今回の分類同型の追加名・actualFiber_value・functorHomEvaluate_arrowが宣言されていないことをgit grepで確認した。git diff --check通過。証跡は /private/tmp/isw2-build354.log、isw2-validation354.json、isw2-declaration-collision-scan354.json。既存Lean・⑤aのファイル・公式入口・公式監査は変更していない。コードは4139b0da4に保存した。これによりraw側のGrothendieckの二つの分類同型は、元の比較射の単位の厳密な式を使って実fiberで追える。残る重み付きnerveの標準単位とnativeな指定fiber評価との照合、native側の底変換同型の同じfiber同型への照合、全Yoneda評価・局所化の全前合成の充満忠実性による全変換の一致は、次の検査単位として維持する。R03h・R03d・3b-4aは未完。

## 287. 次の重み付きnerveの元の単位の評価：型の確認と残り（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 287.1 次の検査単位の型（未証明）

次は既存のweightedNerveNativeStraighteningUnitIsoの同じ順射と、元の指定fiber評価の同じ成分の合成を、元のweightedNerveFiberMapへ合わせる。次の型を/private/tmp/isw2-weighted-native-unit-fiber-type.leanで、等式そのものをPropとして定義して検査した。個別Leanは終了コード0、表示は関数の型だけで、証明は置いていない。本体・manifest・監査・済みの数には追加していない。

以下ではKanObjectはKerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC、kanDiagramCoherentNerve_vertexとkanObjectForgetはKerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes、weightedNerveProjection・weightedNerveFiberMapはKerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategoriesの既存の宣言。Fの値のKan性は(F.obj c).isKanComplexから局所instanceで供給し、新しい仮定にはしない。

```lean
lemma weightedNerveNativeStraighteningUnitIso_fiber_value
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    let p := weightedNerveProjection (F ⋙ kanObjectForget)
    functorHomEvaluate (weightedNerveNativeStraighteningUnitIso F).hom
        (ULift.up (nerveVertex c)) ≫
      (leftStraighteningInfinityDiagram_fiberIso p (nerveVertex c)).hom =
        eqToHom (congrArg HomotopyCategory.mk
          ((kanDiagramCoherentNerve_vertex F c).trans
            (spaceInfinityVertex_eq_coherent (F.obj c)))) ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show F.obj c ⟶ leftFibrationFiberObject (nerveVertex c)
              (leftFibrationObjectOf p) from
            weightedNerveFiberMap (F ⋙ kanObjectForget) c))
```

既存の単位・係数移送の法則の照合として、見込み250〜650行。これはこの重み付き単位の照合だけの見込みで、R03d以下の全残りの見込みではない。まだ既定の計算上限内での証明・本体化はしていない。

### 287.2 使う既存の元の比較と順序

1. leftStraighteningInfinityDiagram_representationIsoは、元のfirstVertex局所化の全前合成の充満忠実性で、同じ制限上の同型をpreimageVertexIsoとして戻している。まず同じpreimageの順射を制限して元の順射へ戻す法則を使い、零単体のfirstVertexで評価する。leftStraighteningInfinityMap_evaluateIsoも同じ零単体のfirstVertexFiberIsoから作られており、その同じ成分へ合わせる。
2. 同じnerveStraighteningRepresentationIsoとnerveCoherentTransportRepresentationIsoの評価を、元のstrict transportの評価へ合わせる。最後は既存のweightedNerveTransportUnit_evaluateが、標準単位とその評価の合成を元のweightedNerveFiberMapへ厳密に一致させる。
3. raw側ではtotalElementsNativeClassificationIsoの元の三因子を保持する。今回のleftClassification_of_precompositionEquivalence_hom・fiber_valueは、その中の二つのGrothendieckの分類同型を元の実射へ戻す入口。既存のgrothendieckKanCoefficientComparison_unitとsimplicialElementsGrothendieckReplacementMap_unitを使う。最初の三辺のmixed比較では、元の単位ラベルのaug₀・probe比較・右置換単位と、元のrightFrameReplacementUnitの自然性で同じ零単体を追う。
4. native側のstrictBETotJointNativeHomClassificationIsoは、元のleftStraighteningInfinityDiagram_baseChangeIsoの逆。その同じ成分を、元のvertexFiberPullbackIsoと同じ底の等式へ合わせる。元のmの単位点の像と元の恒等点の比較は§285で得ており、mの弱同値性は前提にしていない。
5. 全変換の一致には、モデル源の局所化に沿う全前合成の充満忠実性と、既存のcanonicalYonedaTransformationFiberEvaluation_isQCatEquivalenceおよび同じ指定恒等点の比較が候補になる。この既存の評価は任意の標的への全変換空間を扱う。共変のHom側へ移す際は、同じ反転・両端交換・IdentityCoordinatesの恒等点の式を保つ。ここには未検証の照合が残り、対象ごとの一致で代用しない。
6. R03hの元の全interval族の等式を維持し、元のnative fiber射自身の弱同値性、R03dの全関手同型と元の固定始域の同型のHEqを閉じる。その後はR02・R03→R04・R05→R11・R12のTotの分、停止点3b-4aの報告、実現R06〜R10の順。点つきKanのTotは作らない。

### 287.3 今回の検証済みの区切り

前回81e99bcecから新規16本・1,033行を検証して保存した。R03iの型は閉じたが、R03h・R03d・3b-4aは未完であり、停止点3b-4aの完了報告ではない。自レーンは248本・16,886行／外枠22,000行、残り5,114行。登録候補一覧はformalization-plans/stage-ii/inf-supply-b/is-w2-be-20261114-modules.jsonを更新済み。公式入口・公式監査への登録とmainへの取り込みは調整役が行うため、こちらでは変更していない。鍵は全て返却済み。/goalは元の全範囲を維持する。

## 288. 元の表現同型の前合成と零単体評価の法則（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。R03d・R03hは未完了。

§287の単位の評価の前提として、既存のfully faithfulな前合成の逆像が同じ指定同型へ戻る法則を先に切り出す。新しい構成・数学の一覧項目ではなく、既存構成の前合成・評価の法則と証明の分割。全FunctorIsoの等式を保持し、零単体でのArrowの等式はその帰結としてのみ使う。本体の対象ビルド・監査はこれから行う。

### FullyFaithfulFunctorIsoPrecomposition（59行）

```lean
lemma fullyFaithfulPreimageFunctorIso_precomp {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (hi : IsFullyFaithful ((pre i).app X))
    {F G : B ⟶ X} (e : FunctorIso (i ≫ F) (i ≫ G)) :
    FunctorIso.precomp (f := F) (g := G)
      (hi.preimageVertexIso (x := functorVertex F) (y := functorVertex G) e) i = e

lemma fullyFaithfulPreimageFunctorIso_evaluate {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (hi : IsFullyFaithful ((pre i).app X))
    {F G : B ⟶ X} (e : FunctorIso (i ≫ F) (i ≫ G)) (x : A _⦋0⦌) :
    functorHomEvaluate
      (hi.preimageVertexIso (x := functorVertex F) (y := functorVertex G) e).hom
      (i.app (Opposite.op ⦋0⦌) x) = functorHomEvaluate e.hom x

```

### TransportSimplexFirstVertexZero（48行）

```lean
lemma transportSimplexFirstVertexMap_ulift_zero_vertex {B : SSet.{u}} (b : B _⦋0⦌) :
    ((SSet.uliftFunctor.{u+1,u}).map (transportSimplexFirstVertexMap B)).app
      (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (transportSimplexIndex b))) = ULift.up b

```

### LeftStraighteningRepresentationRestriction（67行）

```lean
lemma leftStraighteningInfinityDiagram_representationIso_precomp {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    let k := transportSimplexFirstVertexMap B
    (leftStraighteningInfinityDiagram_representationIso p R).precomp
      ((SSet.uliftFunctor.{u+1,u}).map k) =
      leftStraighteningInfinityDiagram_firstVertexTransportIso p ≪≫
        nerveCoherentTransportRepresentationIso (pullback.snd p k) (R.nativeRestrict k)

lemma leftStraighteningInfinityDiagram_representationIso_precomp_evaluate {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p))
    (x : ((SSet.uliftFunctor.{u+1,u}).obj (nerve (TransportSimplexCategory B))) _⦋0⦌) :
    let k := transportSimplexFirstVertexMap B
    functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso p R).hom
      (((SSet.uliftFunctor.{u+1,u}).map k).app (Opposite.op ⦋0⦌) x) =
    functorHomEvaluate (leftStraighteningInfinityDiagram_firstVertexTransportIso p ≪≫
      nerveCoherentTransportRepresentationIso (pullback.snd p k) (R.nativeRestrict k)).hom x

```

### LeftStraighteningRepresentationZeroEvaluation（54行）

```lean
lemma leftStraighteningInfinityDiagram_representationIso_zero_evaluate_arrow {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) (b : B _⦋0⦌) :
    let k := transportSimplexFirstVertexMap B
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso p R).hom
      (ULift.up b)) =
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagram_firstVertexTransportIso p ≪≫
      nerveCoherentTransportRepresentationIso (pullback.snd p k) (R.nativeRestrict k)).hom
        (ULift.up (nerveVertex (transportSimplexIndex b))))

```

### 288.5 検収と残り

4本・6補題・229行を本体に追加。初回の対象ビルド355は、分割先のProject.FibrationAuxiliaries.FunctorCategoriesのopen不足で失敗し、当該openを補った。再検査355bは共有鍵 --class impl --wait 3600 と1700秒guardを一回使用し、対象4本のビルド（依存を含む3,105 jobs）・小監査とも終了0。小監査は256モジュール・1,679宣言、propext・Classical.choice・Quot.soundのみ。sorryAx・追加公理なし。既存Lean宣言は変更していない。

累計は252モジュール・17,115行（外枠22,000行まで4,885行）、自レーンの実環境宣言は1,672。公式の入口・root・監査への登録はしていない。登録対象はis-w2-be-20261114-modules.jsonに追加した4本。宣言名の照合ではmain a4388efc9のEInfinity/3,745ファイル・13,373名と、自レーン618ファイル・1,937名の間に異なるファイルの同名宣言0、自レーン内部も0。genericな新規6名は今回の元の構成の前合成・評価則である。

証跡：/private/tmp/isw2-build355b.log、AuditISW2BKCells355.lean、isw2-validation355.json、isw2-declaration-collision-scan355.json。git diff --check通過。B4′の結果は§268のまま（統合81683a2ab、書換え0・保留0）。

この検収で§287の重み付きnative単位の実fiber評価の等式そのものを閉じたとはしない。今回の前合成の全FunctorIso等式を使い、同じ表現空間の同じ指定同型と、元のfirstVertexFiberIso・fiber評価への輸送をつなぐ段が残る。R03hの全interval族の等式・R03dの指定全関手同型・3b-4aは未完了。型・範囲を弱めず、⑤aの既存ファイルは変更していない。

## 289. 元のnative単位の自己比較の消去と、同じ全表現同型との合成（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

既存のsmallFiberTransportRepresentationVertexIso_uniqueを使い、同じ表現を自分自身と比較する同型は恒等であることを示す。それを元のnerve比較へ写し、元のnative単位を元のstrict単位・opposite比較・同じ表現同型の逆の合成へ正規化する。新しい数学の項目ではなく、既存構成の単位・合成・評価の法則と証明の分割。§287の実fiber評価の等式は、この正規化だけではまだ得られない。全FunctorIsoの等式を保つ。

#### TransportRepresentationSelfComparison（62行）

```lean
lemma smallFiberTransportRepresentationVertexIso_self {E B : SSet.{u+1}} (p : E ⟶ B) [LeftFibration p]
    (hp : HasSmallSimplexFibers p) (R : LeftTransportRepresentation p) :
    smallFiberTransportRepresentationVertexIso p hp R R = Iso.refl (HomotopyCategory.mk (transportWitnessVertex R))

lemma smallFiberTransportRepresentationDiagramIso_self {E B : SSet.{u+1}} (p : E ⟶ B) [LeftFibration p]
    (hp : HasSmallSimplexFibers p) (R : LeftTransportRepresentation p) :
    smallFiberTransportRepresentationDiagramIso p hp R R = Iso.refl (HomotopyCategory.mk (functorVertex R.diagram))

lemma nerveCoherentTransportRepresentationIso_self {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    nerveCoherentTransportRepresentationIso p (nerveLeftTransportRepresentation p) =
      Iso.refl (HomotopyCategory.mk (functorVertex (leftCoherentTransport p)))

lemma nerveStraighteningRepresentationIso_self {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    nerveStraighteningRepresentationIso p (nerveLeftTransportRepresentation p) =
      leftStraighteningCoherentMap_oppositeVertexIso p
```

#### NativeNerveUnitNormalization（85行）

```lean
lemma leftStraighteningInfinityDiagram_nerveCandidateIso_normalized {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    leftStraighteningInfinityDiagram_nerveCandidateIso p =
      leftStraighteningInfinityDiagram_representationIso p (nerveLeftTransportRepresentation p) ≪≫
        (leftStraighteningCoherentMap_oppositeVertexIso p).symm

lemma weightedNerveNativeStraighteningUnitIso_normalized {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedNerveNativeStraighteningUnitIso F =
      weightedNerveStraighteningUnitIso F ≪≫
        leftStraighteningCoherentMap_oppositeVertexIso (weightedNerveProjection (F ⋙ kanObjectForget)) ≪≫
        (leftStraighteningInfinityDiagram_representationIso
          (weightedNerveProjection (F ⋙ kanObjectForget))
          (nerveLeftTransportRepresentation (weightedNerveProjection (F ⋙ kanObjectForget)))).symm

lemma weightedNerveNativeStraighteningUnitIso_trans_representationIso {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedNerveNativeStraighteningUnitIso F ≪≫
      leftStraighteningInfinityDiagram_representationIso
        (weightedNerveProjection (F ⋙ kanObjectForget))
        (nerveLeftTransportRepresentation (weightedNerveProjection (F ⋙ kanObjectForget))) =
    weightedNerveStraighteningUnitIso F ≪≫
      leftStraighteningCoherentMap_oppositeVertexIso (weightedNerveProjection (F ⋙ kanObjectForget))

lemma weightedNerveNativeStraighteningUnitIso_representation_evaluate {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    functorHomEvaluate (weightedNerveNativeStraighteningUnitIso F).hom
        (ULift.up (nerveVertex c)) ≫
      functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso
        (weightedNerveProjection (F ⋙ kanObjectForget))
        (nerveLeftTransportRepresentation (weightedNerveProjection (F ⋙ kanObjectForget)))).hom
        (ULift.up (nerveVertex c)) =
    functorHomEvaluate (weightedNerveStraighteningUnitIso F).hom (ULift.up (nerveVertex c)) ≫
      functorHomEvaluate (leftStraighteningCoherentMap_oppositeVertexIso
        (weightedNerveProjection (F ⋙ kanObjectForget))).hom (ULift.up (nerveVertex c))
```

### 289.3 検収と残り

新規2本147行、公開8補題・局所instance一つ。対象ビルド356（依存を含む3,105 jobs）と小監査はともに終了0。鍵は --class impl --wait 3600、一枚の整理券でビルド・監査の間だけ使用、gtimeout 1700秒。小監査は258モジュール・1,688宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。git diff --check通過。main a4388efc9のEInfinity/3,745ファイル13,373名と、自レーン620ファイル1,945名の照合で異なるファイルの同名宣言0、内部も0。証跡は/private/tmp/isw2-build356.log、isw2-validation356.json、isw2-declaration-collision-scan356.json。

累計254本・17,262行、実環境1,681宣言。外枠22,000行まで4,738行。登録候補の一覧is-w2-be-20261114-modules.jsonに2本を追加した。既存のLean宣言・⑤aのファイル・公式入口・公式監査は変更していない。§288の4本は70d5f311bに保存済み。

元のnative単位に同じ表現同型を後合成すると、元のstrict単位とopposite比較の合成へ厳密に戻る。この全FunctorIsoの等式とその評価は閉じた。一方、§287の右辺にある実weightedNerveFiberMapのホモトピー類との等式は未証明。nerveLeftTransportRepresentationのcomparisonはleftCoherentTransportDirectComparisonであり、その公開の存在命題は底上の射と前合成同値性を与える。自己単位則から、この射が元のstrict transport評価と一致するとは推論しない。同じ指定された比較と同じfiber評価との両立を示す工程が残る。

次は今回の正規化を使い、元のfirstVertex制限・同じ表現比較・実fiber評価の式を照合する。R03hの同じnative fiber射と元の固定始域のroofの全interval族の等式も維持する。点の同型や今回の自己単位則で全族の等式を代用しない。R03d・R03hと3b-4aは未完で、停止点3b-4aの報告ではない。新しい仮定や界面の変更は追加していない。

## 290. 同じcoslice・pinched・edgewise三角形の全interval族での移送（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

R03hの全パラメータの式を進めるため、既存のcosliceFiberRightMappingEquivalenceとtwistedArrowHomPinchedEquivalence_coslice、同じedgewise三角形の指定同型を、任意のKを始域とする全interval族の等式へ移す。既存構成の単位三角形・係数移送の法則であり、新しい数学の一覧項目は増やさない。FunctorIsoから同じ実ホモトピーを取り、既存のintervalFamilyHom_eq_of_homotopyへ渡す。Kの準圏性・単体集合のモデル構造・点ごとの等式から全族への推論は使わない。

#### TwistedHomIntervalFamilyComparison（70行）

```lean
lemma cosliceFiberRightMappingEquivalence_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (f : K ⟶ vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) :
    intervalFamilyHom (f ≫ (cosliceFiberRightMappingEquivalence x y).hom ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (f ≫ cosliceFiberToIntervalMappingSpace x y)

lemma twistedArrowHomPinchedEquivalence_coslice_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (f : K ⟶ vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) :
    intervalFamilyHom (f ≫ cosliceTwistedHomMap x y ≫
      (twistedArrowHomPinchedEquivalence x y).hom ≫ pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (f ≫ cosliceFiberToIntervalMappingSpace x y)

lemma twistedArrowHomPinchedEquivalence_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (g : K ⟶ twistedArrowHomSpace x y) :
    intervalFamilyHom (g ≫ (twistedArrowHomPinchedEquivalence x y).hom ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (g ≫ (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y)

lemma twistedArrowHomOppositePinchedEquivalence_edgewise_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (g : K ⟶ edgewiseSubdivision (twistedArrowHomSpace x y)) :
    intervalFamilyHom (g ≫ edgewiseLeft (twistedArrowHomSpace x y) ≫
      (twistedArrowHomOppositePinchedEquivalence x y).hom ≫ pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (g ≫ edgewiseRight (twistedArrowHomSpace x y) ≫
        (twistedArrowHomPinchedEquivalence x y).hom ≫ pinchedHomToIntervalMappingSpace x y)
```

今回の四式は同じ指定逆と比較射を保持する。元のnative射を同じcoslice側の全族へ送り、元のroofの全族と照合する工程はまだ残る。R03h・R03d・3b-4aの完了とはしない。

### 290.2 検収と残り

新規1本70行・公開4補題。対象ビルド357（依存を含む2,287 jobs）と小監査はともに終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒。小監査は259モジュール・1,697宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。新規モジュールの実環境宣言は8。従来モジュールTwistedHomPinchedComparisonの環境宣言はimport閉包の変化で15から16となり、ソースの追加4補題を監査の宣言増分9とは同一視していない。既存Leanのソースは変更していない。

累計255本・17,332行、実環境1,690宣言。外枠22,000行まで4,668行。main a4388efc9のEInfinity/3,745ファイル13,373名と自レーン621ファイル1,949名を照合し、異なるファイルの同名宣言0、内部も0。git diff --check通過。公式入口・公式監査は変更せず、登録候補の一覧is-w2-be-20261114-modules.jsonに1本を追加した。証跡：/private/tmp/isw2-build357.log、isw2-validation357.json、isw2-declaration-collision-scan357.json。§289の2本は0c24adfd9に保存済み。

元の反対twisted Homの任意の族について、同じedgewiseLeftの指定逆とedgewiseRight・同じcoslice比較の指定逆を使う一本の式へまとめる前提計算も一時ファイルで検査中。これを元のnative射へ適用し、同じcorrected pairingと元のroofの全族を比較する工程が残る。R03h・R03d・3b-4aの完成とはしない。今回の全Kの等式は点ごとの等式を代用せずに既存の三角形を移送したものである。目標の型・範囲と外枠は維持する。

## 291. 元のnative射の全interval族を同じ指定逆の一本の式へ戻す次の検査単位（2026-11-15、個別検査）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§290の次に、同じedgewiseLeftの指定逆・edgewiseRight・同じcoslice比較の指定逆を、一つの全interval族の式へ合成する。一般の反対twisted Homでの式は/private/tmp/isw2-opposite-interval-family.leanの個別検査2で終了0（名前空間Equivalenceのopenを追加して再検査）。本体のモジュールにはまだ追加しておらず、§290の検証済み255本・17,332行の数は増やさない。

その式を元のstrictBETotJointSourceNativePinchedMapへ適用する型も次のとおり。新しい数学ではなく、元の既存比較射の定義と同じ指定三角形の係数移送である。元の射を別の同値へ置き換えない。モデル源の両端の定義的簡約を大きなsimpでまとめて扱うと型の照合に失敗したため、元のnative pinched射の定義からの等式hmapをrflで切り出し、その後で全族の法則を適用する形へ証明を分けた。計算上限は上げていない。

以下は本体で検証済みの新規宣言ではなく、次の個別検査の型案。最後のBEへの適用は/private/tmp/isw2-native-pinched-interval-family.leanの検査4（ハンドル28748）で検査中。対象ビルド・小監査・ソースのコミットはまだであり、成功したとは記録しない。

```lean
lemma twistedArrowHomOppositePinchedEquivalence_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (g : K ⟶ (twistedArrowHomSpace x y).op) :
    intervalFamilyHom (g ≫ (twistedArrowHomOppositePinchedEquivalence x y).hom ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (g ≫ (isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y)

lemma strictBETotJointSourceNativePinchedMap_interval_family_normalization (P : strictBETotJointHomIndex A) :
    let x := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop))
    let y := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
    let e := SSet.opFunctor.mapIso (eqToIso
      (congrArg (fun b => vertexFiber (twistedArrowProjection (CAlg_R A)) b)
        (strictBETotJointNativeHomInput_model_vertex A P)))
    intervalFamilyHom (strictBETotJointSourceNativePinchedMap A P ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (strictBETotJointSourceNativeOppositeFiberMap A P ≫ e.hom ≫
        (isQCatEquivalence_of_trivialKanFibration (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y)
```

次はこの元のnative射の同じ全族を、同じcorrected pairingの全族へ戻し、§269以降の元のroofのaugmentation・評価・標的置換の全族の式と照合する。R03hの最終の全interval族の等式と、元の実射自身の弱同値性は未証明。R03dと3b-4aの残りも維持する。今回の既存構成の移送の法則を、新しい数学の完成や停止点3b-4aとは数えない。§289・§290の検証済みコードは0c24adfd9・6c1483d21に保存した。作業木に未検証のLeanは追加していない。

## 292. 元の射の定義式と、反対twisted Homの全族の合成則を分割（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§291の個別検査4は、BEへの全族の適用の宣言でkernel deterministic timeoutとなった。上限は変更していない。元のnative射の定義式だけを独立した補題へ分けた検査isw2-native-pinched-formula1は終了0。その補題を同じファイルの後続の全族の式で使う検査split1も後続の宣言でkernel deterministic timeoutとなった。

次に任意の合成f≫hに対する汎用の移送則を分割した。大きなBEのimportを含む一時ファイルでは汎用のrwの証明自体がkernel deterministic timeoutになったが、BEをimportせず、等式hhをsubstで消去してから結合則だけを使う形へ分けたisw2-opposite-interval-family-composed1は終了0。BEの既存instanceを使う方も検査したが、失敗箇所は同じ旧汎用rwの補題だった。次の2モジュールに独立させて対象ビルド・小監査を行い、その検証済み汎用補題をimportしてBEへの適用を検査する。全て既存構成の係数移送・合成則と証明の分割で、新しい数学の一覧項目は追加しない。§291の元の全族の型は維持する。

#### TwistedHomOppositeIntervalFamilyComparison（57行）

```lean
lemma twistedArrowHomOppositePinchedEquivalence_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (g : K ⟶ (twistedArrowHomSpace x y).op) :
    intervalFamilyHom (g ≫ (twistedArrowHomOppositePinchedEquivalence x y).hom ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (g ≫ (isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y)

lemma twistedArrowHomOppositePinchedEquivalence_interval_family_comp {K T C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (f : K ⟶ T) (e : T ⟶ (twistedArrowHomSpace x y).op)
    (h : T ⟶ Basic.pinchedHom x y)
    (hh : h = e ≫ (twistedArrowHomOppositePinchedEquivalence x y).hom) :
    intervalFamilyHom ((f ≫ h) ≫ pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (f ≫ e ≫ (isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y)
```

#### StrictDiagramTotJointSourceNativePinchedFactorization（49行）

```lean
lemma strictBETotJointSourceNativePinchedMap_factorization (P : strictBETotJointHomIndex A) : strictBETotJointSourceNativePinchedMap A P =
      strictBETotJointSourceNativeOppositeFiberMap A P ≫
        (SSet.opFunctor.mapIso (eqToIso
          (congrArg (fun b => vertexFiber (twistedArrowProjection (CAlg_R A)) b)
            (strictBETotJointNativeHomInput_model_vertex A P)))).hom ≫
        (twistedArrowHomOppositePinchedEquivalence
          ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
            (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
          ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
            (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))).hom
```

### 292.3 検収

2本106行、公開3補題・局所instance二つ。対象ビルド358は依存を含む12,251 jobsで成功、小監査も終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルド・小監査の間だけ使用。小監査は261モジュール・1,703宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計257本・17,438行、実環境1,696宣言。外枠22,000行まで4,562行。git diff --check通過。main a4388efc9のEInfinity/3,745ファイル13,373名と自レーン623ファイル1,952名を照合し、異なるファイル間の重複0、内部も0。既存Lean・⑤aのファイル・公式入口・公式監査は変更していない。証跡は/private/tmp/isw2-build358.log、isw2-validation358.json、isw2-declaration-collision-scan358.json。

対象ビルド済みの汎用モジュールをimportし、元のnative側の既存instanceを再利用する一時ファイルisw2-native-pinched-interval-imported1は終了0。§291の元のnative射の全interval族の正規化という同じ型が個別検査を通った。単一ファイルに汎用補題の証明も展開した検査とは区別する。計算上限は上げず、次に本体へ配置して対象ビルド・小監査を行う。R03hのroofとの最終等式・R03d・3b-4aは未完。

## 293. 元のnative射自身の全interval族の正規化を本体へ（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§291の型を弱めずに本体へ配置する。§292の検証済みの汎用合成則をimportし、元のnative pinched射を同じ因子の合成として代入する。新しい数学の項目ではなく、同じ指定比較の定義・合成・係数移送の法則。§292のコードはef0c24e9bに保存済み。

#### StrictDiagramTotJointSourceNativeIntervalFamily（76行）

```lean
lemma strictBETotJointSourceNativePinchedMap_interval_family_normalization (P : strictBETotJointHomIndex A) :
    let x := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop))
    let y := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
    let e := SSet.opFunctor.mapIso (eqToIso
      (congrArg (fun b => vertexFiber (twistedArrowProjection (CAlg_R A)) b)
        (strictBETotJointNativeHomInput_model_vertex A P)))
    intervalFamilyHom (strictBETotJointSourceNativePinchedMap A P ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (strictBETotJointSourceNativeOppositeFiberMap A P ≫ e.hom ≫
        (isQCatEquivalence_of_trivialKanFibration (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y)
```

R03hの右辺の元のroofの全族との最終等式はまだ得られていない。元の射自身の弱同値性やR03dの全関手同型の検収とは区別する。

### 293.2 検収

新規1本76行・公開1補題。§291の元のnative射自身についての全interval族の正規化の同じ型を閉じた。対象ビルド359（依存を含む12,251 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用した。カーネル・heartbeat・再帰の上限は変更していない。小監査は262モジュール・1,701宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。

新規モジュールの実環境宣言は1。import閉包の変化によりTwistedHomIntervalFamilyComparisonの環境宣言は8→6、TwistedHomPinchedComparisonは16→15となり、監査合計は1,703→1,701。両モジュールのLeanソースは変更しておらず、新規宣言数と監査増減を同一視しない。自レーン累計258本・17,514行、実環境1,694宣言。外枠22,000行まで4,486行。main a4388efc9のEInfinity/3,745ファイル13,373名と自レーン624ファイル1,953名を照合し、異なるファイル間の同名宣言0、内部も0。git diff --check通過。

既存のLean宣言・⑤aのファイル・公式入口・公式監査は変更していない。登録候補の一覧is-w2-be-20261114-modules.jsonに追加した。証跡：/private/tmp/isw2-build359.log、isw2-validation359.json、isw2-declaration-collision-scan359.json。全ての鍵は返却済み。

### 293.3 R03hに残る全族の照合

今回閉じた正規化の右辺は、元の反対fiber射に、同じ入力頂点の等式のop輸送、同じedgewiseLeftの指定逆、edgewiseRight、同じcoslice比較の指定逆、cosliceの区間比較を順に合成した全族である。残るR03hは、この同じ全族のintervalFamilyHomを、strictBETotJointSourceRoofNormalizedPinchedComparisonの全族のintervalFamilyHomと同定すること。既存の正規化を使って左辺を戻せるが、右辺の元のroofとの等式はまだ証明していない。

次の証明では、元のstrictBETotJointSourceFiberPairingIsoとその全射影の等式を保持して、正規化されたnative全族を元のaugmentation・評価・標的置換の全族へ接続する。roof側では§269以降のNerveColumnのaugmentation逆と評価の全族の式、元の局所化の全三角形とのroof_naturality、pinchedEndpointEquivalence_familyによる同じ両端の輸送を使う。元のcorrected pairingの一つの頂点の類の一致だけで、この全族の等式を推論しない。§287のより強い重み付きnative単位のfiber値の式を、未証明のまま使用しない。

局所化の全三角形の消去に使う、次の既存構成の自然性の共役式は一時ファイルisw2-column-roof-conjugation1で個別検査・終了0。まだ本体のモジュールには追加しておらず、上の累計行数には含めない。既存のNerveColumn.roof_naturalityの左端の指定同型を反転して移しただけの法則である。

```lean
lemma sameColumnRoofConjugation {I C : Type u} [Category.{u} I] [Category.{u} C]
    {E : SSet.{u}} [Quasicategory E] {F G : nerve C ⟶ E} (e : FunctorIso F G)
    (V : I ⥤ C) {X Y : C} (p : V ⟶ (Functor.const I).obj X)
    (hpF : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)
    (hpG : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map G).toTruncated)
    (s : V ⟶ (Functor.const I).obj Y) :
    (e.precomp (nerveMap ((Functor.const I).obj X))).inv ≫
      (NerveColumn.augmentationIso F V p hpF).inv ≫ NerveColumn.hom F s ≫
      (e.precomp (nerveMap ((Functor.const I).obj Y))).hom =
      (NerveColumn.augmentationIso G V p hpG).inv ≫ NerveColumn.hom G s
```

R03h・R03d・3b-4aは未完。一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。停止点3b-4aの検収とはせず、R03d→R02・R03→R04・R05→R11・R12のTotの分、停止点の報告後に実現R06〜R10という元の範囲・順序を維持する。

## 294. 元の全局所化三角形によるroof共役と同じ定値族の成分（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§293.3のroof側の工程。既存のNerveColumn.roof_naturalityから元の全三角形の共役を求め、元の定値通常図式への制限を同じ指定成分の定値族へ戻す。sameFunctorIso_constant_familyの既存の合成同型はeqToIsoなので、全FunctorHomのArrowとして端点の等式を保持したまま元の成分へ正規化できる。任意のnerve I全体で述べ、一つの頂点での評価は使わない。新しい数学の一覧項目ではなく、既存構成の自然性・係数移送・合成の法則と証明の分割である。

最後のroof共役則に現れるhaは、元のroofのintervalFamilyHomが既存のNerveColumnの全roofと一致するという入力。その入力には既存のstrictBETotJointSourceRoofPinchedComparison_column_roofを代入する予定で、使う側の不足する比較を仮定に移す入口ではない。型つき一覧のR03h・R03dを弱めない。個別検査isw2-column-roof-constant3は終了0（前の検査2の合成の括弧の型不一致を結合則で修正）。以下を本体へ置いて対象ビルド・小監査を行う。

#### NerveColumnRoofTransport（83行）

```lean
lemma roof_conjugation {I C : Type u} [Category.{u} I] [Category.{u} C]
    {E : SSet.{u}} [Quasicategory E] {F G : nerve C ⟶ E} (e : FunctorIso F G)
    (V : I ⥤ C) {X Y : C} (p : V ⟶ (Functor.const I).obj X)
    (hpF : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)
    (hpG : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map G).toTruncated)
    (s : V ⟶ (Functor.const I).obj Y) :
    (e.precomp (nerveMap ((Functor.const I).obj X))).inv ≫
      (NerveColumn.augmentationIso F V p hpF).inv ≫ NerveColumn.hom F s ≫
      (e.precomp (nerveMap ((Functor.const I).obj Y))).hom =
      (NerveColumn.augmentationIso G V p hpG).inv ≫ NerveColumn.hom G s

lemma constantRestriction_iso_arrow {I C : Type u} [Category.{u} I] [Category.{u} C]
    {E : SSet.{u}} [Quasicategory E] {F G : nerve C ⟶ E} (e : FunctorIso F G) (c : C) :
    Arrow.mk (e.precomp (nerveMap ((Functor.const I).obj c))).hom =
      Arrow.mk (constantFunctorHomMap (nerve I) (e.app (nerveVertex c)).hom)

lemma constantRestriction_iso_inv_arrow {I C : Type u} [Category.{u} I] [Category.{u} C]
    {E : SSet.{u}} [Quasicategory E] {F G : nerve C ⟶ E} (e : FunctorIso F G) (c : C) :
    Arrow.mk (e.precomp (nerveMap ((Functor.const I).obj c))).inv =
      Arrow.mk (constantFunctorHomMap (nerve I) (e.app (nerveVertex c)).inv)

lemma roof_constant_conjugation_arrow {I C : Type u} [Category.{u} I] [Category.{u} C]
    {E : SSet.{u}} [Quasicategory E] {F G : nerve C ⟶ E} (e : FunctorIso F G)
    (V : I ⥤ C) {X Y : C} (p : V ⟶ (Functor.const I).obj X)
    (hpF : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)
    (hpG : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map G).toTruncated)
    (s : V ⟶ (Functor.const I).obj Y)
    (a : FunctorHom (SSet.const (F.app (Opposite.op ⦋0⦌) (nerveVertex X)) : nerve I ⟶ E)
      (SSet.const (F.app (Opposite.op ⦋0⦌) (nerveVertex Y))))
    (ha : Arrow.mk a = Arrow.mk ((NerveColumn.augmentationIso F V p hpF).inv ≫ NerveColumn.hom F s)) :
    Arrow.mk (constantFunctorHomMap (nerve I) (e.app (nerveVertex X)).inv ≫ a ≫
      constantFunctorHomMap (nerve I) (e.app (nerveVertex Y)).hom) =
      Arrow.mk ((NerveColumn.augmentationIso G V p hpG).inv ≫ NerveColumn.hom G s)
```

この検収だけでnative側とroof側の全族の最終等式や3b-4aを完成としない。

### 294.2 検収

新規1本83行・公開4補題。対象ビルド360（依存を含む7,217 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒。小監査は263モジュール・1,706宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計259本・17,597行、実環境1,699宣言。外枠22,000行まで4,403行。新規モジュールの実環境宣言は5。git diff --check通過。main a4388efc9のEInfinity/3,745ファイル13,373名と自レーン625ファイル1,957名を照合し、異なるファイル間の重複0、内部も0。証跡：/private/tmp/isw2-build360.log、isw2-validation360.json、isw2-declaration-collision-scan360.json。既存Lean・⑤aのファイル・公式入口・公式監査は変更していない。

既存のstrictBETotJointSourceRoofPinchedComparison_column_roofを実際にhaへ代入したBEでの適用も、一時ファイルisw2-roof-native-column2で終了0。最初の検査ではpinchedEndpointEquivalence_familyの推論された終点がHoの関手値から取り出した頂点となり、元のモデル源の指定頂点との型照合に失敗した。x'・y'を元の二つの指定頂点に明示して直した。対象ビルド済みの汎用補題をimportする形で、全局所化三角形を消去して元のnativeな底の全augmentation逆・評価へ戻せた。次に本体へ配置し、対象ビルド・小監査を行う。R03hのnative射側との最終等式・R03d・3b-4aは未完。

## 295. 元のroof比較の全局所化三角形の消去と指定された両端への全族の輸送（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§294の汎用則を実際に適用する。元のstrictBETotJointSourceRoofPinchedComparison_column_roofを、そのままhaへ代入する。元の全局所化三角形c.triangleと、元のpinchedEndpointEquivalence_familyを使うと、元のroofNativePinchedComparisonの全interval族は、同じnativeモデル源の元のframe augmentationの逆と元の評価の像へ戻る。さらに元のprobe・標的置換の指定同型で両端を戻す全族の等式を得る。これは既存構成の自然性・係数移送・合成の法則で、数学の一覧項目は増やさない。

個別検査isw2-roof-native-column2とisw2-roof-native-normalized-family1は終了0。前者の初回の型の不一致はpinchedEndpointEquivalence_familyのx'・y'を元のモデル源の指定頂点に明示して修正。§294の検証済みコードは1bdf91594に保存した。次の三宣言を本体へ配置し、対象ビルド・小監査を行う。

#### StrictDiagramTotJointSourceRoofNativeFamily（98行）

```lean
lemma strictBETotJointSourceRoofFrameAugmentation_inverted (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    IsInvertibleEdge ((nerve.edgeMk
      ((strictBETotJointSourceRoofFrameAugmentation A P).app s)).map
      (strictBETotModelSource A)).toTruncated

lemma strictBETotJointSourceRoofNativePinchedComparison_column_roof (P : strictBETotJointHomIndex A) :
    Arrow.mk (intervalFamilyHom (strictBETotJointSourceRoofNativePinchedComparison A P ≫
      pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk ((NerveColumn.augmentationIso (strictBETotModelSource A)
      (strictBETotJointSourceRoofFrameDiagram A P)
      (strictBETotJointSourceRoofFrameAugmentation A P)
      (strictBETotJointSourceRoofFrameAugmentation_inverted A P)).inv ≫
      NerveColumn.hom (strictBETotModelSource A)
        (strictBETotJointSourceRoofFrameEvaluation A P))

lemma strictBETotJointSourceRoofNormalizedPinchedComparison_interval_family (P : strictBETotJointHomIndex A) :
    let K := nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ
    intervalFamilyHom (strictBETotJointSourceRoofNormalizedPinchedComparison A P ≫
      pinchedHomToIntervalMappingSpace _ _) =
      constantFunctorHomMap K (strictBETotJointRoofProbeEndpointIso A P).inv ≫
        intervalFamilyHom (strictBETotJointSourceRoofNativePinchedComparison A P ≫
          pinchedHomToIntervalMappingSpace _ _) ≫
        constantFunctorHomMap K (strictBETotJointRoofTargetEndpointUnitIso A P).inv
```

元のnative fiber射とこの同じroofの全族の最終等式R03hは、まだ未証明である。今回の右辺側の照合だけで元のnative射自身の弱同値性・R03d・3b-4aを完成とはしない。

### 294.3 既存の同趣旨の補題を再利用し、自レーンの未取り込みの重複を撤回（§295の検査後）

次の照合のため定値自然変換の既存宣言を調べたところ、mainに既存のPowerOperation/NerveColumnRoofConjugation.leanのSerrePositivity.EInfinity.PowerOperation.nerveColumnRoofConjugation_arrow、およびNerveColumnConstantRestriction.leanのnerveColumnConstantRestriction_arrowがあることを確認した。今回追加したNerveColumnRoofTransportの一般のaの版と同趣旨だが、今回のBE適用は実pinched族fを持つため、既存のfの版で足りる。発見時にチャットで報告した。⑤aの既存ファイルは変更せず、既存宣言を完全修飾名で再利用する形を検査した。

このworktreeに既存のoleanがなかったため、共有鍵 --class impl --wait 3600と1700秒guardで当該既存1モジュールだけ対象ビルドし、7,224 jobsで成功（isw2-build362-existing-transport.log）。次の個別検査isw2-roof-native-existing-transport2は終了0。functorIsoEvaluate_eq_appで既存の同じ成分の表記を揃えただけで、BEの三宣言の型は全く同じまま。変更前後の主張の型の文字列も照合した。

1bdf91594の自レーンの新規NerveColumnRoofTransport.leanはmainに存在せず、公式登録もないことを確認した。同ファイルを使う本体のimporterは今回の未コミットのBE新規ファイルだけ。この自レーンの83行・4補題を撤回し、登録候補一覧から外した。mainの既存宣言は一つも変更・削除していない。過去の§294の対象ビルド・監査の結果はその時点の検証の履歴であり、最終の登録候補にはこの汎用ファイルを含めない。

### 295.2 最終の依存を既存の補題へ変更した検査

変更前の361対象ビルド・監査はともに終了0（12,256 jobs、264モジュール・1,708宣言、標準三公理のみ）。証跡isw2-validation361.jsonは変更前のソースのSHA256を持つ。最終の依存では当該自レーン汎用ファイルを使わず、既存PowerOperationの同趣旨の宣言を直接使う。BEの三宣言の型を保ったまま、362対象ビルドと小監査を行う。登録候補の正本は更新したis-w2-be-20261114-modules.json。

### 295.3 最終の依存での検収

既存のPowerOperation.nerveColumnRoofConjugation_arrowを再利用する最終ソースの362対象ビルド（依存を含む12,255 jobs）・小監査はともに終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用。小監査は263モジュール・1,704宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。最終の新規BEモジュールは98行・公開3補題・実環境宣言3。全て元の実roofと同じ指定局所化三角形・同じ両端同型を使い、全パラメータのintervalFamilyHomを扱う。

未取り込みの汎用83行を撤回した最終の自レーンは259本・17,612行、実環境1,697宣言。外枠22,000行まで4,388行。登録候補のis-w2-be-20261114-modules.jsonはこの最終ソースの259本。mainの既存宣言・⑤aのファイル・公式入口・公式監査は変更していない。宣言名照合はmain a4388efc9のEInfinity/3,745ファイル13,373名と自レーン候補626ファイルからの1,956名で、異なるファイル間の重複0、内部も0。候補数は撤回された削除パスも含む索引の候補数で、本体の現存モジュール数は一覧の259本。git diff --check通過。証跡：/private/tmp/isw2-build362.log、isw2-validation362.json、isw2-declaration-collision-scan362.json。

この検収で右辺の元のroofの全局所化三角形の消去と、元の指定probe・標的置換による全族の輸送を閉じた。native fiber射側から同じ全族への最終照合R03h、元の実射自身の弱同値性、R03d・3b-4aは未完のまま。§293のnative射自身の全族の正規化と今回の全roofの式を使い、その残りを詰める。

次に使う、同じprobe射のモデル源の二つの宇宙表示と元のprobe頂点同型のArrowの照合は、個別検査isw2-model-source-edge1およびisw2-roof-probe-endpoint-arrow1で終了0。一時ファイルだけで、本体への対象ビルド・監査はまだ。今回はこの二補題を検収済みモジュール数・行数には含めない。未検証の新規Leanは作業木に残していない。全ての鍵は返却済み。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。停止点3b-4aの完了報告ではない。

## 296. 指定されたprobe頂点同型と、同じ元のprobe射の像を照合（2026-11-16）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§295.3の一時検査済みの二補題を本体へ移す。strictBETotModelSourceとalgebraCAlgSourceの同じ実射の辺は、共通のcAlgLocalizationSourceへ送る元の一単体が一致する。これを元のframedLimitProbeComparisonへ適用し、strictBETotJointRoofProbeEndpointIsoの順射が同じ元のprobe射のnative像であることをArrowとして照合する。新しい数学の項目ではなく、既存の宇宙表示と指定同型の係数移送の法則。既存のprobe比較・CAlg源・局所化三角形を選び直さない。

個別検査isw2-model-source-edge1・isw2-roof-probe-endpoint-arrow1は終了0。mainのEInfinityにも今回の二つの宣言名がないことをgit grepで確認した。この二補題は指定された同じ両端成分の照合であり、一般の全パラメータの等式を点での一致から推論するものではない。§293のnative全族と§295のroof全族の最終照合は、別に全族の形で維持する。

#### StrictDiagramTotJointRoofProbeArrow（46行）

```lean
lemma strictBETotModelSource_edge {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    (((nerve.edgeMk ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map f)).map
      (strictBETotModelSource A)).edge) =
      (((nerve.edgeMk f).map (algebraCAlgSource A)).edge)

lemma strictBETotJointRoofProbeEndpointIso_hom_arrow (P : strictBETotJointHomIndex A) :
    Arrow.mk (strictBETotJointRoofProbeEndpointIso A P).hom =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          (framedLimitProbeComparison A (AsSmall.down.obj P).1.unop))).map
        (strictBETotModelSource A)))
```

対象ビルド・小監査を行ってから検収する。既存の⑤aのファイル・公式入口・公式監査は変更しない。

### 296.2 検収

新規1本46行・公開2補題・実環境宣言2。対象ビルド363（依存を含む12,242 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用した。小監査は264モジュール・1,706宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計260本・17,658行、実環境1,699宣言。外枠22,000行まで4,342行。git diff --check通過。main a4388efc9のEInfinity/3,745ファイル13,373名と自レーン候補626ファイルからの1,958名を照合し、異なるファイル間の重複0、内部も0。

証跡：/private/tmp/isw2-build363.log、isw2-validation363.json、isw2-declaration-collision-scan363.json。登録候補の一覧is-w2-be-20261114-modules.jsonに追加した。mainの既存宣言・⑤aのファイル・公式入口・公式監査は変更していない。既存の原模型のinstanceをローカルに再利用し、新しい模型の仮定は追加していない。§295の最終のBE三宣言のコードは450a6f6aeに保存済み。

指定probe同型の実際の元の射との照合は閉じたが、一般の全族の一致をこの二補題だけから推論しない。次は同じcoslice普遍円柱の制限・自然性の全族の法則を使い、native側のcorrected pairingの同じ全比較をroofの式へ接続する。R03hの最終の全interval族の等式、R03d・3b-4aは未完。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

## 297. 指定coslice普遍円柱の全パラメータでの制限と自然性（2026-11-16）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

同じ普遍円柱の制限の厳密な等式を示し、任意のパラメータ準圏からcosliceへのFunctorIsoに沿う全HoFun射の自然性を証明する。既存の円柱の自然性・定値への後合成の単位則・2圏のwhisker_exchangeの法則であり、新しい数学の項目は足さない。点ごとの同値への置換ではない。R03hの同じ全族の最終照合はまだ未完である。

一時ファイルisw2-point-coslice-unit-complete4の個別Lean検査は終了0。複雑な係数の前後合成をprivateな型つき略記に分割してelaborationを収めた。計算上限は上げていない。FunctorIsoの後合成の順射は既存functorIso_postcomp_homで合わせる。公開の最終型にprivate略記は露出しない。以下はprivateな証明分割も含む主張の型。各部分は200行未満。既存の⑤aのファイル、公式入口・公式監査は変更しない。

```lean
lemma pointCosliceFamilyHomotopy_precomp_h {A C : SSet.{u}} (c : C _⦋0⦌)
    (a : A ⟶ sliceUnder (yonedaEquiv.symm c)) :
    (a ▷ (Δ[1] : SSet.{u})) ≫ (pointCosliceFamilyHomotopy (𝟙 (sliceUnder (yonedaEquiv.symm c)))).h =
      (pointCosliceFamilyHomotopy a).h

lemma pointCosliceFamilyHomotopy_precomp_arrow {A C : SSet.{u}} (c : C _⦋0⦌)
    (a : A ⟶ sliceUnder (yonedaEquiv.symm c)) :
    Arrow.mk ((hoFunctor.map ((pre a).app C)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy (𝟙 (sliceUnder (yonedaEquiv.symm c))))))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (pointCosliceFamilyHomotopy a)))

private def cosliceCoefficientPost {K J C : SSet.{u}} {a b : K ⟶ J}
    (p : J ⟶ C) (α : FunctorHom a b) : FunctorHom (a ≫ p) (b ≫ p)

private def cosliceCoefficientPre {K J C : SSet.{u}} {p q : J ⟶ C}
    (a : K ⟶ J) (β : FunctorHom p q) : FunctorHom (a ≫ p) (a ≫ q)

private lemma samePointCosliceUnitWhiskerNaturality {K C : SSet.{u}} [Quasicategory K] [Quasicategory C]
    (c : C _⦋0⦌) {a b : K ⟶ sliceUnder (yonedaEquiv.symm c)} (α : FunctorHom a b) :
    let J

private lemma cosliceCoefficientPostConstArrow {K J C : SSet.{u}} [Quasicategory J]
    {a b : K ⟶ J} (α : FunctorHom a b) (c : C _⦋0⦌) :
    Arrow.mk (cosliceCoefficientPost (SSet.const c : J ⟶ C) α) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex (SSet.const c : K ⟶ C))))

private lemma cosliceCompArrow {D : Type*} [Category* D] {a b c a' b' c' : D}
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g')

private lemma samePointCosliceUnitNaturalityArrow {K C : SSet.{u}} [Quasicategory K] [Quasicategory C]
    (c : C _⦋0⦌) {a b : K ⟶ sliceUnder (yonedaEquiv.symm c)} (e : FunctorIso a b) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy a)) ≫
      (e.postcomp (sliceUnderProjection (yonedaEquiv.symm c))).hom) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy b)))

lemma pointCosliceFamilyHomotopy_naturality {K C : SSet.{u}} [Quasicategory K] [Quasicategory C]
    (c : C _⦋0⦌) {a b : K ⟶ sliceUnder (yonedaEquiv.symm c)} (e : FunctorIso a b) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy a)) ≫
      (e.postcomp (sliceUnderProjection (yonedaEquiv.symm c))).hom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy b))
```

対象ビルド364と小監査で検収する。

### 297.2 検収

新規1本143行、公開3補題、実環境宣言5。対象ビルド364（依存を含む1,954 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用した。小監査265モジュール・1,711宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計261本・17,801行、実環境1,704宣言。外枠22,000行まで4,199行。名前照合の異なるファイル間の重複0、内部も0。git diff --check通過。証跡isw2-build364.log・isw2-validation364.json・isw2-declaration-collision-scan364.json。登録候補一覧に追加した。

既存の円柱の全HoFun射について自然性を閉じた。元のnative fiber射とroofの全interval族の照合R03h・R03d・3b-4aは未完。次に、この同じ円柱をfiberへ制限した射と既存intervalFamilyHomの厳密な対応を照合し、同じcoslice比較の全族へ接続する。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

## 298. 同じcoslice fiberのinterval族を同じ普遍円柱へ厳密に接続（2026-11-16）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

既存のcosliceFiberToIntervalMappingSpaceのuncurry則で、同じfiber族のintervalFamilyHomが、包含後の同じpointCosliceFamilyHomotopyのHoFun射に一致することをArrowとして照合する。任意のパラメータ単体集合を扱い、準圏・Kanの追加仮定を要しない。円柱の終点の厳密な射影と定値表示の差だけをArrowで保持する。既存構成の係数表示の法則で、新しい数学の項目ではない。

```lean
lemma cosliceFiber_intervalFamilyHom_arrow {K C : SSet.{u}} {x y : C _⦋0⦌}
    (f : K ⟶ vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) :
    Arrow.mk (intervalFamilyHom (f ≫ cosliceFiberToIntervalMappingSpace x y)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy (f ≫ vertexFiberι _ y))))
```

一時ファイルisw2-coslice-fiber-interval-family2の個別検査は終了0。対象ビルド365と小監査を行う。これにより§293の同じnative族のcoslice正規化を§297の全関手圏の自然性へ渡せるが、元のcorrected pairingの比較の全射影を使ったR03hの最後の等式は、まだ別に必要。⑤a・公式入口・公式監査は変更しない。

### 298.2 検収

新規1本47行・公開1補題・実環境宣言1。対象ビルド365（依存を含む1,954 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用。小監査266モジュール・1,712宣言、標準三公理のみ、sorryAx・追加公理なし。自レーン累計262本・17,848行、実環境1,705宣言。外枠まで4,152行。宣言名の照合で異なるファイル間の重複0、内部も0、git diff --check通過。証跡isw2-build365.log・isw2-validation365.json・isw2-declaration-collision-scan365.json。登録候補の一覧に追加。既存宣言・⑤a・公式入口・公式監査は変更していない。R03h・R03d・3b-4aは未完。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 298.3 次の厳密な通常圏の表示の照合（未検証）

元のraw pairingの標的を固定して反対表示にすると、通常圏のUnderの同じ射の族となる。その全次数のcoslice表示には、本体に既存のNerveComparison.nerveUnderMap・nerveUnderChain・cosliceTwistedArrowMapが使える。次の既存構成同士の照合を一時ファイルisw2-under-coslice-twisted.leanで検討した。

```lean
lemma nerveUnderMap_comp_cosliceTwistedArrowMap
    {C : Type u} [Category.{u} C] (c : C) :
    nerveUnderMap c ≫ cosliceTwistedArrowMap (nervePoint c) =
      twistedPairingNerveMap ((Functor.const (Under c)).obj (Opposite.op c))
        (Under.forget c) (fun i => i.hom)
        (fun {_ _} f => by simpa using Under.w f)
```

同じ既存の構成の表示・自然性の法則であり、新しい数学の項目は増やさない。型のelaborationと全単体への展開は確認したが、証明は未完。最後の個別検査isw2-under-coslice-twisted3は終了1（以下の未解決の等式）。検証済み本数・行数・宣言数には含めず、一時ファイルだけに残した。

```lean
cosliceEdgewiseCollapse ⦋n⦌ ≫ (pointJoinStdSimplexIso n).hom ≫
    (SSet.yonedaEquiv (X := nerve C)).symm (nerveUnderChain c σ) =
  (edgewiseWeightIso n).hom ≫
    (SSet.yonedaEquiv (X := nerve C)).symm
      (twistedPairingSimplex ((Functor.const (Under c)).obj (Opposite.op c))
        (Under.forget c) (fun i => i.hom) σ)
```

残りは、同じedgewise重みの左半分を最初の点に潰し右半分の順序を保持する式と、Under.wを使った交差射の合成則。その後も元のcorrected pairingの指定全同型・同じ底のpathとの照合が必要で、通常圏の表示のこの補題だけからR03hの全族の最終等式を推論しない。元のnative fiber射自身の弱同値性・R03d・3b-4aは未完。共有鍵は返却済み、起動中の自レーンのビルドなし。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

## 299. Underの同じ全射族のcoslice表示とtwisted pairingの厳密な一致（2026-11-16）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§298.3の未完の照合を証明した。元のedgewise重みを標準単体で読み、同じ崩壊の左半分を零、右半分を元の順序の後続頂点に送る式を証明した。同じ長い射列の全対象・全射を照合し、交差ブロックにはUnder.wを使った。自然性や原射の選択を置き換えていない。既存構成同士の表示の法則・証明分割で、数学の一覧は増やさない。

一時ファイルisw2-collapse-standard5の個別Lean検査は終了0。最初の型の展開ではYonedaの対象をnerve Cに明示した。交差射の反対圏の恒等射はchangeで元の通常圏の恒等射と明示してから既存のid_compを使った。計算上限は変更しない。以下はprivateな証明分割も含む主張の型。各部分200行未満。

```lean
private def collapseStandard (n : ℕ) : (Δ[n+n+1] : SSet.{u}) ⟶ Δ[n+1]

private def collapseOrder (n : ℕ) : Fin (n+n+1+1) →o Fin (n+2)

private lemma collapseOrder_map (n : ℕ) :
    stdSimplex.map (SimplexCategory.mkHom (collapseOrder.{u} n)) = collapseStandard.{u} n

private lemma collapseStandard_left (n : ℕ) :
    stdSimplex.map (SimplexCategory.mkHom (joinLeftOrderHom n n)) ≫ collapseStandard.{u} n =
      (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) : Δ[n] ⟶ Δ[0]) ≫
        joinInl Δ[0] Δ[n] ≫ (pointJoinStdSimplexIso n).hom

private lemma collapseStandard_right (n : ℕ) :
    stdSimplex.map (SimplexCategory.mkHom (joinRightOrderHom n n)) ≫ collapseStandard.{u} n =
      stdSimplex.δ (0 : Fin (n+2))

private lemma collapseOrder_left (n : ℕ) (i : Fin (n+1)) :
    collapseOrder.{u} n (joinLeftOrderHom n n i) = 0

private lemma collapseOrder_right (n : ℕ) (i : Fin (n+1)) :
    collapseOrder.{u} n (joinRightOrderHom n n i) = i.succ

private lemma collapseOrder_left_val (n : ℕ) (i : Fin (n+n+1+1)) (hi : i.val < n+1) :
    collapseOrder.{u} n i = 0

private lemma collapseOrder_right_val (n : ℕ) (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) :
    collapseOrder.{u} n i = (twistedPairingRightIndex i hi).succ

private lemma collapseUnderChain {C : Type u} [Category.{u} C] (c : C)
    {n : ℕ} (σ : Fin (n+1) ⥤ Under c) :
    (collapseOrder.{u} n).monotone.functor ⋙ nerveUnderChain c σ =
      twistedPairingSimplex ((Functor.const (Under c)).obj (Opposite.op c))
        (Under.forget c) (fun i => i.hom) σ

lemma nerveUnderMap_comp_cosliceTwistedArrowMap {C : Type u} [Category.{u} C] (c : C) :
    nerveUnderMap c ≫ cosliceTwistedArrowMap (nervePoint c) =
      twistedPairingNerveMap ((Functor.const (Under c)).obj (Opposite.op c)) (Under.forget c)
        (fun i => i.hom) (fun {_ _} f => by simp)
```

対象ビルド366・小監査で検収する。これは元のraw pairingの全次数のcoslice表示に用いる照合であり、同じcorrected pairingの指定pathを通じた全族の最終等式R03hは別に残る。⑤a・公式入口・公式監査は変更しない。

### 299.2 検収

新規1本148行、公開1補題・実環境宣言3。対象ビルド366（依存を含む1,586 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用。小監査267モジュール・1,715宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計263本・17,996行、実環境1,708宣言。外枠まで4,004行。宣言名の照合で異なるファイル間の重複0、内部も0。git diff --check通過。証跡isw2-build366.log・isw2-validation366.json・isw2-declaration-collision-scan366.json。登録候補一覧に追加。元の構成・既存宣言・⑤a・公式入口・公式監査は変更しない。

Underの同じ全射族の二つの表示の厳密な一致は閉じた。これを局所化後の同じ全円柱へ送り、元のcorrected pairingの指定全同型と同じpathに接続する段は残る。R03h・R03d・3b-4aは未完。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 299.3 次の同じ円柱と通常変換の照合の型（未検証）

次は同じUnderの普遍射の円柱を、既存nerveNatTransHomotopyの全円柱に照合する。型は次の形（underUnitは同じ通常圏の普遍射のprivateな略記）。既存構成の単位・表示・自然性の法則であり、数学の一覧は増やさない。

```lean
private def underUnit {C : Type u} [Category.{u} C] (c : C) :
    (Functor.const (Under c)).obj c ⟶ Under.forget c where
  app x := x.hom
  naturality {_ _} f := by simpa using (Under.w f).symm

lemma underCosliceCylinder {C : Type u} [Category.{u} C] (c : C) :
    (pointCosliceFamilyHomotopy (nerveUnderMap c)).h =
      (nerveNatTransHomotopy (underUnit c)).h
```

一時ファイルisw2-under-coslice-cylinder1は型のelaboration後、証明の三つの義務で終了1。型の検査と証明の完了を区別し、検証済みの本数・行数・宣言数には含めていない。本体の新規Leanは全て検証済みでコミットした。

使える既存の法則：NerveComparison.nerve_hom_ext_oneは任意の始域から通常圏のnerveへの全写像を一次単体上の厳密な一致で判定する。JoinCylinderSimplex.joinCylinderMap_stdSimplex_valは区間の各頂点の値が零か一かにより、円柱の左・右の値を計算する。nerveNatTransHomotopy_componentは元の通常自然変換の成分を回収する。必要なのは通常圏のnerveへの円柱全体の等式であり、一般の準圏へのHoFun射について成分の一致のみから全族の等式を推論するものではない。

この照合を元のモデル源で後合成し、§299の同じtwisted pairing表示、§297の全HoFun自然性、§298の同じfiberのinterval表示へ接続する。さらに元のcorrected pairingの指定全同型とその同じ全射影のpathを保つ照合が残る。R03h・R03d・3b-4aは未完、目標は継続中。共有鍵返却済み、起動中の自レーンの検査なし。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

## 300. 同じUnderの全coslice円柱と元の通常自然変換の全像の一致（2026-11-16）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§299.3の全円柱の照合を証明し、任意の通常図式Vと元の指定自然変換ηへ一般化した。指定モデル源Fへの後合成でも、同じ全HoFun射が元のnerveNatTransHom ηの像に一致することをArrowとして示す。元の自然変換・円柱・モデル源を選び直さない。既存構成の単位・自然性・表示の法則で、数学の一覧は増やさない。

通常圏のnerveへの二つの全円柱にnerve_hom_ext_oneを適用し、区間の一次単体を二つの端点と恒等辺に分けた。端点は同じh₀・h₁、混合辺は同じjoin円柱の切断1の式とcosliceの直接評価で回収した。通常自然変換側は既存の関手圏nerve比較の評価式で同じ構造射を回収した。その後、§297の同じ普遍円柱の前合成則と既存の通常自然変換の前合成則を使って全図式へ移す。一般の準圏へのHoFun射について点ごとの一致から全族を推論していない。

一時ファイルisw2-under-coslice-cylinder18の個別Lean検査は終了0。elaborationのため零単体の二つの表示とnerveの恒等作用を明示し、計算上限は変更していない。以下はprivateな証明分割も含む型（全ファイル209行、各部分200行未満）。

```lean
private def underUnit {C : Type u} [Category.{u} C] (c : C) :
    (Functor.const (Under c)).obj c ⟶ Under.forget c

private lemma interval_one_cases (t : (Δ[1] : SSet.{u}) _⦋1⦌) :
    t = (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 0) ∨
      t = stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) ∨
        t = (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 1)

private lemma leftPrism_mixed {A : SSet.{u}} (σ : A _⦋1⦌) :
    (leftMappingSpacePrism A).app (Opposite.op ⦋1⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), σ) =
      Join.mkOfSum (n

private lemma underUnitCylinder_mixed {C : Type u} [Category.{u} C] (c : C)
    (σ : (nerve (Under c)) _⦋1⦌) :
    (nerveNatTransHomotopy (underUnit c)).h.app (Opposite.op ⦋1⦌)
      (σ, stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) = ComposableArrows.mk₁ (σ.obj 1).hom

private lemma underCosliceCylinder {C : Type u} [Category.{u} C] (c : C) :
    (pointCosliceFamilyHomotopy (nerveUnderMap c)).h =
      (nerveNatTransHomotopy (underUnit c)).h

lemma nerveUnderLift_pointCosliceFamilyHomotopy {I C : Type u} [Category.{u} I]
    [Category.{u} C] {c : C} {V : I ⥤ C} (η : (Functor.const I).obj c ⟶ V) :
    (pointCosliceFamilyHomotopy (nerveMap (Under.lift V η) ≫ nerveUnderMap c)).h =
      (nerveNatTransHomotopy η).h

lemma nerveUnderLift_pointCosliceFamilyHomotopy_postcomp_arrow {I C : Type u}
    [Category.{u} I] [Category.{u} C] {c : C} {V : I ⥤ C}
    (η : (Functor.const I).obj c ⟶ V) {D : SSet.{u}} (F : nerve C ⟶ D) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (pointCosliceFamilyHomotopy
        (nerveMap (Under.lift V η) ≫ nerveUnderMap c)) F))) =
      Arrow.mk ((hoFunctor.map ((ihom (nerve I)).map F)).toFunctor.map
        (nerveNatTransHom η))
```

対象ビルド367・小監査で検収する。mainの既存宣言・⑤a・公式入口・公式監査は変更しない。R03hの同じnative fiber射とroofの最終の全族の照合、R03d・3b-4aは未完。

### 300.2 検収

新規1本209行、公開2補題・実環境宣言2。対象ビルド367（依存を含む2,054 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用。小監査268モジュール・1,717宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計264本・18,205行、実環境1,710宣言。外枠まで3,795行。宣言名の照合で異なるファイル間の重複0、内部も0。mainのInfinityCategoriesについても公開の二宣言名をgit grepし、既存宣言との重複なし。git diff --check通過。証跡isw2-build367.log・isw2-validation367.json・isw2-declaration-collision-scan367.json。登録候補の一覧に追加。既存宣言・⑤a・公式入口・公式監査は変更していない。

任意の通常図式と元の自然変換の同じcoslice円柱、指定モデル源の後合成後の全HoFun射の像の一致は閉じた。元のcorrected pairingの同じ指定pathを通じたnative fiber射とroofの最終全族の等式R03h・R03d・3b-4aは未完。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

## 301. 同じ指定自然変換の全twisted pairingと、その指定モデル源の像の厳密な一致（2026-11-16）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§299のUnderの普遍族の厳密な等式を、元のUnder.lift V ηで前合成し、任意の指定自然変換ηの同じ全pairingへ移した。さらに既存cosliceTwistedArrowMap_postcompを使い、同じ指定モデル源Fで後合成した全写像も厳密に照合する。§300の同じ円柱の全HoFun射と今回のtwisted-arrowの全写像は、両方とも元の同じηを使う。新しい族や逆は選ばず、既存構成の前合成・後合成・自然性の法則として数学の一覧は増やさない。

一時ファイルisw2-under-lift-twisted4の個別Lean検査は終了0。当初、既存のCosliceTwistedArrowNaturalityのoleanがなかったため、共有鍵 --class impl --wait 3600・1700秒guardで当該既存1モジュールだけをビルドし、3,848 jobsで成功。既存のファイルを変更・複製せず、既存の補題を完全修飾で使う。結合順序だけの差はCategory.assocで合わせた。

```lean
lemma nerveUnderLift_comp_cosliceTwistedArrowMap {I C : Type u} [Category.{u} I]
    [Category.{u} C] {c : C} {V : I ⥤ C} (η : (Functor.const I).obj c ⟶ V) :
    nerveMap (Under.lift V η) ≫ nerveUnderMap c ≫ cosliceTwistedArrowMap (nervePoint c) =
      twistedPairingNerveMap ((Functor.const I).obj (Opposite.op c)) V (fun i => η.app i)
        (fun {_ _} f => by simpa using (η.naturality f).symm)

lemma nerveUnderLift_comp_cosliceTwistedArrowMap_postcomp {I C : Type u}
    [Category.{u} I] [Category.{u} C] {c : C} {V : I ⥤ C}
    (η : (Functor.const I).obj c ⟶ V) {D : SSet.{u}} (F : nerve C ⟶ D) :
    nerveMap (Under.lift V η) ≫ nerveUnderMap c ≫ sliceUnderPostcomp (nervePoint c) F ≫
      cosliceTwistedArrowMap (nervePoint c ≫ F) =
      twistedPairingNerveMap ((Functor.const I).obj (Opposite.op c)) V (fun i => η.app i)
        (fun {_ _} f => by simpa using (η.naturality f).symm) ≫ edgewiseSubdivisionMap F
```

対象ビルド368と小監査で検収する。§300.2の数値はisw2-validation367.jsonの実集計に訂正済み（公開2補題・実環境2宣言、2,054 jobs、監査1,717宣言、自レーン実環境1,710宣言）。この表示の一致だけでR03hの同じcorrected pairingを通じる最終等式、R03d・3b-4aを完了とはしない。⑤a・公式入口・公式監査は変更しない。

### 301.2 検収

新規1本46行、公開2補題・実環境宣言4。対象ビルド368（依存を含む3,858 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用。小監査269モジュール・1,721宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計265本・18,251行、実環境1,714宣言。外枠まで3,749行。宣言名の照合で異なるファイル間の重複0、内部も0。git diff --check通過。証跡isw2-build368.log・isw2-validation368.json・isw2-declaration-collision-scan368.json。登録候補一覧に追加。既存宣言・⑤a・公式入口・公式監査は変更していない。

同じ元の指定自然変換から、円柱側とtwisted-arrow側の全像を厳密に照合する法則は閉じた。元の固定標的のpairingを反対圏のcosliceとして表示する際の両端交換、および元のcorrected pairingの全同型と同じ底のpathを保つ最終照合が残る。R03h・R03d・3b-4aは未完。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 301.3 次の両端交換の型と、同じ重みの反転の検査

固定標的の元のpairingを、反対圏で始点を固定したcosliceとして読むため、同じtwisted pairingの両端交換の法則を調べている。二重反対同値はC→Cᵒᵖᵒᵖの向きなので(opOpEquivalence C).inverseを使う。次の型はいずれも既存の構成の自然性・反転の表示の法則で、数学の一覧は増やさない。

```lean
private lemma standardIso_end_hom (n : ℕ) (e : (Δ[n] : SSet.{u}) ≅ Δ[n]) :
    e.hom = 𝟙 _

lemma edgewiseWeightReverse_standard (n : ℕ) :
    (edgewiseWeightReverseIso.{u} ⦋n⦌).inv ≫
      SSet.opFunctor.map (edgewiseWeightIso n).hom ≫ (stdSimplex.opIso ⦋n+n+1⦌).hom =
        (edgewiseWeightIso n).hom

private lemma oppositePairing_naturality {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)
    {i j : I} (f : i ⟶ j) :
    (((B ⋙ (opOpEquivalence C).inverse).map f).unop) ≫ (h i).op ≫ A.map f = (h j).op

lemma twistedPairingNerveMap_opposite_swap {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) :
    twistedPairingNerveMap (B ⋙ (opOpEquivalence C).inverse) A (fun i => (h i).op)
      (oppositePairing_naturality A B h hh) ≫
      edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
        twistedArrowOppositeSwap (nerve C) = twistedPairingNerveMap A B h hh
```

standardIso_end_homとedgewiseWeightReverse_standardを含む一時ファイルisw2-twisted-weight-reversal2の個別Lean検査は終了0。標準単体の自己同型の射が恒等である既存Mathlibのiso_eq_iso_reflを、stdSimplexの充満忠実性で移して使った。これにより、同じ重みの反転と同じ標準単体同型を組み合わせた式は、座標の新しい選択なしに一致する。まだ本体の対象ビルド・監査をしていないため、検収済みの本数・行数・宣言数には含めない。

oppositePairing_naturalityの型と証明は一時ファイルisw2-twisted-pairing-opposite3でelaborateされ、残ったのはtwistedPairingNerveMap_opposite_swapの各次数の全射の等式（検査全体は未解決の義務で終了1）。その全写像の等式はまだ未証明。新しいモデル仮定は足さない。通常圏のnerveの反転は既存nerveOppositeIsoとnerveUnreverseChain、重みの反転は上の同じ比較を使って進める。

R03h・R03d・3b-4aは未完。検収済みの本体は全てコミット済み、未完の次の検査は一時ファイルだけ。共有鍵は返却済みで、起動中の自レーンの検査はない。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

## 302. 元の同じpairingの反対表示と両端交換の全単体での厳密な一致（2026-11-16）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§301.3の同じtwisted pairingの両端交換の法則を証明した。重みの同じ反転と標準単体表示を、標準単体の自己同型の既存の一意性で照合する。通常のnerveの反転とYoneda表示の整合性を同じnerveOppositeIsoで示し、元の長い射列の全対象・全射を反転したpairingと厳密に照合した。左・交差・右の三ブロックを扱い、元の入力の自然性から反対側の同じ自然性を導く。全パラメータの写像の等式であり、各点の同値に弱めていない。

一時ファイルisw2-twisted-swap-reverse2、isw2-pairing-reverse-chain2、全体のisw2-twisted-pairing-opposite-complete1の個別Lean検査は全て終了0。§301.3の独立のedgewiseWeightReverse_standardは全swapの証明内で同じ同型の一意性を直接使えるため、本体の独立の公開宣言にはせず、一時の検査記録のままとした。新しい選択・数学の項目・模型仮定・計算上限は追加しない。全て既存の反転・自然性・合成則の法則と証明の分割。以下はprivateな分割も含む主張の型。ファイルの行数は検収で記す。各部分は200行未満。

```lean
private lemma standardIso_end_hom (n : ℕ) (e : (Δ[n] : SSet.{u}) ≅ Δ[n]) :
    e.hom = 𝟙 _

private lemma nerveReverseChain_yoneda {C : Type u} [Category.{u} C] {n : ℕ}
    (τ : (nerve C) _⦋n⦌) :
    (stdSimplex.opIso ⦋n⦌).inv ≫ SSet.opFunctor.map (SSet.yonedaEquiv.symm τ) ≫
      (nerveOppositeIso (C

lemma twistedArrowOppositeSwap_nerve_reverse {C : Type u} [Category.{u} C] (n : ℕ)
    (τ : (nerve C) _⦋n+n+1⦌) :
    (twistedArrowOppositeSwap (nerve C)).app (Opposite.op ⦋n⦌)
      ((edgewiseWeightIso n).hom ≫ SSet.yonedaEquiv.symm (nerveReverseChain τ) ≫
        (nerveOppositeIso (C

private lemma rev_left_index {n : ℕ} (i : Fin (n+n+1+1))
    (hi : i.val < n+1) (hr : ¬ i.rev.val < n+1) :
    twistedPairingRightIndex i.rev hr = twistedPairingLeftIndex i hi

private lemma rev_right_index {n : ℕ} (i : Fin (n+n+1+1))
    (hi : ¬ i.val < n+1) (hr : i.rev.val < n+1) :
    twistedPairingLeftIndex i.rev hr = twistedPairingRightIndex i hi

private lemma op_heq_of_endpoints {C : Type u} [Category.{u} C]
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : HEq f g) : HEq f.op g.op

private lemma thin_op_heq {C : Type u} [Category.{u} C] {N : ℕ}
    (F : Fin N ⥤ C) {a b c d : Fin N} (ha : a = c) (hb : b = d)
    {f : a ⟶ b} {g : c ⟶ d} : HEq (F.map f).op (F.map g).op

private lemma cross_op {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    {n : ℕ} (σ : Fin (n+1) ⥤ I) (a b : Fin (n+1)) :
    twistedPairingCross (B ⋙ (opOpEquivalence C).inverse) A (fun i => (h i).op) σ a b =
      (twistedPairingCross A B h σ b a).op

private lemma cross_op_heq {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    {n : ℕ} (σ : Fin (n+1) ⥤ I) {a b c d : Fin (n+1)} (ha : a = c) (hb : b = d) :
    HEq (twistedPairingCross A B h σ a b).op (twistedPairingCross A B h σ c d).op

lemma twistedPairingSimplex_reverse {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    {n : ℕ} (σ : Fin (n+1) ⥤ I) :
    twistedPairingSimplex (B ⋙ (opOpEquivalence C).inverse) A (fun i => (h i).op) σ =
      nerveReverseChain (twistedPairingSimplex A B h σ)

private lemma oppositePairing_naturality {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)
    {i j : I} (f : i ⟶ j) :
    (((B ⋙ (opOpEquivalence C).inverse).map f).unop) ≫ (h i).op ≫ A.map f = (h j).op

lemma twistedPairingNerveMap_opposite_swap {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) :
    twistedPairingNerveMap (B ⋙ (opOpEquivalence C).inverse) A (fun i => (h i).op)
      (oppositePairing_naturality A B h hh) ≫
      edgewiseSubdivisionMap (nerveOppositeIso (C
```

対象ビルド369と小監査で検収する。R03h・R03d・3b-4aは未完。⑤a・公式入口・公式監査は変更しない。

### 302.2 本体の公開宣言の検査での修正

369対象ビルドではTwistedNerveOppositeSimplexは通ったが、TwistedPairingOppositeの公開定理の型にprivateなoppositePairing_naturalityを使っており、公開型からアクセスできないため失敗した。監査には到達していない。通常の一時ファイルの個別検査が通ったことだけを、公開モジュールの検収とはしない。

最終の公開型では、この自然性の証明を同じHHの引数へ直接書く。privateな仮定や略記を公開型へ露出させず、元のhhから同じ自然性を導くだけで、主張を弱めない。同じ数学の型はproof irrelevanceで変わらない。unusedとなったprivateな自然性の補題は本体から除き、§302の上の型の表示は一時ファイルの分割の記録として残す。370で同じ二本の対象ビルドと小監査を行う。

### 302.3 検収

最終の新規2本は181行・46行、計227行。公開3補題・実環境宣言4。公開型の自然性の証明を元のhhから直接導く形へ直した370対象ビルド（依存を含む3,148 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用。小監査271モジュール・1,725宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計267本・18,478行、実環境1,718宣言。外枠まで3,522行。宣言名の照合で異なるファイル間の重複0、内部も0。git diff --check通過。証跡isw2-build370.log・isw2-validation370.json・isw2-declaration-collision-scan370.json。登録候補一覧に追加。既存宣言・⑤a・公式入口・公式監査は変更していない。

元の同じtwisted pairingの両端交換と反対表示の全写像の等式は閉じた。これを元の固定標的の自然変換へ適用し、同じモデル源の後合成と厳密に可換にする法則の検査を続ける。R03hの同じcorrected pairingの指定pathを通じた全族の最終等式、R03d・3b-4aは未完。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

## 303. 元の固定標的の全pairingを、同じ反対cosliceの指定モデル源での像として回収（2026-11-16）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

§302の全両端交換の法則を、任意の元の自然変換η : V→const cへ適用した。既存のNatTrans.op ηを同じUnder.liftで読み、元の同じ固定標的の全pairingを厳密に回収する。さらに、同じ反対モデル源Fop = nerveOppositeIso.inv ≫ opFunctor.map Fで後合成し、cosliceOppositeTwistedArrowMapを通すと、元のpairingを指定モデル源Fへ送った全写像に一致する。新しい逆・別のpath・置換の選択は足さない。既存の反転・前後合成・自然性・単位の法則で、数学の一覧は増やさない。

同じ両端交換が任意の元の関手Fと厳密に可換である法則は、一般の準圏の部分なのでKerodonの元のcosliceと両端交換の隣に置く。Underと通常の自然変換の二つの照合は既存NerveComparisonの隣に置く。固定点をOpposite.op cに明示し、自然変換の反対はQuiver.Hom.opでなくNatTrans.opと明記する。元の自然性と単位則は型を明示して直接合成し、計算上限は変更しない。

一時ファイルisw2-under-fixed-target-pairing5と、検証済み本体のTwistedPairingOppositeを実際にimportしたisw2-under-fixed-target-compiled1の個別Lean検査はともに終了0。以下が公開の型。追加仮定はなく、元のη・Fだけを使う。

```lean
lemma twistedArrowOppositeSwap_naturality {C D : SSet.{u}} (F : C ⟶ D) :
    edgewiseSubdivisionMap (SSet.opFunctor.map F) ≫ twistedArrowOppositeSwap D =
      twistedArrowOppositeSwap C ≫ edgewiseSubdivisionMap F

lemma nerveUnderLift_opposite_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : I ⥤ C} (η : V ⟶ (Functor.const I).obj c) :
    nerveMap (Under.lift (X := Opposite.op c) V.op (NatTrans.op η)) ≫ nerveUnderMap (Opposite.op c) ≫
      cosliceTwistedArrowMap (nervePoint (Opposite.op c)) ≫
        edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
          twistedArrowOppositeSwap (nerve C) =
      twistedPairingNerveMap V.op ((Functor.const Iᵒᵖ).obj c)
        (fun i => η.app i.unop) (by
          intro i j f
          change V.map f.unop ≫ η.app i.unop ≫ 𝟙 c = η.app j.unop
          calc
            _ = V.map f.unop ≫ η.app i.unop := congrArg (fun g => V.map f.unop ≫ g)
              (Category.comp_id (η.app i.unop))
            _ = η.app j.unop := (η.naturality f.unop).trans (Category.comp_id _))

lemma nerveUnderLift_opposite_native_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : I ⥤ C} (η : V ⟶ (Functor.const I).obj c) {D : SSet.{u}}
    (F : nerve C ⟶ D) :
    let Fop := (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map F
    nerveMap (Under.lift (X := Opposite.op c) V.op (NatTrans.op η)) ≫
      nerveUnderMap (Opposite.op c) ≫ sliceUnderPostcomp (nervePoint (Opposite.op c)) Fop ≫
        cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop) =
      twistedPairingNerveMap V.op ((Functor.const Iᵒᵖ).obj c)
        (fun i => η.app i.unop) (by
          intro i j f
          change V.map f.unop ≫ η.app i.unop ≫ 𝟙 c = η.app j.unop
          calc
            _ = V.map f.unop ≫ η.app i.unop := congrArg (fun g => V.map f.unop ≫ g)
              (Category.comp_id (η.app i.unop))
            _ = η.app j.unop := (η.naturality f.unop).trans (Category.comp_id _)) ≫
        edgewiseSubdivisionMap F
```

対象ビルド371と小監査で検収する。元のcorrected pairingの全同型とその同じ指定pathを通じたR03hの最終照合、R03d・3b-4aは未完。⑤a・公式入口・公式監査は変更しない。

### 303.2 切り出した一般部分のimportの検査

371対象ビルドは、一般部分へコピーした不要なopen NerveComparisonが、その一般部分のimportには存在せず失敗した。監査には到達していない。一般部分はNerveComparisonを使わないため、importを増やさず不要なopenを削除した。主張・証明の計算・仮定は変えない。372で同じ二本の対象ビルドと小監査を再実行する。

### 303.3 検収

最終の新規2本は42行・92行、計134行。公開3補題・実環境宣言4。372対象ビルド（依存を含む3,862 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用。小監査273モジュール・1,729宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計269本・18,612行、実環境1,722宣言。外枠まで3,388行。宣言名の照合で異なるファイル間の重複0、内部も0。git diff --check通過。証跡isw2-build372.log・isw2-validation372.json・isw2-declaration-collision-scan372.json。登録候補一覧に追加。既存宣言・⑤a・公式入口・公式監査は変更していない。

固定標的の元の同じ全族と、その指定モデル源でのnative pairingの厳密な一致は閉じた。次は元のBEのfiber包含とsource-frame評価へ同じ全写像の式を適用する。R03h・R03d・3b-4aは未完。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

## 304. 同じfiberの添字を保つrightOp表示と、元の全pairingの前合成・係数移送（2026-11-16）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

BEの元のsource-frame評価VはDᵒᵖ→Cなので、元のfiber Dからの表示には既存Functor.rightOpとNatTrans.rightOpを使う。同じデータのこの係数表示に§303の証明を適用し、二重反対の新しい添字への輸送を追加せず、元のDそのものの全写像の等式にした。元のη・Fからの同じ族で、仮定を追加しない。元のpairingの通常関手Hによる前合成と、両端と同じ実射の等式による係数移送の法則も明記した。いずれも既存構成の表示・前後合成・自然性の法則、数学の一覧は増やさない。

一時ファイルisw2-under-rightop-pairing1・isw2-pairing-precomp1の個別Lean検査は終了0。計算上限・既存の宣言・⑤aのファイルは変更しない。以下が型。

```lean
lemma twistedPairingNerveMap_precomp {J I C : Type u} [Category.{u} J] [Category.{u} I]
    [Category.{u} C] (H : J ⥤ I) (A : I ⥤ Cᵒᵖ) (B : I ⥤ C)
    (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) :
    nerveMap H ≫ twistedPairingNerveMap A B h hh =
      twistedPairingNerveMap (H ⋙ A) (H ⋙ B) (fun i => h (H.obj i))
        (fun {_ _} f => hh (H.map f))

lemma twistedPairingNerveMap_congr {I C : Type u} [Category.{u} I] [Category.{u} C]
    {A A' : I ⥤ Cᵒᵖ} {B B' : I ⥤ C} (ha : A = A') (hb : B = B')
    (h : ∀ i, (A.obj i).unop ⟶ B.obj i) (h' : ∀ i, (A'.obj i).unop ⟶ B'.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)
    (hh' : ∀ {i j} (f : i ⟶ j), (A'.map f).unop ≫ h' i ≫ B'.map f = h' j)
    (hv : ∀ i, HEq (h i) (h' i)) :
    twistedPairingNerveMap A B h hh = twistedPairingNerveMap A' B' h' hh'

lemma nerveUnderLift_rightOp_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : Iᵒᵖ ⥤ C} (η : V ⟶ (Functor.const Iᵒᵖ).obj c) :
    nerveMap (Under.lift (X := Opposite.op c) V.rightOp (NatTrans.rightOp η)) ≫ nerveUnderMap (Opposite.op c) ≫
      cosliceTwistedArrowMap (nervePoint (Opposite.op c)) ≫
        edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
          twistedArrowOppositeSwap (nerve C) =
      twistedPairingNerveMap V.rightOp ((Functor.const I).obj c)
        (fun i => η.app (Opposite.op i)) (by
          intro i j f
          change V.map f.op ≫ η.app (Opposite.op i) ≫ 𝟙 c = η.app (Opposite.op j)
          calc
            _ = V.map f.op ≫ η.app (Opposite.op i) := congrArg (fun g => V.map f.op ≫ g)
              (Category.comp_id (η.app (Opposite.op i)))
            _ = η.app (Opposite.op j) := (η.naturality f.op).trans (Category.comp_id _))

lemma nerveUnderLift_rightOp_native_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : Iᵒᵖ ⥤ C} (η : V ⟶ (Functor.const Iᵒᵖ).obj c) {D : SSet.{u}}
    (F : nerve C ⟶ D) :
    let Fop := (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map F
    nerveMap (Under.lift (X := Opposite.op c) V.rightOp (NatTrans.rightOp η)) ≫
      nerveUnderMap (Opposite.op c) ≫ sliceUnderPostcomp (nervePoint (Opposite.op c)) Fop ≫
        cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop) =
      twistedPairingNerveMap V.rightOp ((Functor.const I).obj c)
        (fun i => η.app (Opposite.op i)) (by
          intro i j f
          change V.map f.op ≫ η.app (Opposite.op i) ≫ 𝟙 c = η.app (Opposite.op j)
          calc
            _ = V.map f.op ≫ η.app (Opposite.op i) := congrArg (fun g => V.map f.op ≫ g)
              (Category.comp_id (η.app (Opposite.op i)))
            _ = η.app (Opposite.op j) := (η.naturality f.op).trans (Category.comp_id _)) ≫
        edgewiseSubdivisionMap F
```

対象ビルド373と小監査で検収する。元のBEのfiber包含と同じsource-frame評価への適用、および元のcorrected pairingの全同型と指定pathの最終照合を続ける。R03h・R03d・3b-4aは未完。公式入口・公式監査は変更しない。

### 304.2 検収

新規2本は41行・87行、計128行。公開4補題・実環境宣言5。373対象ビルド（依存を含む3,864 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用。小監査275モジュール・1,734宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計271本・18,740行、実環境1,727宣言。外枠まで3,260行。宣言名の照合で異なるファイル間の重複0、内部も0。git diff --check通過。証跡isw2-build373.log・isw2-validation373.json・isw2-declaration-collision-scan373.json。登録候補一覧に追加。既存宣言・⑤a・公式入口・公式監査は変更していない。

同じ添字のrightOp表示と、同じ全pairingの前合成・係数移送は閉じた。BEの実際のfiber包含の両端の全関手と、元のsource-frame評価の直接の照合を続ける。R03h・R03d・3b-4aは未完。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

## 305 同じBE fiberの全pairingと同じ指定pathの表示の照合（11-16）

既存の同じfiber包含の両端の関手をroof-frame表示と等号で合わせ、元の評価のpairingを全単体上で回収する。そこから同じraw coslice familyを表示し、元のcorrected pairingの全同型を端点の等号だけで移す。最後に射影後の元の全pathを保持する。新しい数学の項目は追加せず、既存構成の再添字・係数移送・等号による表示変更の法則と証明の分割である。

一つの検査ファイルでは射影のHEqのkernel検査が時間制限に達した。計算上限は変えず、三つのモジュールへ分割する。次の型を対象ビルド374と小監査で検収する（未検収）。

```lean
lemma strictBETotJointSourceFiberDomain_roof_eq (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
      FrameHom.liftedSourceFrameArrowDomain (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A)) =
      (strictBETotJointSourceRoofFrameDiagram A P).rightOp

lemma strictBETotJointSourceFiberCodomain_roof_eq (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
      FrameHom.liftedSourceFrameArrowCodomain (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A)) =
      (Functor.const _).obj (modelRelativeObject (operad A).Algebra
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))

lemma strictBETotJointSourceFiberPairing_roof_eq (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      strictBETotJointSourcePairing A =
    twistedPairingNerveMap (strictBETotJointSourceRoofFrameDiagram A P).rightOp
      ((Functor.const _).obj (modelRelativeObject (operad A).Algebra
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)))
      (fun s => (strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s)) (by
        intro s t f
        change (strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
          (strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s) ≫ 𝟙 _ = _
        calc
          _ = (strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
            (strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s)

def strictBETotJointSourceRawCosliceFamily (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    let c := modelRelativeObject (operad A).Algebra
      ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    let Fop := (nerveOppositeIso (C := (modelRelativeCategory (operad A).Algebra).category)).inv ≫
      SSet.opFunctor.map (strictBETotModelSource A)
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
      sliceUnder (nervePoint (Opposite.op c) ≫ Fop)

lemma strictBETotJointSourceRawCosliceFamily_pairing (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    let c := modelRelativeObject (operad A).Algebra
      ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    let Fop := (nerveOppositeIso (C := (modelRelativeCategory (operad A).Algebra).category)).inv ≫
      SSet.opFunctor.map (strictBETotModelSource A)
    strictBETotJointSourceRawCosliceFamily A P ≫ cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop) =
      simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceNativePairing A

def strictBETotJointSourceCorrectedRawCosliceIso (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    let c := modelRelativeObject (operad A).Algebra
      ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    let Fop := (nerveOppositeIso (C := (modelRelativeCategory (operad A).Algebra).category)).inv ≫
      SSet.opFunctor.map (strictBETotModelSource A)
    FunctorIso
      (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceCorrectedPairing A)
      (strictBETotJointSourceRawCosliceFamily A P ≫ cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop))

lemma strictBETotJointSourceCorrectedRawCosliceIso_postcomp (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceCorrectedRawCosliceIso A P).postcomp (twistedArrowProjection (CAlg_R A)))
      ((strictBETotJointSourceFiberPairingIso A P).postcomp (twistedArrowProjection (CAlg_R A)))

lemma strictBETotJointSourceCorrectedRawCosliceIso_original_path (A : Type u) [CommRing A]
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceCorrectedRawCosliceIso A P).postcomp (twistedArrowProjection (CAlg_R A)))
      (FunctorIso.precomp (eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          strictBETotJointSourcePairingBasePathIso A)
            (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P))
```

R03h・R03d・3b-4aは未完。公式入口・公式監査・⑤aは変更しない。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 305.1 kernel検査の分割

余錐familyの定義までの二本の対象ビルドは終了0（12,262 jobs）。公開モジュールの自然性の証明引数を明記した。射影のHEqは、分割後も定義の展開の照合でkernel時間制限に達した。同じ値である次の定義等式を独立に検査し、既存の `functorIsoOfEq_postcomp_heq_of_eq` に渡す。型・上限・指定された比較の値は変えない。これは同じ定義の展開の分割である。

```lean
lemma strictBETotJointSourceCorrectedRawCosliceIso_eq (A : Type u) [CommRing A]
    (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceCorrectedRawCosliceIso A P =
      functorIsoOfEq (strictBETotJointSourceFiberPairingIso A P) rfl
        (strictBETotJointSourceRawCosliceFamily_pairing A P).symm
```

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 305.2 指定値を直接書く分割

定義等式だけの追加もkernelの展開で時間制限に達したため、その未検証の補題は採用しない。射影の型に、同じ `functorIsoOfEq` の移送済みの値を直接書き、既存の法則をそのまま適用する。元の全同型と元の底のpathを保持する内容は同一であり、条件や結論は弱めない。最終の検査対象の二つの型は次のとおり（305冒頭の別名表示を置き換える）。

```lean
lemma strictBETotJointSourceCorrectedRawCosliceIso_postcomp (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    HEq ((functorIsoOfEq (strictBETotJointSourceFiberPairingIso A P) rfl
      (strictBETotJointSourceRawCosliceFamily_pairing A P).symm).postcomp (twistedArrowProjection (CAlg_R A)))
      ((strictBETotJointSourceFiberPairingIso A P).postcomp (twistedArrowProjection (CAlg_R A)))

lemma strictBETotJointSourceCorrectedRawCosliceIso_original_path (A : Type u) [CommRing A]
    (P : strictBETotJointHomIndex A) :
    HEq ((functorIsoOfEq (strictBETotJointSourceFiberPairingIso A P) rfl
      (strictBETotJointSourceRawCosliceFamily_pairing A P).symm).postcomp (twistedArrowProjection (CAlg_R A)))
      (FunctorIso.precomp (eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          strictBETotJointSourcePairingBasePathIso A)
            (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P))

```

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

### 305.3 検収

新規3本は110行・83行・51行、計244行。公開6補題と2定義、実環境宣言12。374対象ビルド（依存を含む12,263 jobs）・小監査とも終了0。共有鍵 --class impl --wait 3600、一枚の整理券、gtimeout 1700秒でビルドと小監査の間だけ使用。小監査278モジュール・1,746宣言、propext・Classical.choice・Quot.soundのみ、sorryAx・追加公理なし。自レーン累計274本・18,984行、実環境1,739宣言。外枠まで3,016行。宣言名の照合でmainのEInfinityとの異なるファイル間の重複0、内部も0。git diff --check通過。証跡isw2-build374.log・isw2-validation374.json・isw2-declaration-collision-scan374.json。登録候補一覧に追加。既存宣言・⑤a・公式入口・公式監査は変更していない。

元のfiber包含の全pairingを同じsource-frame評価の全pairingと厳密に同定し、同じraw coslice familyとして回収した。同じcorrected pairingの全同型を端点の等号で移した値の射影は、元の指定された全pathそのものの制限を保持する。別名の定義を展開して照合する検査はkernel時間制限に達したが、最終の二つの型は同じ端点移送の項を直接書く305.2の形で通過した。計算上限は上げていない。

残りは、この全同型と同じ両端のpathから、元のnative fiber自身の全interval族を、元のroofの全interval族へ照合する部分である。全pairingの同定や指定pathの保持だけからその最終等式を主張してはいない。pointCosliceFamilyHomotopyの全族の自然性と、同じsource-frame評価の全円柱の照合を次に用いる。R03h・R03d・3b-4aは未完。

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 12／全体 25（うち追加 13）。

