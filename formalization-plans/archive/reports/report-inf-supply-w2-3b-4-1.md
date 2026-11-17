# IS-W2 の報告（report-inf-supply-w2.md） — 3b-4 前半（R01〜R03g、外枠の再見積もり）（§161〜§235、2026-11-14〜11-15）

元の報告：[report-inf-supply-w2.md](../../stage-ii/inf-supply-b/report-inf-supply-w2.md)

## 161. 3b-4開始：R01と同じstrict図式・実U比較の入口（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R01完了。R02・R04は同じ元のstrict図式・全評価と既存U比較を前合成する入口だけで、native全錐族・極限性・台の加群Totへの最終比較が完成したとは数えない。

### 161.1 3b-3との境目・Tot先行の具体化

§152の受け渡しを維持する。R01〜R04のstrict入力について、元のBE right frame/end・全図式射・同じalgebraCAlgSourceを使う。R05でstrict複体図式の∞局所化と全Fun比較を使う所、R09〜R10で③-aの元の実現余錐の全族を使う所が3b-3との境目。加群版のstrict図式評価の同値からBE値の任意coherent図式の厳密化を得たとは扱わない。

R02〜R03の模型側では `FramedLimitCones` のKan錐空間・指定重み、`FramedLimitHomPiZero` の通常局所化Hom、一般 `ModelRightFrameComparison` の実right-frameとpinched Homの全比較を区別して使う。π₀のHom同値や通常局所化の随伴だけをnative全錐の普遍性と取り違えない。既存 `FramedLimit*`・`CAlgUnderlyingDerivedComparison`・⑤aは変更しない。既存の無条件 `cAlgForgetDerived_mapJoinCone_isLimit` は、構成したBE極限錐の像の検収に使い、逆方向に用いない。

### 161.2 R11・R12で合わせる既存の欄

読み取りで確認：`EInfinity/Interface/Theory` の `TotalizationCone D x` は **`{ c : JoinCone D // c.vertex = x ∧ IsLimitCone c }`**。`ofCosimplicial_forget` は全 `FunctorIso`、`ofCosimplicial_restrict` も全 `FunctorIso`。既存の型と指定頂点を変えない。

またBE実例の `Theory.lean` で `discrete` に入るものは **`discreteCAlgUnderEmbedding`**（源は `Under (CommRingCat.of A)`）であり、単にCommAlgCat源の `discreteCAlgEmbedding` で代用しない。既存の全源表示は `nerveMap (commAlgCatEquivUnder ...).inverse ≫ discreteCAlgEmbedding`。従ってR11の元の離散BE図式は、この同じinverseと `discreteAlgebraFunctor` を図式へ後合成したものに固定する。`cosimplicialCochains` は既存の `discreteAlgebraModule`・交代余面・整数次数への零延長の全関手で、今回G10の離散入口に使った全関手との表示の法則を照合する。

R12の係数制限は既存の `coefficientRestriction f`（strict代数）と `barrattEcclesRestrict f`（実CAlg）に固定。`barrattEcclesRestrict_sourceIso` は `algebraCAlgSource T ≫ barrattEcclesRestrict f` と `nerveMap (coefficientRestriction f) ≫ algebraCAlgSource S` の全比較。R12ではこの同じ比較の評価前合成を全錐族の右境界に保ち、左境界をTot頂点の比較に一致させる。R11の最終出口は次の既存欄そのものである（紙、未実装）：

```lean
-- S : Type u, [CommRing S]。FtotはR01を同じUnder→CommAlgCat→BE図式へ制限した全関手。
FunctorIso (Ftot S ≫ cAlgForgetDerived S)
  (nerveMap (cosimplicialCochains S) ≫ complexOrdinaryDerivedSource S)
-- 同じFtotの指定頂点を保持する。
(X : CosimplicialRingAlgebra S) →
  TotalizationCone (cosimplicialNerve X ≫ discreteCAlgUnderEmbedding S)
    (atVertex (Ftot S) (nerveVertex X))
-- S T : Type u, [CommRing S] [CommRing T], f : S →+* T。
FunctorIso
  (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj (restrictRingAlgebra f)) ≫ Ftot S)
  (Ftot T ≫ barrattEcclesRestrict f)
```

R11・R12はこの欄と同じ全族の両境界を照合してから完了と数える。ここでは仮定・sorry付きのLean宣言を追加していない。

### 161.3 今回の検証済みの型

共通：`A : Type u`、`[CommRing A]`。

登録候補：`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotalizationComparison`（33行）。

```lean
def strictBETotVertex :
    nerve (AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) ⟶ CAlg_R A

theorem strictBETotVertex_at (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (strictBETotVertex A).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ F) =
      (algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ ((framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F))

```

登録候補：`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotalizationInput`（74行）。

```lean
def strictBECosimplicialNerve (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      nerve (operad A).Algebra

def strictBECosimplicialDiagram (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶ CAlg_R A

def strictBECosimplicialEvaluationNerve :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⊗
      nerve (AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) ⟶
        nerve (operad A).Algebra

def strictBECosimplicialEvaluation :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⊗
      nerve (AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) ⟶ CAlg_R A

theorem strictBECosimplicialEvaluationNerve_at
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))
      (Δ[0] : SSet.{u+1})) ≫ (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex F)) ≫
        strictBECosimplicialEvaluationNerve A = strictBECosimplicialNerve A F

```

登録候補：`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUnderlyingSource`（44行）。

```lean
def strictBETotUnderlyingSourceIso :
    FunctorIso (strictBETotVertex A ≫ cAlgForgetDerived A)
      (nerveMap (framedLimitFunctor A (AsSmall.{u} SimplexCategory) ⋙
        Operad.Algebra.forget (operad A)) ≫ complexOrdinaryDerivedSource A)

def strictBECosimplicialUnderlyingDiagramIso
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    FunctorIso (strictBECosimplicialDiagram A F ≫ cAlgForgetDerived A)
      (strictBECosimplicialNerve A F ≫ algebraUnderlyingDerivedSource A)

def strictBECosimplicialUnderlyingEvaluationIso :
    FunctorIso (strictBECosimplicialEvaluation A ≫ cAlgForgetDerived A)
      (strictBECosimplicialEvaluationNerve A ≫ algebraUnderlyingDerivedSource A)

```

### 161.4 検収・実測・次の接続

コード **`03e732bf0`**。R01の最初の対象ビルド205は `.app _` の零単体の次数推論で失敗し、両方の次数を明示して修正。計算上限を増やさず個別検査を通した後、最終対象ビルド206は **9,459 jobs・終了コード0**、三本だけの小監査 **12（2・7・3）宣言、標準三公理のみ**。205を成功の回として数えない。ログ `/private/tmp/isw2-build205.log`・`206.log`、監査 `/private/tmp/AuditISW2BER01Input.lean`。ハンドル終了コード0を確認済み、鍵返却済み。整理券一枚、`--class impl --wait 3600`、対象ビルド・小監査中だけ使用。sorry・独自公理0。

3b-4の検証済みは **3モジュール・151行**、外枠15,000行まで14,849行。登録候補は別の `is-w2-be-20261114-modules.json` に記録し、G10の366本・22,870行と混ぜない。200行超のファイルなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。

次はR02の元のframe計算対象と全図式評価の間のnative全錐族、およびR03の実right-frame Homとpinched Homの同じ制限の比較を接続する。今回のU源比較だけでR04の加群Totとの最終同型が済んだとは数えない。承認待ち・範囲変更・規模による停止ではなく、検証済みの保存点。Tot先行・実現・任意coherent BE図式の段0までの/goalはactiveのまま保持する。


## 162. 同じBE frameの全Hom比較・重み付き錐空間（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R03の実frame比較の準備。R02・R03のnative全錐・極限性を完了とは数えない。

### 162.1 今回の型（既存構成の法則）

共通：`A : Type u`、`[CommRing A]`、`K : Type u`、`[SmallCategory K]`。局所の模型構造は既存 `modelCategory A`。新しい模型構造・重み・置換を作らない。以下の型は各ファイルの同じ変数・openの下で読む。

`StrictDiagramTotModelSource`（100行）：

```lean
def strictBETotModelNerveIso :
    nerve (modelRelativeCategory (operad A).Algebra).category ≅
      nerve (allAlgebraRelativeCategory A).category

theorem strictBETotModelNerveIso_weakEdges :
    (strictBETotModelNerveIso A).inv.app (Opposite.op ⦋1⦌) ''
      weakNerveEdges (allAlgebraRelativeCategory A) =
        weakNerveEdges (modelRelativeCategory (operad A).Algebra)

def strictBETotModelSource :
    nerve (modelRelativeCategory (operad A).Algebra).category ⟶ CAlg_R A

theorem strictBETotModelSource_isLocalization :
    IsLocalization (strictBETotModelSource A)
      (weakNerveEdges (modelRelativeCategory (operad A).Algebra))

theorem strictBETotModelSource_vertex (X : (operad A).Algebra) :
    (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X)) =
      (algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)
```

`StrictDiagramTotRightFrameComparison`（41行）：

```lean
def strictBETotRightFramePinchedEquivalence
    (X : (operad A).Algebra) [IsCofibrant X] (Y : (operad A).Algebra) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u+1,u}).obj ((rightFrameHom (rightFrameFamily A) X).obj Y))
      (pinchedHom ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))
```

`StrictDiagramTotRightFrameCoherent`（41行）：

```lean
def strictBETotRightFrameCoherentComparison
    (X : (operad A).Algebra) [IsCofibrant X] :
    (FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X) (rightFrameFamily A) 0)
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X) (rightFrameFamily A) 6)) ×
      FrameHom.CoherentLocalizationComparison
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (operad A).Algebra)) (strictBETotModelSource A)
```

`StrictDiagramTotTensorFrame`（75行）：

```lean
def strictBETotTensorWeights : SimplexCategory ⥤ (Kᵒᵖᵒᵖ ⥤ SSet.{u})

def strictBETotTensorFrameFamily :
    (K ⥤ (operad A).Algebra)ᵒᵖ ⥤ SimplexCategory ⥤ (operad A).Algebraᵒᵖ

theorem strictBETotTensorFrameFamily_obj (F : K ⥤ (operad A).Algebra) :
    (strictBETotTensorFrameFamily A K).obj (op F) =
      HomotopyWeight.tensorFrame Kᵒᵖ (HomotopyWeight.framedLimitWeight K)
        (rightFrameDiagram A K F) := rfl

/-- 同じ標準零単体の単位則は、全図式射に自然な零次同型を与える。 -/
def strictBETotTensorFrameZeroIso :
    strictBETotTensorFrameFamily A K ⋙
      (evaluation SimplexCategory (operad A).Algebraᵒᵖ).obj ⦋0⦌ ≅
        framedLimitOpFunctor A K

def strictBETotTensorFrameZeroIso :
    strictBETotTensorFrameFamily A K ⋙
      (evaluation SimplexCategory (operad A).Algebraᵒᵖ).obj ⦋0⦌ ≅
        framedLimitOpFunctor A K

def strictBETotTensorFrameAugmentation :
    strictBETotTensorFrameFamily A K ⟶
      framedLimitOpFunctor A K ⋙ Functor.const SimplexCategory
```

`StrictDiagramTotTensorFrameProperties`（61行）：

```lean
theorem strictBETotTensorFrame_reedyCofibrant (F : K ⥤ (operad A).Algebra) :
    reedyLeft simplex (cofibrations (operad A).Algebraᵒᵖ)
      (initial.to ((strictBETotTensorFrameFamily A K).obj (op F)))

theorem strictBETotTensorFrame_homotopicallyConstant (F : K ⥤ (operad A).Algebra)
    {n m : SimplexCategory} (α : n ⟶ m) :
    weakEquivalences (operad A).Algebraᵒᵖ
      (((strictBETotTensorFrameFamily A K).obj (op F)).map α)

theorem strictBETotTensorFrameAugmentation_weak
    (F : K ⥤ (operad A).Algebra) (n : SimplexCategory) :
    weakEquivalences (operad A).Algebraᵒᵖ
      (((strictBETotTensorFrameAugmentation A K).app (op F)).app n)

def strictBETotTensorFrameConeIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    ((SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
      ((strictBETotTensorFrameFamily A K).obj (op F))).obj (op (framedLimitProbe A Y))) ≅
        (framedLimitConeSpace A K Y).obj F
```

`StrictDiagramTotFrameHomComparison`（73行）：

```lean
abbrev strictBETotFrameCommonFamily

def strictBETotFrameHomLeft :
    FrameOverFunctor.hom (FrameOverFunctor.resolution (rightFrameFamily A)
      (framedLimitOpFunctor A K)) ⟶ FrameOverFunctor.hom (strictBETotFrameCommonFamily A K)

def strictBETotFrameHomRight :
    FrameOverFunctor.hom (strictBETotTensorFrameFamily A K) ⟶
      FrameOverFunctor.hom (strictBETotFrameCommonFamily A K)

theorem strictBETotFrameHomLeft_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) [IsCofibrant Y] :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomLeft A K).app (op (op F))).app (op Y))

theorem strictBETotFrameHomRight_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) [IsCofibrant Y] :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomRight A K).app (op (op F))).app (op Y))
```

`StrictDiagramTotProbeFrameComparison`（50行）：

```lean
def strictBETotFrameHomLeftSourceIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    ((FrameOverFunctor.hom (FrameOverFunctor.resolution (rightFrameFamily A)
      (framedLimitOpFunctor A K))).obj (op (op F))).obj (op Y) ≅
      ((rightFrameHom (rightFrameFamily A) Y).obj ((framedLimitFunctor A K).obj F))

theorem strictBETotProbeFrameHomLeft_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomLeft A K).app (op (op F))).app (op (framedLimitProbe A Y)))

theorem strictBETotProbeFrameHomRight_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomRight A K).app (op (op F))).app (op (framedLimitProbe A Y)))
```

### 162.2 同じものの比較と未完了の境界

`AsSmall` のmodelRelativeCategoryと、既存のULiftHomによるallAlgebraRelativeCategoryのnerve同型を、同じ対象・射から構成。その逆像の弱辺集合を照合し、既存の全代数の局所化を前合成して同じmodelSourceを得る。既存のmodelRightFramePinchedEquivalence・全targetについてのmodelRightFrameCoherentComparisonへその源を渡す。

同じframedLimitWeightとrightFrameDiagramを実現する全関手を標準単体で評価。零次同型による増大写像・Reedy cofibrant・homotopically constant・増大の弱同値性は既存tensorFrameの法則。`tensorFrameHomIso`は元のframedLimitConeSpaceとの**全単体集合の同型**。計算対象のright frameとこのtensor frameの共通frameを、既存FrameOverFunctorで取る。左右の比較は元の同じ任意probeで無条件に単体的ホモトピー同値。rightFrameHomへの源の同定は`rightFrameHomOpIso`であり、定義的等式で代用しない。

これはπ₀だけの比較ではないが、指定native錐の全制限との最終照合は未完了。元の指定頂点・脚・全単体の錐とnative極限性を次に接続する。既存通常局所化の随伴だけからnative普遍性を結論しない。

### 162.3 検収

モデル源・pinched比較の二本はコード`bad328231`、対象ビルド208 **9,817 jobs・終了0**、二本の小監査**19（9・10）宣言・標準三公理のみ**。207・209は既存の必要依存だけの対象ビルドで、それぞれ9,730・2,423 jobs・終了0。

210は四本の対象ビルド自体は成功したが、合併監査で自動生成された局所instance名の衝突を検出したため、検収成功とは数えない。未コミットの五本の局所instanceに個別の名前を与え、既存検証済み宣言は変更せず修正。最終211は五本の対象ビルド **9,835 jobs・終了0**、BE新規全10本の小監査 **64（2・7・3・9・10・4・10・6・7・6）宣言・標準三公理のみ**。実ハンドル8092の終了0を確認。sorry・独自公理0。計算上限の変更なし。

整理券一枚、`--class impl --wait 3600`、ビルドと小監査の間だけ保持し返却済み。ログ`/private/tmp/isw2-build208.log`・`211.log`、最終監査`/private/tmp/AuditISW2BEFrameComplete.lean`。main・入口・公式監査・⑤a・既存FramedLimit*・CAlgUnderlyingDerivedComparisonの変更なし。

3b-4の検証済み **10モジュール・592行**（外枠15,000行）。登録候補は `is-w2-be-20261114-modules.json`。200行超の新規ファイルなし。承認待ちの停止ではなく検証済みの保存点で、/goalの続きへ進む。


## 163. 同じ全strict BE図式の評価・頂点・forgetの局所化（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R05の局所化上の源と三つの全関手の因子化を証明分割。R02〜R05の最終結論が済んだとは数えない。

### 163.1 R05の源と、同じ全strict図式の保持

§152の `TotBE`・`ForgetStrictBEInfinity` の源を、元のstrict BE図式のnerveと、その同じobjectwise擬同型の辺集合の `edgeLocalization` とする。元の全図式の評価・元のframedLimitFunctorによる全頂点・同じforgetを、既存局所化の全関手圏の普遍性で延長した。それぞれ元の全strict図式の全射列との指定FunctorIsoを保持する。BE値の任意coherent図式の厳密化や評価比較の同値を主張しない。

forgetの入力は元の `AsSmall.{u} Δ` の図式を指定 `AsSmall.up` でΔへ引き戻し、元の `Operad.Algebra.forget` を後合成するもの。図式の各射は元の同じ成分の `.hom` に厳密に等しい。このobjectwise擬同型は加群図式の既存指定局所化で反転される。R05の `ForgetStrictBEInfinity` の全因子化までを実装し、最終の `TotBE ≫ U` と `ForgetStrictBEInfinity ≫ TotDA` の比較はR02〜R04の同じ全錐の照合から続ける。

### 163.2 検証済みの型

共通：`A : Type u`、`[CommRing A]`。次は各ファイルの変数とopenの下で読む。

`StrictDiagramTotLocalization`（50行）：

```lean
abbrev StrictBETotDiagramNerve : SSet.{u+1}

def strictBETotDiagramWeakEdges : Set ((StrictBETotDiagramNerve A) _⦋1⦌)

theorem strictBETotDiagramWeakEdges_mk₁
    {F G : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra} (f : F ⟶ G) :
    ComposableArrows.mk₁ f ∈ strictBETotDiagramWeakEdges A ↔
      ∀ j, QuasiIso (f.app j).hom

def StrictBETotDiagramInfinity : SSet.{u+1}

instance strictBETotDiagramInfinity_quasicategory :
    Quasicategory (StrictBETotDiagramInfinity A)

def strictBETotDiagramLocalization :
    StrictBETotDiagramNerve A ⟶ StrictBETotDiagramInfinity A

theorem strictBETotDiagramLocalization_isLocalization :
    IsLocalization (strictBETotDiagramLocalization A) (strictBETotDiagramWeakEdges A)
```

`StrictDiagramTotEvaluationLocalization`（94行）：

```lean
def strictBETotDiagramFamily : StrictBETotDiagramNerve A ⟶
    (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
      (CAlg_R A) := curry (strictBECosimplicialEvaluation A)

/-- 点での全評価は元の同じ通常評価のnerveに一致。 -/
theorem strictBETotDiagramFamily_evaluation (j : AsSmall.{u} SimplexCategory) :
    strictBETotDiagramFamily A ≫ evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ j)) =
      nerveMap ((CategoryTheory.evaluation (AsSmall.{u} SimplexCategory)
        (operad A).Algebra).obj j) ≫ algebraCAlgSource A

theorem strictBETotDiagramFamily_evaluation (j : AsSmall.{u} SimplexCategory) :
    strictBETotDiagramFamily A ≫ evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ j)) =
      nerveMap ((CategoryTheory.evaluation (AsSmall.{u} SimplexCategory)
        (operad A).Algebra).obj j) ≫ algebraCAlgSource A

theorem strictBETotDiagramFamily_inverts :
    InvertsEdges (strictBETotDiagramFamily A) (strictBETotDiagramWeakEdges A)

theorem exists_strictBETotLocalizedEvaluation :
    ∃ ev : StrictBETotDiagramInfinity A ⟶
        (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
          (CAlg_R A),
      Nonempty (FunctorIso (strictBETotDiagramLocalization A ≫ ev)
        (strictBETotDiagramFamily A))

def strictBETotLocalizedEvaluation : StrictBETotDiagramInfinity A ⟶
    (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
      (CAlg_R A) := (exists_strictBETotLocalizedEvaluation A).choose

/-- 延長の指定全同型は元の全strict評価を保持する。 -/
def strictBETotLocalizedEvaluation_factor :
    FunctorIso (strictBETotDiagramLocalization A ≫ strictBETotLocalizedEvaluation A)
      (strictBETotDiagramFamily A)

def strictBETotLocalizedEvaluation_factor :
    FunctorIso (strictBETotDiagramLocalization A ≫ strictBETotLocalizedEvaluation A)
      (strictBETotDiagramFamily A)
```

`StrictDiagramTotVertexLocalization`（57行）：

```lean
theorem strictBETotVertex_inverts :
    InvertsEdges (strictBETotVertex A) (strictBETotDiagramWeakEdges A)

theorem exists_strictBETotLocalizedVertex :
    ∃ V : StrictBETotDiagramInfinity A ⟶ CAlg_R A,
      Nonempty (FunctorIso (strictBETotDiagramLocalization A ≫ V) (strictBETotVertex A))

def strictBETotLocalizedVertex : StrictBETotDiagramInfinity A ⟶ CAlg_R A
```

`StrictDiagramTotUnderlyingLocalization`（86行）：

```lean
def strictBETotForgetDiagram :
    (AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) ⥤
      StrictComplexDiagram A .cosimplicial

theorem strictBETotForgetDiagram_map
    {F G : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra} (f : F ⟶ G)
    (j : SimplexCategory) :
    ((strictBETotForgetDiagram A).map f).app j = (f.app (AsSmall.up.obj j)).hom := rfl

/-- 元の全BE図式から、同じ加群図式の指定局所化への写像。 -/
def strictBETotForgetDiagramSource :
    StrictBETotDiagramNerve A ⟶ StrictDiagramInfinity A .cosimplicial

def strictBETotForgetDiagramSource :
    StrictBETotDiagramNerve A ⟶ StrictDiagramInfinity A .cosimplicial

theorem strictBETotForgetDiagramSource_inverts :
    InvertsEdges (strictBETotForgetDiagramSource A) (strictBETotDiagramWeakEdges A)

theorem exists_strictBETotLocalizedForget :
    ∃ U : StrictBETotDiagramInfinity A ⟶ StrictDiagramInfinity A .cosimplicial,
      Nonempty (FunctorIso (strictBETotDiagramLocalization A ≫ U)
        (strictBETotForgetDiagramSource A))

def strictBETotLocalizedForget :
    StrictBETotDiagramInfinity A ⟶ StrictDiagramInfinity A .cosimplicial

def strictBETotLocalizedForget_factor :
    FunctorIso (strictBETotDiagramLocalization A ≫ strictBETotLocalizedForget A)
      (strictBETotForgetDiagramSource A)
```

### 163.3 検収・残り

対象ビルド212：最初の三本 **9,489 jobs・終了0**、BE新規全13本の小監査 **90（2・7・3・9・10・4・10・6・7・6・13・8・5）宣言・標準三公理のみ**。その前の個別検査では `nerve.edgeMk` の像と `edgeOfSimplex` の表示を明示して照合した。計算上限は増やしていない。

213はforgetの輸送で `InvertsEdges` の暗黙引数名を誤り失敗、検収成功とは数えない。`a` に修正し、既存の反転命題を `IsInvertibleEdge` の同じ辺として明示。個別検査の終了0後、最終214は **9,492 jobs・終了0**、BE新規全14本の小監査 **99（2・7・3・9・10・4・10・6・7・6・13・8・5・9）宣言・標準三公理のみ**。実ハンドル51046・93720の終了0を確認、鍵返却済み。sorry・独自公理0。

整理券は同時に一枚だけ、`--class impl --wait 3600`、対象ビルド・小監査の間だけ保持。ログ`/private/tmp/isw2-build212.log`・`214.log`、小監査`/private/tmp/AuditISW2BEUnderlyingLocalization.lean`。公式監査・入口・main・⑤a・既存FramedLimit*・CAlgUnderlyingDerivedComparisonは変更していない。

3b-4の検証済み **14モジュール・879行**、外枠15,000行まで14121行。新規200行超のファイルなし。登録候補を同じBE用JSONに追記。G10の366本とは分ける。

次はR02〜R03の核心へ戻る。同じ実frameのHom比較と重み付き錐空間の同型は§162で検証済みだが、これだけで元のCAlg図式上の指定native全錐とその極限性は得ていない。全族の錐を独立な点ごとの錐から自然だと仮定したり、通常局所化の随伴の余単位をnativeな全錐の代用にしたりしない。元の実frameの標準射を持つ全錐を構成し、同じ制限射との等式を追跡する。今回の局所化の因子化はこの構成後のR05へ再利用する。保存点であり、承認待ち・外枠・新規数学による停止ではない。/goalはactiveのまま。


## 164. 普遍重み付き錐・元のprobe・実Homの標準点（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R02・R03の既存随伴単位・零次同型の法則を分割。指定native錐・その極限性は未完了。

### 164.1 元の普遍錐を固定する

同じFrameWeightRealizationの随伴の単位を、元の重みで評価する。これが `strictBETotUniversalWeightedCone` で、随伴で戻すと**同じ元の計算対象の恒等射**になる。任意の元の射が表す重み付き錐は、この単位への同じ前合成。元の全計算関手の射の反対は、同じframe族の射の実現のmateそのものでもある。

元の計算対象の同じ `framedLimitProbeComparison` を前合成すると、同じ `framedLimitConeSpace` の具体的な普遍probe錐の零単体が得られる。さらに元の `strictBETotTensorFrameConeIso` は、零次同型にそのprobe比較を合成したHomを、**その同じ零単体**に写す。この同定を単なるπ₀上の等式へ弱めていない。

### 164.2 検証済みの型

共通のunit則の宇宙・圏・余極限の仮定はソースと同じ。BE側は `A : Type u`、`[CommRing A]`、`K : Type u`、`[SmallCategory K]`。

`SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightUnitNaturality`（26行）：

```lean
theorem unit_frame_naturality {B B' : K ⥤ SimplexCategory ⥤ C}
    (a : B ⟶ B') (W : Kᵒᵖ ⥤ SSet.{w}) :
    (adjunction K B').unit.app W ≫ ((homFamily K).map a.op).app ((functor K B').obj W) =
      (adjunction K B).unit.app W ≫ (hom K B).map ((map K a).app W)
```

`SerrePositivity.EInfinity.HomotopyWeight.TensorConeUnitPoint`（36行）：

```lean
theorem tensorFrameHomIso_point (Y : C)
    (f : (FrameWeightRealization.functor K B).obj W ⟶ Y) :
    (((tensorFrameHomIso K W B).hom.app Y).app (Opposite.op ⦋0⦌))
      ((tensorFrameZeroIso K W B).hom ≫ f) =
        conePoint Kᵒᵖ W ((FrameWeightRealization.adjunction K B).homEquiv W Y f)
```

`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalWeightedCone`（67行）：

```lean
def strictBETotUniversalWeightedCone (F : K ⥤ (operad A).Algebra) :
    HomotopyWeight.framedLimitWeight K ⟶
      (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).obj
        (op ((framedLimitFunctor A K).obj F))

theorem strictBETotUniversalWeightedCone_identity (F : K ⥤ (operad A).Algebra) :
    ((FrameWeightRealization.adjunction Kᵒᵖ (rightFrameDiagram A K F)).homEquiv
      (HomotopyWeight.framedLimitWeight K)
      (op ((framedLimitFunctor A K).obj F))).symm
        (strictBETotUniversalWeightedCone A K F) = 𝟙 _

theorem strictBETotUniversalWeightedCone_precomp (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (f : Y ⟶ (framedLimitFunctor A K).obj F) :
    (weightedCotensorHomEquiv A K F (HomotopyWeight.weight K) Y) f =
      strictBETotUniversalWeightedCone A K F ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).map f.op

def strictBETotFrameMap {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    rightFrameDiagram A K G ⟶ rightFrameDiagram A K F

theorem strictBETotFrameMap_eq {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    strictBETotFrameMap A K f = (rightFrameDiagramFamily A K).map f.op

theorem strictBETotFunctor_map_op {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    ((framedLimitFunctor A K).map f).op =
      (FrameWeightRealization.map Kᵒᵖ ((rightFrameDiagramFamily A K).map f.op)).app
        (HomotopyWeight.framedLimitWeight K)
```

`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalProbeCone`（46行）：

```lean
def strictBETotUniversalProbeWeightedCone (F : K ⥤ (operad A).Algebra) :
    HomotopyWeight.framedLimitWeight K ⟶
      (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).obj
        (op (framedLimitProbe A ((framedLimitFunctor A K).obj F)))

theorem strictBETotUniversalProbeWeightedCone_comparison
    (F : K ⥤ (operad A).Algebra) :
    strictBETotUniversalProbeWeightedCone A K F =
      weightedCotensorHomEquiv A K F (HomotopyWeight.weight K)
        (framedLimitProbe A ((framedLimitFunctor A K).obj F))
        (framedLimitProbeComparison A ((framedLimitFunctor A K).obj F))

def strictBETotUniversalProbeConePoint (F : K ⥤ (operad A).Algebra) :
    ((framedLimitConeSpace A K ((framedLimitFunctor A K).obj F)).obj F) _⦋0⦌
```

`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalProbePointComparison`（43行）：

```lean
theorem strictBETotTensorFrameConeIso_universalPoint
    (F : K ⥤ (operad A).Algebra) :
    ((strictBETotTensorFrameConeIso A K F ((framedLimitFunctor A K).obj F)).hom.app
      (Opposite.op ⦋0⦌))
        ((strictBETotTensorFrameZeroIso A K).hom.app (op F) ≫
          (framedLimitProbeComparison A ((framedLimitFunctor A K).obj F)).op) =
      strictBETotUniversalProbeConePoint A K F
```

### 164.3 全自然性の未検証部を区別する

共通の `FrameWeightRealization.unit_frame_naturality` は、既存の `unit_conjugateEquiv_symm` を直接代入して証明済み。一方、それをBE全図式族の評価表示と独立なrightFrameDiagram表示の間で一括照合する特殊化では、定義展開が200,000 heartbeatsに当たった。型・計算上限は変更せず、単位則・同じ全frame族の射・実現の射の表示を小さく分割した。

特殊化の全自然性の未検証部分は `/private/tmp/StrictBETotUniversalWeightedConeNaturality-draft.lean.txt` に残し、成功した宣言・対象ビルドに含めない。残る型は次（同じ元の全frame族の射で、別の比較射を選ばない）：

```lean
theorem strictBETotUniversalWeightedCone_naturality
    {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    strictBETotUniversalWeightedCone A K F ≫
      ((FrameWeightRealization.homFamily Kᵒᵖ).map
        ((rightFrameDiagramFamily A K).map f.op).op).app
          (op ((framedLimitFunctor A K).obj F)) =
      strictBETotUniversalWeightedCone A K G ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K G)).map
          (((framedLimitFunctor A K).map f).op)
```

この未検証部を一覧から除外したり、R02の全族を点ごとの錐だけへ縮めたりしない。次の指定native錐の構成と合わせて閉じる。現時点の `strictBETotUniversalProbeConePoint` をnative join錐の代用にはしない。

### 164.4 検収

215は共通単位則と既存ConePointsの依存だけの対象ビルド **2,325 jobs・終了0**。型照合の途中の個別検査は、未検証部でheartbeat・一時ファイルのインデント・開いた記法の不足を検出した回を成功に数えず、上記の検証済み部を合併した `CheckBETotUniversalProbePointComparison2.lean` の終了0を確認してから対象ビルドした。計算上限は増やしていない。

最終216：新規五本の対象ビルド **4,018 jobs・終了0**、3b-4新規全19本の小監査 **113（2・7・3・9・10・4・10・6・7・6・13・8・5・9・1・1・7・3・2）宣言・標準三公理のみ**。実ハンドル92611・41565の終了0を確認、鍵返却済み。ログ `/private/tmp/isw2-build215.log`・`216.log`、小監査 `/private/tmp/AuditISW2BEUniversalPoint.lean`。sorry・独自公理0。

同時に整理券一枚、`--class impl --wait 3600`。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。新規200行超のファイルなし。これは保存点であり、承認待ちや外枠による停止ではない。

3b-4新規は **19モジュール・1097行**（今回218行、共通二本を含む。外枠15,000行）。登録候補JSONにも共通二本を記録し、BSやG10の登録候補と混ぜない。次は元の試験対象とprobeのnative Homの始点を合わせ、同じ普遍錐・制限射へ接続する。/goalはactive。


## 165. 元の全BE図式と正本Hom∞の全比較・普遍錐の全自然性（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R02・R03の元の全Hom比較・源移送・単位自然性まで。native join錐・極限性はまだ未完了。

### 165.1 同じ全単体と同じ源を保持する

§164.3で未検証だった `strictBETotUniversalWeightedCone_naturality` は、**報告した型のまま閉じた**。同じ全frame族の対象表示と同じ計算対象の反対表示を小さな等式で正規化してから、既存のmateの単位則を適用した。計算上限は変更していない。独立な二つの構成を同じものだと仮定することも、全自然性を点ごとの等式に置き換えることもしていない。

元のprobe比較の実辺が与える源の頂点同型と、既存の `pinchedPrecomposeEquivalence` を用い、元の任意の試験対象に対する実right-frame Homから同じnative pinched Homへの無条件の全空間同値を得た。その頂点同型の順射は元のprobe辺の同じ類であり、実比較の順射は同じframe比較と同じprobe比較の逆による前合成。

さらに既存 `FrameHom.rightFrameTerminalHomIso`（原本Yonedaの全比較を代入済み）を、既存六辺の全coherent比較と合成。元のright-frame Homの全標的図式から正本 `homInfinityCovariant` への**全FunctorIso**を得た。probe比較の源同型の反転・宇宙持ち上げを元のco-Yonedaで写すことで、こちらも元の任意の試験対象に無条件化。点ごとの逆を選んで自然だと仮定していない。

モデル相対圏のAsSmall表示から元の全代数のnerveへの比較ではHom宇宙が異なるため、その包含を元の全nerve上で直接記述した。指定modelSourceへの合成は、元の `algebraCAlgSource` と**全単体で厳密に等しい**。この一致を使って全Hom∞比較を元の全代数源へ戻し、さらに元の同じstrict BE余単体図式の全nerveへ前合成した。

### 165.2 今回の検証済みの型

共通：`A : Type u`、`[CommRing A]`。普遍錐の全自然性には `K : Type u`、`[SmallCategory K]`。局所の模型とfactorizationは既存と同じ具体的なもの。源cofibrancyを要求する欄と、同じprobeで無条件化した欄を区別する。

`StrictDiagramTotProbeNativeHomComparison`（65行）：

```lean
def strictBETotProbeSourceIso (X : (operad A).Algebra) :
    VertexIso ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (framedLimitProbe A X)))
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))

theorem strictBETotProbeSourceIso_hom (X : (operad A).Algebra) :
    (strictBETotProbeSourceIso A X).hom = Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk (framedLimitProbeComparison A X)).map (algebraCAlgSource A)).toTruncated

def strictBETotProbeNativeHomEquivalence (X Y : (operad A).Algebra) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u+1,u}).obj
        ((rightFrameHom (rightFrameFamily A) (framedLimitProbe A X)).obj Y))
      (pinchedHom ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))

theorem strictBETotProbeNativeHomEquivalence_hom (X Y : (operad A).Algebra) :
    (strictBETotProbeNativeHomEquivalence A X Y).hom =
      (strictBETotRightFramePinchedEquivalence A (framedLimitProbe A X) Y).hom ≫
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
          (strictBETotProbeSourceIso A X).inv
```

`StrictDiagramTotUniversalWeightedConeNaturality`（45行）：

```lean
theorem strictBETotFrameDiagram_obj (F : K ⥤ (operad A).Algebra) :
    (rightFrameDiagramFamily A K).obj (op F) = rightFrameDiagram A K F

theorem strictBETotFunctor_obj_op (F : K ⥤ (operad A).Algebra) :
    op ((framedLimitFunctor A K).obj F) =
      (FrameWeightRealization.functor Kᵒᵖ
        ((rightFrameDiagramFamily A K).obj (op F))).obj
          (HomotopyWeight.framedLimitWeight K)

theorem strictBETotUniversalWeightedCone_naturality
    {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    strictBETotUniversalWeightedCone A K F ≫
      ((FrameWeightRealization.homFamily Kᵒᵖ).map
        ((rightFrameDiagramFamily A K).map f.op).op).app
          (op ((framedLimitFunctor A K).obj F)) =
      strictBETotUniversalWeightedCone A K G ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K G)).map
          (((framedLimitFunctor A K).map f).op)
```

`StrictDiagramTotModelSourceComparison`（40行）：

```lean
def strictBETotModelUpNerve :
    nerve (operad A).Algebra ⟶
      nerve (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (operad A).Algebra).category

theorem strictBETotModelSource_up :
    strictBETotModelUpNerve A ≫ strictBETotModelSource A = algebraCAlgSource A
```

`StrictDiagramTotFrameHomInfinity`（43行）：

```lean
def strictBETotFrameHomInfinityIso (X : (operad A).Algebra) [IsCofibrant X] :
    FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X)
        (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)))
```

`StrictDiagramTotProbeHomInfinityComparison`（57行）：

```lean
def strictBETotProbeHomInfinitySourceIso (X : (operad A).Algebra) :
    FunctorIso
      (homInfinityCovariant ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (framedLimitProbe A X))))
      (homInfinityCovariant ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex X)))

def strictBETotProbeFrameHomInfinityIso (X : (operad A).Algebra) :
    FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
          (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)))
```

`StrictDiagramTotAlgebraHomInfinityComparison`（64行）：

```lean
def strictBEAlgebraProbeHomInfinityIso (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
            (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (algebraCAlgSource A) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)))

def strictBETotDiagramProbeHomInfinityIso
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra)
    (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialNerve A F) ≫
        (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
          FrameHom.rightFrameHammockCoherentDiagram
            ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
              (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialDiagram A F) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)))
```

### 165.3 検収

217は先頭の整理券で調整役の監査を待ち、同じ実ハンドル39750を生存確認し続けた。再起動・整理券の重複発行なし。最終 **9,818 jobs・終了0**、新規全20本の小監査 **123（§164の113に新規10）宣言・標準三公理のみ**。

218はその終了0・返却後に次の一枚を発行し、残る五本と必要な既存依存だけを対象ビルド。**10,583 jobs・終了0**、新規全25本の小監査 **166（2・7・3・9・10・4・10・6・7・6・13・8・5・9・1・1・7・3・2・10・4・4・10・11・14）宣言・標準三公理のみ**。実ハンドル80009の終了0を確認。鍵返却済み。ログ `/private/tmp/isw2-build217.log`・`218.log`、最終小監査 `/private/tmp/AuditISW2BEHomInfinity.lean`。

個別検査でprobeのcofibrancyを型推論へ渡す必要、AsSmall包含のHom宇宙の違い、Functor.hextの射の異種等式を明示する必要を検出して修正した。既存依存を一時合併した検査では `stdSimplex` の名前衝突があったため一時ファイルだけを完全修飾し、既存ソースを変えなかった。最終218は各実モジュールを独立にビルドし、合併監査も成功した。これにより一時合併検査だけから成功を推測していない。

sorry・独自公理0。計算上限の変更なし。`--class impl --wait 3600`、同時整理券一枚、ビルド・小監査の間だけ鍵を保持。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

3b-4の検証済み **25モジュール・1411行**（今回314行、共通二本を含む。外枠15,000行）。新規200行超のファイルなし。登録候補は同じBE用JSONへ追記。R02・R03のnative錐・極限性を完成とは数えず、次の接続は重み付きframe錐とnative切断の間の比較。/goalはactive。

## 166. 一覧外の数学：選んだ一点重みとnative切断のBK重みの比較（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。検証済みコードは `98df07409`（§165、25本・1,411行、166宣言、標準三公理のみ）。R02・R03の残りの経路で、以下の数学的補題が必要になったため報告する。Leanの新しい証明・公理・仮定は追加していない。

### 166.1 必要になった追加の型：R03a案

`J := AsSmall.{u} SimplexCategory`、`I := Jᵒᵖᵒᵖ`。元のBE計算対象は選ばれた `HomotopyWeight.framedLimitWeight J` を使う。一方、既存のnative切断との比較は `bousfieldKanWeight I`（各値 `N(I/i)`）を使う。この二つを定義的に同じだと扱えない。必要なのは、同じ一つの重みの射による制限が、全Kan係数図式についてホモトピー同値になること。

追加を提案する主張の型は次のとおり（`J`・`I`は略記せず展開）：

```lean
-- universe u
-- open CategoryTheory
-- open SerrePositivity.EInfinity
-- open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
-- open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

theorem exists_strictBETotWeightComparison :
    ∃ j : bousfieldKanWeight ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⟶
        HomotopyWeight.framedLimitWeight (AsSmall.{u} SimplexCategory),
      ∀ (H : ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⥤ SSet.{u}),
        (∀ i, SSet.KanComplex (H.obj i)) →
          IsSimplicialHomotopyEquivalence (weightedSectionsPre j H)
```

向きは `j : BK → W` から `sections(W,H) → sections(BK,H)`。一つの `j` を全Hに使うので、元の係数図式の射に関する自然性は既存 `weightedSectionsPre` の法則で保持できる。元のframe・重み・計算対象は変更せず、重み比較を通して元の普遍錐をnative切断へ送る。`[ModelCategory SSet]` は型に足さない。

型そのものは `/private/tmp/CheckISW2WeightComparisonStatement.lean` に同じPropとして記述し、個別検査の**終了0**を確認した（ログ `/private/tmp/checkISW2WeightComparisonStatement2.log`）。これは定理の証明ではなく、型の検査だけである。本体には追加していない。

### 166.2 なぜ既存構成の法則だけとは数えなかったか

- `HomotopyWeight.weight_cofibrant`・`framedLimitWeight_cofibrant` は選んだ小対象分解の重みの射影cofibrancyを証明する。別の具体的な重み `bousfieldKanWeight` の射影cofibrancyや、その重みとのHom空間の比較はそのままでは得られない。
- `weightedSectionsPre_homotopyEquivalence_of_extensions` は、**全ての成分ごとのanodyneな自然変換に対する延長性**を係数図式に要求する。今回の入力の各値がKanであるだけでは、その強い延長性を代入できない。
- `coneSpace_kanComplex`・`coneSpace_map_boundary_rlp` は、固定した射影cofibrant重みに対する係数方向の法則である。異なる二つの重みを比較する今回の型の証明にはなっていない。
- `YonedaHomotopyWeight`・抽象projective図式モデルの入口は値圏のModelCategory等を仮定する。これをSSetに無条件に代入したり、禁止された `[ModelCategory SSet]` を足したりしない。
- §165の全Hom∞比較は元の正本Hom関手まで接続したが、二つの重みの違いを消す定理ではない。通常局所化の随伴・π₀の同値・忘却Uの極限保存で、この重み比較を代用しない。

このため、随伴単位や全自然性の表示を分割した§164〜165とは異なり、R03aは新しい数学的補題として扱う。§152の一覧は既存frame Homとnative切断の橋を使う所で、この二つの具体的な重みのHom不変性を独立に洗い出していなかった。

### 166.3 証明の見込みと配置

候補の経路は、まず指定されたBK重みについて自由境界による細胞分解を示すこと。次数nの鎖 `i₀ → … → iₙ → i` を、最後の射 `iₙ → i` に関して自由な図式として扱い、非退化な鎖の境界の付加から射影cofibrancyを得る。その中で使う型は次：

```lean
-- open CategoryTheory Limits
(HomotopyWeight.boundaries ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ)).rlp.llp
  (initial.to (bousfieldKanWeight ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ)))
```

このPropの型も `/private/tmp/CheckISW2BKWeightStatement.lean` で検査済み。次に既存 `comparison_rlp` を用いて `BK → W` を一つ持ち上げ、両方の重みの射影cofibrancyと各値の可縮性を使って、全Kan係数図式への制限のHom不変性を証明する。この部分もモデル構造を仮定せず、自由境界・ホーンの持ち上げとして書く必要がある。

置き場所の案：共通の細胞・持ち上げの部分は新規 `HomotopicalAlgebra/Diagram/`、指定Δ・二重反対・選んだWへの特殊化は新規 `EInfinity/HomotopyWeight/`。既存のFramedLimit*・⑤a・入口・公式監査は変えない。見込みは細胞の部分300〜700行、重みのHom不変性と指定比較250〜450行、計550〜1,150行。現時点の1,411行と合わせても外枠15,000行には届かないが、行数でなく型つき一覧の停止規則による判断である。

### 166.4 停止の理由と現在地

IS-W2 §18.2が参照する `coordination.md` §2の明文は、**「止まって報告するのは、新しい構成・新しい定理（既存の構成の法則でないもの）、まとまりの外のもの、外枠に届くときだけ」**。今回は新しい数学的補題R03aの追加の判断が必要と解した。検証済みの全25本は先にコミットし、対象ビルド218・小監査166宣言の終了0、鍵の返却、作業木に未検証のLean変更がないことを確認してから、この紙の報告を保存した。

**R03aを型つき一覧に追加して進めるか、別の既存の橋を指定してもらう所で当該Lean作業を止める。** R02・R03・R04以降を完成とは数えない。停止点3b-4aにはまだ届いていない。外枠・型・既存界面は変更しない。/goalの全範囲は保持し、complete・paused・blockedには変更していない。

## 167. R03a 承認後：自由細胞と元の骨格の厳密な付着（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 13（うち追加 1）。§166のR03aはユーザー承認・IS-W2 §19により一覧へ追加済み。mainを `2ca5e7878` で取り込み、§19を確認して再開した。R03aそのもの・R02・R03のnative錐の完成とは数えない。

### 167.1 今回閉じた証明分割

BKの単体を「台の射列＋最後の射」に厳密に分解し、退化性が台だけで決まることを示した。非退化細胞の図式は終頂点の表現可能関手の余積である。これに任意の単体集合をテンソルした全関手からの射は標準生成元で一意に決まるため、各終頂点での境界の持ち上げを同じ全図式の射へ束ねられる。

さらに任意の単体集合値図式の骨格を全関手として作り、その塔の余極限が元の図式であることを証明した。BKの非退化細胞のYoneda写像で旧骨格を引き戻すと元の標準境界になる。全自由細胞から連続する二つの元の骨格への射と、その厳密な可換性も証明した。これはR03aの細胞分解の証明分割であり、独立の新しい数学の項目は追加していない。

今回の10本は747行、各200行以下。3b-4の検証済みは **35モジュール・2,158行**（共通を含む、外枠15,000）。当初のR03aの細胞部分300〜700行に対し747行で、余積の添字替え・骨格押し出しの照合がまだ残るため上振れしている。元の重み・型・⑤aの欄は変更しない。

### 167.2 証明分割・既存構成の法則の型

以下は全て今回の新規ファイル内。namespace・universe・変数は各ソースのまま。構成の本体は省略し、主張・構成の型を記録する。R03aの追加以外に一覧の追加は0。

#### BousfieldKanSimplex（84行）

```lean
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

abbrev SimplexData (n : ℕ) (i : I)

def overSimplex {n : ℕ} {i : I} (s : SimplexData I n i) :
    ComposableArrows (Over i) n

def simplexData {n : ℕ} {i : I} (s : ComposableArrows (Over i) n) :
    SimplexData I n i := ⟨s ⋙ Over.forget i, (s.obj (Fin.last n)).hom⟩

/-- 復元したover射列の各対象は元の同じ対象。 -/
theorem overSimplex_simplexData_obj {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) (a : Fin (n+1)) :
    (overSimplex I (simplexData I s)).obj a = s.obj a

theorem overSimplex_simplexData_obj {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) (a : Fin (n+1)) :
    (overSimplex I (simplexData I s)).obj a = s.obj a

theorem overSimplex_simplexData {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) : overSimplex I (simplexData I s) = s

theorem simplexData_overSimplex {n : ℕ} {i : I} (s : SimplexData I n i) :
    simplexData I (overSimplex I s) = s

def simplexEquiv (n : ℕ) (i : I) :
    ComposableArrows (Over i) n ≃ SimplexData I n i

theorem simplexData_postcomp {n : ℕ} {i j : I} (f : i ⟶ j)
    (s : ComposableArrows (Over i) n) :
    simplexData I (s ⋙ Over.map f) =
      ⟨(simplexData I s).1, (simplexData I s).2 ≫ f⟩

```

#### BousfieldKanDegenerate（68行）

```lean
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits SSet
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

theorem sigma_delta_eq_of_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) (n+1)) (k : Fin (n+1))
    (t : ComposableArrows I n)
    (ht : (nerve I).σ k t = s ⋙ Over.forget i) :
    (nerve (Over i)).σ k ((nerve (Over i)).δ k.castSucc s) = s

theorem degenerate_iff_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) :
    s ∈ (nerve (Over i)).degenerate n ↔
      (s ⋙ Over.forget i) ∈ (nerve I).degenerate n

theorem nondegenerate_iff_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) :
    s ∈ (nerve (Over i)).nonDegenerate n ↔
      (s ⋙ Over.forget i) ∈ (nerve I).nonDegenerate n

```

#### BousfieldKanFreeCells（78行）

```lean
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits SSet
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

abbrev NondegenerateData (n : ℕ) (i : I)

def nondegenerateEquiv (n : ℕ) (i : I) :
    (nerve (Over i)).nonDegenerate n ≃ NondegenerateData I n i

def freeCellDiagram (n : ℕ) : I ⥤ Type u

def nondegenerateDiagram (n : ℕ) : I ⥤ Type u

def nondegenerateDiagramIso (n : ℕ) :
    nondegenerateDiagram I n ≅ freeCellDiagram I n

```

#### BousfieldKanRepresentableCells（58行）

```lean
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits Opposite SSet
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

abbrev cellRepresentables (n : ℕ) (c : (nerve I).nonDegenerate n) : I ⥤ Type u

def freeCellCofan (n : ℕ) : Cofan (cellRepresentables I n)

def freeCellDesc {n : ℕ} {Z : I ⥤ Type u}
    (f : ∀ c, cellRepresentables I n c ⟶ Z) : freeCellDiagram I n ⟶ Z

def freeCellCofanIsColimit (n : ℕ) : IsColimit (freeCellCofan I n)

```

#### SimplicialDiagramSkeleton（102行）

```lean
universe u
namespace SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open CategoryTheory Limits SSet
open scoped Simplicial

theorem skeleton_image_le {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n).image f ≤ Y.skeleton n

def skeletonMap {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n : SSet.{u}) ⟶ (Y.skeleton n : SSet.{u})

@[reassoc] theorem skeletonMap_ι {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    skeletonMap f n ≫ (Y.skeleton n).ι = (X.skeleton n).ι ≫ f

theorem skeletonMap_id (X : SSet.{u}) (n : ℕ) : skeletonMap (𝟙 X) n = 𝟙 _

theorem skeletonMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    skeletonMap (f ≫ g) n = skeletonMap f n ≫ skeletonMap g n

def skeletonFamily : I ⥤ ℕ ⥤ SSet.{u}

def skeletonFiltration : ℕ ⥤ I ⥤ SSet.{u} := (skeletonFamily I W).flip

/-- 同じ骨格の塔から元の図式重みへの余錐。 -/
def skeletonCocone : Cocone (skeletonFiltration I W)

def skeletonCocone : Cocone (skeletonFiltration I W)

def skeletonCoconeIsColimit : IsColimit (skeletonCocone I W)

```

#### SimplicialCellSkeleton（45行）

```lean
universe u
namespace SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open CategoryTheory SSet
open scoped Simplicial

theorem nondegenerate_preimage_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    (X.skeleton n).preimage (yonedaEquiv.symm c.val) = ∂Δ[n]

theorem nondegenerate_range_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    Subcomplex.range (yonedaEquiv.symm c.val) ≤ X.skeleton (n+1)

theorem nondegenerate_boundary_range_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    Subcomplex.range (∂Δ[n].ι ≫ yonedaEquiv.symm c.val) ≤ X.skeleton n

```

#### BousfieldKanCellTensor（107行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.DiagramModel SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkCellWeight (n : ℕ) : I ⥤ SSet.{u}

def bkCellTensor (n : ℕ) : SSet.{u} ⥤ I ⥤ SSet.{u}

def bkCellGenerator {n : ℕ} (c : (nerve I).nonDegenerate n) (X : SSet.{u}) :
    X ⟶ ((bkCellTensor I n).obj X).obj (c.val.obj (Fin.last n))

theorem bkCellGenerator_naturality {n : ℕ} (c : (nerve I).nonDegenerate n)
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    bkCellGenerator I c X ≫ ((bkCellTensor I n).map f).app (c.val.obj (Fin.last n)) =
      f ≫ bkCellGenerator I c Y

def bkCellDesc {n : ℕ} (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n))) :
    (bkCellTensor I n).obj X ⟶ Z

theorem bkCellGenerator_desc {n : ℕ} (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n)))
    (c : (nerve I).nonDegenerate n) :
    bkCellGenerator I c X ≫ (bkCellDesc I X Z f).app (c.val.obj (Fin.last n)) = f c

theorem bkCellDesc_unique {n : ℕ} (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n)))
    (m : (bkCellTensor I n).obj X ⟶ Z)
    (hm : ∀ c, bkCellGenerator I c X ≫ m.app (c.val.obj (Fin.last n)) = f c) :
    m = bkCellDesc I X Z f

theorem bkCellHom_ext {n : ℕ} {X : SSet.{u}} {Z : I ⥤ SSet.{u}}
    {m m' : (bkCellTensor I n).obj X ⟶ Z}
    (h : ∀ c, bkCellGenerator I c X ≫ m.app (c.val.obj (Fin.last n)) =
      bkCellGenerator I c X ≫ m'.app (c.val.obj (Fin.last n))) : m = m'

```

#### BousfieldKanCellLifting（58行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.DiagramModel SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

theorem bkCellTensor_map_llp (n : ℕ) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.I f) :
    (boundaries I).rlp.llp ((bkCellTensor I n).map f)

```

#### BousfieldKanCellAttachment（77行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel SerrePositivity.DiagramModel.BousfieldKanCells
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkCellSimplex {n : ℕ} (c : (nerve I).nonDegenerate n) :
    (nerve (Over (c.val.obj (Fin.last n)))).nonDegenerate n

abbrev bkSkeleton := skeletonFiltration I (bousfieldKanWeight I)

/-- 全標準細胞から元の重みへの同じYoneda評価。 -/
def bkCellEvaluation (n : ℕ) : (bkCellTensor I n).obj Δ[n] ⟶ bousfieldKanWeight I

def bkCellEvaluation (n : ℕ) : (bkCellTensor I n).obj Δ[n] ⟶ bousfieldKanWeight I

def bkCellBoundary (n : ℕ) : (bkCellTensor I n).obj (∂Δ[n] : SSet.{u}) ⟶
    (bkSkeleton I).obj n

def bkCellTop (n : ℕ) : (bkCellTensor I n).obj Δ[n] ⟶ (bkSkeleton I).obj (n+1)

theorem bkCellTop_ι (n : ℕ) :
    bkCellTop I n ≫ (skeletonCocone I (bousfieldKanWeight I)).ι.app (n+1) =
      bkCellEvaluation I n

theorem bkCellAttachment_comm (n : ℕ) :
    bkCellBoundary I n ≫ (bkSkeleton I).map (homOfLE (Nat.le_succ n)) =
      (bkCellTensor I n).map ∂Δ[n].ι ≫ bkCellTop I n

```

#### BousfieldKanCellCoproduct（70行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkCellComponentInclusion {n : ℕ} {i : I} (s : NondegenerateData I n i)
    (X : SSet.{u}) : X ⟶ ((bkCellTensor I n).obj X).obj i

def bkCellComponentCofan (n : ℕ) (i : I) (X : SSet.{u}) :
    Cofan (fun _ : NondegenerateData I n i => X)

def bkCellComponentDesc {n : ℕ} {i : I} (X Z : SSet.{u})
    (f : NondegenerateData I n i → (X ⟶ Z)) :
    ((bkCellTensor I n).obj X).obj i ⟶ Z

@[reassoc] theorem bkCellComponentInclusion_desc {n : ℕ} {i : I} (X Z : SSet.{u})
    (f : NondegenerateData I n i → (X ⟶ Z)) (s : NondegenerateData I n i) :
    bkCellComponentInclusion I s X ≫ bkCellComponentDesc I X Z f = f s

def bkCellComponentCofanIsColimit (n : ℕ) (i : I) (X : SSet.{u}) :
    IsColimit (bkCellComponentCofan I n i X)

theorem bkCellComponentHom_ext {n : ℕ} {i : I} {X Z : SSet.{u}}
    {f g : ((bkCellTensor I n).obj X).obj i ⟶ Z}
    (h : ∀ s : NondegenerateData I n i,
      bkCellComponentInclusion I s X ≫ f = bkCellComponentInclusion I s X ≫ g) : f = g

```

### 167.3 検証と残り

main取り込み後の219は既存の25本を対象ビルドし **10,619 jobs・終了0**、小監査166宣言・標準三公理のみ。220は自由細胞の先行4本を検証し、合計200宣言。import整理と骨格・自由テンソルの3本を加えた221は **1,590 jobs・終了0**、新規全32本の小監査 **231宣言・標準三公理のみ**。222は境界照合・付着・成分余積の3本を対象ビルドし **1,605 jobs・終了0**、新規全35本の小監査 **255宣言・標準三公理のみ**。実ハンドル35419・61534の終了0を確認し、鍵返却済み。ログ `/private/tmp/isw2-build219.log`〜`222.log`、最終小監査 `/private/tmp/AuditISW2BKCells222.lean`。

個別検査ではover圏のeqToHom、退化の最終頂点、Yoneda同値の往復、自由な生成元を評価する型を明示して修正した。計算上限の変更・sorry・独自公理なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの作業木は変更していない。登録候補は同じBE用JSONへ追記した。

次は相対細胞の添字と自由細胞の余積を照合し、同じ骨格の押し出しから全BK重みの射影cofibrancyを得る。その後に同じjを選び、全Kan係数の制限のホモトピー同値を示す。相対細胞の添字替えの下書きは個別検査中で、この検証済み10本のコミットには含めない。全体の/goalは保持し、停止点3b-4aにもまだ届いていない。

## 168. 同じ重み比較の中間定理 R03a.1 の追加（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 14（うち追加 2）。IS-W2 §19の「同じまとまりの中で一つの見込みが1,500行以下」の枠を使い、R03aのKan係数への制限の不変性を次の中間定理 **R03a.1** に分けて一覧へ追加する。R03a・R03a.1とも未完了。⑤aの欄の型・元の重み・native錐の型に変更なし。

```lean
-- universe u
-- open CategoryTheory Limits
-- open SerrePositivity.EInfinity
-- open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
-- open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

theorem weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant
    (I : Type u) [SmallCategory I] (V W : I ⥤ SSet.{u}) (f : V ⟶ W)
    (hV : (HomotopyWeight.boundaries I).rlp.llp (initial.to V))
    (hW : (HomotopyWeight.boundaries I).rlp.llp (initial.to W))
    (hf : ∀ i, IsWeakHomotopyEquivalence (f.app i))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre f H)
```

型は `/private/tmp/CheckProjectiveWeightComparison.lean` で個別検査し、終了0。これは型の検査であって証明ではない。前段で個別検査を終えた元のBKの射影cofibrancyと指定された同じjの構成に、このHom不変性と各値の可縮性を合わせるのがR03aの経路。

証明の案：自由ホーンの小対象分解でfを射影anodyneな左射と成分ごとのKan fibrationな右射へ分ける。左射は成分ごとのanodyneでもあるので、hfと二つ組から右射は成分ごとのtrivial Kan fibration。両方の元の重みの射影cofibrancyを使い、右射の切断と同じシリンダーによるホモトピーを取る。左射の制限は、パラメーター境界とのpushout-productの持ち上げでtrivial Kan fibrationとなる。この二つを同じ制限射の合成として合わせ、実際のホモトピー同値を得る。SSet・図式圏のModelCategoryは仮定しない。

見込みは自由ホーンと点ごとの性質250〜400行、相対テンソルの持ち上げと切断空間の照合350〜550行、分解とホモトピー・最終の合成300〜450行、計900〜1,400行。一つの中間定理として1,500行以下で、R01〜R03とR03aの重み比較の同じまとまり。既存構成の法則と証明分割は各型を追記し、200行を超えるファイルは行数も記録する。見込みが1,500を超えると判明した場合・別のまとまりが必要な場合には検証済みを保存して報告する。

前段の223は相対細胞の添字替え・各成分の評価・同じ骨格の押し出しを対象ビルドし、**1,608 jobs・終了0、38モジュール291宣言・標準三公理のみ**。実ハンドル60582の終了0・鍵返却を確認済み。BK全体のcofibrancyと一つの指定比較射の224は同時整理券一枚で待機中であり、その終了前に検証済みとは数えない。

## 169. 元のBK重みの射影cofibrancyと一つの指定比較射（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 14（うち追加 2）。§168のR03a.1は§19の枠で追加済み。R03a・R03a.1の完成とは数えない。

### 169.1 検証済みの到達点

元の相対細胞の添字をBK自由細胞の添字に一致させ、全評価で余積の同型を指定した。各成分の評価が、同じ非退化単体のYoneda射そのものであることも閉じた。これによりMathlibの元の相対細胞の押し出しを、BKの同じ自由境界と二つの骨格の押し出しへ輸送し、評価関手で図式全体の押し出しへ戻した。

左持ち上げ性の押し出し・逐次合成に対する安定性と、前段の元の骨格の余極限を使い、**任意の小圏Iについて元のbousfieldKanWeight Iが射影cofibrant**であることを証明した。最後に指定された二重反対化した一点比較の右持ち上げ性から、一つの `bkFramedWeightComparison J : BK(Jᵒᵖᵒᵖ) → framedLimitWeight J` を選び、元の一点比較を厳密に保つ等式を証明した。このjは係数Hに依存しない。まだその切断空間の制限のホモトピー同値は未完了。

### 169.2 今回の証明分割・法則の型

#### BousfieldKanCellReindex（75行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkInitialCellEquiv (n : ℕ) (i : I) :
    relativeCellComplexOfMono.Cell ((⊥ : (nerve (Over i)).Subcomplex).ι) n ≃
      NondegenerateData I n i

theorem bkInitialCellEquiv_simplex (n : ℕ) (i : I)
    (c : relativeCellComplexOfMono.Cell ((⊥ : (nerve (Over i)).Subcomplex).ι) n) :
    ((nondegenerateEquiv I n i).symm (bkInitialCellEquiv I n i c)).val = c.simplex

def bkCellReindexIsColimit {n : ℕ} {i : I} {α : Type u}
    (e : α ≃ NondegenerateData I n i) (X : SSet.{u}) :
    IsColimit (Cofan.mk (((bkCellTensor I n).obj X).obj i)
      (fun a : α => bkCellComponentInclusion I (e a) X))

def bkCellReindexIso {n : ℕ} {i : I} {α : Type u}
    (e : α ≃ NondegenerateData I n i) (X : SSet.{u}) :
    (∐ fun _ : α => X) ≅ ((bkCellTensor I n).obj X).obj i

@[reassoc] theorem bkCellReindexIso_ι {n : ℕ} {i : I} {α : Type u}
    (e : α ≃ NondegenerateData I n i) (X : SSet.{u}) (a : α) :
    Sigma.ι (fun _ : α => X) a ≫ (bkCellReindexIso I e X).hom =
      bkCellComponentInclusion I (e a) X

```

#### BousfieldKanCellEvaluation（81行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.BousfieldKanCells
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

@[reassoc] theorem bkCellComponentInclusion_cellDesc {n : ℕ} {i : I}
    (s : NondegenerateData I n i) (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n))) :
    bkCellComponentInclusion I s X ≫ (bkCellDesc I X Z f).app i =
      f s.1 ≫ Z.map s.2

@[reassoc] theorem bkCellComponentInclusion_map {n : ℕ} {i : I}
    (s : NondegenerateData I n i) {X Y : SSet.{u}} (f : X ⟶ Y) :
    bkCellComponentInclusion I s X ≫ ((bkCellTensor I n).map f).app i =
      f ≫ bkCellComponentInclusion I s Y

theorem bkCellSimplex_map {n : ℕ} {i : I} (s : NondegenerateData I n i) :
    ((bousfieldKanWeight I).map s.2).app (op ⦋n⦌) (bkCellSimplex I s.1).val =
      ((nondegenerateEquiv I n i).symm s).val

@[reassoc] theorem bkCellComponent_evaluation {n : ℕ} {i : I}
    (s : NondegenerateData I n i) :
    bkCellComponentInclusion I s Δ[n] ≫ (bkCellEvaluation I n).app i =
      yonedaEquiv.symm ((nondegenerateEquiv I n i).symm s).val

@[reassoc] theorem bkCellComponent_top_ι {n : ℕ} {i : I}
    (s : NondegenerateData I n i) :
    bkCellComponentInclusion I s Δ[n] ≫ (bkCellTop I n).app i ≫
      (((bousfieldKanWeight I).obj i).skeleton (n+1)).ι =
        yonedaEquiv.symm ((nondegenerateEquiv I n i).symm s).val

@[reassoc] theorem bkCellComponent_boundary_ι {n : ℕ} {i : I}
    (s : NondegenerateData I n i) :
    bkCellComponentInclusion I s (∂Δ[n] : SSet.{u}) ≫ (bkCellBoundary I n).app i ≫
      (((bousfieldKanWeight I).obj i).skeleton n).ι =
        ∂Δ[n].ι ≫ yonedaEquiv.symm ((nondegenerateEquiv I n i).symm s).val

```

#### BousfieldKanSkeletonPushout（81行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.BousfieldKanCells
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkSkeletonInitialIso (n : ℕ) (i : I) :
    (skeletonOfMono ((⊥ : (nerve (Over i)).Subcomplex).ι) n : SSet.{u}) ≅
      ((bkSkeleton I).obj n).obj i

@[reassoc] theorem bkSkeletonInitialIso_ι (n : ℕ) (i : I) :
    (bkSkeletonInitialIso I n i).hom ≫ ((nerve (Over i)).skeleton n).ι =
      (skeletonOfMono ((⊥ : (nerve (Over i)).Subcomplex).ι) n).ι

theorem bkCellAttachment_isPushout_app (n : ℕ) (i : I) :
    IsPushout ((bkCellBoundary I n).app i) (((bkCellTensor I n).map ∂Δ[n].ι).app i)
      (((bkSkeleton I).map (homOfLE (Nat.le_succ n))).app i) ((bkCellTop I n).app i)

theorem bkCellAttachment_isPushout (n : ℕ) :
    IsPushout (bkCellBoundary I n) ((bkCellTensor I n).map ∂Δ[n].ι)
      ((bkSkeleton I).map (homOfLE (Nat.le_succ n))) (bkCellTop I n)

```

#### BousfieldKanCofibrant（51行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkSkeletonZeroIsInitial : IsInitial ((bkSkeleton I).obj 0)

theorem bkSkeleton_step_llp (n : ℕ) :
    (boundaries I).rlp.llp ((bkSkeleton I).map (homOfLE (Nat.le_succ n)))

def bkSkeletonTransfinite :
    (boundaries I).rlp.llp.TransfiniteCompositionOfShape ℕ (initial.to (bousfieldKanWeight I))

theorem bousfieldKanWeight_cofibrant :
    (boundaries I).rlp.llp (initial.to (bousfieldKanWeight I))

```

#### BousfieldKanChosenComparison（57行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (J : Type u) [SmallCategory J]

abbrev framedLimitWeightComparison := (doubleOpWeights J).map (comparison J)

theorem framedLimitWeightComparison_rlp :
    (boundaries Jᵒᵖᵒᵖ).rlp (framedLimitWeightComparison J)

def bkFramedPointMap : bousfieldKanWeight Jᵒᵖᵒᵖ ⟶ (doubleOpWeights J).obj (point J)

def bkFramedComparisonSquare :
    CommSq (initial.to (framedLimitWeight J)) (initial.to (bousfieldKanWeight Jᵒᵖᵒᵖ))
      (framedLimitWeightComparison J) (bkFramedPointMap J)

def bkFramedWeightComparison : bousfieldKanWeight Jᵒᵖᵒᵖ ⟶ framedLimitWeight J

theorem bkFramedWeightComparison_point :
    bkFramedWeightComparison J ≫ framedLimitWeightComparison J = bkFramedPointMap J

```

### 169.3 検証・実測と残り

223はこのうち先行3本で **1,608 jobs・終了0、38モジュール291宣言**。224は全体のcofibrancyと一つの比較射の2本を対象ビルドし **1,615 jobs・終了0、新規全40モジュール309宣言・標準三公理のみ**。両方の実ハンドル60582・52517の終了0を確認し、鍵返却済み。ログ `/private/tmp/isw2-build223.log`・`224.log`、小監査 `/private/tmp/AuditISW2BKCells224.lean`。同時整理券一枚、`--class impl --wait 3600`、ビルドと小監査の間だけ鍵を保持。sorry・独自公理・計算上限の変更0。

今回345行、各200行以下。3b-4の検証済みは **40本・2,503行**。R03aの細胞と比較射の構成は累計1,092行で、当初の細胞の見込み300〜700行に対し約1.6倍。元の骨格への全自然な輸送と既存押し出しの四つの射の等式を明示する行数が増えた。Hom不変性は§168の中間定理R03a.1（900〜1,400行）として別に見積もった。全外枠15,000行にはまだ十分余地がある。

次の自由ホーン・相対テンソル・native切断のKan性の新規下書きは個別検査中。この検証済み5本のコミットには含めない。元の重み・既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査は変更していない。/goalはactiveのまま、Hom不変性へ続ける。

## 170. R03a.1前半の検証と見込みの半分での途中報告（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 14（うち追加 2）。R03aとR03a.1は未完了。

### 170.1 到達点・検証

自由ホーンの生成族の小対象性と各値の右類を作った。その全生成左類が、各値でanodyneとなることも、既存の余積・押し出し・逐次合成・レトラクトの法則から証明した。自由ホーンの射とパラメーターの単射の相対テンソルは、各値のKan fibrationを持ち上げる。これを同じweightedCornerと元のcurry・uncurryへ転置し、**射影anodyneな重み制限は、各値がKanな係数についてtrivial Kan fibration**となることを示した。射影cofibrantな両重みでは、元の切断空間がKanであることも証明し、実際の単体的ホモトピー同値まで閉じた。

重みの元の射の自由ホーン分解について、左射の各値のanodyne性、中間重みの射影cofibrancy、右射の各値のfibration性・弱同値性を閉じた。**標的の各値がKanの場合**には、右射は各値で境界右持ち上げ性を持つ。この補助で一般の非Kan標的を代用しない。一般の比較への復帰には、両方の重みのホーン置換と同じ指定比較の分解を使う。

225は先行5本で **1,721 jobs・終了0、新規全45本325宣言**。226は分解の2本で **2,612 jobs・終了0、新規全47本334宣言・標準三公理のみ**。実ハンドル76288・48784の終了0・鍵返却を確認済み。ログ `/private/tmp/isw2-build225.log`・`226.log`、小監査 `/private/tmp/AuditISW2BKCells226.lean`。対象のみ、同時整理券一枚、`--class impl --wait 3600`、ビルドと小監査の間だけ鍵を保持。

### 170.2 実測と残りの再見込み（止まらず継続）

今回7本402行、各200行以下。3b-4の検証済みは **47本・2,905行**。初期§152.4の合計5,700〜9,800行の下端の半分2,850行を超えたので、早めに共通規則の途中報告を残す。R03aの細胞と一つの比較射の構成1,092行に対し、R03a.1は現時点402行（見込み900〜1,400行）。重みの同じ区間ホモトピーを元の切断制限へ運ぶ下書きは個別検査中で、検証済みの行数には含めていない。

残りの見込み：R03a.1の切断・区間ホモトピーと分解の最終接続500〜850行、R03aの指定jへの特殊化・可縮性の照合100〜250行、R02〜R03の元のnative錐族と普遍性への最後の接続700〜1,200行、R04〜R05は1,000〜1,800行、実現R06〜R10は2,800〜4,800行、R11〜R12は500〜900行。合計の残り5,600〜9,800行、全体約8,500〜12,700行で、外枠15,000行を維持する。native錐への接続はまだ未実測のため幅を残す。一般のHom不変性をR03a.1へ分けた分で、初期のR01〜R03の1,400〜2,300行は上振れしている。

ここで止まらず、検証済みを保存してR03a.1の残りへ進む。型・範囲・既存の模型・⑤aの欄を弱めていない。SSet/図式圏のModelCategory仮定・sorry・独自公理・計算上限の変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査は変更していない。

### 170.3 証明分割・法則の型

全てR03a.1の証明分割または既存構成の法則。追加の一覧項目は§168以外0。

#### ProjectiveHornGenerators（36行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits
variable (K : Type u) [SmallCategory K]

abbrev horns : MorphismProperty (K ⥤ SSet.{u})

instance horns_smallObjectArgument : (horns K).HasSmallObjectArgument.{u}

theorem horns_rlp : (horns K).rlp =
    ModelGeneration.EvaluationFamily.detected (evaluation K) SSet.modelCategoryQuillen.J.rlp

```

#### ProjectiveHornValues（62行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet
variable (K : Type u) [SmallCategory K]

theorem free_horn_anodyne (k l : K) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.J f) : SSet.anodyneExtensions (((free K k).map f).app l)

theorem horns_evaluation_le (l : K) :
    horns K ≤ SSet.anodyneExtensions.inverseImage (evaluation K l)

theorem anodyne_relativeCells_le :
    Quillen.relativeCells.{u} SSet.anodyneExtensions ≤ SSet.anodyneExtensions

theorem projectiveHorn_anodyne {F G : K ⥤ SSet.{u}} (f : F ⟶ G)
    (hf : (horns K).rlp.llp f) (l : K) : SSet.anodyneExtensions (f.app l)

```

#### ProjectiveHornCorner（50行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.PointwiseAdjunction
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

theorem projectiveHorn_corner_lifting {V W F G : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : (horns I).rlp.llp j) {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (p : F ⟶ G) (hp : ∀ i, Fibration (p.app i)) :
    HasLiftingProperty (weightedCorner j f).ι p

```

#### NativeWeightedSections（52行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I] (W : I ⥤ SSet.{u})

def coneSpaceParameterIso : WeightedCones.tensorDiagram I W ≅ weightedParameterFunctor W

def coneSpaceNativeSectionsIso : WeightedCones.coneSpace I W ≅ weightedSectionsFunctor W

theorem weightedSections_kanComplex_of_projective_cofibrant
    (hW : (boundaries I).rlp.llp (initial.to W))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    SSet.KanComplex (weightedSections W H)

```

#### ProjectiveWeightRestriction（89行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped Simplicial SSet.modelCategoryQuillen
variable {I : Type u} [SmallCategory I]

theorem weightedSectionsPre_trivialKanFibration_of_corner_extensions
    {W W' H : I ⥤ SSet.{u}} (j : W ⟶ W')
    (hcorner : ∀ n, ∀ a : (weightedCorner j (boundary n).ι).pt ⟶ H,
      ∃ b : W' ⊗ (Functor.const I).obj (Δ[n] : SSet.{u}) ⟶ H,
        (weightedCorner j (boundary n).ι).ι ≫ b = a) :
    TrivialKanFibration (weightedSectionsPre j H)

theorem weightedSectionsPre_trivialKanFibration_of_projectiveHorn
    {V W H : I ⥤ SSet.{u}} (j : V ⟶ W) (hj : (horns I).rlp.llp j)
    (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    TrivialKanFibration (weightedSectionsPre j H)

theorem weightedSectionsPre_homotopyEquivalence_of_projectiveHorn
    {V W H : I ⥤ SSet.{u}} (j : V ⟶ W) (hj : (horns I).rlp.llp j)
    (hV : (boundaries I).rlp.llp (initial.to V))
    (hW : (boundaries I).rlp.llp (initial.to W))
    (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (weightedSectionsPre j H)

```

#### ProjectiveHornFactorization（55行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

theorem projectiveHorn_cofibration {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : (horns I).rlp.llp j) : (boundaries I).rlp.llp j

def projectiveHornFactorization {V W : I ⥤ SSet.{u}} (j : V ⟶ W) :
    MorphismProperty.MapFactorizationData (horns I).rlp.llp (horns I).rlp j

theorem projectiveHornFactorization_i_anodyne {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    SSet.anodyneExtensions ((projectiveHornFactorization I j).i.app i)

theorem projectiveHornFactorization_p_fibration {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    Fibration ((projectiveHornFactorization I j).p.app i)

theorem projectiveHornFactorization_cofibrant {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hV : (boundaries I).rlp.llp (initial.to V)) :
    (boundaries I).rlp.llp (initial.to (projectiveHornFactorization I j).Z)

```

#### ProjectiveHornWeakFactorization（58行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

theorem projectiveHornFactorization_i_weak {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    IsWeakHomotopyEquivalence ((projectiveHornFactorization I j).i.app i)

theorem projectiveHornFactorization_p_weak {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : ∀ i, IsWeakHomotopyEquivalence (j.app i)) (i : I) :
    IsWeakHomotopyEquivalence ((projectiveHornFactorization I j).p.app i)

theorem projectiveHornFactorization_p_boundary_rlp {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : ∀ i, IsWeakHomotopyEquivalence (j.app i))
    (hW : ∀ i, SSet.KanComplex (W.obj i)) (i : I) :
    SSet.modelCategoryQuillen.I.rlp ((projectiveHornFactorization I j).p.app i)

```

## 171. R03a・R03a.1 の完了：同じ一つの重み比較（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 14（うち追加 2）。済みはR01・R03a・R03a.1。R02・R03の指定native錐族・極限性は未完了であり、この重み比較をもって完成とは数えない。

### 171.1 一覧の型のまま閉じた内容

**R03a.1** `weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant` は§168の一般の型のまま証明した。元の射影cofibrantな二重み間の成分ごとの弱同値から、全Kan係数図式への元の制限写像の実際の単体的ホモトピー同値を得る。標的重みがKanでない場合も含む。

まず同じ区間パラメーターを持つ全重みの自然変換を、普遍評価に前合成して元の切断空間の区間ホモトピーへ転置し、両端点が元の制限写像に厳密に一致することを示した。境界右類の射の切断を元の標的重みのcofibrancyで取り、始域重みのcofibrancyで区間境界を持ち上げることにより、同じ全重みの区間収縮を作った。これが右射の制限の実際のホモトピー逆を与える。

各値がKanな標的への自由ホーン分解では、前段の射影anodyneな制限とこの境界右類の制限を合成した。一般の標的は、元の標的の終射の自由ホーン分解によるKan置換を使う。元の比較をその左射へ合成して前のKan標的の場合に適用し、Kanな切断空間での二対三則で元の制限へ戻った。一般の非Kan標的へのfibrationを無条件にtrivialと扱っていない。

**R03a** `exists_strictBETotWeightComparison` は§166で承認された型のまま閉じた。元のBK重みの各値が元のover圏の終対象によって弱可縮であることと、指定された一点比較の境界右類から、**選んだ同じjの全成分が弱同値**であることを示した。これと両方の重みの元の射影cofibrancyをR03a.1へ代入した。

存在するjは `strictBETotWeightComparison := bkFramedWeightComparison (AsSmall SimplexCategory)` として一つに固定した。係数H・その全射ごとに選び直さない。元のW・二重反対添字・重みの制限の向きは保持した。高次自然性やnative錐の構成を、この存在主張だけで代用しない。

### 171.2 最終検証

227は区間転置・両端点の1本で **1,622 jobs・終了0、48モジュール347宣言**。228は区間境界・テンソル持ち上げ・切断収縮・一般比較の4本で **2,708 jobs・終了0、52モジュール362宣言**。229は元のjの各値の比較とBE指定比較の2本で **2,772 jobs・終了0、新規全54モジュール368宣言・標準三公理のみ**。実ハンドル34287・45990・89120の終了0を確認し、鍵返却済み。ログ `/private/tmp/isw2-build227.log`〜`229.log`、最終小監査 `/private/tmp/AuditISW2BKCells229.lean`。

一時合併の検査では他のimportが収縮補題を補っていたため、各値の比較を独立に検査して不足した `MonoRightLiftingContraction` の直接importを明示した。最終229は各実モジュールを独立にビルドしてから全新規の小監査を実行した。sorry・独自公理・計算上限の変更0。SSet/図式圏のModelCategory仮定なし。`--class impl --wait 3600`、同時整理券一枚、鍵はビルド・小監査の間だけ。

### 171.3 見込みと実測

今回7本631行、各200行以下。3b-4の検証済みは **54モジュール・3,536行**。登録候補はBE用JSONへ追記し、入口・公式監査の登録は行っていない。

| 追加項目 | 見込み | 実測 | 差 |
| --- | ---: | ---: | ---: |
| R03aのBK細胞・指定比較と最終特殊化 | 550〜1,150 | 1,186 | 上端+36（約3%） |
| R03a.1の一般の重みHom不変性 | 900〜1,400 | 839 | 下端−61 |
| 合計 | 1,450〜2,550 | 2,025 | 範囲内 |

R03aの細胞分解が当初の見込みより大きくなった一方、Hom不変性は既存の二変数随伴輸送・Kan Whitehead・元のホーン小対象性を再利用できたため短く閉じた。R03a.1は§19の1,500行以下の追加の枠を満たした。§170の全体見込み約8,500〜12,700行、外枠15,000行は維持する。

次はR02・R03の元の普遍重み付き錐の点を、同じ全Hom∞比較・R03aを通して指定native錐へ接続する。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの作業木は変更していない。停止点3b-4aにはまだ届いていない。/goalはactiveのまま、そのまま続ける。

### 171.4 今回の証明分割・法則の型

R03a・R03a.1以外の独立の新しい数学の追加は0。

#### WeightedSourceHomotopy（145行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def weightedSourceHomotopySection {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W) (H : I ⥤ SSet.{u}) :
    V ⊗ (Functor.const I).obj (weightedSections W H ⊗ (Δ[1] : SSet.{u})) ⟶ H

def weightedSourceHomotopyMap {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W) (H : I ⥤ SSet.{u}) :
    weightedSections W H ⊗ (Δ[1] : SSet.{u}) ⟶ weightedSections V H

def weightIntervalZero (V : I ⥤ SSet.{u}) :
    V ⟶ V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u})

def weightIntervalOne (V : I ⥤ SSet.{u}) :
    V ⟶ V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u})

theorem weightedSourceHomotopyMap_zero {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (f : V ⟶ W) (h : weightIntervalZero I V ≫ T = f) (H : I ⥤ SSet.{u}) :
    SSet.ι₀ ≫ weightedSourceHomotopyMap I T H = weightedSectionsPre f H

theorem weightedSourceHomotopyMap_one {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (f : V ⟶ W) (h : weightIntervalOne I V ≫ T = f) (H : I ⥤ SSet.{u}) :
    SSet.ι₁ ≫ weightedSourceHomotopyMap I T H = weightedSectionsPre f H

def weightedSectionsPreHomotopy {V W : I ⥤ SSet.{u}} {f g : V ⟶ W}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (h₀ : weightIntervalZero I V ≫ T = f) (h₁ : weightIntervalOne I V ≫ T = g)
    (H : I ⥤ SSet.{u}) : SSet.Homotopy (weightedSectionsPre f H) (weightedSectionsPre g H)

```

#### WeightIntervalBoundary（92行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open scoped Simplicial

theorem weight_boundaryMap_naturality {X Y E F : SSet.{u}} (r : X ⟶ Y) (t : E ⟶ F)
    (a b : X ⟶ E) (c d : Y ⟶ F) (ha : r ≫ c = a ≫ t) (hb : r ≫ d = b ≫ t) :
    (r ▷ (∂Δ[1] : SSet.{u})) ≫ boundaryMap c d = boundaryMap a b ≫ t

theorem weight_boundaryMap_comp {X E B : SSet.{u}} (a b : X ⟶ E) (p : E ⟶ B)
    (h : a ≫ p = b ≫ p) :
    boundaryMap a b ≫ p = fst X (∂Δ[1] : SSet.{u}) ≫ b ≫ p

def weightIntervalBoundary {V W : I ⥤ SSet.{u}} (f g : V ⟶ W) :
    V ⊗ (Functor.const I).obj (∂Δ[1] : SSet.{u}) ⟶ W

theorem weightIntervalBoundary_lift_zero {V W : I ⥤ SSet.{u}} (f g : V ⟶ W)
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (h : (V ◁ (Functor.const I).map ∂Δ[1].ι) ≫ T = weightIntervalBoundary I f g) :
    weightIntervalZero I V ≫ T = f

theorem weightIntervalBoundary_lift_one {V W : I ⥤ SSet.{u}} (f g : V ⟶ W)
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (h : (V ◁ (Functor.const I).map ∂Δ[1].ι) ≫ T = weightIntervalBoundary I f g) :
    weightIntervalOne I V ≫ T = g

```

#### ProjectiveWeightTensorLifting（48行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.PointwiseAdjunction
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

theorem projectiveWeight_tensor_lifting (W : I ⥤ SSet.{u})
    (hW : (boundaries I).rlp.llp (initial.to W))
    {A B : SSet.{u}} (f : A ⟶ B) [Mono f] {F G : I ⥤ SSet.{u}} (p : F ⟶ G)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i)) :
    HasLiftingProperty ((weightedParameterFunctor W).map f) p

```

#### ProjectiveBoundaryContraction（78行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def weightIntervalProjection (V : I ⥤ SSet.{u}) :
    V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V

theorem exists_projectiveBoundary_section {V W : I ⥤ SSet.{u}} (p : V ⟶ W)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i))
    (hW : (boundaries I).rlp.llp (initial.to W)) : ∃ s : W ⟶ V, s ≫ p = 𝟙 W

theorem exists_projectiveBoundary_contraction {V W : I ⥤ SSet.{u}} (p : V ⟶ W)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i))
    (hV : (boundaries I).rlp.llp (initial.to V)) (s : W ⟶ V) (hs : s ≫ p = 𝟙 W) :
    ∃ T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V,
      weightIntervalZero I V ≫ T = p ≫ s ∧ weightIntervalOne I V ≫ T = 𝟙 V

theorem weightedSectionsPre_homotopyEquivalence_of_projectiveBoundary
    {V W : I ⥤ SSet.{u}} (p : V ⟶ W)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i))
    (hV : (boundaries I).rlp.llp (initial.to V))
    (hW : (boundaries I).rlp.llp (initial.to W)) (H : I ⥤ SSet.{u}) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre p H)

```

#### ProjectiveWeightComparison（74行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

theorem projectiveHornReplacement_kan (W : I ⥤ SSet.{u}) (i : I) :
    SSet.KanComplex ((projectiveHornFactorization I (terminal.from W)).Z.obj i)

theorem weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant_kan_target
    (V W : I ⥤ SSet.{u}) (f : V ⟶ W)
    (hV : (boundaries I).rlp.llp (initial.to V))
    (hW : (boundaries I).rlp.llp (initial.to W))
    (hf : ∀ i, IsWeakHomotopyEquivalence (f.app i))
    (hWK : ∀ i, SSet.KanComplex (W.obj i))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre f H)

theorem weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant
    (V W : I ⥤ SSet.{u}) (f : V ⟶ W)
    (hV : (boundaries I).rlp.llp (initial.to V))
    (hW : (boundaries I).rlp.llp (initial.to W))
    (hf : ∀ i, IsWeakHomotopyEquivalence (f.app i))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre f H)

```

#### BousfieldKanComparisonValues（53行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

theorem bousfieldKanWeight_isWeaklyContractible (I : Type u) [SmallCategory I] (i : I) :
    IsWeaklyContractible ((bousfieldKanWeight I).obj i)

theorem framedLimitWeightComparison_weak (i : Jᵒᵖᵒᵖ) :
    IsWeakHomotopyEquivalence ((framedLimitWeightComparison J).app i)

theorem bkFramedWeightComparison_weak (i : Jᵒᵖᵒᵖ) :
    IsWeakHomotopyEquivalence ((bkFramedWeightComparison J).app i)

```

#### StrictDiagramTotWeightComparison（41行）

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

abbrev strictBETotWeightComparison :=
  HomotopyWeight.bkFramedWeightComparison (AsSmall.{u} SimplexCategory)

theorem strictBETotWeightComparison_homotopyEquivalence
    (H : ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⥤ SSet.{u})
    (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre strictBETotWeightComparison H)

theorem exists_strictBETotWeightComparison :
    ∃ j : bousfieldKanWeight ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⟶
        HomotopyWeight.framedLimitWeight (AsSmall.{u} SimplexCategory),
      ∀ (H : ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⥤ SSet.{u}),
        (∀ i, SSet.KanComplex (H.obj i)) →
          IsSimplicialHomotopyEquivalence (weightedSectionsPre j H)

```

## 172. 元のprobe錐から同じBK切断への実写像・指定点の接続（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 14（うち追加 2）。R02・R03は未完了。

### 172.1 今回の到達点

§171までの重み比較を、元の普遍probe錐の**同じ零単体**へ適用した。先に既存のconeSpaceとnativeなweightedSectionsの右随伴同型が同じHom転置を運ぶ式を示し、標準零単体のテンソル同型がnativeな第一射影へ移ることを照合した。その結果、元の `conePoint s` が同じ自然変換sのnative切断の零単体へ移ることを、π₀でなく実際の零単体の等式として証明した。

次に指定した一つの `bkFramedWeightComparison K` の前合成で、同じ普遍probe錐を `BK(Kᵒᵖᵒᵖ) →` 元の右frame Hom係数図式へ送った。元のprobe錐空間から同じBK切断空間への実写像 `strictBETotProbeConeBKMap` を定義し、そのホモトピー同値性を各右frameのKan性とR03a.1から証明した。この同じ写像が元の `strictBETotUniversalProbeConePoint` を指定された `strictBETotUniversalBKProbeConePoint` へ送る等式も閉じた。

元のTot頂点・probe・右frame・一点重み・同じ比較jを保っている。まだBK切断の点から**全図式射を含むnative join錐の族**への接続はしていないため、R02・R03・停止点3b-4aの完成とは数えない。Uの極限保存から元のBE錐の極限性を逆算していない。

### 172.2 検証

230は右随伴の点・重み制限の点・元のBK普遍点の3本で **5,055 jobs・終了0、57モジュール380宣言**。231は同じ実写像のホモトピー同値の1本で **5,105 jobs・終了0、新規全58モジュール387宣言・標準三公理のみ**。実ハンドル31290・34664の終了0を確認し、鍵返却済み。ログ `/private/tmp/isw2-build230.log`・`231.log`、最終小監査 `/private/tmp/AuditISW2BKCells231.lean`。対象ビルドのみで、root・公式監査は流していない。

個別検査では、opaqueなendを展開して転置を同一視する代わりに、元のHom同値の両側の逆性を明示した。またKan性を同じ右随伴の全関手評価の型で明示して型クラス探索に渡した。計算上限の変更・sorry・独自公理0。SSetモデル構造の仮定なし。`--class impl --wait 3600`、同時整理券一枚、ビルドと小監査の間だけ鍵を保持した。

今回4本256行、各200行以下。3b-4の検証済み **58本・3,792行**。登録候補は同じBE用JSONへ追記。全体見込み・外枠15,000行は§170〜171のまま。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの作業木は変更していない。

### 172.3 型と残り

今回全て既存の右随伴・前合成・元の右frameの法則の照合。独立の新しい数学の一覧への追加0。次は同じ係数図式を既存の全Hom∞比較の入口へ合わせ、分類された切断から同じnative join錐へ進む。SimplicialHomとそのopを定義的に同一視せず、元の全自然同型・同じ頂点・両境界を保持する。/goalはactiveのまま続ける。

#### NativeWeightedSectionPoints（67行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I] (W : I ⥤ SSet.{u})

theorem coneSpaceNativeSectionsIso_homEquiv (X : SSet.{u}) (H : I ⥤ SSet.{u})
    (f : (WeightedCones.tensorDiagram I W).obj X ⟶ H) :
    (WeightedCones.adjunction I W).homEquiv X H f ≫ (coneSpaceNativeSectionsIso I W).hom.app H =
      weightedSectionsLift ((coneSpaceParameterIso I W).inv.app X ≫ f)

theorem coneSpaceParameterIso_zero :
    (coneSpaceParameterIso I W).inv.app (Δ[0] : SSet.{u}) ≫ (zeroTensorWeightIso I W).hom =
      fst W ((Functor.const I).obj (Δ[0] : SSet.{u}))

theorem coneSpaceNativeSectionsIso_point {H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    (((coneSpaceNativeSectionsIso I W).hom.app H).app (Opposite.op ⦋0⦌)) (conePoint I W s) =
      SSet.yonedaEquiv (weightedSectionsLift
        (fst W ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s))

```

#### NativeWeightedPointRestriction（46行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def nativeWeightedPoint {W H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    (weightedSections W H) _⦋0⦌

theorem nativeWeightedPoint_pre {V W H : I ⥤ SSet.{u}} (j : V ⟶ W) (s : W ⟶ H) :
    ((weightedSectionsPre j H).app (Opposite.op ⦋0⦌)) (nativeWeightedPoint I s) =
      nativeWeightedPoint I (j ≫ s)

```

#### StrictDiagramTotUniversalBKProbeCone（58行）

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

abbrev strictBETotProbeCoefficients (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    Kᵒᵖᵒᵖ ⥤ SSet.{u}

def strictBETotUniversalBKProbeWeightedCone (F : K ⥤ (operad A).Algebra) :
    bousfieldKanWeight Kᵒᵖᵒᵖ ⟶
      strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F)

def strictBETotUniversalBKProbeConePoint (F : K ⥤ (operad A).Algebra) :
    (weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))) _⦋0⦌

theorem strictBETotUniversalBKProbeConePoint_comparison (F : K ⥤ (operad A).Algebra) :
    ((weightedSectionsPre (HomotopyWeight.bkFramedWeightComparison K)
      (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
        ((((HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
          (HomotopyWeight.framedLimitWeight K)).hom.app
            (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
              (strictBETotUniversalProbeConePoint A K F)) =
      strictBETotUniversalBKProbeConePoint A K F

```

#### StrictDiagramTotBKSections（85行）

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite SSet
open SerrePositivity.DiagramModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotBKSectionsModelCategory : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotBKSectionsProbeCofibrant (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y

theorem strictBETotProbeCoefficients_kanComplex (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    SSet.KanComplex ((strictBETotProbeCoefficients A K F Y).obj i)

theorem strictBETotProbeBKRestriction_homotopyEquivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre (HomotopyWeight.bkFramedWeightComparison K)
      (strictBETotProbeCoefficients A K F Y))

def strictBETotProbeConeBKMap (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    ((framedLimitConeSpace A K Y).obj F) ⟶
      weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ) (strictBETotProbeCoefficients A K F Y)

theorem strictBETotProbeConeBKMap_homotopyEquivalence
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (strictBETotProbeConeBKMap A K F Y)

theorem strictBETotProbeConeBKMap_point (F : K ⥤ (operad A).Algebra) :
    ((strictBETotProbeConeBKMap A K F ((framedLimitFunctor A K).obj F)).app (op ⦋0⦌))
      (strictBETotUniversalProbeConePoint A K F) = strictBETotUniversalBKProbeConePoint A K F

```

## 173. 全rightFrameHom係数と同じBK重みの宇宙移送（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 14（うち追加 2）。R02・R03は未完了。

### 173.1 検証済みの到達点

元の右frameの反対圏Homと全Hom∞比較の入口の `rightFrameHom` を、同じ二重反対添字Kᵒᵖᵒᵖの**全射に自然な同型**として束ねた。元の自然同型 `rightFrameHomOpIso` の各成分を使い、各添字で独立に逆を選んでいない。指定されたBK普遍錐を同じ係数同型の逆で全rightFrameHom図式へ送り、同じ零単体の輸送の等式を閉じた。元の係数同型で戻すと、自然変換全体として元のBK普遍錐に戻る。

次のHom∞比較の入口は `rightFrameHammockKanDiagram` のphase0で、これは元のrightFrameHomの**宇宙持ち上げの後にEx∞を施した全図式**。単に同じKan複体だから定義的に等しいとは扱わない。また元の添字Kの宇宙uからmax(u,v)へのAsSmall変更が必要になるため、既存の0宇宙基底版の法則を、同じ明示的なover列のup・downで一般宇宙へ移した。

新規 `BousfieldKanUniverseWeight` は、`bousfieldKanWeight (AsSmall.{v} J)` と `AsSmall.down ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{max u v,u}` の実同型を、元のdownを順射として指定する。単体・構造射・添字の作用を保持し、別の重みを選んでいない。一般になった宇宙変更の法則なのでKerodon/LimitsAndColimits/HomotopyLimitsAndColimits/へ置いた。既存の0宇宙版やG10のファイルは変更していない。

### 173.2 検証・規模

232は係数の同型・点の後合成の2本で **5,107 jobs・終了0、60モジュール397宣言**。233は一般宇宙の重み同型の1本で **1,242 jobs・終了0、新規全61モジュール408宣言・標準三公理のみ**。実ハンドル84787・79978の終了0・鍵返却を確認。ログ `/private/tmp/isw2-build232.log`・`233.log`、小監査 `/private/tmp/AuditISW2BKCells233.lean`。対象ビルドと小監査だけ、`--class impl --wait 3600`、同時整理券一枚。

今回3本173行、各200行以下。3b-4の検証済み **61本・3,965行**。登録候補の同じJSONには一般のKerodonの1本も追加した。sorry・独自公理・計算上限の変更0。SSetモデルの仮定なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの作業木は変更していない。既存構成の係数移送・自然性の法則の照合であり、新しい独立の数学の一覧への追加0。

### 173.3 次の接続（未証明を明記）

次に必要なのは、同じBK切断の宇宙変更を切断空間全体の同型へ移すこと。型の案を一時ファイル `/private/tmp/CheckBKUniverseSectionsType.lean` で検査し、終了0を確認した。これは型の検査だけで、この同型の証明を済みとは数えていない。

```lean
-- universe u v
-- open CategoryTheory
-- open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

def bousfieldKanUniverseSectionsIso (I : Type u) [SmallCategory I] (H : I ⥤ SSet.{u}) :
    (SSet.uliftFunctor.{max u v,u}).obj (bousfieldKanHolim H) ≅
      bousfieldKanHolim ((AsSmall.down : AsSmall.{v} I ⥤ I) ⋙ H ⋙
        SSet.uliftFunctor.{max u v,u})
```

候補は、今回の同じBK重みの同型、既存の切断の `uliftSectionsIso`・`bousfieldKanSectionsIso`、またはULiftの全忠実性と元の転置の自然性を使う経路。実際の順射と元の指定点・標準脚の等式を保持して組み立てる。続くEx∞への係数の単位については、既存 `BousfieldKanHomotopyInvariance.bousfieldKanMap_homotopyEquivalence` がKan係数の成分ごとの同値から**同じ係数射が誘導するBK切断写像**のホモトピー同値を与える。ここを新しい係数不変性の定理で作り直す必要はない。

その後、既存 `weightedNerveStraighteningUnitIso` と§165の全Hom∞比較を使い、同じ分類像・cosliceの切断へ移す。`fixedVertexConeSpaceEquiv` に戻す際は元の頂点を指定し、全族の両境界と、極限判定のa・ha・heの同じ頂点評価の等式を省略しない。まだnative join錐族を構成・検証したとは数えない。/goalはactiveのまま、次の同じ宇宙の切断の照合へ続ける。

### 173.4 今回の法則の型

#### NativeWeightedPointMap（28行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

theorem nativeWeightedPoint_map {W F G : I ⥤ SSet.{u}} (s : W ⟶ F) (f : F ⟶ G) :
    ((weightedSectionsMap W f).app (Opposite.op ⦋0⦌)) (nativeWeightedPoint I s) =
      nativeWeightedPoint I (s ≫ f)

```

#### StrictDiagramTotProbeCoefficientsComparison（68行）

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeCoefficientComparisonModel : ModelCategory (operad A).Algebra := modelCategory A

def strictBETotProbeRightHomDiagram (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    Kᵒᵖᵒᵖ ⥤ SSet.{u}

def strictBETotProbeCoefficientsIso (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    strictBETotProbeRightHomDiagram A K F Y ≅ strictBETotProbeCoefficients A K F Y

def strictBETotUniversalBKRightHomCone (F : K ⥤ (operad A).Algebra) :
    bousfieldKanWeight Kᵒᵖᵒᵖ ⟶
      strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F)

theorem strictBETotUniversalBKRightHomCone_back (F : K ⥤ (operad A).Algebra) :
    strictBETotUniversalBKRightHomCone A K F ≫
      (strictBETotProbeCoefficientsIso A K F ((framedLimitFunctor A K).obj F)).hom =
        strictBETotUniversalBKProbeWeightedCone A K F

def strictBETotUniversalBKRightHomPoint (F : K ⥤ (operad A).Algebra) :
    (weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F))) _⦋0⦌

theorem strictBETotUniversalBKRightHomPoint_comparison (F : K ⥤ (operad A).Algebra) :
    ((weightedSectionsMap (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (strictBETotProbeCoefficientsIso A K F ((framedLimitFunctor A K).obj F)).inv).app (op ⦋0⦌))
        (strictBETotUniversalBKProbeConePoint A K F) = strictBETotUniversalBKRightHomPoint A K F

```

#### BousfieldKanUniverseWeight（77行）

```lean
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory
variable (J : Type u) [SmallCategory J]

def bousfieldKanUniverseOverLift (j : AsSmall.{v} J) :
    Over ((AsSmall.down : AsSmall.{v} J ⥤ J).obj j) ⥤ Over j

theorem bousfieldKanUniverseOverLift_down (j : AsSmall.{v} J) :
    bousfieldKanUniverseOverLift J j ⋙ Over.post (AsSmall.down : AsSmall.{v} J ⥤ J) = 𝟭 _

theorem bousfieldKanUniverseOverDown_lift (j : AsSmall.{v} J) :
    Over.post (AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanUniverseOverLift J j = 𝟭 _

def bousfieldKanUniverseWeightDown : bousfieldKanWeight (AsSmall.{v} J) ⟶
    (AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{max u v,u}

instance bousfieldKanUniverseWeightDown_isIso : IsIso (bousfieldKanUniverseWeightDown.{u,v} J)

def bousfieldKanUniverseWeightIso : bousfieldKanWeight (AsSmall.{v} J) ≅
    (AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{max u v,u}

```

## 174. 同じBK切断の宇宙変更と指定点（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 14（うち追加 2）。

R02〜R03の係数移送の法則として、ULiftとAsSmall.downによる同じ切断空間の比較を構成した。順射は元の普遍評価の転置で、ULiftの全忠実性から各標準単体上で全単射になることを示した。同じBK重みの指定downとの合成が `bousfieldKanUniverseSectionsIso` の順射である。さらに元の自然変換が定める零単体を、同じdownで運んだ自然変換の零単体へ厳密に送ることを示した。新しいKan置換や別の指定点を選んでいない。

7本・366行追加、累計68本・4331行（外枠15,000行）。いずれも200行以下。既存の宇宙変更・切断の普遍性・係数移送の法則で、一覧の追加項目は増やさない。native join錐の族と極限性はまだ未完で、R02/R03を完了とは数えない。

検証：対象ビルド234は1,262 jobs、235は2,346 jobsで成功。235の小監査は68本・434宣言、標準三公理 `propext`・`Classical.choice`・`Quot.sound` のみ。両ログで成功と監査完走を確認し、235のプロセスも終了済み。sorry・新規公理なし。共通入口と本体監査には登録せず、上記manifestを調整役への登録候補とする。

次は同じ零単体をEx∞の係数単位に運び、既存の全Hom∞比較およびcoslice分類との比較へ接続する。元の頂点と脚の照合を残す。

### 174.1 今回の法則と証明分割の型

#### BousfieldKanUniversePoints（43行）

```lean
def bousfieldKanUniverseCone (s : bousfieldKanWeight I ⟶ H) :
    bousfieldKanWeight (AsSmall.{v} I) ⟶ (weightedDiagramUniverse.{u,v} I).obj H

theorem bousfieldKanUniverseSectionsIso_point (s : bousfieldKanWeight I ⟶ H) :
    (((bousfieldKanUniverseSectionsIso.{u,v} I H).hom).app (Opposite.op ⦋0⦌))
      (ULift.up (nativeWeightedPoint I s)) =
        nativeWeightedPoint (AsSmall.{v} I) (bousfieldKanUniverseCone I s)
```

#### BousfieldKanUniverseSections（32行）

```lean
def bousfieldKanUniverseSectionsIso :
    (SSet.uliftFunctor.{max u v,u}).obj (bousfieldKanHolim H) ≅
      bousfieldKanHolim ((AsSmall.down : AsSmall.{v} I ⥤ I) ⋙ H ⋙
        SSet.uliftFunctor.{max u v,u})

theorem bousfieldKanUniverseSectionsIso_hom :
    (bousfieldKanUniverseSectionsIso.{u,v} I H).hom =
      weightedSectionsUniverseComparison I (bousfieldKanWeight I) H ≫
        weightedSectionsPre (bousfieldKanUniverseWeightDown I) ((weightedDiagramUniverse.{u,v} I).obj H)
```

#### WeightedDiagramUniverse（72行）

```lean
def weightedDiagramUniverse : (I ⥤ SSet.{u}) ⥤ (AsSmall.{v} I ⥤ SSet.{max u v})

instance weightedDiagramUniverse_full : (weightedDiagramUniverse.{u,v} I).Full

instance weightedDiagramUniverse_faithful : (weightedDiagramUniverse.{u,v} I).Faithful

def weightedDiagramUniverseTensorIso (W : I ⥤ SSet.{u}) (A : SSet.{u}) :
    (weightedDiagramUniverse.{u,v} I).obj (W ⊗ (Functor.const I).obj A) ≅
      (weightedDiagramUniverse.{u,v} I).obj W ⊗
        (Functor.const (AsSmall.{v} I)).obj ((SSet.uliftFunctor.{max u v,u}).obj A)

@[reassoc] theorem weightedDiagramUniverseTensorIso_inv_parameter (W : I ⥤ SSet.{u})
    {A B : SSet.{u}} (f : A ⟶ B) :
    ((weightedDiagramUniverse.{u,v} I).obj W ◁
      (Functor.const (AsSmall.{v} I)).map ((SSet.uliftFunctor.{max u v,u}).map f)) ≫
        (weightedDiagramUniverseTensorIso I W B).inv =
      (weightedDiagramUniverseTensorIso I W A).inv ≫
        (weightedDiagramUniverse I).map (W ◁ (Functor.const I).map f)
```

#### WeightedSectionsUniverseComparison（47行）

```lean
def weightedSectionsUniverseEvaluation :
    (weightedDiagramUniverse.{u,v} I).obj W ⊗
      (Functor.const (AsSmall.{v} I)).obj
        ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) ⟶
          (weightedDiagramUniverse.{u,v} I).obj H

def weightedSectionsUniverseComparison :
    (SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H) ⟶
      weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H)

theorem weightedSectionsUniverseComparison_map_uncurry {A : SSet.{u}}
    (f : A ⟶ weightedSections W H) :
    weightedSectionsUncurry ((SSet.uliftFunctor.{max u v,u}).map f ≫
      weightedSectionsUniverseComparison I W H) =
        (weightedDiagramUniverseTensorIso I W A).inv ≫
          (weightedDiagramUniverse I).map (weightedSectionsUncurry f)
```

#### WeightedSectionsUniverseHomEquiv（42行）

```lean
def weightedSectionsUniverseHomEquiv (A : SSet.{u}) :
    (A ⟶ weightedSections W H) ≃
      ((SSet.uliftFunctor.{max u v,u}).obj A ⟶
        weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
          ((weightedDiagramUniverse.{u,v} I).obj H)) where
  toFun f
```

#### WeightedSectionsUniverseIso（62行）

```lean
def weightedSectionsUniverseSimplexEquiv (n : ℕ) :
    ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) _⦋n⦌ ≃
      (weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H)) _⦋n⦌

theorem weightedSectionsUniverseSimplexEquiv_apply {n : ℕ}
    (s : ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) _⦋n⦌) :
    weightedSectionsUniverseSimplexEquiv I W H n s =
      (weightedSectionsUniverseComparison.{u,v} I W H).app (Opposite.op ⦋n⦌) s

instance weightedSectionsUniverseComparison_isIso :
    IsIso (weightedSectionsUniverseComparison.{u,v} I W H)

def weightedSectionsUniverseIso :
    (SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H) ≅
      weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H)
```

#### WeightedSectionsUniversePoints（68行）

```lean
@[reassoc] theorem weightedDiagramUniverseTensorIso_zero_fst (W : I ⥤ SSet.{u}) :
    ((weightedDiagramUniverse.{u,v} I).obj W ◁ (Functor.const (AsSmall.{v} I)).map
      (uliftStdSimplexIso.{u,max u v} 0).inv) ≫
        (weightedDiagramUniverseTensorIso I W (Δ[0] : SSet.{u})).inv ≫
          (weightedDiagramUniverse I).map (fst W ((Functor.const I).obj (Δ[0] : SSet.{u}))) =
      fst ((weightedDiagramUniverse.{u,v} I).obj W)
        ((Functor.const (AsSmall.{v} I)).obj (Δ[0] : SSet.{max u v}))

theorem weightedSectionsUniverseComparison_point {W H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    ((weightedSectionsUniverseComparison.{u,v} I W H).app (Opposite.op ⦋0⦌))
      (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
        (fst W ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s)))) =
        SSet.yonedaEquiv (weightedSectionsLift
          (fst ((weightedDiagramUniverse.{u,v} I).obj W)
            ((Functor.const (AsSmall.{v} I)).obj (Δ[0] : SSet.{max u v})) ≫
              (weightedDiagramUniverse.{u,v} I).map s))
```

## 175. 分類比較から同じ切断模型への接続 R03b（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 15（うち追加 3）。

IS-W2 §19の同じまとまり・1,500行以下の枠で、次の中間項目 **R03b** を追加する。R02〜R03の、元のBK係数のweighted nerveと同じ頂点のcosliceの引き戻しの分類比較から、その二つの射影の切断空間へ戻す段である。全分類同型だけをnative切断や錐そのものと取り違えないために、元の二つの射影を型に指定する。

```lean
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

def classifiedLeftFibrationSectionsEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (η : FunctorIso (leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram q)) :
    QCatEquivalence (simplicialSections p) (simplicialSections q)
```

見込みは250〜500行（同じ底を厳密に保つ復元の比較80〜160行、相対関手空間と元の切断模型の照合100〜180行、合成・BEへの適用70〜160行）。既存 `leftStraighteningInfinityReconstruction`、`smallLeftUnstraighteningComparisonOfFunctorIso` と、底上の前合成同値による `relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence` を使う。共通の復元を頂点とする二本の実写像で比較し、元の切断空間の同型を通して戻す。新しいstrictificationやBE模型は作らない。

これは固定された射影の中間比較であり、R02の全図式射の錐族・R03の極限判定のa・ha・heは残す。元の指定BK点の像と、元の図式の標準脚の一致も後で明記する。この比較だけでnative join錐族を完成と数えない。外枠15,000行・⑤aの既存欄の型は変更しない。見込みが1,500行を超える場合や別のまとまりが必要と分かった場合は、検証済みを保存して報告する。

## 176. 同じEx∞係数とnative錐射影の全分類比較（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 15（うち追加 3）。R03bは§175で追加し個別検査中。R02/R03は未完了。

元のraw right-frame Hom係数を同じAsSmall.downとULiftで運び、元のEx∞単位を合成した。Kan係数への単位が誘導する**実際のBK切断写像**のホモトピー同値を、既存BK係数不変性から証明した。元の指定BK点が同じ宇宙変更と同じ単位により送られる零単体の等式も証明した。

この係数図式は、既存の全frame比較の第零Kan図式を指定添字関手で引き戻したものと定義どおり等しい。そのcoherent nerveも既存の全図式の前合成と等しい。これに元の全Hom∞比較とcoslice分類の全同型を合成し、同じweighted nerveと同じ頂点のnative錐射影の**元の二つのleft fibrationの全分類同型**まで接続した。値ごとの同値だけを集めたものではない。

検証：236は対象ビルド10,630 jobs・70本448宣言、237は10,639 jobs・73本482宣言、238は10,636 jobs・74本497宣言。各対象ビルドと小監査が終了0、標準三公理のみ。対象は新規2本・3本・1本を指定し、rootや公式大監査は実行していない。実ハンドル67359・21555・31411の終了0を確認。個別検査で不足していたKanインスタンスと関手的分解を明示し、計算上限は変更しなかった。

今回6本415行、累計74本・4746行。各200行以下。全て既存の係数移送・全比較の合成・貼り合わせの法則で、これら6本による一覧の追加は0。新しい中間項目は別途§175のR03bだけ。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。

次はR03bの元の切断模型への復帰、その同じ比較を通じた指定点の像と元の標準脚の照合。native join錐の全族や極限判定のa・ha・heはまだ証明したと数えない。

### 176.1 今回の法則の型

#### BousfieldKanExInfinityUnit（53行）

```lean
def bousfieldKanExInfinityCoefficientUnit (H : I ⥤ SSet.{u}) : H ⟶ H ⋙ exInfinity

theorem bousfieldKanExInfinityUnit_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    IsSimplicialHomotopyEquivalence
      (weightedSectionsMap (bousfieldKanWeight I) (bousfieldKanExInfinityCoefficientUnit I H))

theorem bousfieldKanExInfinityUnit_point {H : I ⥤ SSet.{u}}
    (s : bousfieldKanWeight I ⟶ H) :
    ((weightedSectionsMap (bousfieldKanWeight I)
      (bousfieldKanExInfinityCoefficientUnit I H)).app (Opposite.op ⦋0⦌))
        (nativeWeightedPoint I s) = nativeWeightedPoint I
          (s ≫ bousfieldKanExInfinityCoefficientUnit I H)
```

#### StrictDiagramTotProbeKanCoefficients（96行）

```lean
def strictBETotProbeFrameIndex (F : K ⥤ (operad A).Algebra) :
    AsSmall.{u+1} Kᵒᵖᵒᵖ ⥤ AsSmall.{u+1} (operad A).Algebra

theorem strictBETotProbeKanCoefficients_eq (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    (weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj (strictBETotProbeRightHomDiagram A K F Y) ⋙
      exInfinity = strictBETotProbeFrameIndex A K F ⋙
        FrameHom.rightFrameHammockKanDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C

theorem strictBETotProbeRightHomDiagram_kanComplex (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    KanComplex ((strictBETotProbeRightHomDiagram A K F Y).obj i)

theorem strictBETotProbeUniverseCoefficients_kanComplex (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex (((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
      (strictBETotProbeRightHomDiagram A K F Y)).obj i)

theorem strictBETotProbeBKExInfinityUnit_homotopyEquivalence
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (weightedSectionsMap
      (bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ))
      (HomotopyWeight.bousfieldKanExInfinityCoefficientUnit (AsSmall.{u+1} Kᵒᵖᵒᵖ)
        ((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
          (strictBETotProbeRightHomDiagram A K F Y))))

def strictBETotUniversalBKExInfinityCone (F : K ⥤ (operad A).Algebra) :
    bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ) ⟶
      (weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
        (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F)) ⋙ exInfinity

theorem strictBETotUniversalBKExInfinityCone_point (F : K ⥤ (operad A).Algebra) :
    ((weightedSectionsMap (bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ))
      (HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _
        ((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
          (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F))))).app (op ⦋0⦌))
        (((bousfieldKanUniverseSectionsIso.{u,u+1} Kᵒᵖᵒᵖ
          (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F))).hom).app (op ⦋0⦌)
            (ULift.up (strictBETotUniversalBKRightHomPoint A K F))) =
      HomotopyWeight.nativeWeightedPoint _ (strictBETotUniversalBKExInfinityCone A K F)
```

#### StrictDiagramTotProbeCosliceClassification（63行）

```lean
def strictBEAlgebraProbeCosliceClassificationIso (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C

def strictBETotDiagramProbeCosliceClassificationIso
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialNerve A F) ≫
        (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
          FrameHom.rightFrameHammockCoherentDiagram
            ((SimplicialLocalization.modelSourceFrameFamily (C
```

#### StrictDiagramTotProbeKanDiagram（53行）

```lean
def strictBETotProbeKanDiagram (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    AsSmall.{u+1} Kᵒᵖᵒᵖ ⥤ KanObject.{u+1}

theorem strictBETotProbeKanDiagram_frame (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    strictBETotProbeKanDiagram A K F Y = strictBETotProbeFrameIndex A K F ⋙
      FrameHom.rightFrameHammockKanDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C

theorem strictBETotProbeKanDiagram_coherent (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    kanDiagramCoherentNerve (strictBETotProbeKanDiagram A K F Y) =
      (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotProbeFrameIndex A K F)) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C
```

#### StrictDiagramTotBKClassification（74行）

```lean
def strictBETotUniverseDiagram (F : K ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ)) ⟶
      (SSet.uliftFunctor.{u+2,u+1}).obj (CAlg_R A)

def strictBETotKanDiagramCosliceIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    FunctorIso (kanDiagramCoherentNerve (strictBETotProbeKanDiagram A K F Y))
      (strictBETotUniverseDiagram A K F ≫
        leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))))

def strictBETotBKClassificationIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    FunctorIso
      (leftStraighteningCandidate ((weightedNerveKanEnriched (AsSmall.{u+1} Kᵒᵖᵒᵖ)).obj
        ⟨strictBETotProbeKanDiagram A K F Y, trivial⟩).val.hom)
      (strictBETotUniverseDiagram A K F ≫
        leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))))
```

#### StrictDiagramTotBKNativeClassification（76行）

```lean
def strictBETotUniverseSourceDiagram (F : K ⥤ (operad A).Algebra) :
    nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ) ⟶ CAlg_R A

theorem strictBETotUniverseSourceDiagram_lift (F : K ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotUniverseSourceDiagram A K F) =
      strictBETotUniverseDiagram A K F

def strictBETotBKNativeClassificationIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    FunctorIso
      (leftStraighteningInfinityDiagram (weightedNerveProjection
        (strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget)))
      (leftStraighteningInfinityDiagram (coherentConeProjection
        (strictBETotUniverseSourceDiagram A K F)
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
          (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))))
```

## 177. R03b完了と元のΔ図式上の一つの指定native錐（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 15（うち追加 3）。済みはR01・R03a・R03a.1・R03b。R02の全錐族、R03の極限性は未完了。

§175の型のまま `classifiedLeftFibrationSectionsEquivalence` を証明した。元の二つの射影から共通の小さいunstraighteningへの底上の二本の比較を使い、元の切断空間の実際の同値へ戻した。BEでは、同じBK係数の切断から、元のCAlg図式と同じ頂点のnative錐の切断模型への同値を得た。

この比較による**元の普遍BK点の像**を指定頂点の錐との既存全単射で戻して、実際のjoin錐を作った。左境界は元のTot頂点のYoneda射に等しく、同じ切断模型へ戻した点は元のBK点の同じ像に等しい。さらに元のAsSmall・二重反対の指定同型で元のΔ添字に戻した。同型に沿う全図式は `strictBECosimplicialDiagram A F` と厳密に等しく、戻したnative錐 `strictBETotNativeConeAt` の頂点も元のTot頂点そのものである。

**まだ示していないもの**：この一図式の錐の全図式射についての族、元の標準脚の最終照合、元の同じ錐の極限性。そのため `strictBETotNativeConeAt` はR02の全族を完成と数える代用にしない。特にR03の判定のa・ha・heを省略せず、Uの極限保存から逆向きに元のBEの極限性を推論しない。

### 177.1 検証と行数

239：三本の対象ビルド10,639 jobs・終了0、小監査77本527宣言。240：二本の対象ビルド10,642 jobs・終了0、小監査79本539宣言。いずれも標準三公理のみ。実ハンドル35625・74011の終了0を確認、鍵は返却済み。個別検査で元の切断空間のKan性を局所に明示し、計算上限の変更なし。sorry・独自公理0。

今回5本298行、累計79本・5044行（外枠15,000）。各200行以下。R03bの一般形・BEへの適用・元の指定BK点からの錐の組立ては199行で、§175の250〜500行の見込みを51〜301行下回った。添字移送と元のΔ上の錐の照合は別に99行の既存の構成の法則・証明分割で、追加項目には数えない。R03b以外の新しい項目は追加していない。⑤a・既存FramedLimit*・CAlgUnderlyingDerivedComparison・共通入口・公式監査・mainは変更していない。

### 177.2 見込みの半分での追記

§170で初期見込みの下端5,700行の半分を報告済み。今回、初期上端9,800行の半分4,900行も超えた。現在5044行。元の重み比較を作り直す必要はなくなり、元の指定BK点から実際の同じ頂点の錐へ到達した。一方、全族の高次自然性と標準脚の照合の部分には未実測の幅が残る。

残りの見込み：R02〜R03の標準脚・全錐族・極限判定の接続1,000〜2,000行、R04〜R05の台のTotと局所化1,000〜1,800行、実現R06〜R10が2,800〜4,800行、R11〜R12が500〜900行。残り約5,300〜9,500行、累計約10,300〜14,500行。外枠15,000は維持するが上側の余裕は小さく、次の接続の実測で更新する。型・範囲を弱めたり、点ごとの錐を全族と読み替えたりしない。

次は、同じ錐の脚の評価と、既存の全自然比較を使った全族の接続。R03bの切断の逆の選択だけで図式射について厳密な自然性が自動的に得られるとは主張しない。指定された全比較に戻して両境界を照合する。

### 177.3 今回の型

#### ClassifiedSectionsComparison（62行）

```lean
theorem simplicialSectionsMap_isQCatEquivalence_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    IsQCatEquivalence (simplicialSectionsMap f hf)

def classifiedLeftFibrationSectionsEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (η : FunctorIso (leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram q)) :
    QCatEquivalence (simplicialSections p) (simplicialSections q)
```

#### StrictDiagramTotBKNativeSections（55行）

```lean
def strictBETotBKNativeSectionsEquivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    QCatEquivalence
      (bousfieldKanHolim (strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget))
      (coherentConeSectionSpace (strictBETotUniverseSourceDiagram A K F)
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))
```

#### StrictDiagramTotUniverseNativeCone（77行）

```lean
def strictBETotUniverseNativeConePoint (F : K ⥤ (operad A).Algebra) :
    (coherentConeSectionSpace (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A K).obj F)))) _⦋0⦌

def strictBETotUniverseNativeCone (F : K ⥤ (operad A).Algebra) :
    JoinCone (strictBETotUniverseSourceDiagram A K F)

theorem strictBETotUniverseNativeCone_vertexMap (F : K ⥤ (operad A).Algebra) :
    joinInl (Δ[0] : SSet.{u+1}) _ ≫ (strictBETotUniverseNativeCone A K F).val =
      SSet.yonedaEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A K).obj F)))

theorem strictBETotUniverseNativeCone_section (F : K ⥤ (operad A).Algebra) :
    fixedVertexConeSpaceEquiv (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A K).obj F)))
      ⟨strictBETotUniverseNativeCone A K F, strictBETotUniverseNativeCone_vertexMap A K F⟩ =
        strictBETotUniverseNativeConePoint A K F
```

#### StrictDiagramTotUniverseIndex（44行）

```lean
def strictBETotOpOpNerveIso (K : Type u) [SmallCategory K] : nerve Kᵒᵖᵒᵖ ≅ nerve K

def strictBETotUniverseIndexIso (K : Type u) [SmallCategory K] :
    nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ) ≅ (SSet.uliftFunctor.{u+1,u}).obj (nerve K)

theorem strictBETotUniverseSourceDiagram_index (A : Type u) [CommRing A]
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    strictBETotUniverseSourceDiagram A (AsSmall.{u} SimplexCategory) F =
      (strictBETotUniverseIndexIso (AsSmall.{u} SimplexCategory)).hom ≫
        strictBECosimplicialDiagram A F
```

#### StrictDiagramTotNativeConeAt（55行）

```lean
def strictBETotNativeConeAt (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    JoinCone (strictBECosimplicialDiagram A F)

theorem strictBETotNativeConeAt_vertexMap
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    joinInl (Δ[0] : SSet.{u+1}) _ ≫ (strictBETotNativeConeAt A F).val =
      SSet.yonedaEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F)))

theorem strictBETotNativeConeAt_vertex
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (strictBETotNativeConeAt A F).vertex = (algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F))
```

## 178. 指定分類変換を回収する全切断の三角形（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 15（うち追加 3）。R02/R03の全錐族・標準脚・極限性は未完了。

R03bの型は保ち、証明に用いる共通の復元への写像を明示した。従来の `smallLeftUnstraighteningComparisonOfFunctorIso` の公開仕様は底上の比較と前合成同値を与える。指定した分類同型の変換そのものを回収して次の評価を追跡するため、既存 `smallUnstraighteningFunctorHom η.hom` による同じ復元への合成を使用した。代表辺の類が元のη.homに等しい既存回収則を明示している。新しいBE模型・strictification・型の変更はない。

`classifiedLeftFibrationSectionsEquivalence_triangle` は、同じ切断比較を標的の復元へ送ると、元の指定ηを使用する復元射による切断と全関手同型で一致することを証明する。元の後合成の同値の余単位を、同じ元の切断写像で前合成したもの。これをBEのBK切断同型とnative錐切断同型を通して運んだ `strictBETotBKNativeSections_reconstruction` も証明した。零単体・π₀の一致だけで代用していない。

三本166行追加、R03b本体は67→62行。累計82本・5,205行。全て既存構成の回収・余単位・合成の法則と、R03bの証明分割で、追加の一覧項目は0。200行超の新規ファイルなし。main・⑤a・既存FramedLimit*・CAlgUnderlyingDerivedComparison・入口・公式監査は変更していない。修正したR03bはこの枝で追加した未取り込みの宣言であり、型は§175のまま。

検証：依存一本の対象ビルド241は2,561 jobsで終了0。242は新規共通二本と直接importerの指定native錐を再ビルドして10,648 jobs・終了0、小監査81本548宣言。243はBEの回収三角形一本を対象ビルドして10,645 jobs・終了0、小監査82本568宣言。全て標準三公理のみ、sorry・独自公理0。実ハンドル93037・5489・31459の終了0を確認し、鍵は返却済み。既存の回収APIの未ビルド依存で止まった個別検査は成功に数えず、241の後に個別検査と対象ビルドを通した。計算上限は変更していない。

次は元の切断のfiber評価と後合成の厳密な自然性を使い、同じ共通の復元のfiberでこの全三角形を評価する。まだ標準脚そのものとの一致や全図式射の錐族を得たとは数えない。

### 178.1 今回の法則・証明分割の型

#### ClassifiedFibrationTransport（49行）

```lean
def classifiedFibrationTransport :
    E ⟶ smallLeftUnstraightening (leftStraighteningInfinityDiagram q)

theorem classifiedFibrationTransport_projection :
    classifiedFibrationTransport p q η ≫
      smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) = p

theorem classifiedFibrationTransport_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (classifiedFibrationTransport p q η)

theorem classifiedFibrationTransport_edge_hom :
    SSet.Truncated.HomotopyCategory.homMk
      (smallUnstraighteningHomEdge η.hom).toTruncated = η.hom
```

#### ClassifiedSectionsTriangle（45行）

```lean
def classifiedLeftFibrationSectionsEquivalence_triangle :
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
          (leftStraighteningInfinityReconstruction_projection q))
      (simplicialSectionsMap (classifiedFibrationTransport p q η)
        (classifiedFibrationTransport_projection p q η))
```

#### StrictDiagramTotNativeSectionsRecovery（72行）

```lean
def strictBETotBKNativeSections_reconstruction
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    let p := weightedNerveProjection H
    let q := coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
    let η := strictBETotBKNativeClassificationIso A K F Y
    FunctorIso
      (((strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv) ≫
            simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
              (leftStraighteningInfinityReconstruction_projection q))
      ((bousfieldKanSectionsIso H).hom ≫
        simplicialSectionsMap (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η))
```

## 179. 同じ全切断比較の各次数のfiberでの評価（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 15（うち追加 3）。R02/R03の標準脚・全錐族・極限性は未完了。

元の普遍切断を底の指定頂点で制限し、同じ射影のfiberへ持ち上げる `simplicialSectionsFiberEvaluation` を構成した。充填性を仮定せず、元の底上の後合成とこの評価が厳密に可換であることを示した。既存の普遍評価とfiberへの持ち上げの評価・自然性の法則である。

これにより、§178の同じ全切断三角形は各fiberの間の全単体的写像についても関手同型で可換となる。BEへの適用 `strictBETotBKNativeSections_fiber_reconstruction` では、元のBK係数・同じ元の図式・同じ頂点・同じ分類同型を指定した。元のBK切断の像を、native錐の切断へ送ってから共通の復元のfiberへ送る写像と、同じ元の指定分類変換を使って先に共通の復元へ送る写像を全次数で比較する。π₀・零単体だけの比較で代用していない。

検証：244は二本の対象ビルド3,122 jobs・終了0、小監査84本580宣言。245はBEの一本の対象ビルド10,647 jobs・終了0、小監査85本599宣言。いずれも標準三公理のみ、実ハンドル15467・13905の終了0を確認し鍵は返却済み。個別検査で標準単体記法と結合済みの自然性を明示した後に対象ビルドを行った。sorry・独自公理0、計算上限の変更なし。

今回三本177行、累計85本・5,382行。全て既存の評価・後合成・余単位の法則で、追加の一覧項目は0。各200行以下。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。これは標準脚そのものや全図式射のnative錐族・極限性の完了ではない。

### 179.1 次の元の係数での照合

weighted nerveのfiber同型で元の係数H.obj iへ戻し、同じBK重みの恒等射の零単体での評価と合わせる。次は元の構成の評価・単位則として以下を検査する（見込み100〜250行）。まだ証明・検証済みとは数えない。

```lean
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable (I : Type u) [SmallCategory I] (H : I ⥤ SSet.{u})

-- namespace SerrePositivity.EInfinity.HomotopyWeight
-- 元の指定sの零単体を、元の同じ係数へ厳密に戻す。
theorem bousfieldKanSectionsIso_nativeWeightedPoint_fiber
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((weightedNerveFiberIso H i).inv.app (Opposite.op ⦋0⦌))
      ((simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i)).app
        (Opposite.op ⦋0⦌)
        (((bousfieldKanSectionsIso H).hom.app (Opposite.op ⦋0⦌))
          (nativeWeightedPoint I s))) =
      (s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))
```

その後、BEの同じEx∞係数単位と指定BK重み比較へ特殊化し、元の標準脚への正規化を追う。ここでも、R03bの切断同値の逆の選択だけから全図式射の厳密な自然性が自動で出るとは主張しない。

### 179.2 今回の法則の型

#### SectionFiberEvaluation（48行）

```lean
def simplicialSectionsFiberEvaluation (p : E ⟶ B) (b : B _⦋0⦌) :
    simplicialSections p ⟶ vertexFiber p b

@[reassoc] theorem simplicialSectionsFiberEvaluation_ι (p : E ⟶ B) (b : B _⦋0⦌) :
    simplicialSectionsFiberEvaluation p b ≫ vertexFiberι p b =
      lift (SSet.const b) (𝟙 (simplicialSections p)) ≫ simplicialSectionsEvaluation p

theorem simplicialSectionsFiberEvaluation_naturality
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    simplicialSectionsMap f hf ≫ simplicialSectionsFiberEvaluation q b =
      simplicialSectionsFiberEvaluation p b ≫ vertexFiberMap p q f hf b
```

#### ClassifiedSectionsFiberTriangle（50行）

```lean
def classifiedLeftFibrationSectionsEquivalence_fiber_triangle (b : B _⦋0⦌) :
    let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsFiberEvaluation q b ≫
          vertexFiberMap q r (leftStraighteningInfinityReconstruction q)
            (leftStraighteningInfinityReconstruction_projection q) b)
      (simplicialSectionsFiberEvaluation p b ≫
        vertexFiberMap p r (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η) b)
```

#### StrictDiagramTotNativeFiberRecovery（79行）

```lean
def strictBETotBKNativeSections_fiber_reconstruction
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra)
    (b : (nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ)) _⦋0⦌) :
    let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    let p := weightedNerveProjection H
    let q := coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
    let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
    let η := strictBETotBKNativeClassificationIso A K F Y
    FunctorIso
      (((strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv) ≫
            simplicialSectionsFiberEvaluation q b ≫
              vertexFiberMap q r (leftStraighteningInfinityReconstruction q)
                (leftStraighteningInfinityReconstruction_projection q) b)
      ((bousfieldKanSectionsIso H).hom ≫ simplicialSectionsFiberEvaluation p b ≫
        vertexFiberMap p r (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η) b)
```

## 180. 元のBK指定点の係数への厳密な回収と宇宙変更・係数単位（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 15（うち追加 3）。R02/R03の標準脚・全錐族・極限性は未完了。

§179.1の型のまま `bousfieldKanSectionsIso_nativeWeightedPoint_fiber` を証明した。元の指定BK点を切断模型に送り、元の次数のfiberで評価して元の係数へ戻した値は、元の自然変換の恒等射のBK零単体での値に**厳密に等しい**。Kan性・モデル構造の追加なし。

証明は、元のliftとBK切断比較を合成した普遍評価の等式、零次のweighted nerveの初区間の係数計算、元のfiber同型による打ち消しに分割した。不透明なendを展開せず、元の普遍評価・パラメーター自然性・Yonedaの評価・直積の第一射影の法則を使った。

さらに同じAsSmall.down・ULiftで宇宙変更した自然変換と、同じEx∞係数単位を合成した自然変換についても、fiberから回収した値が元の恒等射の値の指定像に等しいことを証明した。BE Totで用いた同じ `strictBETotUniversalBKExInfinityCone` に適用するための一般の係数移送則で、新しい係数・重み・単位を選んでいない。

検証：246は一本の対象ビルド2,606 jobs・終了0、小監査86本602宣言。247は一本の対象ビルド3,376 jobs・終了0、小監査87本605宣言。標準三公理のみ。実ハンドル20536・21339の終了0を確認し、鍵は返却済み。個別検査で零次の係数計算を元の自然変換の型で保持し、AsSmallのup/downを明示してから対象ビルドを通した。sorry・独自公理0、計算上限の変更なし。

二本164行追加、累計87本・5,546行。§179.1の元のfiber回収則は99行で、100〜250行の見込みを1〜151行下回った。宇宙変更と係数単位の評価則は別に65行。全て既存構成の評価・単位・係数移送の法則で、今回の追加の一覧項目は0。200行超の新規ファイルなし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。

次は§179の共通の復元のfiberでの全三角形から、元のnative錐のfiberでの比較へ戻す。これはまだ元の標準脚の最終一致・全錐族・極限性の完成ではない。

### 180.1 今回の法則の型

#### BousfieldKanNativeFiberPoint（99行）

```lean
theorem bousfieldKanSectionsMap_lift_evaluation {A : SSet.{u}}
    (η : bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) :
    (nerve I ◁ (weightedSectionsLift η ≫ bousfieldKanSectionsMap H)) ≫
      simplicialSectionsEvaluation (weightedNerveProjection H) =
        weightedNerveSectionFromTransform η

theorem weightedNerveSectionFromTransform_zero_point
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    (weightedNerveSectionFromTransform
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s)).app
        (Opposite.op ⦋0⦌) (nerveVertex i, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) =
    (weightedNerveConstantLift H i).app (Opposite.op ⦋0⦌)
      ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))

theorem bousfieldKanSectionsIso_nativeWeightedPoint_fiber
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((weightedNerveFiberIso H i).inv.app (Opposite.op ⦋0⦌))
      ((simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i)).app
        (Opposite.op ⦋0⦌)
        (((bousfieldKanSectionsIso H).hom.app (Opposite.op ⦋0⦌))
          (nativeWeightedPoint I s))) =
      (s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))
```

#### BousfieldKanUniverseCoefficientPoint（65行）

```lean
theorem bousfieldKanUniverseCone_identityVertex (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((bousfieldKanUniverseCone.{u,v} I s).app (AsSmall.up.obj i)).app (Opposite.op ⦋0⦌)
      (nerveVertex (Over.mk (𝟙 (((AsSmall.up : I ⥤ AsSmall.{v} I).obj i))))) =
        ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))

theorem bousfieldKanUniverseExInfinityCone_identityVertex
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((bousfieldKanUniverseCone.{u,v} I s ≫ bousfieldKanExInfinityCoefficientUnit _ _).app
      (AsSmall.up.obj i)).app (Opposite.op ⦋0⦌)
        (nerveVertex (Over.mk (𝟙 (((AsSmall.up : I ⥤ AsSmall.{v} I).obj i))))) =
      (exInfinityUnit.app ((SSet.uliftFunctor.{max u v,u}).obj (H.obj i))).app (Opposite.op ⦋0⦌)
        (ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))))

theorem bousfieldKanUniverseExInfinityPoint_fiber
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    let H' := (weightedDiagramUniverse.{u,v} I).obj H ⋙ exInfinity
    let s' := bousfieldKanUniverseCone.{u,v} I s ≫ bousfieldKanExInfinityCoefficientUnit _ _
    ((weightedNerveFiberIso H' (AsSmall.up.obj i)).inv.app (Opposite.op ⦋0⦌))
      ((simplicialSectionsFiberEvaluation (weightedNerveProjection H')
        (nerveVertex (AsSmall.up.obj i))).app (Opposite.op ⦋0⦌)
          (((bousfieldKanSectionsIso H').hom.app (Opposite.op ⦋0⦌))
            (nativeWeightedPoint (AsSmall.{v} I) s'))) =
      (exInfinityUnit.app ((SSet.uliftFunctor.{max u v,u}).obj (H.obj i))).app (Opposite.op ⦋0⦌)
        (ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))))
```

## 181. 元のfiberへ戻す全切断比較 R03c の追加（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 16（うち追加 4）。

IS-W2 §19の、同じまとまり・中間定理一つの見込み1,500行以下の枠で、R02〜R03の中間項目 **R03c** を追加する。§179の三角形は共通の復元のfiberを標的とする。元のnative錐のfiberで同じ脚を比較するため、この共通の復元をfiberの同値で消し、元の切断比較の各次数での作用を保つ。

```lean
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial

-- 元の射影の切断・fiberの既存Kan性を局所インスタンスにする。
theorem exists_classifiedFibrationFiberComparison
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (η : FunctorIso (leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram q)) (b : B _⦋0⦌) :
    ∃ e : QCatEquivalence (vertexFiber p b) (vertexFiber q b),
      Nonempty (FunctorIso
        ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
          simplicialSectionsFiberEvaluation q b)
        (simplicialSectionsFiberEvaluation p b ≫ e.hom))
```

見込み140〜280行：元の二本の復元のfiber同値の合成40〜80行、§179の全三角形を同じ同値の逆で後合成して余単位で消す40〜80行、BEへの特殊化と同じBK指定点の像の照合60〜120行。既存 `CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence` を使う。fibersが同値であるだけで終わらず、元の全切断比較との同じ四角形を型に含める。新しいBE模型・重み・係数・strictificationや⑤aの欄の型に触れない。

この項目を足してそのまま証明へ進む。全図式射の錐族や極限性を完成とは数えない。見込みが1,500行を超える場合・別のまとまりが必要な場合・外枠15,000行に届く場合は、検証済みを保存して報告する。

## 182. R03c完了：元のnative錐のfiberと元のraw BK係数の指定点（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。済みはR01・R03a・R03a.1・R03b・R03c。R02/R03の標準脚・全錐族・極限性は未完了。

§181の型のまま `exists_classifiedFibrationFiberComparison` を証明した。同じ分類変換を使用する共通の復元への二本の実写像を各fiberで同値にし、一方の逆で戻した。元の切断比較の全三角形も同じ逆で後合成し、余単位で消して、元の二つのfiberの同値と**元の全切断比較の同じ四角形**を得た。fiberが同値であるだけで終わらせていない。

BEでは、元のweighted nerveのfiber同型を合成して、元のBK係数から同じ元の図式・頂点のnative錐のfiberへの `strictBETotNativeFiberEquivalence` を得た。全切断比較との四角形、同じ普遍BK指定点の像も照合した。さらに§180の係数移送の評価則を使い、このnative錐のfiberの指定点と、元のraw BK係数の恒等射での値をULift・Ex∞単位で送った指定像との `VertexIso` を得た。

最後の点の比較は `VertexIso` であり、元の二つの零単体が文字どおり等しいと主張していない。一方、§180の係数回収と宇宙変更・単位の値の計算は厳密な等式である。両者を区別する。これを元の標準脚の最終同定や全図式射の錐族、同じ錐の極限性の完了と数えない。

### 182.1 検証と実測

一般形とBEへの適用を合わせて二本224行。§181の140〜280行の見込みの範囲内（下端より84行増、上端より56行減）。個別検査の後、248で二本の対象ビルド10,651 jobs・終了0、小監査89本651宣言・標準三公理のみ。実ハンドル39993の終了0を確認し、鍵は返却済み。sorry・独自公理0、計算上限の変更なし。累計89本・5,770行、外枠15,000行。各200行以下。

追加の一覧項目は§181のR03cだけで、ここに含まれるfiber同値の合成・余単位の四角形・同じBK点での評価・raw係数への正規化はその証明分割または既存構成の法則。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。

### 182.2 次の接続の注意

元のnative錐の脚を、元のraw frame Homと指定BK重み比較の評価へ戻す接続が具体化した。次は既存のframeから正本Homへの単位の正規化と、元の指定weighted普遍錐の評価に合わせる。元の一点重みへの比較とBK比較の可換式だけから、全ての零次の選択が文字どおり同じだとは推論しない。

極限判定のa・haは、既存 `Project.HomotopyDiagramComparison.coherentConeSourceFamily` と `coherentConeSourceFamily_evaluation` が、同じ錐・同じ頂点について候補を与える。CAlgの既存のcoherent nerve表示との照合はこれからであり、ここでは特殊化済みとは数えない。残るheは、この同じ族の制限写像と元のweighted Hom比較の同値性を結ぶこと。固定した始域ごとの全標的のHom比較を、始域にも自然な全比較と自動的に読み替えない。必要な始域の作用・元のframeの単位との両立を既存APIから明示して進める。

### 182.3 今回の型

#### ClassifiedFibrationFiberComparison（80行）

```lean
def classifiedFibrationFiberEquivalence (b : B _⦋0⦌) :
    QCatEquivalence (vertexFiber p b) (vertexFiber q b)

def classifiedFibrationFiberEquivalence_sectionsIso (b : B _⦋0⦌) :
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsFiberEvaluation q b)
      (simplicialSectionsFiberEvaluation p b ≫ (classifiedFibrationFiberEquivalence p q η b).hom)

theorem exists_classifiedFibrationFiberComparison (b : B _⦋0⦌) :
    ∃ e : QCatEquivalence (vertexFiber p b) (vertexFiber q b),
      Nonempty (FunctorIso
        ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
          simplicialSectionsFiberEvaluation q b)
        (simplicialSectionsFiberEvaluation p b ≫ e.hom))
```

#### StrictDiagramTotNativeFiberComparison（144行）

```lean
def strictBETotNativeFiberEquivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    QCatEquivalence ((strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i)
      (vertexFiber (coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) (nerveVertex i))

def strictBETotNativeFiberEquivalence_sectionsIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    FunctorIso
      ((strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv ≫
            simplicialSectionsFiberEvaluation _ (nerveVertex i))
      ((bousfieldKanSectionsIso H).hom ≫
        simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i) ≫
          (weightedNerveFiberIso H i).inv ≫ (strictBETotNativeFiberEquivalence A K F Y i).hom)

def strictBETotNativeFiberEquivalence_universalPointIso
    (F : K ⥤ (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    VertexIso
      ((simplicialSectionsFiberEvaluation _ (nerveVertex i)).app (Opposite.op ⦋0⦌)
        (((coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
            (nerveVertex ((framedLimitFunctor A K).obj F)))).inv.app (Opposite.op ⦋0⦌))
              (strictBETotUniverseNativeConePoint A K F)))
      (((strictBETotNativeFiberEquivalence A K F ((framedLimitFunctor A K).obj F) i).hom.app
        (Opposite.op ⦋0⦌)) (((strictBETotUniversalBKExInfinityCone A K F).app i).app
          (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))))

def strictBETotNativeFiberEquivalence_rawPointIso
    (F : K ⥤ (operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    let Y := (framedLimitFunctor A K).obj F
    let j : AsSmall.{u+1} Kᵒᵖᵒᵖ := AsSmall.up.obj i
    VertexIso
      ((simplicialSectionsFiberEvaluation _ (nerveVertex j)).app (Opposite.op ⦋0⦌)
        (((coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv.app
            (Opposite.op ⦋0⦌)) (strictBETotUniverseNativeConePoint A K F)))
      (((strictBETotNativeFiberEquivalence A K F Y j).hom.app (Opposite.op ⦋0⦌))
        ((exInfinityUnit.app ((SSet.uliftFunctor.{u+1,u}).obj
          ((strictBETotProbeRightHomDiagram A K F Y).obj i))).app (Opposite.op ⦋0⦌)
            (ULift.up (((strictBETotUniversalBKRightHomCone A K F).app i).app
              (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))))))
```


## 183. 元の同じnative錐の始域族aと頂点評価ha（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。R03のhe・極限性、R02の全錐族は未完了。

既存のCAlgの頂点全単射で、元の同じnative錐の頂点を表示する対象を指定し、その頂点の厳密な等式を証明した。この対象と同じ元の錐に、既存 `coherentConeSourceFamily` と `coherentConeSourceFamily_evaluation` を代入して、全始域Homの族aと標準coslice fiber比較に一致する頂点評価haを接続した。

`strictBETotNativeConeAt_isLimit_of_sourceRestriction` は**残りのheを仮定した既存判定の特殊化**であり、R03の無条件の極限性を証明したとは数えない。同じ族の制限写像と、元のweighted Homの同値を比較してheを閉じる仕事が残る。既存のCAlgSimplicialCategory・cAlgVertexEquivだけを使い、新しいCAlg模型や代表の選択を作っていない。

検証：249で新規一本の対象ビルド10,662 jobs・終了0、小監査90本659宣言、標準三公理のみ。実ハンドル45305の終了0を確認、鍵は返却済み。sorry・独自公理0、計算上限の変更なし。

新規一本75行、累計90本・5,845行。既存の始域族と判定の特殊化・証明分割で、一覧への追加は0。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

文書の補正：型の抽出で `let H := ...` の代入を宣言本体の始まりと誤認し、一部の再掲が `let H` の途中で切れていた。§177.3・§178.1・§179.2・§180.1・§182.3を現行のソースの完全な型から再掲し直した。これらの再掲のファイル行数は現行版の値で、各節本文の当時の検証・実測とは区別する。数学的な型やこれまでの監査結果は変更していない。

次は元のright frame Homの始域作用を全関手として明示し、元のprobeつき係数の同型の始域自然性を照合する。固定始域ごとの全標的比較を、始域にも自然と仮定してheを閉じない。

### 183.1 今回の既存構成の特殊化の型

```lean
def strictBETotNativeConeSourceObject
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) : CAlgSimplicialCategory A

theorem strictBETotNativeConeSourceObject_vertex
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (strictBETotNativeConeAt A F).vertex =
      coherentNerveVertex (strictBETotNativeConeSourceObject A F)

def strictBETotNativeConeSourceFamily
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) (X : CAlgSimplicialCategory A) :
    (SSet.uliftFunctor.{u+1,u+1}).obj
      (SimplicialCategory.sHom X (strictBETotNativeConeSourceObject A F)).op ⟶
        coherentConeSectionSpace (strictBETotNativeConeAt A F).val (coherentNerveVertex X)

theorem strictBETotNativeConeSourceFamily_evaluation
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) (X : CAlgSimplicialCategory A) :
    strictBETotNativeConeSourceFamily A F X ≫
      coherentConeApexEvaluation (strictBETotNativeConeAt A F) (strictBETotNativeConeSourceObject A F)
        (strictBETotNativeConeSourceObject_vertex A F) X =
      coherentCosliceFiberComparison X (strictBETotNativeConeSourceObject A F)

theorem strictBETotNativeConeAt_isLimit_of_sourceRestriction
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra)
    (he : ∀ X : CAlgSimplicialCategory A,
      IsSimplicialHomotopyEquivalence (strictBETotNativeConeSourceFamily A F X ≫
        coneSectionRestriction (strictBETotNativeConeAt A F) (coherentNerveVertex X))) :
    IsLimitCone (strictBETotNativeConeAt A F)
```

## 184. 元のright frame Homの全始域作用と普遍BK錐の射での正規化（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。R03のhe・無条件の極限性、R02の全錐族は未完了。

既存のcoyonedaを同じright frame図式へwhiskeringすることで、`rightFrameHomBifunctor` を二変数の全関手としてまとめた。固定始域での値は元のrightFrameHomそのもの。始域の作用は既存 `MixedFrame.rightSourceMap` の前合成そのものであり、元のrightFrameHomUnitもこの始域の作用について厳密に自然である。

BEでは既存probe関手を前合成し、元のraw Hom係数とweighted Hom係数を全始域で束ねた。元の `strictBETotProbeCoefficientsIso` は全始域の自然同型としても両立する。元のprobe・frame・係数・射を変更していない。

さらに元の射 f : Y → Tot(F) による同じ普遍BK錐の始域作用を、元のweighted Hom同値の同じ射 `framedLimitProbeComparison A Y ≫ f` の像へ正規化した。`strictBETotBKProbeArrowCone_comparison` は元の重み・添字図式間の**自然変換の厳密な等式**。係数同型の始域自然性、既存weightedCotensorHomEquiv_precomp、既存probe比較自然変換の自然性を合成した。新しい数学の項目ではなく、既存構成の係数移送・単位・前合成の法則である。

### 184.1 検証と実測

250：再利用する既存MixedFrameSource一本の依存ビルド1,723 jobs・終了0。251：新規二本と既存FramedLimitComparisonの依存を対象ビルドして5,113 jobs・終了0、小監査92本673宣言。252：普遍BK錐の始域正規化一本を対象ビルドして5,114 jobs・終了0、小監査93本678宣言。全て標準三公理のみ、実ハンドル43038・47206・83040の終了0を確認し、鍵は返却済み。sorry・独自公理0、計算上限の変更なし。

新規三本178行、累計93本・6,023行（外枠15,000）。各200行以下。既存構成の全係数の表示と自然性・単位則なので、追加の一覧項目は0。既存FramedLimit*はimportで使うだけで変更していない。CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainも変更していない。

個別検査では未ビルドの既存API依存を250・251でビルドし、probe自然変換の成分を一般の対象で先に照合した。計算対象の不透明なendを展開して計算上限を上げる方法は取っていない。

### 184.2 まだ必要なcoherentな接続

ここで示したのは元の通常圏の**全始域関手と厳密な自然変換の法則**であり、固定始域ごとの全Hom∞比較を始域にも自然とした結果ではない。nativeな標準族aの制限と元のweighted Hom同値を結ぶheには、同じ単位で正規化された両変数の比較か、それと同等な全パラメーターの評価則が必要である。

次の紙の確認では、今回の二変数raw Hom関手を同じAsSmall・ULift・Ex∞でKan図式にした全coherent入力と、同じCAlg源の二変数 `twistedArrowHomInfinity` の入力を同じ底で揃える。固定始域の制限が既存 `strictBETotProbeFrameHomInfinityIso` とどう一致するかも型に含めて検討する。点ごとのHom同値やπ₀の自然性だけで、全joint比較やheを閉じたと主張しない。新しい中間定理が要ると分かった段階で、§19に従い実際の型と1,500行以内かどうかの見込みを記録する。

### 184.3 今回の既存構成の法則の型

#### RightFrameHomBifunctor（56行）

```lean
def rightFrameHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}

theorem rightFrameHomBifunctor_obj (X : C) :
    (rightFrameHomBifunctor r).obj (Opposite.op X) = rightFrameHom r X

theorem rightFrameHomBifunctor_map {X Y : C} (f : X ⟶ Y) :
    (rightFrameHomBifunctor r).map f.op =
      Functor.whiskerLeft (rightFrameDiagram r) (MixedFrame.rightSourceMap f)

def ordinaryHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}

theorem rightFrameHomUnit_source {X Y : C} (f : X ⟶ Y) :
    ordinaryHomBifunctor.map f.op ≫ rightFrameHomUnit r X =
      rightFrameHomUnit r Y ≫ (rightFrameHomBifunctor r).map f.op
```

#### StrictDiagramTotProbeSourceFunctor（60行）

```lean
def strictBETotProbeRightHomBifunctor :
    (operad A).Algebraᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u}

def strictBETotProbeRightHomSourceFunctor (F : K ⥤ (operad A).Algebra) :
    (operad A).Algebraᵒᵖ ⥤ Kᵒᵖᵒᵖ ⥤ SSet.{u}

theorem strictBETotProbeRightHomSourceFunctor_obj (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    (strictBETotProbeRightHomSourceFunctor A K F).obj (Opposite.op Y) =
      strictBETotProbeRightHomDiagram A K F Y

def strictBETotProbeCoefficientsSourceFunctor (F : K ⥤ (operad A).Algebra) :
    (operad A).Algebraᵒᵖ ⥤ Kᵒᵖᵒᵖ ⥤ SSet.{u}

def strictBETotProbeCoefficientsSourceIso (F : K ⥤ (operad A).Algebra) :
    strictBETotProbeRightHomSourceFunctor A K F ≅ strictBETotProbeCoefficientsSourceFunctor A K F
```

#### StrictDiagramTotUniversalSourceNaturality（62行）

```lean
def strictBETotBKProbeArrowCone (F : K ⥤ (operad A).Algebra)
    {Y : (operad A).Algebra} (f : Y ⟶ (framedLimitFunctor A K).obj F) :
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight
      Kᵒᵖᵒᵖ ⟶ strictBETotProbeRightHomDiagram A K F Y

theorem strictBETotBKProbeArrowCone_comparison (F : K ⥤ (operad A).Algebra)
    {Y : (operad A).Algebra} (f : Y ⟶ (framedLimitFunctor A K).obj F) :
    strictBETotBKProbeArrowCone A K F f ≫ (strictBETotProbeCoefficientsIso A K F Y).hom =
      HomotopyWeight.bkFramedWeightComparison K ≫
        weightedCotensorHomEquiv A K F (HomotopyWeight.weight K) (framedLimitProbe A Y)
          (framedLimitProbeComparison A Y ≫ f)
```

## 185. 両変数の入力と固定始域の制限の厳密な照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。R02の全錐族・標準脚の最終正規化、R03の無条件の極限性は未完了。

元のprobeつきright frame Homの二変数関手をuncurryし、同じAsSmall・ULift・Ex∞による全Kan図式とcoherentな入力を作った。正本側は同じCAlg源の両射影をtwistedArrowHomInfinityの底へ送る。始域の反変性には、同じnerveOppositeIsoの逆を使う。

両入力の始域を固定すると、それぞれ既存の第零frame比較の入力と同じ共変Hom∞に**全単体で厳密に等しい**。反転同型の逆と定値写像の可換則を一般の小圏で証明し、これを使って正本側を照合した。これは既存構成の係数移送・前合成則で、一覧への新規定理の追加は0。二入力を結ぶ全FunctorIsoはまだ証明していない。固定始域ごとの比較をそのまま両変数の比較と見なさない。

### 185.1 検証と実測

253：JointHomInput一本の対象ビルド10,624 jobs・終了0、小監査94本693宣言。254：NerveOppositeConstantとJointHomRestriction二本の対象ビルド10,626 jobs・終了0、小監査96本698宣言。全て標準三公理のみ。実ハンドル91462・76154の終了0を確認し、鍵は返却済み。sorry・独自公理0、計算上限の変更なし。

今回三本の行数は下の型一覧に記載。累計96本・6,170行（外枠15,000）。登録予定一覧を更新した。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 185.2 残る接続の位置

同じ普遍単位で正規化されたjoint比較、または同等の全パラメーター評価則がheへの残る接続である。今回の制限等式は、その比較を構成するときに既存の固定始域比較との両立を明記するための型の照合である。既存の豊穣Yoneda比較とframe比較のどこで始域のcoherenceを作るかを先に確認する。

### 185.3 既存構成の法則と入力の型

#### StrictDiagramTotJointHomInput（119行）

```lean
abbrev strictBETotJointHomIndex

def strictBETotJointRawHom :
    ((operad A).Algebraᵒᵖ × (operad A).Algebra) ⥤ SSet.{u}

def strictBETotJointRawHomKan : strictBETotJointHomIndex A ⥤ KanObject.{u+1}

def strictBETotJointRawHomCoherent :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1}

def strictBETotJointHomSourceIndex :
    strictBETotJointHomIndex A ⥤ (AsSmall.{u+1} (operad A).Algebra)ᵒᵖ

def strictBETotJointHomTargetIndex :
    strictBETotJointHomIndex A ⥤ AsSmall.{u+1} (operad A).Algebra

def strictBETotJointNativeHomInput :
    nerve (strictBETotJointHomIndex A) ⟶ (CAlg_R A).op ⊗ CAlg_R A

def strictBETotJointNativeHomCoherent :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1}

def strictBETotJointHomFixSource (X : (operad A).Algebra) :
    AsSmall.{u+1} (operad A).Algebra ⥤ strictBETotJointHomIndex A

theorem strictBETotJointRawHom_fixSource (X : (operad A).Algebra) :
    CategoryTheory.Prod.sectR (Opposite.op X) (operad A).Algebra ⋙ strictBETotJointRawHom A =
      rightFrameHom (rightFrameFamily A) (framedLimitProbe A X)

theorem strictBETotJointRawHomKan_fixSource (X : (operad A).Algebra) :
    strictBETotJointHomFixSource A X ⋙ strictBETotJointRawHomKan A =
      FrameHom.rightFrameHammockKanDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C

theorem strictBETotJointRawHomCoherent_fixSource (X : (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotJointHomFixSource A X)) ≫
      strictBETotJointRawHomCoherent A =
    FrameHom.rightFrameHammockCoherentDiagram
      ((SimplicialLocalization.modelSourceFrameFamily (C

```

#### NerveOppositeConstant（52行）

```lean
theorem nerveOppositeIso_inv_constant (c : C) (n : ℕ) :
    ((nerveOppositeIso (C

theorem nerveOppositeIso_inv_const {K : SSet.{u}} (c : C) :
    SSet.const (X

```

#### StrictDiagramTotJointHomRestriction（76行）

```lean
theorem strictBETotJointNativeHomInput_fixSource (X : (operad A).Algebra) :
    nerveMap (strictBETotJointHomFixSource A X) ≫ strictBETotJointNativeHomInput A =
      lift (SSet.const (SSet.opObjEquiv.symm
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))))
          (strictBETotModelSource A)

theorem strictBETotJointNativeHomCoherent_fixSource (X : (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotJointHomFixSource A X)) ≫
      strictBETotJointNativeHomCoherent A =
    (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A) ≫
      homInfinityCovariant ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))

```

## 186. 最初の三辺の両変数の全関手同型（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。R02・R03の未完了部分は§185と同じ。

元の関手的source frame・right frameの混合Homを始域にも反変な全関手として束ねた。左右の混合比較の始域自然性は、同じaugmentationの自然性と圏の結合則そのものである。BEでは同じprobe関手・標的の次数零置換・uncurry・ULiftを使い、六辺のうち最初の三辺を全両変数の自然変換にした。

各辺の弱同値性には既存のrightFrameHammockFamilyEdge_weakを同じ入力で代入した。全自然変換自身をKan化して全関手圏で反転し、`strictBETotJointFirstSpanComparison` を得た。元の両変数raw Homとsource frame Homの**全関手同型**であり、点ごとの同値の選択ではない。ただし終点はsource frame Homであり、正本Hom∞との全同型はまだ含まない。

### 186.1 検証・実測と累計の訂正

255：二本の対象ビルド10,626 jobs・終了0、小監査98本739宣言・標準三公理のみ。実ハンドル13255の終了0を確認し、鍵を返却した。sorry・独自公理0、計算上限変更なし。

今回二本242行（83＋159）、manifestの全ファイルを再集計した累計98本・6,412行（外枠15,000）。§185の三本は247行（119＋52＋76）、その時点の再集計6,170行は正しい。§184の累計6,023行には100行の過大計上があり、正しくは5,923行だった。以後はmanifestから再集計した値を用いる。過去の報告の検証結果と宣言数は変わらない。

今回の二本は既存比較の自然性・係数移送・合成の法則で、一覧の新規定理の追加には数えない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 186.2 既存構成の法則の型

#### RightMixedBifunctor（83行）

```lean
def rightMixedBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}

theorem rightMixedBifunctor_obj (X : C) :
    (rightMixedBifunctor q r).obj (Opposite.op X) = rightMixedFamily (q.atObject X) r

def sourceFrameHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}

def rightMixedLeftBifunctorMap : sourceFrameHomBifunctor q ⟶ rightMixedBifunctor q r

def rightMixedRightBifunctorMap : rightFrameHomBifunctor r ⟶ rightMixedBifunctor q r

theorem rightMixedLeftBifunctorMap_app (X : C) :
    (rightMixedLeftBifunctorMap q r).app (Opposite.op X) =
      rightMixedLeft (q.atObject X) r

theorem rightMixedRightBifunctorMap_app (X : C) :
    (rightMixedRightBifunctorMap q r).app (Opposite.op X) =
      rightMixedRight (q.atObject X) r
```

#### StrictDiagramTotJointFirstSpan（159行）

```lean
def strictBETotJointFirstSpanBifunctor :
    Fin 4 → ((operad A).Algebraᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u})

def strictBETotJointFirstSpanUnit :
    strictBETotJointFirstSpanBifunctor A 0 ⟶ strictBETotJointFirstSpanBifunctor A 1

def strictBETotJointFirstSpanRight :
    strictBETotJointFirstSpanBifunctor A 1 ⟶ strictBETotJointFirstSpanBifunctor A 2

def strictBETotJointFirstSpanLeft :
    strictBETotJointFirstSpanBifunctor A 3 ⟶ strictBETotJointFirstSpanBifunctor A 2

def strictBETotJointFirstSpanDiagram (i : Fin 4) :
    ((operad A).Algebraᵒᵖ × (operad A).Algebra) ⥤ SSet.{u+1}

def strictBETotJointFirstSpanEdgeSource : Fin 3 → Fin 4

def strictBETotJointFirstSpanEdgeTarget : Fin 3 → Fin 4

def strictBETotJointFirstSpanEdge (i : Fin 3) :
    strictBETotJointFirstSpanDiagram A (strictBETotJointFirstSpanEdgeSource i) ⟶
      strictBETotJointFirstSpanDiagram A (strictBETotJointFirstSpanEdgeTarget i)

theorem strictBETotJointFirstSpanEdge_weak (i : Fin 3)
    (P : (operad A).Algebraᵒᵖ × (operad A).Algebra) :
    IsWeakHomotopyEquivalence ((strictBETotJointFirstSpanEdge A i).app P)

def strictBETotJointFirstSpanKanDiagram (i : Fin 4) :
    strictBETotJointHomIndex A ⥤ KanObject.{u+1}

def strictBETotJointFirstSpanKanEdge (i : Fin 3) :
    strictBETotJointFirstSpanKanDiagram A (strictBETotJointFirstSpanEdgeSource i) ⋙ kanObjectForget ⟶
      strictBETotJointFirstSpanKanDiagram A (strictBETotJointFirstSpanEdgeTarget i) ⋙ kanObjectForget

def strictBETotJointFirstSpanCoherent (i : Fin 4) :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1}

def strictBETotJointFirstSpanEdgeIso (i : Fin 3) :
    FunctorIso (strictBETotJointFirstSpanCoherent A (strictBETotJointFirstSpanEdgeSource i))
      (strictBETotJointFirstSpanCoherent A (strictBETotJointFirstSpanEdgeTarget i))

theorem strictBETotJointFirstSpanCoherent_zero :
    strictBETotJointFirstSpanCoherent A 0 = strictBETotJointRawHomCoherent A

def strictBETotJointFirstSpanComparison :
    FunctorIso (strictBETotJointRawHomCoherent A) (strictBETotJointFirstSpanCoherent A 3)
```

## 187. R03d：同じ固定始域比較で正規化された両変数比較の追加（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03dは未証明。

IS-W2 §19の承認済みの中間定理の枠により、R01〜R03のまとまりにR03dを追加する。型は次のとおり。両変数の同じ入力の全FunctorIsoを要求し、始域を固定した制限は既存の同じ `strictBETotProbeFrameHomInfinityIso` と一致させる。HEqは§185の二つの制限等式による型の移送を記すためのもので、点ごとの同値や可換性への弱化ではない。

```lean
theorem exists_strictBETotJointHomComparison (A : Type u) [CommRing A] :
  ∃ e : FunctorIso (strictBETotJointRawHomCoherent A) (strictBETotJointNativeHomCoherent A),
    ∀ X : (operad A).Algebra,
      HEq (e.precomp ((SSet.uliftFunctor.{u+2,u+1}).map
        (nerveMap (strictBETotJointHomFixSource A X))))
        (strictBETotProbeFrameHomInfinityIso A X)
```

この主張の型を一時ファイル `/private/tmp/CheckStrictBEJointComparisonType.lean` のPropとして検査し、実ハンドル58644の終了0を確認した。定理の証明や本体への登録はまだしていない。

残りの見込みは950〜1,450行：全パラメーターのaugmentationとroofを同じ底上に置く450〜700行、元の豊穣Yoneda・指定局所化比較へ運ぶ300〜450行、同じ固定始域比較との正規化200〜300行。今回の既存法則242行はこの残りに含めない。全体の外枠は15,000行のまま。

短い経路を先に試す。source frameのaugmentationを全始域と全次数の自然変換として同じ局所化へ送り、弱辺を全関手圏で反転する。その同じ逆と元の射から、両端を変数とする一つの表示された比較を作り、分類に送る。固定始域では既存のframe・Yoneda・同じ局所化二胞体に戻ることを照合する。`FrameLeftRoofPrecompose` の各射の局所化内の等式だけを、全高次の自然性の証明として使わない。

まとまり外の定理、1,500行を超える見込み、⑤aの欄の型への変更が必要と分かった場合は、検証済みをコミットして報告する。今回は同じR03のまとまりで上端1,450行なので、承認を待たずR03dの証明へ進む。

## 188. 全始域・全次数の同じaugmentationの一つの逆（R03dの前半、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03dは未完了。

同じ関手的source frameのaugmentationを、全始域と全source次数の積添字でuncurryし、元のprobe比較自然変換と合成した。同じCAlgの指定モデル源へ送った全円柱について、全ての成分の辺の可逆性から円柱自身を全関手圏で反転した。逆を対象・次数ごとに選んでいない。

共通部分はKerodon 4.8の `NerveTransformationInversion` に置いた。既存のnerve円柱と既存の指定辺の点ごとの反転判定を合成した、通常の自然変換の係数移送・反転の法則である。BEの各成分の弱同値性は、元の解消のaugmentationと元のprobe比較の合成則から従う。局所化の反転辺の集合と指定された辺の型は、同じ一単体の一致で合わせた。

### 188.1 検証と実測

256：新規二本の対象ビルド10,628 jobs・終了0、小監査100本754宣言・標準三公理のみ。実ハンドル21505の終了0を確認し、鍵を返却した。sorry・独自公理0、計算上限変更なし。今回143行、累計100本・6,555行（外枠15,000）。R03dの残るjoint表示と分類・固定始域との正規化はまだ証明していない。

この二本はR03dの既存の自然変換・反転則であり、新しい一覧項目は増やさない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 188.2 型

#### NerveTransformationInversion（52行）

```lean
def nerveTransformationPostHomotopy : SSet.Homotopy (nerveMap F ≫ L) (nerveMap G ≫ L)

def nerveTransformationPostIso
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    FunctorIso (nerveMap F ≫ L) (nerveMap G ≫ L)

theorem nerveTransformationPostIso_hom
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    (nerveTransformationPostIso η L hη).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (nerveTransformationPostHomotopy η L))

```

#### StrictDiagramTotJointAugmentation（91行）

```lean
abbrev strictBETotJointSourceFrameIndex

def strictBETotJointSourceFrameEvaluation :
    strictBETotJointSourceFrameIndex A ⥤ AsSmall.{u+1} (operad A).Algebra

def strictBETotJointSourceFrameConstant :
    strictBETotJointSourceFrameIndex A ⥤ AsSmall.{u+1} (operad A).Algebra

def strictBETotJointSourceFrameAugmentation :
    strictBETotJointSourceFrameEvaluation A ⟶ strictBETotJointSourceFrameConstant A

theorem strictBETotJointSourceFrameAugmentation_weak (P : strictBETotJointSourceFrameIndex A) :
    weakEquivalences (operad A).Algebra
      (AsSmall.down.map ((strictBETotJointSourceFrameAugmentation A).app P))

theorem strictBETotJointSourceFrameAugmentation_inverted (P : strictBETotJointSourceFrameIndex A) :
    IsInvertibleEdge ((nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app P)).map
      (strictBETotModelSource A)).toTruncated

def strictBETotJointSourceFrameAugmentationIso :
    FunctorIso (nerveMap (strictBETotJointSourceFrameEvaluation A) ≫ strictBETotModelSource A)
      (nerveMap (strictBETotJointSourceFrameConstant A) ≫ strictBETotModelSource A)

```

## 189. 元の全source frame射の要素圏と両端の四角形（R03d、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03dは未完了。

既存のresolutionHomを二度uncurryし、全始域・全標的・全単体次数のHom係数の要素圏を取った。元の各射の始域を反変な関手、標的を共変な関手として記録した。要素圏の全射について、同じ実際の射が与える可換四角形を証明した。始域のframeの自然性と元の要素圏のmap_valの合成であり、新しい比較射やframeは選んでいない。

257：新規一本の対象ビルド1,126 jobs・終了0、小監査101本761宣言・標準三公理のみ。実ハンドル35588の終了0を確認し、鍵を返却済み。sorry・独自公理0、計算上限変更なし。今回65行、累計101本・6,620行（外枠15,000）。R03dに関係する§188以降の検証済みは208行。

この要素圏は元の係数の表示と自然性の法則なので、新しい一覧項目には数えない。R03dの残りは、同じ全要素圏と同じaugmentationの大域的な逆から正本Hom∞への比較を作り、分類と固定始域の既存比較との一致を示すこと。始域が反変なので、今回の四角形を通常の二つの共変関手の自然変換として扱わない。点ごとのroofのホモトピーだけで全高次自然性を済ませることもしない。

次は同じ両端を持つ全要素の射をtwisted arrowへ送る全写像を組み立てる。厳密なtwisted arrowの同型全体を新たに作る必要があるとはまだ判断していない。まず既存のedgewise重みの標準単体表示と元の可換四角形で必要な写像を作る短い経路を試す。R03dの型と§187の見込みの範囲で進め、追加の中間定理が必要な場合は§19の枠に従って型と見込みを記録する。

既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 189.1 既存構成の表示・自然性の型（65行）

```lean
def sourceFrameArrowCoefficients :
    ((Cᵒᵖ × C) × SimplexCategoryᵒᵖ) ⥤ Type v

abbrev SourceFrameArrowElements

def sourceFrameArrowParameters : SourceFrameArrowElements Q R ⥤
    ((Cᵒᵖ × C) × SimplexCategoryᵒᵖ)

def sourceFrameArrowDomain : SourceFrameArrowElements Q R ⥤ Cᵒᵖ

def sourceFrameArrowCodomain : SourceFrameArrowElements Q R ⥤ C

def sourceFrameArrowValue (s : SourceFrameArrowElements Q R) :
    ((sourceFrameArrowDomain Q R).obj s).unop ⟶ (sourceFrameArrowCodomain Q R).obj s

theorem sourceFrameArrowValue_naturality {s t : SourceFrameArrowElements Q R} (f : s ⟶ t) :
    ((sourceFrameArrowDomain Q R).map f).unop ≫ sourceFrameArrowValue Q R s ≫
      (sourceFrameArrowCodomain Q R).map f = sourceFrameArrowValue Q R t

```

## 190. 指定された射列の長い単体と交差射の全自然性（R03d、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03dは未完了。

全要素圏の反変・共変の両端と元の射から、同じ「始域の逆順・零番の射・標的の順序」の長い通常nerveの単体を作った。恒等射と合成を元の両端の関手と圏の合成則で確認した。左右の型の移送はeqToHomによる同じ共役として明示し、元の射を保持する異種等式も証明した。新しい充填・逆・頂点ごとの同値は選んでいない。

元の可換四角形を仮定すると、対角の交差射は元の射であり、基点を零番以外へ移しても同じ交差射になる。この等式から交差射の任意の順序射による再添字付けの厳密な自然性を得た。面・退化の両方を含む。両半分の対象の座標も元の同じedgewiseの座標で照合した。

258：三本の対象ビルド1,556 jobs・終了0、小監査104本808宣言・標準三公理のみ。実ハンドル36320の終了0を確認し、鍵返却済み。sorry・独自公理0、計算上限変更なし。今回294行（151＋50＋93）、累計104本・6,914行（外枠15,000）。R03dの§188以降の検証済みは502行。既存構成の合成・自然性・係数移送則なので一覧項目の追加は0。

射列全体を実際のedgewise重みの再添字付けと照合する `TwistedPairingReindex` は個別検査中で、今回のコミットと検証済みの数には含めない。R03dの全FunctorIso、固定始域の既存比較との一致、he、R03の無条件の極限性はまだ未完了。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 190.1 共通の入力と既存構成の法則の型

以下でI・Cは同じ宇宙の小圏、A : I ⥤ Cᵒᵖ、B : I ⥤ C、h : ∀ i, (A.obj i).unop ⟶ B.obj i。hhは元の可換四角形 `∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j`。σ : Fin (n+1) ⥤ I。CrossNaturalityの三つの補題はhhを明示的な入力に持つ。

#### TwistedPairingSimplex（151行）

```lean
def twistedPairingLeftIndex {n : ℕ} (i : Fin (n+n+1+1)) (hi : i.val < n+1) : Fin (n+1)

def twistedPairingRightIndex {n : ℕ} (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) : Fin (n+1)

def twistedPairingCross (a b : Fin (n+1)) :
    (A.obj (σ.obj a)).unop ⟶ B.obj (σ.obj b)

theorem twistedPairingCross_left (a b c : Fin (n+1)) (hab : b ≤ a) :
    (A.map (σ.map (homOfLE hab))).unop ≫ twistedPairingCross A B h σ b c =
      twistedPairingCross A B h σ a c

theorem twistedPairingCross_right (a b c : Fin (n+1)) (hbc : b ≤ c) :
    twistedPairingCross A B h σ a b ≫ B.map (σ.map (homOfLE hbc)) =
      twistedPairingCross A B h σ a c

def twistedPairingSimplexObj (i : Fin (n+n+1+1)) : C

theorem twistedPairingSimplexObj_left (i : Fin (n+n+1+1)) (hi : i.val < n+1) :
    twistedPairingSimplexObj A B σ i = (A.obj (σ.obj (twistedPairingLeftIndex i hi))).unop

theorem twistedPairingSimplexObj_right (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) :
    twistedPairingSimplexObj A B σ i = B.obj (σ.obj (twistedPairingRightIndex i hi))

theorem twistedPairingTransport_comp {X Y Z U V W : C} (p : X = U) (q : Y = V) (r : Z = W)
    {f : U ⟶ V} {g : V ⟶ W} {k : U ⟶ W} (hk : k = f ≫ g) :
    eqToHom p ≫ k ≫ eqToHom r.symm =
      (eqToHom p ≫ f ≫ eqToHom q.symm) ≫ (eqToHom q ≫ g ≫ eqToHom r.symm)

theorem twistedPairingTransport_heq {X Y U V : C} (p : X = U) (q : Y = V) (f : U ⟶ V) :
    HEq (eqToHom p ≫ f ≫ eqToHom q.symm) f

def twistedPairingSimplexMap (i j : Fin (n+n+1+1)) (hij : i ≤ j) :
    twistedPairingSimplexObj A B σ i ⟶ twistedPairingSimplexObj A B σ j

theorem twistedPairingSimplexMap_id (i : Fin (n+n+1+1)) :
    twistedPairingSimplexMap A B h σ i i le_rfl = 𝟙 _

theorem twistedPairingSimplexMap_comp (i j k : Fin (n+n+1+1))
    (hij : i ≤ j) (hjk : j ≤ k) :
    twistedPairingSimplexMap A B h σ i k (hij.trans hjk) =
      twistedPairingSimplexMap A B h σ i j hij ≫ twistedPairingSimplexMap A B h σ j k hjk

def twistedPairingSimplex : Fin (n+n+1+1) ⥤ C
```

#### TwistedPairingCrossNaturality（50行）

```lean
theorem twistedPairingCross_diagonal (i : Fin (n+1)) :
    twistedPairingCross A B h σ i i = h (σ.obj i)

theorem twistedPairingCross_changeBase (p a b : Fin (n+1)) (hpa : p ≤ a) (hpb : p ≤ b) :
    twistedPairingCross A B h σ a b =
      (A.map (σ.map (homOfLE hpa))).unop ≫ h (σ.obj p) ≫ B.map (σ.map (homOfLE hpb))

theorem twistedPairingCross_reindex {m : ℕ} (α : Fin (m+1) →o Fin (n+1))
    (a b : Fin (m+1)) :
    twistedPairingCross A B h (α.monotone.functor ⋙ σ) a b =
      twistedPairingCross A B h σ (α a) (α b)
```

#### TwistedPairingCoordinates（93行）

```lean
theorem twistedPairingLeftVertex_lt (n : ℕ) (i : Fin (n+1)) :
    (edgewiseLeftVertex n i).val < n+1

theorem twistedPairingRightVertex_not_lt (n : ℕ) (i : Fin (n+1)) :
    ¬ (edgewiseRightVertex n i).val < n+1

theorem twistedPairingLeftIndex_vertex (n : ℕ) (i : Fin (n+1))
    (hi : (edgewiseLeftVertex n i).val < n+1) :
    twistedPairingLeftIndex (edgewiseLeftVertex n i) hi = i

theorem twistedPairingRightIndex_vertex (n : ℕ) (i : Fin (n+1))
    (hi : ¬ (edgewiseRightVertex n i).val < n+1) :
    twistedPairingRightIndex (edgewiseRightVertex n i) hi = i

theorem twistedPairingSimplex_obj_left (i : Fin (n+1)) :
    (twistedPairingSimplex A B h σ).obj (edgewiseLeftVertex n i) = (A.obj (σ.obj i)).unop

theorem twistedPairingSimplex_obj_right (i : Fin (n+1)) :
    (twistedPairingSimplex A B h σ).obj (edgewiseRightVertex n i) = B.obj (σ.obj i)

theorem twistedPairingSimplexMap_left_heq (i j : Fin (n+n+1+1)) (hij : i ≤ j)
    (hi : i.val < n+1) (hj : j.val < n+1) :
    HEq (twistedPairingSimplexMap A B h σ i j hij)
      (A.map (σ.map (homOfLE (show twistedPairingLeftIndex j hj ≤ twistedPairingLeftIndex i hi
        by dsimp [twistedPairingLeftIndex]; exact Nat.sub_le_sub_left hij _)))).unop

theorem twistedPairingSimplexMap_cross_heq (i j : Fin (n+n+1+1)) (hij : i ≤ j)
    (hi : i.val < n+1) (hj : ¬ j.val < n+1) :
    HEq (twistedPairingSimplexMap A B h σ i j hij)
      (twistedPairingCross A B h σ (twistedPairingLeftIndex i hi) (twistedPairingRightIndex j hj))

theorem twistedPairingSimplexMap_right_heq (i j : Fin (n+n+1+1)) (hij : i ≤ j)
    (hi : ¬ i.val < n+1) (hj : ¬ j.val < n+1) :
    HEq (twistedPairingSimplexMap A B h σ i j hij)
      (B.map (σ.map (homOfLE (show twistedPairingRightIndex i hi ≤ twistedPairingRightIndex j hj
        by dsimp [twistedPairingRightIndex]; exact Nat.sub_le_sub_right hij _))))
```

## 191. 同じtwisted arrowへの全写像と二射影、R03dの半分での実測（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03d・R02・R03は未完了。

### 191.1 今回の検証済み

元の長い射列が実際のedgewise重みの全順序射と厳密に両立することを証明し、`twistedPairingNerveMap` として一つの全単体写像にした。元の射の四角形を使うのは交差射の基点変更・再添字付けであり、面・退化をすべて含む。

同じ射列の左右の標準区間への全制限も証明した。右は元の標的の射列、左は元の反変の始域の逆反転そのもの。同じnerve反転同型の逆の一般の評価則を合わせ、全写像の右射影がnerveMap B、左射影がnerveMap Aと同じnerveOppositeIso.invの合成であることを、**全写像の厳密な等式**として得た。元の両端の指定底を保つ `twistedPairingNerveMap_projection` が今回の終点。正本Hom∞への全FunctorIsoではまだない。

259：TwistedPairingReindex・TwistedPairingNerve二本、対象ビルド1,559 jobs・終了0、小監査106本821宣言・標準三公理のみ。260：NerveOppositeEvaluation・TwistedPairingRestrictions・TwistedPairingProjections三本、対象ビルド1,572 jobs・終了0、小監査109本829宣言・標準三公理のみ。実ハンドル27277・63636の終了0を確認し、鍵を返却した。sorry・独自公理0、計算上限変更なし。

今回五本375行（159＋48＋32＋69＋67）、累計109本・7,289行（外枠15,000）。R03dの§188以降の検証済みは877行で、§187の見込み950〜1,450行の半分を越えた。既存構成の係数移送・自然性の法則とR03dの証明の分割であり、追加の一覧項目は0。全五本200行以下。

### 191.2 残りの見込みと、先に紙で確認する接続

残りは、全要素圏上で作った同じ射を、全パラメーターを保ってKan係数の分類へ運び、元の固定始域の比較へ正規化すること。次の三点をソースで確認した。

1. `leftStraighteningInfinityDiagram p` は `[LeftFibration p]` を要求する。全source frame Homの要素圏の射影にはこの仮定はないので、そのまま分類に代入できない。
2. `sourceFrameElementsFamily` の元のaugmentationは `nerve (Elementsᵒᵖ)` からHomへ向かう。今回の全要素圏のfiberは `Elements` である。この反対の違いを同一視してaugmentationを使えない。Kan化・反転との全自然性を含む比較が必要。
3. `weightedNerve F` は初区間の重み付き係数の族を持つ。全要素圏のnerveと定義上同じものではない。既存の `Thomason.map_isWeakHomotopyEquivalence` は全空間の弱同値であり、それだけでは同じ底上の全分類比較や指定点の正規化を証明しない。

型の移送・BEへの適用・元の固定始域比較との正規化の残りは、比較の橋を本体の定理として参照できれば350〜550行の暫定見込み。一方、上の1〜3を結ぶ数学的な橋には別に700〜1,100行程度を見込むが、まだ同じ底上の必要な型を確定していない。橋も含めた同じ一まとまりの合計見込みは1,927〜2,527行となり、§187の950〜1,450行は小さかった。

したがって、この線の新しいLeanはここでいったん増やさず、必要な橋の主張を紙で型にする。同じR03のまとまりの**独立した中間定理**として切り出すのが数学的に妥当で、その一つの見込みが1,500行以下なら、IS-W2 §19に従い型と見込みを一覧の追加として記録して進める。単に行数を分けるための補題の分割では、この規則を回避しない。1,500行を超える型、まとまりの外、⑤aの欄の型に関わるものが必要と分かった場合は、検証済みのこのコミットを取り込み点にして型と理由を報告する。

この確認でG10へ戻ったり、R03dの型を点ごとのHom同値・π₀の自然性へ弱めたりしない。無条件のnative極限性を得たとは主張しない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 191.3 今回の型

共通の入力は§190.1のI・C・A・B・h・hh・σ。再添字付けの入力αはSimplexCategory.mk m ⟶ SimplexCategory.mk n。

#### TwistedPairingReindex（159行）

```lean
theorem twistedPairingLeftVertex_index {n : ℕ} (i : Fin (n+n+1+1)) (hi : i.val < n+1) :
    edgewiseLeftVertex n (twistedPairingLeftIndex i hi) = i

theorem twistedPairingRightVertex_index {n : ℕ} (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) :
    edgewiseRightVertex n (twistedPairingRightIndex i hi) = i

theorem twistedPairingReindex_left (i : Fin (m+m+1+1)) (hi : i.val < m+1) :
    edgewiseWeightReindexOrderHom.{u} α i =
      edgewiseLeftVertex n (α.toOrderHom (twistedPairingLeftIndex i hi))

theorem twistedPairingReindex_right (i : Fin (m+m+1+1)) (hi : ¬ i.val < m+1) :
    edgewiseWeightReindexOrderHom.{u} α i =
      edgewiseRightVertex n (α.toOrderHom (twistedPairingRightIndex i hi))

theorem twistedPairingReindex_leftIndex (i : Fin (m+m+1+1)) (hi : i.val < m+1)
    (hbi : (edgewiseWeightReindexOrderHom.{u} α i).val < n+1) :
    twistedPairingLeftIndex (edgewiseWeightReindexOrderHom.{u} α i) hbi =
      α.toOrderHom (twistedPairingLeftIndex i hi)

theorem twistedPairingReindex_rightIndex (i : Fin (m+m+1+1)) (hi : ¬ i.val < m+1)
    (hbi : ¬ (edgewiseWeightReindexOrderHom.{u} α i).val < n+1) :
    twistedPairingRightIndex (edgewiseWeightReindexOrderHom.{u} α i) hbi =
      α.toOrderHom (twistedPairingRightIndex i hi)

theorem twistedPairingThinMap_heq {D : Type u} [Category.{u} D] {N : ℕ}
    (F : Fin N ⥤ D) {a b c d : Fin N} (ha : a = c) (hb : b = d)
    {f : a ⟶ b} {g : c ⟶ d} : HEq (F.map f) (F.map g)

theorem twistedPairingThinUnopMap_heq {D : Type u} [Category.{u} D] {N : ℕ}
    (F : Fin N ⥤ Dᵒᵖ) {a b c d : Fin N} (ha : a = c) (hb : b = d)
    {f : a ⟶ b} {g : c ⟶ d} : HEq (F.map f).unop (F.map g).unop

theorem twistedPairingCross_heq {a b c d : Fin (n+1)} (ha : a = c) (hb : b = d) :
    HEq (twistedPairingCross A B h σ a b) (twistedPairingCross A B h σ c d)

theorem twistedPairingSimplex_reindex :
    (edgewiseWeightReindexOrderHom.{u} α).monotone.functor ⋙ twistedPairingSimplex A B h σ =
      twistedPairingSimplex A B h (α.toOrderHom.monotone.functor ⋙ σ)
```

#### TwistedPairingNerve（48行）

```lean
theorem twistedPairingWeightIso_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    edgewiseWeight.{u}.map α ≫ (edgewiseWeightIso n).hom =
      (edgewiseWeightIso m).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (edgewiseWeightReindexOrderHom.{u} α))

def twistedPairingNerveMap : nerve I ⟶ TwistedArrow (nerve C)
```

#### NerveOppositeEvaluation（32行）

```lean
theorem nerveOppositeIso_inv_apply {n : ℕ} (σ : ComposableArrows Cᵒᵖ n) :
    (nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌) σ =
      SSet.opObjEquiv.symm (nerveUnreverseChain σ)
```

#### TwistedPairingRestrictions（69行）

```lean
theorem twistedPairingLeftOrder_lt (n : ℕ) (i : Fin (n+1)) :
    (joinLeftOrderHom n n i).val < n+1

theorem twistedPairingLeftIndex_order (n : ℕ) (i : Fin (n+1))
    (hi : (joinLeftOrderHom n n i).val < n+1) :
    twistedPairingLeftIndex (joinLeftOrderHom n n i) hi = i.rev

theorem twistedPairingSimplex_restrict_right :
    (joinRightOrderHom n n).monotone.functor ⋙ twistedPairingSimplex A B h σ = σ ⋙ B

theorem twistedPairingSimplex_restrict_left :
    (joinLeftOrderHom n n).monotone.functor ⋙ twistedPairingSimplex A B h σ =
      nerveUnreverseChain (σ ⋙ A)
```

#### TwistedPairingProjections（67行）

```lean
theorem twistedPairingNerveMap_right :
    twistedPairingNerveMap A B h hh ≫ edgewiseRight (nerve C) = nerveMap B

theorem twistedPairingNerveMap_left :
    twistedPairingNerveMap A B h hh ≫ edgewiseLeft (nerve C) =
      nerveMap A ≫ (nerveOppositeIso (C := C)).inv

theorem twistedPairingNerveMap_projection :
    twistedPairingNerveMap A B h hh ≫ twistedArrowProjection (nerve C) =
      lift (nerveMap A ≫ (nerveOppositeIso (C := C)).inv) (nerveMap B)
```

## 192. R03e：通常のGrothendieck構成の厳密なweighted nerve比較（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは未証明。

§191.2の橋を紙で分けて確認した。最初に、任意の通常のCat値図式のGrothendieck構成のnerveと、各fiberのnerveからなる図式のweighted nerveとの厳密な同型を、**独立した数学的な中間定理R03e**として追加する。元の底の射影と元のfiberの指定頂点を保つ。IS-W2 §19の同じR01〜R03のまとまりの中の中間定理であり、見込みは500〜900行（1,500行以下）なので、承認を待たず進める。

これはR03dの行数だけを分割するための補題ではない。任意の通常のCat値図式に対する二つの既存の全構成を、底上の厳密な単体集合同型と指定頂点の等式で結ぶ、一つの独立した比較定理。全要素圏の射影を既存のweighted nerveの分類へ接続する最初の段に使う。単なる全空間の弱同値とは区別する。

```lean
theorem exists_grothendieckWeightedNerveIso
    {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) :
  ∃ e : nerve (Grothendieck F) ≅ weightedNerve (F ⋙ nerveFunctor),
    e.hom ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
      nerveMap (Grothendieck.forget F) ∧
    ∀ (i : I) (x : F.obj i),
      e.hom.app (Opposite.op ⦋0⦌) (nerveVertex (⟨i,x⟩ : Grothendieck F)) =
        (weightedNerveConstantLift (F ⋙ nerveFunctor) i).app
          (Opposite.op ⦋0⦌) (nerveVertex x)
```

この型を `/private/tmp/CheckISW2GrothWeightedNerveType.lean` のPropとしてLeanで確認し、実ハンドル74299の終了0を確認した。定理の証明を仮定にしたり本体に未証明で登録したりしていない。

置き場所は `InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerve*.lean`。既存の同名ファイルはない。前向きの単体と自然性150〜250行、逆向きの重み係数からのGrothendieck射列150〜250行、両往復150〜250行、射影・指定点の照合50〜150行、計500〜900行。見込みの半分で実測と残りを報告する。

短い経路として、既存の `SliceTransport/GrothendieckCommaTransport.transport` を再利用する。Grothendieck射列の各初区間を同じ最終基底へのCostructuredArrowに送り、その既存のtransportでfiberへ移す。このprefixのnerveが前向きの重み係数になる。逆は各prefixの最終対象と元の係数の自然性から実射を回収する。元のCat関手の合成の型の移送は、既存のtransportが処理する。

### 192.1 後半にまだ必要な判定

別途、全単体集合値図式Fについて、`Grothendieck (F ⋙ Functor.elementsFunctor)` の同じ底上の射影のcontinuousLeftFibrationReplacementを分類すると、元のFのEx∞のKan図式に全関手同型となる、という候補の型も一時ファイルで確認した。261で既存のContinuousLeftFibrationFilling一本を対象ビルド（1,503 jobs・終了0）してから `/private/tmp/CheckISW2ElementsLeftStraighteningType.lean` を通し、実ハンドル62729の終了0を確認した。この候補はまだ一覧に追加しておらず、証明も存在も主張しない。

R03eだけで後半の相対Kan比較が済むとは扱わない。要素圏の反対と元のaugmentation、同じ底上のKan化、元の指定点の回収を、どの既存の全比較で示すかを別に確認する。必要な独立の中間定理があれば、同じく型と見込みで§19を判定する。R03dの元の全FunctorIsoと固定始域の同じ比較への一致という型は保つ。R03eの証明に進む。

## 193. R03eの前向きprefixと元の最終対象の回収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは未完了。

元のGrothendieck射列の各初区間を、同じ最終基底への脚を持つCostructuredArrowの関手へ送った。各射の三角形は元の射列の合成則そのものであり、恒等射・合成も保持する。この関手に既存の `GrothendieckCommaTransport.transport` を後合成してfiberに値を持つprefixを得た。

各対象が元の脚で元のfiber対象を送ったものとなる評価式と、prefixの最終対象が元の同じfiber対象そのものになる厳密な等式を確認した。前向きの指定点の正規化の最初の部分であり、weighted nerveの全係数の自然変換と同型の両往復はまだ作っていない。

262：新規一本の対象ビルド1,168 jobs・終了0、小監査110本840宣言・標準三公理のみ。実ハンドル25109の終了0を確認し、鍵返却済み。sorry・独自公理0、計算上限変更なし。今回65行、累計110本・7,354行（外枠15,000）。R03eは65行／見込み500〜900行であり、まだ半分には達していない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次は同じ初区間の包含と既存transport_naturalityを使い、全prefixをsimplexPrefixWeightからの自然変換として束ねる。逆向きはweighted係数の最終対象と元の係数の自然性からGrothendieck射列を回収する。R03dとnative極限性は引き続き未完了。

### 193.1 型（65行）

共通の入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)`。PrefixIndexはF・σを使わない有限添字の包含。

```lean
def grothWeightedPrefixIndex (i : Fin (n+1)) (k : Fin (i.val+1)) : Fin (n+1)

def grothWeightedPrefixArrow (i : Fin (n+1)) :
    Fin (i.val+1) ⥤ CostructuredArrow (Grothendieck.forget F) (σ.obj i).base

def grothWeightedPrefixFiber (i : Fin (n+1)) : Fin (i.val+1) ⥤ F.obj (σ.obj i).base

theorem grothWeightedPrefixFiber_obj (i : Fin (n+1)) (k : Fin (i.val+1)) :
    (grothWeightedPrefixFiber F σ i).obj k =
      (F.map ((σ.map (homOfLE
        (show grothWeightedPrefixIndex i k ≤ i from Nat.le_of_lt_succ k.isLt))).base)).toFunctor.obj
          (σ.obj (grothWeightedPrefixIndex i k)).fiber

theorem grothWeightedPrefixFiber_last (i : Fin (n+1)) :
    (grothWeightedPrefixFiber F σ i).obj (Fin.last i.val) = (σ.obj i).fiber
```

## 194. R03eの全prefix係数と順向きの単体写像（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは未完了。

prefixの包含に対する自然性を、既存transportの自然性から示した。これをYonedaで元の重み係数の自然変換にし、任意の面・退化への自然性を保つ順向きの単体集合写像に束ねた。元の基底への射影との等式も厳密に成立する。逆向きの単体の関手性と両往復はまだ残る。

263：新規三本の対象ビルド1,172 jobs・終了0、小監査113本852宣言・標準三公理のみ。実ハンドル66924の終了0を確認し、鍵返却済み。今回164行、累計113本・7,518行（外枠15,000）。R03eは229行／見込み500〜900行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

併せて直近の報告の型抜粋で、`where`で始まる構成の本体まで入っていた箇所を型のみへ直した。宣言や型の変更ではない。R03d・R02の指定錐の族・無条件のnative極限性は未完了のまま。次は元のweighted係数から回収した逆向きの射列と両往復を示す。

### 194.1 型

#### GrothendieckWeightedNervePrefixNaturality（55行）

```lean
theorem grothWeightedPrefixArrow_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    grothWeightedPrefixArrow F σ i ⋙ CostructuredArrow.map (S := Grothendieck.forget F) (σ.map f).base =
      (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixArrow F σ j

theorem grothWeightedPrefixFiber_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixFiber F σ j =
      grothWeightedPrefixFiber F σ i ⋙ (F.map (σ.map f).base).toFunctor
```

#### GrothendieckWeightedNerveCoefficients（43行）

```lean
def grothWeightedNerveCoefficients :
    simplexPrefixWeight n ⟶ (σ ⋙ Grothendieck.forget F) ⋙ (F ⋙ nerveFunctor)

def grothWeightedNerveSimplex : weightedNerveSimplex (F ⋙ nerveFunctor) n

theorem grothWeightedNerveSimplex_base :
    (grothWeightedNerveSimplex F σ).1 = σ ⋙ Grothendieck.forget F
```

#### GrothendieckWeightedNerveForward（66行）

```lean
theorem grothWeightedPrefixArrow_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) (i : Fin (m.len+1)) :
    grothWeightedPrefixArrow F (α.toOrderHom.monotone.functor ⋙ σ) i =
      (simplexPrefixRestriction α i).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixArrow F σ (α.toOrderHom i)

theorem grothWeightedPrefixFiber_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) (i : Fin (m.len+1)) :
    grothWeightedPrefixFiber F (α.toOrderHom.monotone.functor ⋙ σ) i =
      (simplexPrefixRestriction α i).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixFiber F σ (α.toOrderHom i)

theorem grothWeightedNerveSimplex_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) :
    grothWeightedNerveSimplex F (α.toOrderHom.monotone.functor ⋙ σ) =
      weightedNerveSimplexMap (F ⋙ nerveFunctor) α (grothWeightedNerveSimplex F σ)

def grothWeightedNerveForward : nerve (Grothendieck F) ⟶ weightedNerve (F ⋙ nerveFunctor)

theorem grothWeightedNerveForward_projection :
    grothWeightedNerveForward F ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
      nerveMap (Grothendieck.forget F)
```

## 195. R03eの逆向きの射列（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは未完了。

各weighted係数のYoneda表示を取り、prefixの最終対象を逆向きのGrothendieck対象とした。係数の自然性は、包含で制限した射列と基底の射に沿って送った射列の厳密な等式である。その最終対象への評価を型の移送に使い、同じ底を持つGrothendieck射を回収した。恒等射・合成則もこの自然性の射への評価と有限順序上の射の一意性から示し、逆向きの全射列に束ねた。

264：新規二本の対象ビルド1,168 jobs・終了0、小監査115本866宣言・標準三公理のみ。実ハンドル19367の終了0を確認し、鍵返却済み。今回118行、累計115本・7,636行（外枠15,000）。R03eは347行／見込み500〜900行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

残りは、両往復と順向き写像の各次数での全単射性、そこからの同じ写像を前向きに持つ単体集合の同型、指定点の等式である。逆向き写像の面・退化との自然性を別に作り直さず、検証済みの順向き自然変換の各成分が可逆であることから全同型を得る。見込みの半分450行に達する前だが、現時点の残りは200〜450行と見積もる。R03d・R02・無条件のnative極限性はまだ閉じていない。

### 195.1 型

#### GrothendieckWeightedNerveInverseData（65行）

```lean
def grothWeightedNerveFiberChain (i : Fin (n+1)) : ComposableArrows (F.obj (s.1.obj i)) i.val

theorem grothWeightedNerveFiberChain_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
      grothWeightedNerveFiberChain F s j =
        grothWeightedNerveFiberChain F s i ⋙ (F.map (s.1.map f)).toFunctor

def grothWeightedNerveInverseObj (i : Fin (n+1)) : Grothendieck F

def grothWeightedNerveInverseIndex {i j : Fin (n+1)} (f : i ⟶ j) : Fin (j.val+1)

theorem grothWeightedNerveInverse_source {i j : Fin (n+1)} (f : i ⟶ j) :
    (F.map (s.1.map f)).toFunctor.obj (grothWeightedNerveInverseObj F s i).fiber =
      (grothWeightedNerveFiberChain F s j).obj (grothWeightedNerveInverseIndex f)

def grothWeightedNerveInverseMap {i j : Fin (n+1)} (f : i ⟶ j) :
    grothWeightedNerveInverseObj F s i ⟶ grothWeightedNerveInverseObj F s j

theorem grothWeightedNerveInverseMap_base {i j : Fin (n+1)} (f : i ⟶ j) :
    (grothWeightedNerveInverseMap F s f).base = s.1.map f
```

#### GrothendieckWeightedNerveInverseFunctor（53行）

```lean
theorem grothWeightedNerveInverseMap_id (i : Fin (n+1)) :
    grothWeightedNerveInverseMap F s (𝟙 i) = 𝟙 (grothWeightedNerveInverseObj F s i)

theorem grothWeightedNerveInverseMap_comp {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) :
    grothWeightedNerveInverseMap F s (f ≫ g) =
      grothWeightedNerveInverseMap F s f ≫ grothWeightedNerveInverseMap F s g

def grothWeightedNerveInverseSimplex : ComposableArrows (Grothendieck F) n

theorem grothWeightedNerveInverseSimplex_base :
    grothWeightedNerveInverseSimplex F s ⋙ Grothendieck.forget F = s.1
```

## 196. R03eの半分での実測（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは対象ビルド前で未完了。

検証済み347行に、両往復・全同型・指定頂点の作業木の四本259行を加えて606行となり、当初見込み500〜900行の半分450行を超えた。作業木を含む累計は7895行／外枠15,000行。両往復と全同型はまとめた個別検査の実ハンドル11719で終了0。指定頂点はまだ個別検査中であり、四本の対象ビルド・小監査は未実施。この時点で未検証分をコミットしない。

残りは指定頂点の次数零の計算、四本の対象ビルドと小監査である。型は§192のR03eを保持しており、見込み500〜900行以内で閉じる見通し。R03dの後半は、同じ底上のKan分類と元のaugmentationの指定点の照合が引き続き必要であり、R03eだけでnative極限性が得られたとは扱わない。

## 197. R03e完了：同じ射影と指定点を持つ厳密なweighted nerve同型（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 18（うち追加 6）。今回R03eが完了。R02・R03・R03dは未完了。

元のweighted係数から回収した射列のprefixは、元の同じ係数の全射列に一致する。対象は係数の自然性の対象への評価、射は同じ関手等式の射への評価で示し、Yonedaの往復で元のweighted単体へ戻した。逆方向の往復も、元のprefixの最終対象と最終射の評価から、元のGrothendieck射列そのものへ戻る等式として示した。

これらの両往復から順向きの既存全写像の各次数が全単射となり、その同じ全写像を前向きに持つ単体集合の同型を得た。元の底への射影の厳密な等式と、元の各fiber対象の指定頂点が同じconstant liftになる等式を併記し、§192のR03eの型をそのまま閉じた。逆写像の自然性を仮定したり、対象ごとの同値で代用したりしていない。

265：四本の対象ビルド1,570 jobs・終了0、小監査119本885宣言・標準三公理のみ。実ハンドル23927の終了0を確認し、鍵返却済み。直前の全個別検査は実ハンドル32248の終了0。今回260行、累計119本・7,896行／外枠15,000。R03eは607行で、当初見込み500〜900行の範囲内（上端との差−293行）。モジュール実ファイルの再集計で§195・196の二行の誤算も修正した。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

R03dの後半へ進むにあたり、`weightedNerveMap_isPrecompositionEquivalence` の入力には両係数のKan性が要ることを確認した。したがって、一般の `nerve (F.obj i)` からKan化への射にそのまま適用することはできない。continuousLeftFibrationReplacementの単位はleft anodyneで、`continuousLeftFibrationHomIso` は同じ底上の全相対Homを保つが、これだけで元の係数の全分類との同型や指定点の正規化が得られたとはしない。次はR03eを同じ底のOverの同型へ持ち上げる既存構成の法則を使い、相対Kan比較の残りを確認する。§192.1の候補はまだ一覧に加えず、未証明のまま使わない。

### 197.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。単体の法則ではさらに `{n : ℕ}` と `s : weightedNerveSimplex (F ⋙ nerveFunctor) n` または `σ : ComposableArrows (Grothendieck F) n` を用いる。

#### GrothendieckWeightedNerveRecovery（63行）

```lean
theorem grothWeightedPrefixFiber_inverse_obj (i : Fin (n+1)) (k : Fin (i.val+1)) :
    (grothWeightedPrefixFiber F (grothWeightedNerveInverseSimplex F s) i).obj k =
      (grothWeightedNerveFiberChain F s i).obj k

theorem grothWeightedPrefixFiber_inverse (i : Fin (n+1)) :
    grothWeightedPrefixFiber F (grothWeightedNerveInverseSimplex F s) i =
      grothWeightedNerveFiberChain F s i

theorem grothWeightedNerveSimplex_inverse :
    grothWeightedNerveSimplex F (grothWeightedNerveInverseSimplex F s) = s
```

#### GrothendieckWeightedNerveRetraction（82行）

```lean
theorem grothWeightedNerveFiberChain_forward (i : Fin (n+1)) :
    grothWeightedNerveFiberChain F (grothWeightedNerveSimplex F σ) i =
      grothWeightedPrefixFiber F σ i

theorem grothWeightedNerveInverseObj_forward (i : Fin (n+1)) :
    grothWeightedNerveInverseObj F (grothWeightedNerveSimplex F σ) i = σ.obj i

theorem grothWeightedPrefixFiber_last_map {i j : Fin (n+1)} (f : i ⟶ j) :
    (grothWeightedPrefixFiber F σ j).map (homOfLE
      (show grothWeightedNerveInverseIndex f ≤ Fin.last j.val from leOfHom f)) =
        eqToHom (by
          rw [grothWeightedPrefixFiber_obj]
          rfl) ≫ (σ.map f).fiber ≫
            eqToHom (grothWeightedPrefixFiber_last F σ j).symm

theorem grothWeightedNerveInverseSimplex_forward :
    grothWeightedNerveInverseSimplex F (grothWeightedNerveSimplex F σ) = σ
```

#### GrothendieckWeightedNerveIso（40行）

```lean
theorem grothWeightedNerveForward_bijective (n : ℕ) :
    Function.Bijective (grothWeightedNerveSimplex F (n := n))

def grothendieckWeightedNerveIso : nerve (Grothendieck F) ≅ weightedNerve (F ⋙ nerveFunctor)

theorem grothendieckWeightedNerveIso_projection :
    (grothendieckWeightedNerveIso F).hom ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
      nerveMap (Grothendieck.forget F)
```

#### GrothendieckWeightedNerveVertex（75行）

```lean
theorem grothWeightedNerveForward_vertex (i : I) (x : F.obj i) :
    (grothWeightedNerveForward F).app (Opposite.op ⦋0⦌)
      (nerveVertex (⟨i,x⟩ : Grothendieck F)) =
        (weightedNerveConstantLift (F ⋙ nerveFunctor) i).app
          (Opposite.op ⦋0⦌) (nerveVertex x)

theorem exists_grothendieckWeightedNerveIso :
    ∃ e : nerve (Grothendieck F) ≅ weightedNerve (F ⋙ nerveFunctor),
      e.hom ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
        nerveMap (Grothendieck.forget F) ∧
      ∀ (i : I) (x : F.obj i),
        e.hom.app (Opposite.op ⦋0⦌) (nerveVertex (⟨i,x⟩ : Grothendieck F)) =
          (weightedNerveConstantLift (F ⋙ nerveFunctor) i).app
            (Opposite.op ⦋0⦌) (nerveVertex x)
```

## 198. 同じ底上の置換同型と元の単位の照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 18（うち追加 6）。R03e完了、R03d・R02・R03は未完了。

検証済みの同じ射影の等式をOver.isoMkに渡し、R03eを元の同じ底のOverの同型にした。この同型を既存のcontinuousLeftFibrationReplacementに送り、元の指定された置換の単位との厳密な可換性を単位の自然性から示した。いずれも既存構成の同型保存・自然性の法則であり、新しい中間の定理の追加ではない。元の係数からの相対Kan分類が成立したとは主張しない。

266：新規一本の対象ビルド1,517 jobs・終了0、小監査120本888宣言・標準三公理のみ。実ハンドル70589の終了0を確認し、鍵返却済み。個別検査も実ハンドル61213の終了0。今回45行、累計120本・7,941行／外枠15,000。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

残りは§197のとおり、同じ底上のKan分類と元のaugmentationの指定点の回収、それを全共同Hom比較へ接続することである。Kan係数を仮定するweightedNerveMapの既存の前合成同値判定を、一般の非Kanなnerve係数へ適用しない。候補§192.1はなお未証明・未登録。R03dの型・固定始域への一致・元の標準脚の型を保って続ける。

### 198.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### GrothendieckWeightedNerveOver（45行）

```lean
def grothendieckWeightedNerveOverIso :
    Over.mk (nerveMap (Grothendieck.forget F)) ≅ Over.mk (weightedNerveProjection (F ⋙ nerveFunctor))

def grothendieckWeightedNerveReplacementIso :
    (continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (nerveMap (Grothendieck.forget F))) ≅
    (continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)))

theorem grothendieckWeightedNerveReplacementIso_unit :
    ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ≫
        (grothendieckWeightedNerveReplacementIso F).hom.left =
      (grothendieckWeightedNerveOverIso F).hom.left ≫
        ((continuousLeftFibrationReplacementUnit (nerve I)).app
          (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)))).left
```

## 199. 底上の同じ置換同型を全分類へ運ぶ（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 18（うち追加 6）。R03d・R02・R03は未完了。

前のターンはR03eの完成とOver・置換単位の照合まで進んだため、進捗あり。今回は作業木がcleanであることとコミット4baf71306を確認して継続した。既存の `leftClassification_overIso` を、検証済みの同じ底上の二つの置換同型に適用した。比較は底全体のFunctorIsoであり、fiberごとの同型による代用ではない。同型保存の既存の法則で、一覧の中間の定理の追加ではない。

267：新規一本の対象ビルド3,125 jobs・終了0、小監査121本892宣言・標準三公理のみ。実ハンドル26874の終了0を確認し、鍵返却済み。個別検査は実ハンドル40480の終了0。今回36行、累計121本・7,977行／外枠15,000。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次に必要なCat値図式の相対Kan比較の分類側の候補を一時ファイル `/private/tmp/CheckISW2CatLeftStraighteningType.lean` のPropとして確認した（実ハンドル60059・終了0）。元の置換単位と元の前向きweighted mapの厳密な等式も保持する、より強い全空間の比較の候補は `/private/tmp/CheckISW2GrothKanLiftType.lean` のPropとして確認した（実ハンドル2743・終了0）。いずれもこの時点では未証明で一覧に追加せず、仮定として使わない。まず既存のleft-anodyne単位に沿う相対延長を使い、元の比較を保持する全空間の射を構成する。射の存在だけでは前合成同値性は得られないことを区別する。

### 199.1 型（共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`）

#### GrothendieckWeightedNerveClassification（36行）

```lean
def grothendieckWeightedNerveReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)))).hom)
```

## 200. R03f：元の単位を固定する相対Kan比較（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 19（うち追加 7）。R03fを追加、未証明。R03d・R02・R03も未完了。

IS-W2 §19の「同じまとまりで一つの見込み1,500行以下」の枠で、次の独立の中間定理R03fを一覧に加える。Cat値図式の各fiberのnerveをKan化することと、そのGrothendieck射影の同じ底上のleft fibration置換を比較する相対版のgroupoid completionである。R03eは厳密な二模型の同型のみで、この相対Kan化を含まないため、既存の構成の法則として数えない。

### 200.1 型

共通の名前空間はGrothendieckWeightedNerveOverと同じ。`exInfinity`・`exInfinityUnit` はTheExInfinityFunctor、`IsPrecompositionEquivalence` はTheHomotopyTheoryOfInfinityCategories.Equivalenceの既存の宣言。

```lean
theorem exists_grothendieckKanCoefficientComparison
    {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) :
  let G := (F ⋙ nerveFunctor) ⋙ exInfinity
  let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
  let R := (continuousLeftFibrationReplacement (nerve I)).obj P
  let η : F ⋙ nerveFunctor ⟶ G :=
    Functor.whiskerLeft (F ⋙ nerveFunctor) exInfinityUnit
  ∃ f : R.left ⟶ weightedNerve G,
    f ≫ weightedNerveProjection G = R.hom ∧
    ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
      grothWeightedNerveForward F ≫ weightedNerveMap η ∧
    IsPrecompositionEquivalence f
```

このPropの型は一時ファイルCheckISW2GrothKanLiftType.leanで確認済み（実ハンドル2743、終了0）。本体に未証明の定理や仮定として入れない。元の全空間の射・同じ底・指定された元の単位との等式を保持する。単なる分類像の存在より強い型であり、後で元の指定点への回収を追える形にする。R03dの固定始域比較との一致の型は変えない。

### 200.2 見込みと経路

置き場所は同じFibrationsOverOrdinaryCategories/GrothendieckKan*.lean。見込み900〜1,450行。元の係数の単位からの射と相対延長（約70〜150行）、bar/scaffoldと元のGrothendieck比較の照合（100〜200行）、同じ底上でfiberの全辺を可逆化する比較の検証（500〜750行）、全空間の前合成同値と元の単位の正規化を束ねる部分（150〜350行）を想定する。独立の中間定理としての上端1,450行であり、任意の細分で§19の枠を回避しない。半分の725行で止まらずに実測と残りを報告する。

短縮の候補：元のnerve係数はquasicategoryであるため、`tautScaffold_isPrecompositionEquivalence_of_quasicategory` を使える。前の一般のweightedNerveMapのKan係数用判定との違いはここにある。R03eとこのscaffoldを介して元の射を保持し、各fiberのEx∞単位が全辺を可逆にすることを同じ底の比較として示す。全空間の通常の弱ホモトピー同値だけで相対版を代用しない。相対延長の存在の既存の法則はすでに個別検査を通ったが、それだけでは最後のIsPrecompositionEquivalenceは得られない。fiberごとの可逆化と同じ底上の比較を示す数学が残る。

⑤aの欄、既存FramedLimit*・CAlgUnderlyingDerivedComparison、点つきKanのTot、[ModelCategory SSet]を追加・変更しない。R03fが閉じた後も、元の要素圏の反対・augmentationとの照合とR03dへの接続を別に検収する。

## 201. 元の置換単位を固定したKan係数への相対延長（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 19（うち追加 7）。R03f・R03d・R02・R03は未完了。

元の全Cat図式のnerveに同じEx∞単位を後合成し、R03eの前向き全写像とweightedNerveMapで、同じ底のKan係数への実射を構成した。元の射影との厳密な等式を確認し、既存のleft-anodyne単位に対する相対延長の定理で、その元の単位との合成が元の実射そのものである延長を得た。この存在と二つの等式は既存構成の法則であり、R03fの最後の前合成同値性はまだ証明していない。

268は不足していた既存ContinuousLeftFibrationAnodyneの対象ビルド1,506 jobsまでは成功したが、その後の個別検査でOver対象の暗黙引数の推論に失敗した（実ハンドル95897・終了1）。対象を明示して個別検査16203・終了0を確認し、269で新規一本の対象ビルド1,866 jobs・終了0と小監査122本899宣言・標準三公理のみを確認した。実ハンドル94522の終了0を確認し、鍵返却済み。

今回69行、累計122本・8,046行／外枠15,000。R03fは69行／見込み900〜1,450行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次はquasicategory値nerve係数のtaut scaffoldをR03eへ接続し、元の射を保つbar/scaffold比較を作る。

### 201.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。各係数のKan性は同じEx∞の既存のinstanceにより明示した。

#### GrothendieckKanCoefficientLift（69行）

```lean
abbrev grothendieckKanCoefficients : I ⥤ SSet.{u}

def grothendieckKanCoefficientUnit : F ⋙ nerveFunctor ⟶ grothendieckKanCoefficients F

def grothendieckKanCoefficientMap :
    nerve (Grothendieck F) ⟶ weightedNerve (grothendieckKanCoefficients F)

theorem grothendieckKanCoefficientMap_projection :
    grothendieckKanCoefficientMap F ≫ weightedNerveProjection (grothendieckKanCoefficients F) =
      nerveMap (Grothendieck.forget F)

theorem exists_grothendieckKanCoefficientLift :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∃ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      f ≫ weightedNerveProjection (grothendieckKanCoefficients F) = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F
```

## 202. 元のbar/scaffoldとKan係数への射の照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 19（うち追加 7）。R03f・R03d・R02・R03は未完了。

元のCat図式のnerve係数にtaut scaffoldを取り、R03eの同じ逆射を後合成して、barから元のGrothendieck射列への全空間の射を得た。同じ基底への射影を保ち、元のKan係数への実射との合成は、barの元の係数単位の自然変換の後にKan係数のtaut scaffoldを続けた射と厳密に一致する。quasicategory係数用の既存のscaffold定理から、この元のbar→Grothendieck射列の射自身の前合成同値性も得た。Kan性を非Kanなnerve係数へ仮定していない。

270：新規一本の対象ビルド2,389 jobs・終了0、小監査123本904宣言・標準三公理のみ。実ハンドル89697の終了0を確認し、鍵返却済み。個別検査66223も終了0。今回59行、累計123本・8,105行／外枠15,000。R03fは128行／見込み900〜1,450行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

残りは、係数のEx∞単位のbar上の相対的な性質から、元の単位を固定する延長の前合成同値性を得る部分である。対象ごとの通常の弱同値から全空間の圏同値を直接主張しない。

### 202.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### GrothendieckKanScaffold（59行）

```lean
def grothendieckNerveScaffold :
    simplicialReplacement (F ⋙ nerveFunctor) ⟶ nerve (Grothendieck F)

theorem grothendieckNerveScaffold_projection :
    grothendieckNerveScaffold F ≫ nerveMap (Grothendieck.forget F) =
      simplicialReplacementProjection (F ⋙ nerveFunctor)

theorem grothendieckNerveScaffold_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (grothendieckNerveScaffold F)

theorem grothendieckNerveScaffold_kanCoefficientMap :
    grothendieckNerveScaffold F ≫ grothendieckKanCoefficientMap F =
      simplicialReplacementMap (grothendieckKanCoefficientUnit F) ≫
        tautScaffold (grothendieckKanCoefficients F)
```

## 203. R03f.1：Kan標的へのanodyne射のleft anodyne性（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 20（うち追加 8）。R03f.1を追加、未証明。

§19の同じまとまり・見込み1,500行以下の枠で、次の一般補題をR03f.1として加える。R03fのEx∞単位の相対的な持ち上げ性に使う数学的な中間定理であり、既存構成の自然性の法則と混同しない。

```lean
theorem anodyneExtensions_leftAnodyne_of_kanTarget
    {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)
    (hf : SSet.anodyneExtensions f) :
  leftAnodyneExtensions f
```

`leftAnodyneExtensions` はTheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrationsの既存の定義。このPropの型は一時ファイルCheckISW2AnodyneKanTargetLeftType.leanで確認済み（実ハンドル37011・終了0）。未証明の宣言や仮定として本体に入れない。

置き場所はKerodon/TheHomotopyTheoryOfInfinityCategories/LeftAndRightFibrations/AnodyneKanTarget.leanを想定する。同名の既存ファイルはない。見込み150〜300行。左ホーンの持ち上げによって、Kan基底上のleft fibrationの全空間もKanであることを既存のkanComplex_of_leftHornFillersに渡せる。一般の持ち上げ問題をY上へ引き戻すと、その射影はKan複体間のleft fibrationであり、既存leftFibration_fibration_of_kanComplexから全ホーンを持ち上げる。hfのanodyne性でその引き戻した射影への持ち上げを得て、元の問題へ戻す。これをleftHornInclusions.rlp.llpとして束ねる。モデル構造の仮定は使わない。

この補題が得られてもbarが係数のleft anodyne射をどのように保つかの検証と、元のR03fの前合成同値性は残る。R03f.1だけをもってR03fまたはR03dの完成とは扱わない。R03f.1の実測は独立に記録し、外枠15,000行にも含める。次はこの型の証明に進む。

## 204. R03f.1完了：Kan標的へのanodyne射はleft anodyne（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 20（うち追加 8）。R03f.1完了。R03f・R03d・R02・R03は未完了。

Kan基底上のleft fibrationについて、基底の左ホーンをKan性で充填し、その充填をleft fibrationで持ち上げた。既存kanComplex_of_leftHornFillersにより全空間もKanとなる。次に任意のleft fibrationへの元の持ち上げ問題をKan標的へ引き戻し、その射影の全ホーン持ち上げ性へanodyne性を適用して元へ戻した。元の射そのものがleftHornInclusions.rlp.llpに属することを証明した。

271：新規一本の対象ビルド1,608 jobs・終了0、小監査124本906宣言・標準三公理のみ。実ハンドル74994の終了0を確認し、鍵返却済み。個別検査66431も終了0。今回61行、累計124本・8,166行／外枠15,000。R03f.1は見込み150〜300行に対して61行（上端との差−239行）。既存のkanComplex_of_leftHornFillersとleftFibration_fibration_of_kanComplexで短縮できた。R03f本体の128行とは独立に記録する。

SSet.modelCategoryQuillenのスコープは、fibrationを全ホーンの右持ち上げ性として読むためにだけ用いる。[ModelCategory SSet]は追加していない。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次は同じEx∞単位のleft anodyne性へ適用し、bar上への移送を検討する。

### 204.1 型

#### AnodyneKanTarget（61行）

```lean
theorem leftFibration_total_kanComplex {E B : SSet.{u}} [KanComplex B]
    (p : E ⟶ B) [LeftFibration p] : KanComplex E

theorem anodyneExtensions_leftAnodyne_of_kanTarget
    {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)
    (hf : SSet.anodyneExtensions f) : leftAnodyneExtensions f
```

## 205. 元のEx∞単位のleft anodyne性への適用（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 20（うち追加 8）。R03f・R03d・R02・R03は未完了。

R03f.1を元の同じexInfinityUnitと既存exInfinityUnit_anodyneへ適用し、その単位自身のleft anodyne性を得た。既存構成の性質の適用であり、一覧の新しい数学的定理には数えない。関手・単位の変更や別のKan模型への置き換えはしていない。

272：新規一本の対象ビルド1,670 jobs・終了0、小監査125本907宣言・標準三公理のみ。実ハンドル72538の終了0を確認し、鍵返却済み。個別検査15355も終了0。今回23行、累計125本・8,189行／外枠15,000。R03f本体の作業は151行、独立のR03f.1は61行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 205.1 型

#### ExInfinityUnitLeftAnodyne（23行）

```lean
theorem exInfinityUnit_leftAnodyne (X : SSet.{u}) :
    leftAnodyneExtensions (exInfinityUnit.app X)
```

## 206. R03f.2：barが各成分のleft anodyne性を保つ（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2を追加、未証明。

同じR03fのまとまりで、§19の見込み1,500行以下の枠により次の独立の中間定理を加える。全ての自然変換に対する一般のbarの保存定理であり、既存の単位の自然性の法則として処理しない。R03f.1のKan標的への判定とは異なる数学である。

```lean
theorem simplicialReplacementMap_leftAnodyne
    {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}
    (η : F ⟶ G) (hη : ∀ i, leftAnodyneExtensions (η.app i)) :
  leftAnodyneExtensions (simplicialReplacementMap η)
```

名前空間はFibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories。`leftAnodyneExtensions` はTheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrationsの既存の性質。型は `/private/tmp/CheckISW2ReplacementLeftType.lean` のPropで確認した（実ハンドル31074・終了0）。未証明の宣言や仮定を本体に登録しない。

見込み650〜1,200行。置き場所は一般の対角の道具がHomotopicalAlgebra/Simplicial/DiagonalLeftAnodyne.lean、bar固有がFibrationsOverOrdinaryCategories/SimplicialReplacementLeftAnodyne*.lean。一般の対角の相対持ち上げ80〜180行、barの行の余積表示と退化のlatchingの相対表示350〜650行、既存のsimplicialReplacementMapへの同定・全移送150〜300行を見込む。半分600行で実測と残りを報告する。独立のbarの保存定理の全体として見積もり、細分で§19の枠を回避しない。

短い経路：既存DiagonalAnodyne.diagonal_map_anodyneは全ホーン用の射の性質を固定しているため、その結論をleft anodyneへ読み替えない。同じ対角の右随伴とrelativeMatchingArrowIsoの証明を、left fibrationと境界内部Homへ適用する。必要なleftAnodyneExtensions_pushoutObjObj_left/rightとleftFibration_pullbackObjObjπは既存のLeftAnodynePushoutProductにある。barの各行は元の基底射列で添字づけた係数の余積であり、BarRowsCoproductの既存の余積表示を再利用する。退化の分裂により相対latchingの非退化部分を係数の同じη.app iの余積へ同定し、left anodyne性を渡す。これをReedy持ち上げと対角の随伴で元の全写像へ戻す。

R03f.2が得られれば、元の係数のEx∞単位に適用し、§202の同じscaffold正方形と§201の元の単位を固定した延長へ接続する。ただし、この時点ではR03fの延長の前合成同値性もR03dの両変数比較も未証明。元の指定点・固定始域の比較の一致という型を保って進める。

## 207. R03f.2の対角の持ち上げと元のbarの行（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

前のターンではR03f.1とEx∞単位への適用が検証済みでコミットされていたため、進捗あり。開始時にcleanな作業木とd4bf795eeを確認した。今回は対角の右随伴の相対matching射を、既存の同じrelativeMatchingArrowIsoで境界内部Homへ同定し、left fibration性を移した。Reedyの持ち上げと元の対角の随伴により、Reedy left anodyneな射の対角そのものがleft anodyneであることを示した。

barの各行は、元の基底射列σで添字づけた同じ係数F(σ(0))の単体集合として構成し、指定された同じ包含を持つ実際の余積であることを確認した。各行の任意の面・退化の写像は、元の基底射列の始点から新たな始点への射による係数の輸送で定義した。恒等射・合成則も元のIとFの関手則から示し、一つの二重単体集合の図式へ束ねた。BarRowsCoproductと同じ余積による考え方を使うが、一般のKerodon側からEInfinityへの依存を追加しないため、同じ宇宙の依存和で直接示した。

273：対角の新規一本の対象ビルド1,635 jobs・終了0、小監査126本909宣言・標準三公理のみ（実ハンドル71484・終了0）。274：行の新規二本の対象ビルド1,172 jobs・終了0、小監査128本931宣言・標準三公理のみ（実ハンドル8005・終了0）。両方とも鍵返却済み。個別検査は10567・74674・68021の終了0を確認した。

今回47＋71＋69＝187行、累計128本・8,376行／外枠15,000。R03f.2は187行／見込み650〜1,200行、まだ半分600行前。元のsimplicialReplacementMapへの対角の同定と、相対latchingが元の各η.app iのleft anodyne性を持つことが残る。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 207.1 型

行の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`、固定した行ではさらに `(n : ℕ)`。

#### DiagonalLeftAnodyne（47行）

```lean
theorem relativeMatching_leftFibrations {E B : SSet.{u}} (p : E ⟶ B)
    (hp : leftFibrations p) (n : ℕ) :
    leftFibrations (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p))

theorem diagonal_map_leftAnodyne {A B : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : A ⟶ B)
    (hf : reedyLeft simplexOp leftAnodyneExtensions f) :
    leftAnodyneExtensions (diagonal.map f)
```

#### SimplicialReplacementRows（71行）

```lean
def simplicialReplacementRow : SSet.{u}

def simplicialReplacementRowInclusion (σ : ComposableArrows I n) :
    F.obj (σ.obj 0) ⟶ simplicialReplacementRow F n

def simplicialReplacementRowCofan : Cofan (fun σ : ComposableArrows I n => F.obj (σ.obj 0))

def simplicialReplacementRowDesc
    (s : Cofan (fun σ : ComposableArrows I n => F.obj (σ.obj 0))) :
    simplicialReplacementRow F n ⟶ s.pt

def simplicialReplacementRowIsColimit : IsColimit (simplicialReplacementRowCofan F n)
```

#### SimplicialReplacementRowReindex（69行）

```lean
def simplicialReplacementRowReindex {m n : SimplexCategory} (α : m ⟶ n) :
    simplicialReplacementRow F n.len ⟶ simplicialReplacementRow F m.len

theorem simplicialReplacementRowReindex_id (n : SimplexCategory) :
    simplicialReplacementRowReindex F (𝟙 n) = 𝟙 (simplicialReplacementRow F n.len)

theorem simplicialReplacementRowReindex_comp {l m n : SimplexCategory}
    (α : l ⟶ m) (β : m ⟶ n) :
    simplicialReplacementRowReindex F (α ≫ β) =
      simplicialReplacementRowReindex F β ≫ simplicialReplacementRowReindex F α

def simplicialReplacementRows : SimplexCategoryᵒᵖ ⥤ SSet.{u}
```

## 208. 元の係数射・対角同型・退化部分の照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

元の係数の自然変換を同じ基底射列の全行に適用し、全ての面・退化との可換性を元の自然性から示した。二重単体集合の対角は、同じ基底射列の係数のYoneda表示だけを変える全同型で元のsimplicial replacementと同定した。元の係数射の対角が、その全同型と指定されたsimplicialReplacementMapを通る同じ射に厳密に一致する等式も示した。

任意の全射作用素が零を零へ送ることから、退化作用素の係数の輸送は同じ始点の等式に沿うeqToHomそのものとなる。各行の任意の基底部分集合を部分複体とし、基底の退化・非退化の二部分が交わらず元の行全体を覆うことを確認した。係数の自然変換は同じ部分を保ち、元の包含と厳密に可換する。この時点では実際の外側のlatchingとの同型性をまだ主張しない。

275：三本の対象ビルド1,296 jobs・終了0、小監査131本947宣言・標準三公理のみ（実ハンドル97624・終了0）。276：部分複体一本の対象ビルド1,174 jobs・終了0、小監査132本956宣言・標準三公理のみ（実ハンドル27094・終了0）。両方とも鍵返却済み。個別検査82533・99836・13226・16512の終了0を確認した。

今回47＋69＋42＋64＝222行、累計132本・8,598行／外枠15,000。R03f.2は409行／見込み650〜1,200行。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。sorry・独自公理0、計算上限変更なし。次は元のlatching図式を同じ退化部分への余錐として読み、その余極限性から相対latchingを非退化成分の同じ係数射へ分離する。

### 208.1 型

共通の入力は `{I : Type u} [SmallCategory I]`。係数は `F G : I ⥤ SSet.{u}`、その射は `η : F ⟶ G`。固定した行では `(n : ℕ)` を用いる。

#### SimplicialReplacementRowMaps（47行）

```lean
def simplicialReplacementRowMap (n : ℕ) :
    simplicialReplacementRow F n ⟶ simplicialReplacementRow G n

theorem simplicialReplacementRowMap_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    simplicialReplacementRowReindex F α ≫ simplicialReplacementRowMap η m.len =
      simplicialReplacementRowMap η n.len ≫ simplicialReplacementRowReindex G α

def simplicialReplacementRowsMap : simplicialReplacementRows F ⟶ simplicialReplacementRows G
```

#### SimplicialReplacementDiagonal（69行）

```lean
def simplicialReplacementDiagonalHom (F : I ⥤ SSet.{u}) :
    diagonal.obj (simplicialReplacementRows F) ⟶ simplicialReplacement F

def simplicialReplacementDiagonalIso (F : I ⥤ SSet.{u}) :
    diagonal.obj (simplicialReplacementRows F) ≅ simplicialReplacement F

theorem simplicialReplacementDiagonalIso_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    diagonal.map (simplicialReplacementRowsMap η) ≫ (simplicialReplacementDiagonalIso G).hom =
      (simplicialReplacementDiagonalIso F).hom ≫ simplicialReplacementMap η
```

#### SimplicialReplacementRowDegeneracies（42行）

```lean
theorem simplicialReplacement_epi_zero {m n : SimplexCategory} (α : m ⟶ n) [Epi α] :
    α.toOrderHom 0 = 0

theorem simplicialReplacement_epi_first {m n : SimplexCategory} (α : m ⟶ n) [Epi α]
    (σ : ComposableArrows I n.len) :
    (α.toOrderHom.monotone.functor ⋙ σ).obj 0 = σ.obj 0

theorem simplicialReplacement_epi_coefficient {m n : SimplexCategory} (α : m ⟶ n) [Epi α]
    (σ : ComposableArrows I n.len) :
    F.map (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))) =
      eqToHom (congrArg (fun i => F.obj (σ.obj i)) (simplicialReplacement_epi_zero α).symm)
```

#### SimplicialReplacementRowParts（64行）

```lean
def simplicialReplacementRowPart (F : I ⥤ SSet.{u}) (n : ℕ)
    (P : Set (ComposableArrows I n)) : (simplicialReplacementRow F n).Subcomplex

abbrev simplicialReplacementDegenerateRow (F : I ⥤ SSet.{u}) (n : ℕ)

abbrev simplicialReplacementNondegenerateRow (F : I ⥤ SSet.{u}) (n : ℕ)

theorem simplicialReplacementRowParts_sup (F : I ⥤ SSet.{u}) (n : ℕ) :
    simplicialReplacementDegenerateRow F n ⊔ simplicialReplacementNondegenerateRow F n = ⊤

theorem simplicialReplacementRowParts_inf (F : I ⥤ SSet.{u}) (n : ℕ) :
    simplicialReplacementDegenerateRow F n ⊓ simplicialReplacementNondegenerateRow F n = ⊥

def simplicialReplacementRowPartMap {F G : I ⥤ SSet.{u}} (η : F ⟶ G) (n : ℕ)
    (P : Set (ComposableArrows I n)) :
    (simplicialReplacementRowPart F n P : SSet.{u}) ⟶ simplicialReplacementRowPart G n P

theorem simplicialReplacementRowPartMap_inclusion {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    (n : ℕ) (P : Set (ComposableArrows I n)) :
    simplicialReplacementRowPartMap η n P ≫ (simplicialReplacementRowPart G n P).ι =
      (simplicialReplacementRowPart F n P).ι ≫ simplicialReplacementRowMap η n
```

## 209. 実際のlatching余錐と元の全単体の回収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

元の外側のlatching図式の各脚は、真に低い次数からの基底射列の像を持つため、同じ行の退化部分に厳密に因子分解する。これらの全脚が元の作用素の合成則で自然な余錐となることを示し、実際のlatchingの余極限から同じ退化部分への比較射を得た。

退化基底の既存の非退化表示は、元と同じ次数の全射が恒等射であることにより、真に低い次数の表示へできる。この同じ全射を元のlatchingの対象に戻した。係数は始点の同じ等式に沿って移送し、latchingの脚との合成でその逆の移送と打ち消される。これにより余錐の脚が退化行の元の各単体を係数も含めて厳密に回収することを示した。被覆性だけで余極限性を主張しない。

277：latching余錐一本の対象ビルド1,646 jobs・終了0、小監査133本966宣言・標準三公理のみ（実ハンドル38799・終了0）。この回は夜の共有鍵の順番待ちを同じ一枚の整理券のまま待ち、終了まで確認した。278：表示とlatching対象一本の対象ビルド1,648 jobs・終了0、小監査134本974宣言・標準三公理のみ（実ハンドル7754・終了0）。279：全射性一本の対象ビルド1,649 jobs・終了0、小監査135本975宣言・標準三公理のみ（実ハンドル28495・終了0）。すべて鍵返却済み。個別検査82141・16898・69787の終了0を確認した。

今回64＋50＋46＝160行、累計135本・8,758行／外枠15,000。R03f.2は569行／見込み650〜1,200行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次は元の二つの表示を同じ非退化表示へ戻す一意性を使い、余錐の余極限性を示す。

### 209.1 型

共通入力は `{I : Type u} [SmallCategory I]`。余錐ではさらに `F : I ⥤ SSet.{u}` と `n : ℕ` を用いる。

#### SimplicialReplacementRowLatchingCocone（64行）

```lean
def simplicialReplacementRowLatchingLeg (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    (simplicialReplacementRows F).obj s.obj.left ⟶ simplicialReplacementDegenerateRow F n

theorem simplicialReplacementRowLatchingLeg_inclusion
    (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    simplicialReplacementRowLatchingLeg F n s ≫ (simplicialReplacementDegenerateRow F n).ι =
      (simplicialReplacementRows F).map s.obj.hom

def simplicialReplacementRowLatchingCocone :
    Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F)

def simplicialReplacementLatchingToDegenerate :
    colimit (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) ⟶
      simplicialReplacementDegenerateRow F n

theorem simplicialReplacementLatchingToDegenerate_fac
    (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    colimit.ι (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) s ≫
      simplicialReplacementLatchingToDegenerate F n = simplicialReplacementRowLatchingLeg F n s
```

#### SimplicialReplacementRowNormalization（50行）

```lean
theorem simplicialReplacement_degenerate_presentation {n : ℕ}
    (σ : ComposableArrows I n) (hσ : σ ∈ (nerve I).degenerate n) :
    ∃ (m : ℕ) (_ : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi α)
      (τ : (nerve I).nonDegenerate m), σ = (nerve I).map α.op τ

def simplicialReplacementLatchingIndexOfEpi {m n : ℕ} (hm : m < n)
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] : LatchingIndex simplexOp (Opposite.op ⦋n⦌)

theorem simplicialReplacementLatchingIndexOfEpi_hom {m n : ℕ} (hm : m < n)
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] :
    (simplicialReplacementLatchingIndexOfEpi hm α).obj.hom = α.op
```

#### SimplicialReplacementRowLatchingSurjective（46行）

```lean
theorem simplicialReplacementRowLatching_jointly_surjective (q : SimplexCategoryᵒᵖ)
    (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    ∃ (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
      (x : ((simplicialReplacementRows F).obj j.obj.left).obj q),
      (simplicialReplacementRowLatchingLeg F n j).app q x = s
```

## 210. R03f.2の半分での実測（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2は未完了。

対象ビルド・小監査済み569行に、既存の非退化表示の次元・単体・全射の一意性を接続した個別検査済み38行を加えて607行となり、上端1,200行の半分600行に達した。38行の個別検査36596は終了0、対象ビルド・小監査280はまだ進行中であり、その分のLeanは未コミットに保つ。作業木を含む累計は8,796行／外枠15,000。

残りは余錐の余極限性、相対latchingの退化・非退化による分離、成分のleft anodyne性と対角への束ね。残り350〜600行、完成時957〜1,207行程度を見込む。元の見込み650〜1,200行の上端付近だが、§19の中間定理一つの1,500行と外枠にはまだ達しない。元の全写像のleft anodyne性を目標のままに保ち、弱同値性や条件つきの判定へ弱めない。新しい型・まとまりの変更はない。

## 211. 同じ非退化表示への因子分解の照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

任意の全射表示の元の単体を既存の非退化表示へ戻し、その二つの合成表示へ既存の次元・単体・全射の一意性を順に適用した。同じ元の非退化表示へ向かう全射γを得て、元の二つの全射についてβ≫γ＝α、元の表示された単体についてX.map γ.op τ＝υという二つの厳密な等式を併記した。既存の非退化表示の一意性の合成・照合であり、R03f.2の同じ証明の分割として扱う。新しい独立の数学的まとまりや仮定を足していない。

280：新規一本の対象ビルド1,649 jobs・終了0、小監査136本976宣言・標準三公理のみ。実ハンドル24681の終了0を確認し、鍵返却済み。個別検査36596も終了0。今回38行、累計136本・8,796行／外枠15,000。R03f.2は607行／見込み650〜1,200行。§210の半分の報告時に未検証だった分も、対象ビルドと小監査まで通った。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次の順序は、元の退化行の余錐の余極限性、相対latchingの分離、各係数のleft anodyne性と元の対角への輸送である。具体的には元のlatching余錐がIsColimitとなることを、§209の全射性と今回の二表示の共通表示で検証する。その後、相対latchingの始域を「標的Gの退化部分と始域Fの非退化部分の余積」へ同定する。相対latching射は、その表示では退化部分上の恒等射と非退化基底射列ごとの同じη.app iの余積となる。ここまでの一意性が全係数も含めて可換することを検収してから、left anodyne性と§207の対角の定理を適用する。余錐の被覆性や基底だけの一意性で余極限性を代用しない。

### 211.1 型（38行）

#### SimplicialReplacementRowCommonPresentation（38行）

```lean
theorem simplicialReplacement_common_nondegenerate_presentation {X : SSet.{u}} {n m k : ℕ}
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] (τ : X.nonDegenerate m)
    (β : ⦋n⦌ ⟶ ⦋k⦌) [Epi β] (υ : X.obj (Opposite.op ⦋k⦌))
    (h : X.map α.op τ = X.map β.op υ) :
    ∃ (γ : ⦋k⦌ ⟶ ⦋m⦌) (_ : Epi γ), β ≫ γ = α ∧ X.map γ.op τ = υ
```

## 212. 元のlatching余錐の余極限性と同じ退化部分の同型（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

前のターンは共通の非退化表示まで検証・コミット済みで進捗あり。開始時にcleanな作業木とe36070d9eを確認した。元の退化作用素が分裂単射であることと、同じ全射表示へ元の係数を回収する法則を示した。共通表示の全射を元のlatchingの射とし、その作用素で元の係数の単体を厳密に回収した。

任意の余錐の二つの表示を、同じ非退化基底表示へ係数ごと戻した。その退化作用素の単射性から、元の係数を含む同じ二つの単体が一致する。余錐の自然性により、任意の余錐で元の二表示の値が同じことを示した。元の被覆する脚から各単体の値を取り、この一致を使って自然な降下射・全脚での一致・一意性を構成した。元のlatching余錐のIsColimitと、実際のlatchingの余極限から同じ退化部分への全同型が得られた。

281：二本の対象ビルド1,652 jobs・終了0、小監査138本983宣言・標準三公理のみ（実ハンドル73674・終了0）。282：余錐の値と余極限の二本の対象ビルド1,654 jobs・終了0、小監査140本997宣言・標準三公理のみ（実ハンドル72177・終了0）。両方とも鍵返却済み。個別検査6095・87431・35572・30108の終了0を確認した。

今回49＋46＋70＋97＝262行、累計140本・9,058行／外枠15,000。R03f.2は869行。現状の残りは境界付きの各係数の持ち上げを行全体へ束ねる部分、元の相対latchingへの適用と対角への移送で300〜450行、完成時1,169〜1,319行程度と再見積もりする。当初の上端1,200行より増える可能性があるが、§19の中間定理一つ1,500行以内の見込みである。外枠も保持する。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

残りの短い経路は、相対latchingの大きな射の同型を別に作り直す代わりに、元の相対latchingの持ち上げ問題を直接解く方法である。退化基底成分では指定されたlatching境界の値を保持し、それ以外の成分では元のη.app iのleft anodyne性で持ち上げ、元の余積から行全体へ降下する。境界の制限と両脚が厳密に一致することを検収し、元の相対latching射のleft anodyne性へ戻す。R03f.2の型・範囲を変えず、条件つきの判定へ弱めない。

### 212.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。余錐の法則ではさらに `(n : ℕ)` を用いる。`c` は元のlatching図式の任意の余錐。

#### SimplicialReplacementRowEpiLifts（49行）

```lean
theorem simplicialReplacementRowReindex_mono {m n : SimplexCategory} (α : m ⟶ n) [Epi α] :
    Mono (simplicialReplacementRowReindex F α)

theorem simplicialReplacementRowReindex_lift {m n : SimplexCategory} (α : m ⟶ n) [Epi α]
    (τ : ComposableArrows I n.len) (q : SimplexCategoryᵒᵖ)
    (x : (simplicialReplacementRow F m.len).obj q)
    (h : (nerve I).map α.op τ = x.1) :
    ∃ y : (F.obj (τ.obj 0)).obj q,
      (simplicialReplacementRowReindex F α).app q ⟨τ,y⟩ = x
```

#### SimplicialReplacementRowLatchingRefinement（46行）

```lean
def simplicialReplacementLatchingRefinement (hm : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α]
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) (γ : j.obj.left.unop ⟶ ⦋m⦌)
    (h : j.obj.hom.unop ≫ γ = α) : simplicialReplacementLatchingIndexOfEpi hm α ⟶ j

theorem simplicialReplacementRowLatching_refine (q : SimplexCategoryᵒᵖ)
    (hm : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] (τ : (nerve I).nonDegenerate m)
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (h : (nerve I).map α.op τ =
      (((simplicialReplacementRows F).map j.obj.hom).app q x).1) :
    ∃ (f : simplicialReplacementLatchingIndexOfEpi hm α ⟶ j)
      (y : (F.obj (τ.val.obj 0)).obj q),
      ((simplicialReplacementRows F).map f.hom.left).app q ⟨τ.val,y⟩ = x
```

#### SimplicialReplacementRowLatchingValues（70行）

```lean
theorem simplicialReplacementRowLatching_value_map
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) {j k : LatchingIndex simplexOp (Opposite.op ⦋n⦌)} (f : j ⟶ k)
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (y : ((simplicialReplacementRows F).obj k.obj.left).obj q)
    (h : ((simplicialReplacementRows F).map f.hom.left).app q x = y) :
    (c.ι.app j).app q x = (c.ι.app k).app q y

theorem simplicialReplacementRowLatching_values_eq
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (j k : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (y : ((simplicialReplacementRows F).obj k.obj.left).obj q)
    (h : (simplicialReplacementRowLatchingLeg F n j).app q x =
      (simplicialReplacementRowLatchingLeg F n k).app q y) :
    (c.ι.app j).app q x = (c.ι.app k).app q y
```

#### SimplicialReplacementRowLatchingColimit（97行）

```lean
theorem simplicialReplacementRowLatching_exists_value
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    ∃ v : c.pt.obj q, ∀ (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
      (x : ((simplicialReplacementRows F).obj j.obj.left).obj q),
      (simplicialReplacementRowLatchingLeg F n j).app q x = s → (c.ι.app j).app q x = v

def simplicialReplacementRowLatchingValue
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    c.pt.obj q

theorem simplicialReplacementRowLatchingValue_fac
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q) :
    simplicialReplacementRowLatchingValue F n c q
      ((simplicialReplacementRowLatchingLeg F n j).app q x) = (c.ι.app j).app q x

def simplicialReplacementRowLatchingDesc
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F)) :
    (simplicialReplacementDegenerateRow F n : SSet.{u}) ⟶ c.pt

def simplicialReplacementRowLatchingIsColimit :
    IsColimit (simplicialReplacementRowLatchingCocone F n)

def simplicialReplacementRowLatchingIso :
    colimit (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) ≅
      simplicialReplacementDegenerateRow F n
```

## 213. R03f.2完了：元のsimplicial replacementのleft anodyne性（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 8／全体 21（うち追加 9）。R03f.2完了。R03f・R03d・R02・R03は未完了。

元の各行と指定部分の包含・係数射・降下の法則を明示した。退化基底成分では元の指定境界の値を固定し、それ以外の成分では元の同じη.app iのleft anodyne性で持ち上げた。元の余積から行全体へ降下させ、元の二つの脚と退化境界の値を厳密な等式で保持する持ち上げを得た。

実際のlatchingと退化部分の同型が、元の係数射と境界比較を厳密に保つことも全ての脚で照合した。元の相対latchingのpushoutの持ち上げ問題では、その逆同型で指定境界を取り出し、行全体の境界付き持ち上げを適用した。pushoutの二つの包含で元の脚を回収することを検収し、元の相対latching射そのもののleft anodyne性を得た。

このReedy left anodyne性を§207の対角の定理へ送り、同じ係数射についての対角同型の自然性で、元のsimplicialReplacementMapそのものへ移した。§206の型を変更せずに閉じた。相対latchingの別の大きな射の同型を作り直す部分は、同じ元のpushoutの直接の持ち上げに置き換えた。元の標的の性質や主張の型を弱める変更ではない。

283：包含の法則・境界の成分・境界付きの行全体の持ち上げ・latching自然性の四本の対象ビルド1,658 jobs・終了0、小監査144本1,014宣言・標準三公理のみ（実ハンドル81758・終了0）。284：元の相対latchingの持ち上げと最後のR03f.2の二本の対象ビルド1,661 jobs・終了0、小監査146本1,017宣言・標準三公理のみ（実ハンドル64724・終了0）。両方とも鍵返却済み。個別検査29337・4919・25258の終了0を確認した。

今回85＋56＋60＋82＋95＋30＝408行、累計146本・9,466行／外枠15,000。R03f.2は1,277行。§206の当初見込み650〜1,200行の上端との差＋77行、§212の再見積もり1,169〜1,319行の範囲内。§19の中間定理一つ1,500行との差−223行である。計算上限の変更なし、sorry・独自公理0。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次は元のEx∞単位のbar上のleft anodyne性に適用し、元のscaffoldの同じ正方形と元の置換単位を固定した延長をつなぐ。延長の前合成同値性（R03f）と元の共同Hom比較（R03d）はなお別の未完了項目であり、R03f.2だけでnative極限性が得られたとは扱わない。

### 213.1 型

共通入力は `{I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}`。境界付きの持ち上げの共通入力は以下のとおり。証明でのみ用いる `hη sq hd ha` もincludeで宣言の前提に明示的に含めている。

```lean
(η : F ⟶ G) (hη : ∀ i, leftAnodyneExtensions (η.app i)) (n : ℕ)
{E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
(a : simplicialReplacementRow F n ⟶ E) (b : simplicialReplacementRow G n ⟶ B)
(d : (simplicialReplacementDegenerateRow G n : SSet.{u}) ⟶ E)
(sq : CommSq a (simplicialReplacementRowMap η n) p b)
(hd : d ≫ p = (simplicialReplacementDegenerateRow G n).ι ≫ b)
(ha : simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫ d =
  (simplicialReplacementDegenerateRow F n).ι ≫ a)
```

#### SimplicialReplacementRowInclusionLaws（85行）

```lean
def simplicialReplacementRowPartInclusion (F : I ⥤ SSet.{u}) (P : Set (ComposableArrows I n))
    (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    F.obj (σ.obj 0) ⟶ simplicialReplacementRowPart F n P

theorem simplicialReplacementRowPartInclusion_inclusion (F : I ⥤ SSet.{u})
    (P : Set (ComposableArrows I n)) (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    simplicialReplacementRowPartInclusion n F P σ hσ ≫ (simplicialReplacementRowPart F n P).ι =
      simplicialReplacementRowInclusion F n σ

theorem simplicialReplacementRowPartInclusion_map (η : F ⟶ G)
    (P : Set (ComposableArrows I n)) (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    η.app (σ.obj 0) ≫ simplicialReplacementRowPartInclusion n G P σ hσ =
      simplicialReplacementRowPartInclusion n F P σ hσ ≫ simplicialReplacementRowPartMap η n P

theorem simplicialReplacementRowInclusion_map (η : F ⟶ G) (σ : ComposableArrows I n) :
    simplicialReplacementRowInclusion F n σ ≫ simplicialReplacementRowMap η n =
      η.app (σ.obj 0) ≫ simplicialReplacementRowInclusion G n σ

theorem simplicialReplacementRow_hom_ext {E : SSet.{u}}
    (f g : simplicialReplacementRow F n ⟶ E)
    (h : ∀ σ, simplicialReplacementRowInclusion F n σ ≫ f =
      simplicialReplacementRowInclusion F n σ ≫ g) : f = g

theorem simplicialReplacementRowDesc_inclusion
    (s : Cofan (fun σ : ComposableArrows I n => F.obj (σ.obj 0))) (σ : ComposableArrows I n) :
    simplicialReplacementRowInclusion F n σ ≫ simplicialReplacementRowDesc F n s = s.inj σ

theorem simplicialReplacementRowPart_hom_ext (P : Set (ComposableArrows I n)) {E : SSet.{u}}
    (f g : (simplicialReplacementRowPart F n P : SSet.{u}) ⟶ E)
    (h : ∀ σ hσ, simplicialReplacementRowPartInclusion n F P σ hσ ≫ f =
      simplicialReplacementRowPartInclusion n F P σ hσ ≫ g) : f = g
```

#### SimplicialReplacementRowBoundaryComponents（56行）

```lean
theorem simplicialReplacementRowBoundary_component (σ : ComposableArrows I n) :
    ∃ l : G.obj (σ.obj 0) ⟶ E,
      η.app (σ.obj 0) ≫ l = simplicialReplacementRowInclusion F n σ ≫ a ∧
      l ≫ p = simplicialReplacementRowInclusion G n σ ≫ b ∧
      ∀ hσ : σ ∈ (nerve I).degenerate n,
        l = simplicialReplacementRowPartInclusion n G ((nerve I).degenerate n) σ hσ ≫ d
```

#### SimplicialReplacementRowBoundaryLift（60行）

```lean
theorem simplicialReplacementRowBoundary_lift :
    ∃ l : simplicialReplacementRow G n ⟶ E,
      simplicialReplacementRowMap η n ≫ l = a ∧ l ≫ p = b ∧
      (simplicialReplacementDegenerateRow G n).ι ≫ l = d
```

#### SimplicialReplacementRowLatchingNaturality（82行）

```lean
theorem simplicialReplacementRowLatchingIso_hom (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).hom = simplicialReplacementLatchingToDegenerate F n

theorem simplicialReplacementRowLatchingIso_inclusion (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).hom ≫ (simplicialReplacementDegenerateRow F n).ι =
      (latchingComparison simplexOp (Opposite.op ⦋n⦌)).app (simplicialReplacementRows F)

theorem simplicialReplacementRowLatchingLeg_map {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    simplicialReplacementRowMap η j.obj.left.unop.len ≫ simplicialReplacementRowLatchingLeg G n j =
      simplicialReplacementRowLatchingLeg F n j ≫
        simplicialReplacementRowPartMap η n ((nerve I).degenerate n)

theorem simplicialReplacementRowLatchingIso_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    (latchingEvaluation simplexOp (Opposite.op ⦋n⦌)).map (simplicialReplacementRowsMap η) ≫
      (simplicialReplacementRowLatchingIso G n).hom =
    (simplicialReplacementRowLatchingIso F n).hom ≫
      simplicialReplacementRowPartMap η n ((nerve I).degenerate n)

theorem simplicialReplacementRowLatchingIso_inv_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫
      (simplicialReplacementRowLatchingIso G n).inv =
    (simplicialReplacementRowLatchingIso F n).inv ≫
      (latchingEvaluation simplexOp (Opposite.op ⦋n⦌)).map (simplicialReplacementRowsMap η)

theorem simplicialReplacementRowLatchingIso_inv_inclusion (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).inv ≫
      (latchingComparison simplexOp (Opposite.op ⦋n⦌)).app (simplicialReplacementRows F) =
      (simplicialReplacementDegenerateRow F n).ι
```

#### SimplicialReplacementReedyLeftAnodyne（95行）

```lean
theorem simplicialReplacementRowsMap_relative_leftAnodyne (n : ℕ) :
    leftAnodyneExtensions (relativeLatchingMap simplexOp (Opposite.op ⦋n⦌)
      (simplicialReplacementRowsMap η))

theorem simplicialReplacementRowsMap_reedy_leftAnodyne :
    reedyLeft simplexOp leftAnodyneExtensions (simplicialReplacementRowsMap η)
```

#### SimplicialReplacementLeftAnodyne（30行）

```lean
theorem simplicialReplacementMap_leftAnodyne
    {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}
    (η : F ⟶ G) (hη : ∀ i, leftAnodyneExtensions (η.app i)) :
    leftAnodyneExtensions (simplicialReplacementMap η)
```

## 214. 元のEx∞係数単位のbar上のleft anodyne性（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 8／全体 21（うち追加 9）。R03f・R03d・R02・R03は未完了。

R03f.2を元のgrothendieckKanCoefficientUnitと元のexInfinityUnit_leftAnodyneへ適用した。同じCat図式の同じEx∞単位からのsimplicialReplacementMapそのものがleft anodyneである。既存の単位の性質の適用であり、新しい中間の数学的定理の追加ではない。

285：新規一本の対象ビルド1,948 jobs・終了0、小監査147本1,018宣言・標準三公理のみ。実ハンドル4709の終了0を確認し、鍵返却済み。個別検査99542も終了0。今回29行、累計147本・9,495行／外枠15,000。実ファイルの機械的な再集計で、§213のBoundaryComponentsの一行の誤算を修正した。R03f.2は21本1,277行、§213までの累計は9,466行。主張や型の変更ではない。

元のscaffoldの同じ正方形へこのleft anodyne性をつなぐため、既存のRelativeFunctorOverEquivalence.relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalenceを確認した。標的がquasicategoryなら、定義域の充填性や比較射の単射性を課さず、任意のleft fibrationへの同じ相対関手空間の制限が同値である。cofinalFunctorSpace/cofinalFunctorPreは同じfiberと前合成で定義されているため、この既存の定理を同じ構成の定義の照合でcofinal性の検査へ移す短い経路を試す。未検証の照合を仮定として使わない。

sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 214.1 型（29行）

#### GrothendieckKanBarLeftAnodyne（29行）

```lean
theorem grothendieckKanCoefficientBarMap_leftAnodyne
    {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) :
    leftAnodyneExtensions (simplicialReplacementMap (grothendieckKanCoefficientUnit F))
```

## 215. 元の比較射と指定単位を固定する延長のcofinal性（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 8／全体 21（うち追加 9）。R03f・R03d・R02・R03は未完了。

既存のRelativeFunctorOverEquivalence.relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalenceを、同じfiberと前合成で定義されたcofinalFunctorPreへ照合した。quasicategoryを標的とする元の前合成同値が、その同じ射のleft cofinal性の検査を満たすことを、定義の照合と既存のKan相対関手空間の同値の検出だけで得た。新しい数学的な検出条件を仮定していない。

これを元のbar/scaffold正方形へ適用した。元のEx∞単位のbarの射のleft anodyne性、その後のKan係数のscaffoldの前合成同値性、元のCat係数からGrothendieck射列へのscaffoldの前合成同値性を、同じ厳密な正方形の等式と既存のleft cofinalな射の合成・消去則へ渡した。元のgrothendieckKanCoefficientMapそのもののleft cofinal性が得られた。さらに元の置換単位はleft anodyneなので、その同じ単位との合成が元の比較射に等しい任意の延長もleft cofinalとなる。元の比較の射や単位を取り替えていない。

286：定義の照合一本の対象ビルド1,794 jobs・終了0、小監査148本1,019宣言・標準三公理のみ（実ハンドル97086・終了0）。287：元の比較と延長のcofinal性一本の対象ビルド2,492 jobs・終了0、小監査149本1,021宣言・標準三公理のみ（実ハンドル14853・終了0）。両方とも鍵返却済み。個別検査34355・14467の終了0を確認した。

今回28＋57＝85行、累計149本・9,580行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。cofinal性だけから任意の射の前合成同値性を主張しない。残りは、同じ底上のleft fibration間の射としてその検出を行う部分である。

### 215.1 型

Grothendieck側の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### PrecompositionCofinality（28行）

```lean
theorem isLeftCofinal_of_precompositionEquivalence
    {X Y : SSet.{u}} [Quasicategory Y] (f : X ⟶ Y) (hf : IsPrecompositionEquivalence f) :
    IsLeftCofinal f
```

#### GrothendieckKanComparisonCofinality（57行）

```lean
theorem grothendieckKanCoefficientMap_isLeftCofinal :
    IsLeftCofinal (grothendieckKanCoefficientMap F)

theorem grothendieckKanCoefficientLift_isLeftCofinal :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∀ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F → IsLeftCofinal f
```

## 216. R03f.3：同じ底上のleft fibration間のcofinal射の検出（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 8／全体 22（うち追加 10）。R03f.3を追加、未証明。

§19の同じまとまり・一つの見込み1,500行以内の枠により、次の独立の中間定理を加える。任意のcofinal射が圏同値だと主張するものではない。同じ底への二つの射が両方ともleft fibrationであり、元の比較射がその底を厳密に保つことを型に持つ。

```lean
theorem isPrecompositionEquivalence_of_leftCofinal_overLeftFibrations
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (hc : IsLeftCofinal f) :
  IsPrecompositionEquivalence f
```

このPropの型は `/private/tmp/CheckISW2CofinalLeftFibComparisonType.lean` で確認した（実ハンドル83289・終了0）。未証明の宣言や仮定を本体へ入れない。置き場所はKerodon/LimitsAndColimits/Cofinality/LeftFibrationComparison.leanなど、一般の同じ底上の検出の節とする。

見込み250〜650行。既存IsLeftCofinal.restrictDiagramを任意の試験left fibrationと同じ底図式qへ適用すると、同じ底上の相対Homの前合成がホモトピー同値となる。試験標的pで恒等射を戻し、逆向きの実射を取る。試験標的qでの同じ前合成の忠実性を使い、二つの合成を同じ恒等射へ結ぶ。相対HomはKanなので、同じ底上の同値の二つの三角形として扱える。元の底がquasicategoryであるため、二つの全空間もquasicategoryである。相対Homから通常の関手空間への同じ包含で三角形を送り、既存の前合成同値のホモトピー逆の判定へ戻す。必要ならisPrecompositionEquivalence_of_homotopyInverseと、各頂点での垂直な辺の可逆性の既存の判定を使う。

これは同じモデルのままcofinal性を前合成同値へ検出する数学的な部分であり、§215の定義の照合の法則として数えない。独立の定理として一つに見積もり、§19の枠を細分で回避しない。半分325行で実測と残りを報告する。

R03f.3が証明できた後に限り、§201の元の単位を固定する延長へ、元の同じ射影の等式と§215のcofinal性を代入し、R03fの全空間の前合成同値を検収する。これがまだ未証明の間はR03f・R03d・native極限性を完了と扱わない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤aの欄を変更しない。

## 217. R03f.3とR03fの完了：同じ底と指定単位を保つ比較（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03f.3・R03fを完了。R03d・R02・R03とnative極限性は未完了。

R03f.3は74行で閉じた（見込み250〜650行、上端との差−576行）。相対Homの前合成を既存のcofinal性の検査へ定義どおり照合し、Kan空間の同値に戻した。試験標的pで恒等射を戻して元の底上の逆向きの射gを取り、単位の同型を得る。この同型を通常の関手空間へ忘れる前に、元の底上の後合成relativeFunctorPostでqへの相対Homへ送った。そこで同じ前合成の充満忠実性から余単位を戻す。最後に二つの相対Homの包含で通常のFunctorIsoへ送り、既存のQCatEquivalenceと前合成同値の判定へ渡した。一般のcofinalな射を同値と扱わず、同じ底上の二つのleft fibrationという仮定を使っている。新しいホモトピーの構成や計算上限の引き上げは不要だった。325行の途中報告点に達する前に全証明が閉じた。

元のgrothendieckKanCoefficientLiftへこの検出を適用し、同じ元の射影と置換単位を固定する任意の延長が前合成同値であることを示した。exists_grothendieckKanCoefficientComparisonは§200のR03fの型どおり、元の比較射を延長し、二つの厳密な等式と元の射自身の前合成同値性を同時に持つ。grothendieckKanCoefficientMapは元のgrothWeightedNerveForwardと元のEx∞係数単位のweightedNerveMapの合成を定義に持ち、取り替えていない。

個別検査LeftFibrationComparison（実ハンドル93403）とGrothendieckKanCoefficientComparison（47447）は終了0。288：検出補題の対象ビルド2,208 jobs・終了0、小監査150本1,023宣言・標準三公理のみ（実ハンドル92698・終了0）。289：元の比較と検出補題の対象ビルド2,636 jobs・終了0、小監査151本1,025宣言・標準三公理のみ（実ハンドル67835・終了0）。鍵は返却済み。今回74＋50＝124行、累計151本・9,704行／外枠15,000。証明のコミットは893ee7a94。

sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次は同じ比較を既存のleftClassification_of_precompositionEquivalenceへ渡し、底全体の分類比較を組み立てる。R03dで要求される元の固定始域比較との等式と、native極限性を先取りして完了としない。

### 217.1 型

補助の相対前合成の照合とR03f.3の適用は既存構成の法則・適用であり、別の数学的な一覧項目は増やしていない。Grothendieck側の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### LeftFibrationComparison（74行）

```lean
lemma IsLeftCofinal.relativeFunctorOverPre_isQCatEquivalence
    {T E F B : SSet.{u}} (r : T ⟶ B) [LeftFibration r]
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (hc : IsLeftCofinal f) :
    IsQCatEquivalence (relativeFunctorOverPre r (show Over.mk p ⟶ Over.mk q from Over.homMk f hf))

theorem isPrecompositionEquivalence_of_leftCofinal_overLeftFibrations
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (hc : IsLeftCofinal f) :
    IsPrecompositionEquivalence f
```

#### GrothendieckKanCoefficientComparison（50行）

```lean
theorem grothendieckKanCoefficientLift_isPrecompositionEquivalence :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∀ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      f ≫ weightedNerveProjection (grothendieckKanCoefficients F) = R.hom →
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F → IsPrecompositionEquivalence f

theorem exists_grothendieckKanCoefficientComparison :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∃ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      f ≫ weightedNerveProjection (grothendieckKanCoefficients F) = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F ∧ IsPrecompositionEquivalence f
```

## 218. 同じKan係数の全図式と元のnative全分類の接続（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

元のR03fの存在から一つの底上の比較射を選び、同じ射について射影・単位の二つの厳密な等式と前合成同値性を記録した。これを既存のleftClassification_of_precompositionEquivalenceへ渡し、底全体のnative分類のFunctorIsoを得た。対象ごとに同型を選んだものではない。

native分類とstrict transportの分類の接続には短い既存の経路があった。同じnerve上の射影pに対して、leftStraighteningInfinityDiagram_representationIsoとnerveStraighteningRepresentationIsoの両方を、同じnerveLeftTransportRepresentation pへ適用する。二つの全関手同型の合成だけでnative分類と候補を比較できる。その後、元のweightedNerveStraighteningUnitIsoを合成する。同じEx∞係数をKanObject値へ記録し直してこれを適用し、その同じ全係数図式から元のGrothendieck置換のnative分類への全FunctorIsoができた。この部分は既存の分類移送・単位・合成の法則であり、新しい独立の数学的な一覧項目は増やしていない。

個別検査：GrothendieckKanClassificationの最初の版96770・終了0、native/strict分類の接続61750・終了0、二本を結合した最終版17493・終了0。290：最初の版の対象ビルド3,328 jobs・終了0、小監査152本1,033宣言・標準三公理のみ（実ハンドル79144・終了0）。291：最終版の二本と直接importerの対象ビルド3,329 jobs・終了0、小監査153本1,045宣言・標準三公理のみ（実ハンドル61295・終了0）。鍵返却済み。今回87＋41＝128行、累計153本・9,832行／外枠15,000。

sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。残る正規化では、sourceFrameElementsFamilyのfiberが元のElementsの反対圏であることと、全SourceFrameArrowElementsのfiberの向きを区別する。次に既存のKan係数のedgewise反転比較・Ex∞単位・反転の弱同値保存を全図式へ合成する係数移送の法則を試す。型の案は次のとおり（見込み100〜220行）。

```lean
def kanHomFamilyOppositeComparisonIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    FunctorIso (kanHomFamilyCoherent F)
      (kanHomFamilyCoherent (F ⋙ SSet.opFunctor))
```

ここで反転するのは値の単体集合のみで、底Cとその全射は保つ。元の係数FへEx∞単位を適用し、その反転と同じEx∞によるKan化を取る。Kan化後の値とその反転の比較には既存kanDiagramOppositeComparisonIsoを使い、同じ二つの自然変換の反転可能性を全関手圏で合成する。単純にFとF.opが厳密に同じとはしない。元のroof比較との等式が証明できるまでR03dを完了と扱わない。

### 218.1 型

Grothendieck側の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### GrothendieckKanClassification（87行）

```lean
def grothendieckKanCoefficientComparison :
    ((continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ⟶
        weightedNerve (grothendieckKanCoefficients F)

theorem grothendieckKanCoefficientComparison_projection :
    grothendieckKanCoefficientComparison F ≫
      weightedNerveProjection (grothendieckKanCoefficients F) =
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom

theorem grothendieckKanCoefficientComparison_unit :
    ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ≫
        grothendieckKanCoefficientComparison F = grothendieckKanCoefficientMap F

theorem grothendieckKanCoefficientComparison_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (grothendieckKanCoefficientComparison F)

def grothendieckKanReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom)
      (leftStraighteningInfinityDiagram
        (weightedNerveProjection (grothendieckKanCoefficients F)))

def grothendieckKanCoefficientDiagram : I ⥤ KanObject.{u}

def grothendieckKanNativeClassificationUnitIso :
    FunctorIso (kanDiagramCoherentNerve (grothendieckKanCoefficientDiagram F))
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom)
```

#### NativeNerveStraighteningComparison（41行）

```lean
def leftStraighteningInfinityDiagram_nerveCandidateIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningCandidate p)

def weightedNerveNativeStraighteningUnitIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (leftStraighteningInfinityDiagram (weightedNerveProjection (F ⋙ kanObjectForget)))
```

## 219. 全係数の反転と元の反対要素nerveの終端augmentationの接続（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§218の係数移送の法則を75行で閉じた（見込み100〜220行）。既存kanDiagramOppositeComparisonIsoでKan化後の値だけを反転し、元のEx∞単位とその反転の全自然変換をKan化した全関手同型を合成した。反転した単位の弱同値性は既存opposite_map_isWeakHomotopyEquivalenceを使う。底の圏や全作用素を変えず、値ごとに逆射を選ばない。

次に、既存nerveOppositeMap_naturalityと同じnerveOppositeIsoを全Cat図式に適用し、元のnerveと反対圏のnerveのKan化の全FunctorIsoを50行で記録した。元の全要素nerveの比較では、既存SimplexNerve.functorとSimplexTerminalNerve.functor、同じoppositeIsoをそのまま使う。これらに同じ全係数図式Fを前合成し、元のaugmentationの自然変換と既存augmentation_localized_isIsoをKan化して、元の全要素nerveの係数から元のFの係数への全FunctorIsoを76行で得た。新しい要素圏や反転模型を構成しておらず、既存構成の単位・自然性・係数移送・合成の法則として記録する。一覧の独立の数学的な項目は増やしていない。

この同型が元の固定始域のroof比較と同じものになるという等式はまだ証明していない。全要素圏のfiberと元の反対要素圏を取り違えず、元の単位・augmentation・roofへ戻る正規化はR03dの残りとして保つ。底全体のFunctorIsoは得られたが、これだけでR03d・R02・R03とnative極限性を完了とは扱わない。

個別検査：KanHomFamilyOpposite70713・終了0、KanNerveOppositeFamily90441・終了0、KanElementsFamily28433・終了0。292は必要な既存二モジュールだけの対象ビルド2,729 jobs・終了0（実ハンドル58640）。293：反転係数の対象ビルド2,802 jobs・終了0、小監査154本1,056宣言・標準三公理のみ（86257・終了0）。294：全Cat図式の反転の対象ビルド2,804 jobs・終了0、小監査155本1,064宣言・標準三公理のみ（85024・終了0）。295：全要素nerveの係数移送の対象ビルド2,934 jobs・終了0、小監査156本1,078宣言・標準三公理のみ（33179・終了0）。いずれも鍵をビルド・小監査の間だけ取り、終了と返却を確認した。

今回75＋50＋76＝201行、累計156本・10,033行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。今後は元の全source frameの要素圏をR03fの同じ底の分類へ接続し、同じ全augmentationの逆からのtwisted pairingと照合する。

### 219.1 型

全係数の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`、全Cat図式の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### KanHomFamilyOpposite（75行）

```lean
lemma kanHomFamilyUnit_isWeakHomotopyEquivalence (X : SSet.{u}) :
    IsWeakHomotopyEquivalence (exInfinityUnit.app X)

def kanDiagramExInfinityUnitIso {C : Type u} [Category.{u} C]
    (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (kanHomFamilyCoherent (F ⋙ kanObjectForget))

def kanHomFamilyOppositeUnit {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    F ⋙ SSet.opFunctor ⟶ (kanHomFamily F ⋙ kanObjectOpFunctor) ⋙ kanObjectForget

def kanHomFamilyOppositeUnitIso {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    FunctorIso (kanHomFamilyCoherent (F ⋙ SSet.opFunctor))
      (kanHomFamilyCoherent ((kanHomFamily F ⋙ kanObjectOpFunctor) ⋙ kanObjectForget))

def kanHomFamilyOppositeComparisonIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    FunctorIso (kanHomFamilyCoherent F)
      (kanHomFamilyCoherent (F ⋙ SSet.opFunctor))
```

#### KanNerveOppositeFamily（50行）

```lean
def catNerveOppositeFamilyMap :
    (F ⋙ nerveFunctor) ⋙ SSet.opFunctor ⟶ (F ⋙ Cat.opFunctor) ⋙ nerveFunctor

lemma catNerveOppositeFamilyMap_weak (i : I) :
    IsWeakHomotopyEquivalence ((catNerveOppositeFamilyMap F).app i)

def catNerveOppositeFamilyUnitIso :
    FunctorIso (kanHomFamilyCoherent ((F ⋙ nerveFunctor) ⋙ SSet.opFunctor))
      (kanHomFamilyCoherent ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor))

def catNerveOppositeFamilyIso :
    FunctorIso (kanHomFamilyCoherent (F ⋙ nerveFunctor))
      (kanHomFamilyCoherent ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor))
```

#### KanElementsFamily（76行）

```lean
abbrev simplexElementsNerveDiagram : I ⥤ SSet.{u}

def simplexElementsOppositeNerveIso :
    (simplexElementsNerveDiagram F) ⋙ SSet.opFunctor ≅ F ⋙ SimplexTerminalNerve.functor

def simplexElementsOppositeNerveKanIso :
    FunctorIso (kanHomFamilyCoherent ((simplexElementsNerveDiagram F) ⋙ SSet.opFunctor))
      (kanHomFamilyCoherent (F ⋙ SimplexTerminalNerve.functor))

def simplexElementsOppositeAugmentation : F ⋙ SimplexTerminalNerve.functor ⟶ F

lemma simplexElementsOppositeAugmentation_weak (i : I) :
    IsWeakHomotopyEquivalence ((simplexElementsOppositeAugmentation F).app i)

def simplexElementsOppositeAugmentationIso :
    FunctorIso (kanHomFamilyCoherent (F ⋙ SimplexTerminalNerve.functor))
      (kanHomFamilyCoherent F)

def simplexElementsKanAugmentationIso :
    FunctorIso (kanHomFamilyCoherent (simplexElementsNerveDiagram F))
      (kanHomFamilyCoherent F)
```

## 220. 全要素圏の同じGrothendieck表示と、元の置換の係数移送則（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

元の全係数Fの各要素圏を、Homだけ同じ宇宙へ持ち上げてCat値図式にした。そのGrothendieck構成と、Fをuncurryした全二重添字の要素圏は、同じ底・単体次数・ラベルと同じ元の射を並べ直す圏同値である。順方向・逆方向、単位・余単位の全自然性、元の底への二つの射影の厳密な等式を148行で示した。比較を自由な圏同値として選んだものではなく、両方向とも元のラベルと元の底の射・単体作用素を保つ。Grothendieckの合成に含まれる等式輸送は、元の単体次数への射影関手のmap_comp・eqToHom_mapで計算した。同じ二つの既存の構成の表示の照合であり、新しい数学的な一覧項目は増やしていない。

次に、既存の連続left-fibration置換が元のcofinalな底上の射を前合成同値へ送ることを46行で記録した。元の置換単位の自然性を同じ全空間の射の等式として使い、元の単位のleft anodyne性、cofinal性の合成・消去則、検証済みR03f.3の同じ底上の検出を合成した。置換も単位も選び直していない。標的の全空間が準圏である場合の、元の底上の前合成同値を移す版も付けた。この仮定は型に明記し、任意の非準圏の標的で同じ検出ができるとは主張していない。これは元の置換関手・単位の自然性と同じ底上の移送の法則であり、独立の数学的な一覧項目は増やしていない。

個別検査：全要素圏の圏同値と射影の最終版13688・終了0、元の置換の移送則79822・終了0。296：全要素圏のGrothendieck表示の対象ビルド1,125 jobs・終了0、小監査157本1,102宣言・標準三公理のみ（実ハンドル89214・終了0）。297：元の置換の移送則の対象ビルド2,219 jobs・終了0、小監査158本1,104宣言・標準三公理のみ（実ハンドル88369・終了0）。鍵返却済み。

今回148＋46＝194行、累計158本・10,227行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次は、この同じ圏同値のnerveを同じ底のOverの射とし、元の置換へ送ってR03fの全分類へ接続する。元の固定始域のroof比較との等式は依然R03dの残りであり、native極限性の完了は主張しない。

### 220.1 型

全係数の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。

#### SimplicialElementsGrothendieck（148行）

```lean
def simplicialElementsCatDiagram : I ⥤ Cat.{u,u}

abbrev SimplicialTotalElements

def simplicialTotalElementsProjection : SimplicialTotalElements F ⥤ I

lemma uliftElements_eqToHom_hom {K : SSet.{u}} {x y : ULiftHom.{u} K.Elements}
    (h : x = y) : (eqToHom h).down.hom = eqToHom (congrArg (fun z => z.obj) h)

def simplicialElementsGrothendieckForward :
    Grothendieck (simplicialElementsCatDiagram F) ⥤ SimplicialTotalElements F

def simplicialElementsGrothendieckObject (X : SimplicialTotalElements F) :
    Grothendieck (simplicialElementsCatDiagram F)

def simplicialElementsGrothendieckHom {X Y : SimplicialTotalElements F} (f : X ⟶ Y) :
    simplicialElementsGrothendieckObject F X ⟶ simplicialElementsGrothendieckObject F Y

def simplicialElementsGrothendieckInverse :
    SimplicialTotalElements F ⥤ Grothendieck (simplicialElementsCatDiagram F)

def simplicialElementsGrothendieckEquivalence :
    Grothendieck (simplicialElementsCatDiagram F) ≌ SimplicialTotalElements F

theorem simplicialElementsGrothendieckForward_projection :
    simplicialElementsGrothendieckForward F ⋙ simplicialTotalElementsProjection F =
      Grothendieck.forget (simplicialElementsCatDiagram F)

theorem simplicialElementsGrothendieckInverse_projection :
    simplicialElementsGrothendieckInverse F ⋙ Grothendieck.forget (simplicialElementsCatDiagram F) =
      simplicialTotalElementsProjection F
```

#### ContinuousLeftFibrationEquivalenceMap（46行）

```lean
theorem continuousLeftFibrationReplacement_map_isPrecompositionEquivalence_of_leftCofinal
    {B : SSet.{u}} [Quasicategory B] {X Y : Over B} (f : X ⟶ Y)
    (hc : IsLeftCofinal f.left) :
    IsPrecompositionEquivalence ((continuousLeftFibrationReplacement B).map f).left

theorem continuousLeftFibrationReplacement_map_isPrecompositionEquivalence
    {B : SSet.{u}} [Quasicategory B] {X Y : Over B} [Quasicategory Y.left]
    (f : X ⟶ Y) (hf : IsPrecompositionEquivalence f.left) :
    IsPrecompositionEquivalence ((continuousLeftFibrationReplacement B).map f).left
```

## 221. 元の全要素圏の置換単位を保つnative全分類への接続（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§220の同じ圏同値の逆方向のnerveを、同じ底nerve I上のOverの射にした。元の射そのものの前合成同値性は既存nerveQCatEquivalenceに同じ圏同値を渡して得た。次に元のcontinuousLeftFibrationReplacementでこの同じOverの射を送り、元の二つの置換単位との厳密な正方形を、その同じ単位の自然性から得た。§220の置換の移送則と既存leftClassification_of_precompositionEquivalenceを適用し、全要素圏の元の置換のnative分類と同じGrothendieck表示の元の置換のnative分類を、底全体のFunctorIsoで比較した。

これにR03fから得た同じGrothendieck係数の全分類単位を合成した。得られたsimplicialElementsNativeClassificationUnitIsoの始域は、各要素圏のHomを持ち上げた同じCat図式から来るgrothendieckKanCoefficientDiagramであり、終域は元の全二重添字の要素圏の元の置換のnativeな全分類である。元のFそのもののKan化と厳密に同じとは主張していない。Homの宇宙持ち上げを既存の全nerve同型で外し、§219の反対要素nerveの同じaugmentationへつなぐ照合は、次の接続として残す。

同じ底上の圏同値・nerve・置換・分類移送・R03fの既存の構成を合成したものであり、独立の数学的な一覧項目は増やしていない。元の固定始域のroof比較との全FunctorIsoの等式は、依然R03dの残り。元の全augmentationの逆を使ったtwisted pairingと、この同じ全要素分類の単位を同じ底上で照合してから、その制限を元の固定始域比較へ戻す必要がある。各fiberの同値や底全体のFunctorIsoの存在だけで、その正規化の等式まで証明した扱いにはしない。

個別検査の最終版8707・終了0。298：対象ビルド3,336 jobs・終了0、小監査159本1,115宣言・標準三公理のみ（実ハンドル40611・終了0）。鍵返却済み。今回90行、累計159本・10,317行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 221.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。

#### SimplicialElementsClassification（90行）

```lean
def simplicialElementsGrothendieckOverMap :
    Over.mk (nerveMap (simplicialTotalElementsProjection F)) ⟶
      Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F)))

theorem simplicialElementsGrothendieckOverMap_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (simplicialElementsGrothendieckOverMap F).left

def simplicialElementsGrothendieckReplacementMap

theorem simplicialElementsGrothendieckReplacementMap_unit :
    ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).left ≫
        (simplicialElementsGrothendieckReplacementMap F).left =
      (simplicialElementsGrothendieckOverMap F).left ≫
        ((continuousLeftFibrationReplacementUnit (nerve I)).app
          (Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F))))).left

theorem simplicialElementsGrothendieckReplacementMap_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (simplicialElementsGrothendieckReplacementMap F).left

def simplicialElementsGrothendieckReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F))))).hom)

def simplicialElementsNativeClassificationUnitIso :
    FunctorIso
      (kanDiagramCoherentNerve (grothendieckKanCoefficientDiagram (simplicialElementsCatDiagram F)))
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom)
```

## 222. 元の全係数図式へ戻したnative全要素分類（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§221の始域に残っていたHomの持ち上げを、元の同じ全射列へup・downを適用する実同型で外した。元の圏の関手への自然性も同じ射列で計算している。元のnerveと同じ宇宙で比較できるため、係数に新たな外側のULiftは入れない。既存のMixedNerveやNerveULiftHomは変更せず、一般の宇宙の表記で同じup・downの法則を56行で記録した。

この同じ実同型を全係数の要素圏に自然に適用し、Kan化の全関手同型へ送った。§219の元の全要素nerveから反対要素nerveの元の終端augmentationへの比較と、§221の元の単位を保つnative全分類比較を合成した。totalElementsNativeClassificationIsoの始域は元のFのkanHomFamilyCoherentそのものであり、終域は同じFをuncurryした全要素圏の元の連続left-fibration置換のnative全分類である。型つきの定義は60行。点ごとの比較への弱化や、異なる置換・augmentationの選択はしていない。既存構成の宇宙・係数移送と合成の法則として記録し、独立の数学的な一覧項目は増やしていない。

元の単位と元の反対要素augmentationを使っているが、その比較が元の固定始域のroof比較の全FunctorIsoと同じになるというR03dの正規化は、まだ証明していない。今回の全分類の接続の存在を、その等式の代用にはしない。

個別検査：Homの宇宙比較24895・終了0、二本を結合した全係数比較76861・終了0。299：二本と直接importerの対象ビルド3,564 jobs・終了0、小監査161本1,131宣言・標準三公理のみ（実ハンドル75950・終了0）。鍵返却済み。今回56＋60＝116行、累計161本・10,433行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 222.1 型

全係数の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。

#### NerveHomUniverseIso（55行）

```lean
def nerveHomUniverseIso : nerve (ULiftHom.{max u v} C) ≅ nerve C

theorem nerveHomUniverseIso_naturality {D : Type u} [Category.{v} D] (F : C ⥤ D) :
    nerveMap (ULiftHom.down.{v,u,max u v} ⋙ F ⋙ ULiftHom.up) ≫
      (nerveHomUniverseIso D).hom = (nerveHomUniverseIso C).hom ≫ nerveMap F
```

#### TotalElementsNativeClassification（61行）

```lean
def totalElementsNerveCoefficientIso :
    simplicialElementsCatDiagram F ⋙ nerveFunctor ≅ simplexElementsNerveDiagram F

def totalElementsNerveCoefficientKanIso :
    FunctorIso (kanHomFamilyCoherent (simplicialElementsCatDiagram F ⋙ nerveFunctor))
      (kanHomFamilyCoherent (simplexElementsNerveDiagram F))

def totalElementsNativeClassificationIso :
    FunctorIso (kanHomFamilyCoherent F)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom)
```

## 223. BEの元の第三図式への適用と同じ全実射の回収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

全source-frame Homの両変数の添字をAsSmallで、係数だけをULiftで同じ宇宙に持ち上げた全図式から、同じ元のSourceFrameArrowElementsへのdownを52行で記録した。対象では元の両変数・単体次数とラベルのdownを取り、射では元の両変数の射・単体作用素を保つ。元のパラメーターへの射影の厳密な等式と、回収する実射が元のULiftされたラベルのdownそのものという等式を付けた。新しい全要素や射の模型は選んでいない。

これをBEの元のprobeに関手的source frameを適用した図式と、元の標的置換へ適用した。strictBETotJointSourceCoefficientsは元のstrictBETotJointFirstSpanDiagram A 3のAsSmall.downによる前合成そのものであり、その等式はrflである。元の第三図式から、同じ全要素圏の元の置換のnativeな全分類への全FunctorIsoができた。さらに元のstrictBETotJointFirstSpanComparisonを合成し、両変数raw Homから同じnative全分類への全FunctorIsoを得た。BE固有の適用は72行。既存構成の全係数表示・単位・移送と合成の法則として記録し、独立の数学的な一覧項目は増やしていない。

この比較の終域は元の全source-frame要素圏のnativeな全分類であり、正本の二変数Hom∞そのものへの比較はまだ組み立てていない。次は、回収した同じ実射の全pairingと同じ両端を既存twistedPairingNerveMapへ渡し、元の全augmentationの逆による両端の移送へ進む。元の固定始域のroof比較との全FunctorIsoの等式が閉じるまでR03dの完了としない。

個別検査：全要素のdown11509・終了0、BEへの適用を二本結合した検査67659・終了0。300：対象ビルド10,697 jobs・終了0、小監査163本1,153宣言・標準三公理のみ（実ハンドル11457・終了0）。対象とその依存だけのビルドでありrootビルドや公式の大監査は実行していない。鍵はビルド・小監査の間だけ取り、終了と返却を確認した。

今回52＋72＝124行、累計163本・10,557行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 223.1 型

全source-frame係数の共通入力は `{C : Type u} [Category.{v} C] (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)`。BE側は `(A : Type u) [CommRing A]`、元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。

#### LiftedSourceFrameElements（52行）

```lean
abbrev liftedSourceFrameIndex

def liftedSourceFrameCoefficients : liftedSourceFrameIndex (C := C) ⥤ SSet.{max u v}

def liftedSourceFrameElementsDown :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ SourceFrameArrowElements Q R

theorem liftedSourceFrameElementsDown_parameters :
    liftedSourceFrameElementsDown Q R ⋙ sourceFrameArrowParameters Q R =
      Functor.Elements.π (Functor.uncurry.obj (liftedSourceFrameCoefficients Q R)) ⋙
        (AsSmall.down.prod (𝟭 SimplexCategoryᵒᵖ))

theorem liftedSourceFrameElementsDown_value
    (X : SimplicialTotalElements (liftedSourceFrameCoefficients Q R)) :
    sourceFrameArrowValue Q R ((liftedSourceFrameElementsDown Q R).obj X) = X.val.down
```

#### StrictDiagramTotJointSourceElements（72行）

```lean
def strictBETotJointSourceFrame :
    (operad A).Algebra ⥤ SimplexCategory ⥤ (operad A).Algebra

def strictBETotJointSourceCoefficients : strictBETotJointHomIndex A ⥤ SSet.{u+1}

theorem strictBETotJointSourceCoefficients_eq :
    strictBETotJointSourceCoefficients A =
      AsSmall.down ⋙ strictBETotJointFirstSpanDiagram A 3

abbrev StrictBETotJointSourceElements

def strictBETotJointSourceElementsProjection :
    StrictBETotJointSourceElements A ⥤ strictBETotJointHomIndex A

def strictBETotJointSourceElementsDown

def strictBETotJointSourceElementsClassificationIso :
    FunctorIso (strictBETotJointFirstSpanCoherent A 3)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj
          (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).hom)

def strictBETotJointRawSourceElementsClassificationIso :
    FunctorIso (strictBETotJointRawHomCoherent A)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj
          (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).hom)
```

## 224. 同じ全source-frame実射のnative twisted pairingと厳密な両端（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§223で回収した同じ全実射の始域・標的をAsSmallの同じ宇宙へ持ち上げ、任意の全要素の射における同じ反変・共変の四角形を元のsourceFrameArrowValue_naturalityで検証した。元の射の全pairingに既存twistedPairingNerveMapを適用した。同じpairingの二射影は元の始域・標的の全nerve写像そのものであり、既存の全射影式を適用して厳密な等式を得た。64行。

これをBEの同じ元の全source-frame実射へ適用し、元のstrictBETotModelSourceのedgewiseSubdivisionMapを合成した。得られたstrictBETotJointSourceNativePairingは、同じ全要素圏のnerveからTwistedArrow (CAlg_R A)への全単体に自然な写像である。元の始域・標的を同じモデル源へ送った二変数の底への厳密な射影式を、既存twistedArrowProjection_naturalityと元の全pairingの射影式を合成して得た。BE固有の適用は60行。模型の中身を新しく使う構成ではなく、既存の同じモデル源とtwisted pairingの全自然性・係数移送の法則の適用であり、独立の数学的な一覧項目は増やしていない。

このpairingの始域端点は元のsource-frameの各次数の対象であり、まだ元の試験対象Xへ変更していない。§188の元の全augmentationの同じ逆を全要素のパラメーターへ引き戻し、その端点の変更を行う。元の両変数のnative入力への厳密化と元の固定始域のroof比較との等式は、R03dの残りとして保つ。今回のpairingの存在と厳密な射影式だけからR03dやnative極限性の完了を主張しない。

個別検査：元の全pairing5427・終了0、BEへの適用を二本結合した検査1985・終了0。301：対象ビルド10,708 jobs・終了0、小監査165本1,166宣言・標準三公理のみ（実ハンドル18475・終了0）。対象とその依存のみで、rootビルドや公式の大監査は実行していない。鍵返却済み。

今回64＋60＝124行、累計165本・10,681行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 224.1 型

一般側の共通入力は `{C : Type u} [Category.{v} C] (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)`。BE側は `(A : Type u) [CommRing A]`、元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。

#### LiftedSourceFramePairing（64行）

```lean
def liftedSourceFrameArrowDomain :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ (AsSmall.{max u v} C)ᵒᵖ

def liftedSourceFrameArrowCodomain :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ AsSmall.{max u v} C

def liftedSourceFrameArrowValue
    (X : SimplicialTotalElements (liftedSourceFrameCoefficients Q R)) :
    ((liftedSourceFrameArrowDomain Q R).obj X).unop ⟶
      (liftedSourceFrameArrowCodomain Q R).obj X

theorem liftedSourceFrameArrowValue_naturality
    {X Y : SimplicialTotalElements (liftedSourceFrameCoefficients Q R)} (f : X ⟶ Y) :
    ((liftedSourceFrameArrowDomain Q R).map f).unop ≫ liftedSourceFrameArrowValue Q R X ≫
      (liftedSourceFrameArrowCodomain Q R).map f = liftedSourceFrameArrowValue Q R Y

def liftedSourceFramePairing :
    nerve (SimplicialTotalElements (liftedSourceFrameCoefficients Q R)) ⟶
      TwistedArrow (nerve (AsSmall.{max u v} C))

theorem liftedSourceFramePairing_projection :
    liftedSourceFramePairing Q R ≫ twistedArrowProjection (nerve (AsSmall.{max u v} C)) =
      CartesianMonoidalCategory.lift
        (nerveMap (liftedSourceFrameArrowDomain Q R) ≫
          (nerveOppositeIso (C := AsSmall.{max u v} C)).inv)
        (nerveMap (liftedSourceFrameArrowCodomain Q R))
```

#### StrictDiagramTotJointSourcePairing（60行）

```lean
def strictBETotJointSourcePairing :
    nerve (StrictBETotJointSourceElements A) ⟶
      TwistedArrow (nerve (AsSmall.{u+1} (operad A).Algebra))

def strictBETotJointSourceNativePairing :
    nerve (StrictBETotJointSourceElements A) ⟶ TwistedArrow (CAlg_R A)

def strictBETotJointSourceNativePairingBase :
    nerve (StrictBETotJointSourceElements A) ⟶ (CAlg_R A).op ⊗ CAlg_R A

theorem strictBETotJointSourceNativePairing_projection :
    strictBETotJointSourceNativePairing A ≫ twistedArrowProjection (CAlg_R A) =
      strictBETotJointSourceNativePairingBase A
```

## 225. 元の全augmentationの同じ比較を全実射の始域へ引き戻す（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

元のnerve反転同型の逆の自然性を、元の順写像の自然性と同じ二つの逆を合成する法則として30行で記録した（reassoc生成の同じ末尾付きの等式を含む）。元の全実射の始域と単体次数を、§188の全augmentationの反対添字へ送る同じ関手を53行で記録した。その添字への評価の引き戻しは元の実射の始域そのものでrfl、定値端の引き戻しは元の試験対象の射影へ戻り、元の定値図式の恒等射の合成則で示した。頂点の同一視だけではなく、全関手の等式である。

同じ反対添字のnerveと元のnerve反転同型の逆を、元の全augmentationのFunctorIsoのopへの前合成に使った。両端は同じ評価・定値の全関手の等式と反転同型の全自然性で、それぞれ元の実射の始域と元の試験対象のnativeな反変の全図式へ厳密に戻る。strictBETotJointSourceAugmentationDomainIsoは元の一つの全augmentationの比較をそのまま引き戻したものであり、逆を各対象や各単体で独立に選ばない。端点比較の適用は89行。既存構成の自然性・単位・反転・係数移送・合成の法則として記録し、独立の数学的な一覧項目は増やしていない。

この同型の逆を元の全pairingへ作用させ、元の試験対象を始域とする同じ正本Hom∞の全比較へ戻す部分はまだ残る。またpairingの標的は元のright-frame置換後なので、元の全標的置換単位の同じ逆による端点比較も必要。元の固定始域のroof比較との全FunctorIsoの等式と、同じ底上のnative Homへの比較の同値性は未証明であり、R03d・R02・R03の完了とは扱わない。

個別検査：反転同型の逆の自然性33516・終了0、元の全augmentationの添字と両端55221・終了0、三本を結合した最終の端点比較79466・終了0。302：対象ビルド10,713 jobs・終了0、小監査168本1,183宣言・標準三公理のみ（実ハンドル77879・終了0）。鍵返却済み。今回30＋53＋89＝172行、累計168本・10,853行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 225.1 型

BE側の共通入力は `(A : Type u) [CommRing A]`、元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。反転同型の逆の自然性にはreassoc生成の同じ末尾付きの等式もある。

#### NerveOppositeInverseNaturality（30行）

```lean
theorem nerveOppositeIso_inv_naturality
    {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) :
    nerveMap F.op ≫ (nerveOppositeIso (C := D)).inv =
      (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map (nerveMap F)
```

#### StrictDiagramTotJointSourceParameters（53行）

```lean
def strictBETotJointSourceParameterIndex :
    StrictBETotJointSourceElements A ⥤ (strictBETotJointSourceFrameIndex A)ᵒᵖ

theorem strictBETotJointSourceParameterIndex_evaluation :
    strictBETotJointSourceParameterIndex A ⋙ (strictBETotJointSourceFrameEvaluation A).op =
      FrameHom.liftedSourceFrameArrowDomain (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A))

theorem strictBETotJointSourceParameterIndex_constant :
    strictBETotJointSourceParameterIndex A ⋙ (strictBETotJointSourceFrameConstant A).op =
      strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomSourceIndex A
```

#### StrictDiagramTotJointSourceAugmentationComparison（89行）

```lean
def strictBETotJointSourceNativeDomain :
    nerve (StrictBETotJointSourceElements A) ⟶ (CAlg_R A).op

def strictBETotJointSourceOriginalNativeDomain :
    nerve (StrictBETotJointSourceElements A) ⟶ (CAlg_R A).op

def strictBETotJointSourceAugmentationInput :
    nerve (StrictBETotJointSourceElements A) ⟶ (nerve (strictBETotJointSourceFrameIndex A)).op

theorem strictBETotJointSourceAugmentationInput_evaluation :
    strictBETotJointSourceAugmentationInput A ≫
      SSet.opFunctor.map (nerveMap (strictBETotJointSourceFrameEvaluation A) ≫
        strictBETotModelSource A) = strictBETotJointSourceNativeDomain A

theorem strictBETotJointSourceAugmentationInput_constant :
    strictBETotJointSourceAugmentationInput A ≫
      SSet.opFunctor.map (nerveMap (strictBETotJointSourceFrameConstant A) ≫
        strictBETotModelSource A) = strictBETotJointSourceOriginalNativeDomain A

def strictBETotJointSourceAugmentationDomainIso :
    FunctorIso (strictBETotJointSourceNativeDomain A)
      (strictBETotJointSourceOriginalNativeDomain A)
```

## 226. 元の全標的置換単位の同じ逆による端点の回収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

元のstrictBETotModelSourceが全弱自然変換を全FunctorIsoへ送る法則を41行で記録した。元の局所化の弱辺反転と既存nerveTransformationPostIsoをその同じ自然変換へ適用する。元の全自然変換を別の辺や成分に取り替えず、元のモデル源を保つ。§188の全augmentationで用いた同じ既存の反転手順を、一般の全自然変換に記す係数移送の法則である。

元のrightFrameReplacementと元のrightFrameReplacementUnitを、同じAsSmallのモデル源の添字に記録した。各成分が元のモデル弱同値であることは、同じrightFrameReplacementUnit_trivialCofibrationの第二成分を使う。これを上の同じモデル源の全弱自然変換の反転へ渡し、全標的置換単位自身の全FunctorIsoを得た。元の全実射の標的の関手は、元の全標的射影へこの同じ置換を合成したものとrflで一致する。その同じ全標的単位の比較を元の全標的射影へ前合成し、逆を取ることで、実射の置換後の標的から元の標的への全FunctorIsoを得た。83行。

§225の始域比較と今回の標的比較がそろったが、二つを同じ二変数のnativeな底の比較へまとめる部分と、その比較を元の全pairingの同じ底への射へ厳密化する部分はまだ残る。元の固定始域のroof比較との全FunctorIsoの等式と、同じ底上の比較の同値性も未証明。既存の全単位・弱辺反転・係数移送・合成の法則として記録し、独立の数学的な一覧項目は増やしていない。型に関する既存の仮定や範囲は弱めていない。

個別検査：全弱自然変換の移送5039・終了0、二本を結合した最終の標的比較11777・終了0。303：対象ビルド10,712 jobs・終了0、小監査170本1,200宣言・標準三公理のみ（実ハンドル58672・終了0）。鍵返却済み。今回41＋83＝124行、累計170本・10,977行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 226.1 型

共通入力は `(A : Type u) [CommRing A]`、元のmodelCategory Aを局所的に使う。全標的置換側は元のmappingCofibrantFactorization Aも局所的に使う。

#### StrictDiagramTotModelWeakTransformation（41行）

```lean
def strictBETotModelWeakTransformationIso
    {J : Type (u+1)} [SmallCategory J]
    {F G : J ⥤ AsSmall.{u+1} (operad A).Algebra} (η : F ⟶ G)
    (hη : ∀ j, weakEquivalences (operad A).Algebra (AsSmall.down.map (η.app j))) :
    FunctorIso (nerveMap F ≫ strictBETotModelSource A) (nerveMap G ≫ strictBETotModelSource A)
```

#### StrictDiagramTotJointTargetReplacement（83行）

```lean
def strictBETotTargetReplacement :
    AsSmall.{u+1} (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra

def strictBETotTargetReplacementUnit :
    𝟭 (AsSmall.{u+1} (operad A).Algebra) ⟶ strictBETotTargetReplacement A

theorem strictBETotTargetReplacementUnit_weak (Y : AsSmall.{u+1} (operad A).Algebra) :
    weakEquivalences (operad A).Algebra
      (AsSmall.down.map ((strictBETotTargetReplacementUnit A).app Y))

def strictBETotTargetReplacementNativeIso :
    FunctorIso (strictBETotModelSource A)
      (nerveMap (strictBETotTargetReplacement A) ≫ strictBETotModelSource A)

theorem strictBETotJointSourceCodomain_replacement :
    FrameHom.liftedSourceFrameArrowCodomain (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A)) =
    strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A ⋙
      strictBETotTargetReplacement A

def strictBETotJointSourceNativeCodomain :
    nerve (StrictBETotJointSourceElements A) ⟶ CAlg_R A

def strictBETotJointSourceOriginalNativeCodomain :
    nerve (StrictBETotJointSourceElements A) ⟶ CAlg_R A

def strictBETotJointSourceTargetReplacementIso :
    FunctorIso (strictBETotJointSourceNativeCodomain A)
      (strictBETotJointSourceOriginalNativeCodomain A)
```

## 227. 元の二つの全端点比較を元の二変数native入力へまとめる（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

既存functorHomTensorEquivとその合成則により、二つの全FunctorIsoの同じ順方向・逆方向を直積の二成分として戻し、直積値の全FunctorIsoにする法則を46行で記録した。順逆条件は元の二つの同型の順逆条件と元の二つの射影関手のmap_idへ帰着する。パラメーターの準圏性は要求せず、二つの元の同型を保持する。既存のh Funの直積分解を合成する法則であり、別の数学的な比較の存在を仮定していない。

同じ元のnative pairingの底は、§225・§226の元の始域・標的の全図式の組に厳密に等しい。元の試験対象と元の標的の組は、元の全要素圏からの同じ射影でstrictBETotJointNativeHomInputを前合成したものに厳密に等しい。いずれも全写像の等式を示し、この二つの等式で上の積の同型を移送した。strictBETotJointSourceNativePairingBaseIsoは元の全pairingの底から元の二変数native入力の引き戻しへの全FunctorIsoである。BE固有の適用は60行。既存構成の同じ二つの端点比較・自然性・係数移送・合成の法則として記録し、独立の数学的な一覧項目は増やしていない。

同じ底上の射への補正には既存pathCorrectedFunctorSquareを使えることを確認した。これは指定した元の底のFunctorIsoのpathと、元の成分へのexactComponentIso、およびそのpostcompが元の同型へ戻る等式を保持する。元の二つの端点の逆から作った同じ底の同型をこの既存の補正へ渡し、同じ底上のnative Homの全空間への射を作る。補正後の射の同値性、元の固定始域のroof比較との全FunctorIsoの等式はまだ残る。

個別検査：二同型の積3906・終了0、二本を結合したBEの底の比較29830・終了0。304：必要な既存FunctorHomTensorのみの対象ビルド5,931 jobs・終了0（実ハンドル52371・終了0）。305：二本と直接importerの対象ビルド12,210 jobs・終了0、小監査172本1,217宣言・標準三公理のみ（実ハンドル34181・終了0）。対象とその依存のみで、rootビルドや公式の大監査は実行していない。鍵返却済み。

今回46＋60＝106行、累計172本・11,083行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 227.1 型

BE側の共通入力は `(A : Type u) [CommRing A]`、元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。

#### FunctorIsoPairing（46行）

```lean
def functorIsoPair {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    FunctorIso (lift f h) (lift g k)
```

#### StrictDiagramTotJointPairingBaseComparison（60行）

```lean
theorem strictBETotJointSourceNativePairingBase_eq_lift :
    strictBETotJointSourceNativePairingBase A =
      lift (strictBETotJointSourceNativeDomain A) (strictBETotJointSourceNativeCodomain A)

theorem strictBETotJointSourceOriginalNativeEndpoints_eq :
    lift (strictBETotJointSourceOriginalNativeDomain A)
      (strictBETotJointSourceOriginalNativeCodomain A) =
        nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A

def strictBETotJointSourceNativePairingBaseIso :
    FunctorIso (strictBETotJointSourceNativePairingBase A)
      (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A)
```

## 228. 指定された元の端点比較を保つ、同じ底上のnative Homへの実射（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§227の元の全端点比較の同じ逆を、元のnative pairingの射影へfunctorIsoOfEqで移送し、同じ底のFunctorIsoを指定した。これを既存pathCorrectedFunctorSquareへ渡した。twistedArrowProjectionのleft-fibration性と既存leftFibration_equivalenceLiftingだけを使い、元のpairingを同じ元の二変数native入力の上へ補正した。補正後の射影は元のnative入力の同じ全要素射影による引き戻しに厳密に等しい。

補正後と元のpairingの比較には、指定pathから来る既存exactComponentIsoを使った。そのpostcompは、元の端点比較の逆自身を、同じ厳密な射影の等式のeqToIsoと合成したものに等しい。別の同型を選んだものではなく、この等式をstrictBETotJointSourceCorrectedPairingIso_postcompとして保持する。同じ正本Homの全空間を元のnative入力によるtwistedArrowProjectionのpullbackとして記し、補正後のpairingと元の全要素圏の射影をpullback.liftへ渡した。得られたstrictBETotJointSourceNativeHomMapは、元の全要素圏から同じ元の二変数の底上のnative Hom全空間への実際の全写像である。元の底への射影と補正後のpairingの回収の両方が厳密な等式として成立する。103行。

既存の全端点比較、指定pathの相対持ち上げとpullbackの合成・自然性の法則の適用として記録し、独立の数学的な一覧項目は増やしていない。この全写像がcofinalか、元の置換からの延長が前合成同値かは、今回の存在やpathの等式から先取りしていない。元の固定始域のroof比較との全FunctorIsoの等式もR03dの残り。

個別検査の最終版30336・終了0。306：必要な既存二モジュールのみの対象ビルド1,873 jobs・終了0（実ハンドル82144・終了0）。307：元の指定pathを保つ全写像の対象ビルド12,222 jobs・終了0、小監査173本1,236宣言・標準三公理のみ（実ハンドル30168・終了0）。鍵返却済み。§228までの累計173本・11,186行／外枠15,000。

### 228.1 型

共通入力は `(A : Type u) [CommRing A]`。元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使い、nativeな積の準圏性には既存quasicategory_tensorを適用する。

#### StrictDiagramTotJointPairingCorrection（103行）

```lean
def strictBETotJointSourcePairingBasePathIso :
    FunctorIso
      (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A)
      (strictBETotJointSourceNativePairing A ≫ twistedArrowProjection (CAlg_R A))

def strictBETotJointSourcePairingCorrection :
    PathCorrectedFunctorSquare (twistedArrowProjection (CAlg_R A))
      (strictBETotJointSourceNativePairing A)
      (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A)
      (strictBETotJointSourcePairingBasePathIso A)

def strictBETotJointSourceCorrectedPairing :
    nerve (StrictBETotJointSourceElements A) ⟶ TwistedArrow (CAlg_R A)

theorem strictBETotJointSourceCorrectedPairing_projection :
    strictBETotJointSourceCorrectedPairing A ≫ twistedArrowProjection (CAlg_R A) =
      nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A

def strictBETotJointSourceCorrectedPairingIso :
    FunctorIso (strictBETotJointSourceCorrectedPairing A) (strictBETotJointSourceNativePairing A)

theorem strictBETotJointSourceCorrectedPairingIso_postcomp :
    (strictBETotJointSourceCorrectedPairingIso A).postcomp (twistedArrowProjection (CAlg_R A)) =
      eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          strictBETotJointSourcePairingBasePathIso A

def strictBETotJointNativeHomTotalSpace : SSet.{u+1}

def strictBETotJointNativeHomProjection :
    strictBETotJointNativeHomTotalSpace A ⟶ nerve (strictBETotJointHomIndex A)

def strictBETotJointSourceNativeHomMap :
    nerve (StrictBETotJointSourceElements A) ⟶ strictBETotJointNativeHomTotalSpace A

theorem strictBETotJointSourceNativeHomMap_projection :
    strictBETotJointSourceNativeHomMap A ≫ strictBETotJointNativeHomProjection A =
      nerveMap (strictBETotJointSourceElementsProjection A)

theorem strictBETotJointSourceNativeHomMap_pairing :
    strictBETotJointSourceNativeHomMap A ≫
      pullback.fst (twistedArrowProjection (CAlg_R A)) (strictBETotJointNativeHomInput A) =
        strictBETotJointSourceCorrectedPairing A
```

## 229. 元の置換単位を固定したnative Homへの延長と終域の全分類（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

同じ正本Hom全空間の射影のleft-fibration性を、元のtwistedArrowProjectionのleft-fibration性の同じpullbackとして記録した。元の全要素圏のnerveからのstrictBETotJointSourceNativeHomMapを、元の連続left-fibration置換の同じ単位に沿い、既存exists_relativeFunctorExtension_of_leftAnodyneで延長した。exists_strictBETotJointSourceNativeLiftは、元の同じ底への射影の厳密な等式と、元の同じ置換単位との合成がstrictBETotJointSourceNativeHomMapそのものに等しいという厳密な三角形を同時に要求する。別の全写像の存在に取り替えていない。

また同じ正本Hom全空間のnative全分類を、元のstrictBETotJointNativeHomCoherentへつなぐ全FunctorIsoを付けた。既存leftStraighteningInfinityDiagram_baseChangeIsoを元のtwistedArrowProjectionと元の二変数native入力へ適用するだけであり、twistedArrowHomInfinityの定義そのものに戻る。延長と終域の比較を合わせて66行。既存の相対延長・単位・引き戻し・全分類の底変換の法則の適用として記録し、独立の数学的な一覧項目は増やしていない。

これで、raw Homから元の全要素置換の全分類への比較、元のnative Homの全空間の分類から元のnative Hom図式への比較、そしてその間の元の単位を固定した実射が、同じ全二変数の底の上で揃った。ただし中間のこの実射の同値性は未証明。次は元の固定始域の同じ全roof比較を使い、この同じ実射の同値性と、合成した全FunctorIsoの元の固定始域比較との一致を検収する。任意の別の全同型の存在、pointwiseな比較だけ、またはcofinal性を未証明の仮定として置く形へ弱めない。R03d・R02・R03とnative極限性の完了は主張しない。

個別検査：元の単位を固定する延長28513・終了0、終域の底変換比較を含む最終版49885・終了0。308：延長の最初の版の対象ビルド12,223 jobs・終了0、小監査174本1,240宣言・標準三公理のみ（実ハンドル93277・終了0）。309：終域の底変換比較を含む最終版の対象ビルド12,223 jobs・終了0、小監査174本1,245宣言・標準三公理のみ（実ハンドル26554・終了0）。対象とその依存のみで、rootビルドや公式の大監査は実行していない。鍵返却済み。

§228・§229で今回103＋66＝169行、累計174本・11,252行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 229.1 型

共通入力は `(A : Type u) [CommRing A]`。元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。strictBETotJointNativeHomProjection_leftFibrationは同じファイル内で局所instanceとして使う。

#### StrictDiagramTotJointSourceNativeLift（66行）

```lean
lemma strictBETotJointNativeHomProjection_leftFibration :
    LeftFibration (strictBETotJointNativeHomProjection A)

theorem exists_strictBETotJointSourceNativeLift :
    let P : Over (nerve (strictBETotJointHomIndex A)) :=
      Over.mk (nerveMap (strictBETotJointSourceElementsProjection A))
    let R := (continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj P
    ∃ f : R.left ⟶ strictBETotJointNativeHomTotalSpace A,
      f ≫ strictBETotJointNativeHomProjection A = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app P).left ≫ f =
        strictBETotJointSourceNativeHomMap A

def strictBETotJointNativeHomClassificationIso :
    FunctorIso (leftStraighteningInfinityDiagram (strictBETotJointNativeHomProjection A))
      (strictBETotJointNativeHomCoherent A)
```

## 230. R03g：元のGrothendieck単位のfiber制限の弱同値判定（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 23（うち追加 11）。R03gを追加、未証明。

IS-W2 §19の同じR01〜R03のまとまり・一つの見込み1,500行以内の枠により、元の単位のfiber制限の弱同値判定をR03gとして追加する。共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

```lean
theorem grothendieckFiberUnit_isWeakHomotopyEquivalence (i : I) :
  IsWeakHomotopyEquivalence (grothendieckFiberUnit F i)
```

採用する元のfiber包含を明記する。weightedNerveConstantLift (F ⋙ nerveFunctor) iに、元のstrictなgrothendieckWeightedNerveIso Fのinvを合成したものをgrothendieckFiberInclusion F iとする。この包含に元のcontinuousLeftFibrationReplacementUnitを合成し、同じ底の指定頂点のfiberへvertexFiberLiftした元の実写像がgrothendieckFiberUnit F iである。元の単位・比較・包含を保持し、弱同値になる別の写像の存在への変更はしない。後のroof比較との照合もこの明記した同じ包含と単位を通す。

同じR03fの比較をそのfiberへ制限したgrothendieckFiberComparison F iとの合成が、元のgrothendieckKanCoefficientUnit Fのi成分と元のweightedNerveFiberMapの合成そのものに等しいことを、全単体の厳密な等式grothendieckFiberUnit_comparisonとして個別検査した（実ハンドル16869・終了0）。型だけの一時検査CheckGrothendieckFiberUnitWeakType.leanも終了0（7258）。R03gの証明はまだ仮定にも宣言にもしていない。

見込み150〜350行。元のR03fの同じ比較は前合成同値なので、既存vertexFiberMap_isQCatEquivalence_of_precompositionEquivalenceで同じfiberの比較を同値と検出する。元のEx∞単位はanodyneで弱同値、元のweightedNerveFiberMapはstrictな同型である。上の全単体の厳密な等式を弱同値の合成・消去則へ渡して、元のgrothendieckFiberUnit自身の弱同値性を得る。新しい数学的なfiberの判定として一つに見積もり、既存の構成の法則だけとは数えない。半分175行で実測と残りを報告する。

置き場所はKerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckFiberUnit.lean。R03gの後に、この同じfiberの単位と、元の同じnative Hom写像の合成を元の固定始域のroof比較へ照合する。R03gだけでnative Hom写像の同値性やR03dの全FunctorIsoの正規化が済んだとはしない。検証済み本体の累計は引き続き174本・11,252行／外枠15,000。今回の未検収のLeanは一時ファイル内である。

### 230.1 同じ包含・単位と比較の型（個別検査済み、対象ビルド前）

```lean
abbrev grothendieckReplacement : Over (nerve I)

def grothendieckFiberInclusion (i : I) : nerve (F.obj i) ⟶ nerve (Grothendieck F)

theorem grothendieckFiberInclusion_projection (i : I) :
    grothendieckFiberInclusion F i ≫ nerveMap (Grothendieck.forget F) = SSet.const (nerveVertex i)

def grothendieckFiberUnit (i : I) :
    nerve (F.obj i) ⟶ vertexFiber (grothendieckReplacement F).hom (nerveVertex i)

def grothendieckFiberComparison (i : I) :
    vertexFiber (grothendieckReplacement F).hom (nerveVertex i) ⟶
      vertexFiber (weightedNerveProjection (grothendieckKanCoefficients F)) (nerveVertex i)

theorem grothendieckFiberUnit_comparison (i : I) :
    grothendieckFiberUnit F i ≫ grothendieckFiberComparison F i =
      (grothendieckKanCoefficientUnit F).app i ≫
        weightedNerveFiberMap (grothendieckKanCoefficients F) i
```

## 231. R03g完了：同じ元のGrothendieck単位の指定fiber制限は弱同値（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03gを完了。R03d・R02・R03は未完了。

R03gを111行で閉じた（見込み150〜350行、上端との差−239行）。元のstrictなgrothendieckWeightedNerveIsoのinvを通した同じ定値fiberの包含に、元の置換単位を合成し、指定fiberへの元の実写像grothendieckFiberUnitを取った。同じR03fの全比較からのfiber比較grothendieckFiberComparisonは、既存の前合成同値のfiberへの制限によって同値となる。

元の単位のfiber制限とこの同じfiber比較の合成は、元のEx∞係数単位と元のweightedNerveFiberMapの合成そのものに厳密に等しい。この等式は元の全単位の厳密な三角形、元のstrict同型の逆条件、weightedNerveConstantLift_mapの全自然性だけで示した。元のEx∞単位はanodyneであり、既存homotopyEquivalence_pre_of_anodyneとπ₀の全単射で弱同値と検査できる。元のweightedNerveFiberMapはstrictな同型である。弱同値の合成と同じfiber比較の消去により、元のgrothendieckFiberUnit自身の弱同値性が得られた。充填性や弱同値性を新しい仮定として追加していない。途中報告点175行に達する前に全証明が閉じた。

個別検査の最終版59023・終了0。310：対象ビルド3,412 jobs・終了0、小監査175本1,258宣言・標準三公理のみ（実ハンドル51386・終了0）。鍵返却済み。今回111行、累計175本・11,363行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次は§220・§221の同じ全要素圏とGrothendieck表示の厳密な係数移送と元の置換単位の自然性を使い、この同じfiber単位の弱同値を元の全要素圏のfiberへ戻す。その後に、元の同じnative Hom写像を合成した写像と元の固定始域のroof比較を照合する。R03gだけでnative Hom写像の同値性やR03dの全FunctorIsoの正規化が済んだとはしない。

### 231.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。fiberのKan性は既存のleft-fibrationのfiberのKan性と元のEx∞係数のKan性を局所instanceとして使う。

#### GrothendieckFiberUnit（111行）

```lean
abbrev grothendieckReplacement : Over (nerve I)

def grothendieckFiberInclusion (i : I) : nerve (F.obj i) ⟶ nerve (Grothendieck F)

theorem grothendieckFiberInclusion_projection (i : I) :
    grothendieckFiberInclusion F i ≫ nerveMap (Grothendieck.forget F) = SSet.const (nerveVertex i)

def grothendieckFiberUnit (i : I) :
    nerve (F.obj i) ⟶ vertexFiber (grothendieckReplacement F).hom (nerveVertex i)

def grothendieckFiberComparison (i : I) :
    vertexFiber (grothendieckReplacement F).hom (nerveVertex i) ⟶
      vertexFiber (weightedNerveProjection (grothendieckKanCoefficients F)) (nerveVertex i)

theorem grothendieckFiberUnit_comparison (i : I) :
    grothendieckFiberUnit F i ≫ grothendieckFiberComparison F i =
      (grothendieckKanCoefficientUnit F).app i ≫
        weightedNerveFiberMap (grothendieckKanCoefficients F) i

theorem grothendieckFiberComparison_isQCatEquivalence (i : I) :
    IsQCatEquivalence (grothendieckFiberComparison F i)

theorem grothendieckFiberUnit_isWeakHomotopyEquivalence (i : I) :
    IsWeakHomotopyEquivalence (grothendieckFiberUnit F i)
```

## 232. R03gを元の全要素圏の同じfiber単位へ係数移送する（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03d・R02・R03は未完了。

元のstrictなGrothendieck表示から元の全要素圏への順写像を、§231の同じ指定fiber包含へ合成した。元の全要素射影への射影は同じ頂点で定値となる。この同じ包含に元の全要素圏の置換単位を合成し、同じ指定fiberへの実写像simplicialElementsFiberUnitを取った。

§221の同じ二つの表示の元の置換比較をそのfiberへ制限し、その同じ比較の前合成同値性からfiberの同値性を得た。元の全要素の単位のfiber制限とこの同じfiber比較の合成は、R03gの元のGrothendieck単位のfiber制限そのものに厳密に等しい。等式は、元の置換単位の自然性、元の同じ全要素とGrothendieck表示の厳密な往復、およびfiberの包含後の射の計算だけで示した。この等式と弱同値の消去則で、R03gを元のsimplicialElementsFiberUnit自身の弱同値性へ移した。100行。

R03gの同じ元の写像を既存の厳密な係数表示と元の単位の自然性で移送する法則として記録し、独立の数学的な一覧項目は増やしていない。元のfiber包含は定義で明記し、写像を別の同値の存在へ変更していない。次は元のnative Hom写像と元の単位を固定する延長を、その同じfiber包含へ制限する厳密な三角形を追跡する。元のnative Hom写像のfiber制限の弱同値性と、元の固定始域のroof比較との全同型の一致はまだ残る。

個別検査の最終版86234・終了0。311：対象ビルド3,420 jobs・終了0、小監査176本1,271宣言・標準三公理のみ（実ハンドル97632・終了0）。鍵返却済み。今回100行、累計176本・11,463行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 232.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。fiberのKan性は既存のleft-fibrationのfiberのKan性を局所instanceとして使う。

#### SimplicialElementsFiberUnit（100行）

```lean
abbrev simplicialElementsReplacement : Over (nerve I)

def simplicialElementsFiberInclusion (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶ nerve (SimplicialTotalElements F)

theorem simplicialElementsFiberInclusion_projection (i : I) :
    simplicialElementsFiberInclusion F i ≫ nerveMap (simplicialTotalElementsProjection F) =
      SSet.const (nerveVertex i)

def simplicialElementsFiberUnit (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶
      vertexFiber (simplicialElementsReplacement F).hom (nerveVertex i)

def simplicialElementsFiberComparison (i : I) :
    vertexFiber (simplicialElementsReplacement F).hom (nerveVertex i) ⟶
      vertexFiber (grothendieckReplacement (simplicialElementsCatDiagram F)).hom (nerveVertex i)

theorem simplicialElementsFiberUnit_comparison (i : I) :
    simplicialElementsFiberUnit F i ≫ simplicialElementsFiberComparison F i =
      grothendieckFiberUnit (simplicialElementsCatDiagram F) i

theorem simplicialElementsFiberComparison_isQCatEquivalence (i : I) :
    IsQCatEquivalence (simplicialElementsFiberComparison F i)

theorem simplicialElementsFiberUnit_isWeakHomotopyEquivalence (i : I) :
    IsWeakHomotopyEquivalence (simplicialElementsFiberUnit F i)
```

## 233. 元のnative Hom写像と単位を固定する延長のfiber制限（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03d・R02・R03は未完了。

元の全要素圏から底上への写像を、既存の同じfiber包含へ制限するsimplicialElementsFiberMapを定義した。元の置換単位を固定する延長について、そのfiberへの制限と元のfiber単位の合成がこの写像に厳密に等しいことを示した。既存の包含・単位・延長の合成則であり、新しい数学的な一覧項目は増やしていない。

BEへの特殊化では同じ全パラメータのstrictBETotJointSourceNativeHomMapを制限した。fiber単位自体の弱同値性はR03gの係数移送から得た。hm・huは元の底射影と元の単位を固定する条件で、§229の実際の延長が満たすものを使う。native Hom写像のfiber制限自身の弱同値性、延長自身の同値性、元の固定始域のroof比較との全FunctorIsoの一致はまだ証明していない。

個別検査は一般版23702・BE版31608とも終了0。312の対象ビルドは12,227 jobsで成功（既存依存を含む対象ビルドでありrootビルドではない）。続く小監査は178本・1,280宣言、標準三公理のみ。ログ/private/tmp/isw2-build312.logの両成功と該当プロセスの終了を確認した。元の実行ハンドルは会話圧縮後に復元できなかったため終了コードを推測して記載しない。鍵を重複取得せず、ビルドを再実行していない。

今回2本101行、累計178本・11,564行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。

### 233.1 型

一般版の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`、BE版は `(A : Type u) [CommRing A]`。BEのmodel構造とfunctorial factorizationは既存の指定された局所instanceを使う。

#### SimplicialElementsFiberMap（43行）

```lean
def simplicialElementsFiberMap {E : SSet.{u}} (p : E ⟶ nerve I)
    (h : nerve (SimplicialTotalElements F) ⟶ E)
    (hh : h ≫ p = nerveMap (simplicialTotalElementsProjection F)) (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶ vertexFiber p (nerveVertex i)

theorem simplicialElementsFiberUnit_map {E : SSet.{u}} (p : E ⟶ nerve I)
    (h : nerve (SimplicialTotalElements F) ⟶ E)
    (hh : h ≫ p = nerveMap (simplicialTotalElementsProjection F))
    (m : (simplicialElementsReplacement F).left ⟶ E)
    (hm : m ≫ p = (simplicialElementsReplacement F).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).left ≫ m = h) (i : I) :
    simplicialElementsFiberUnit F i ≫ vertexFiberMap _ p m hm (nerveVertex i) =
      simplicialElementsFiberMap F p h hh i
```

#### StrictDiagramTotJointSourceNativeFiber（58行）

```lean
def strictBETotJointSourceNativeFiberMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
      vertexFiber (strictBETotJointNativeHomProjection A) (nerveVertex P)

theorem strictBETotJointSourceFiberUnit_isWeakHomotopyEquivalence (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P)

theorem strictBETotJointSourceNativeFiberUnit_map
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).left ≫ m =
        strictBETotJointSourceNativeHomMap A) (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P ≫
      vertexFiberMap _ (strictBETotJointNativeHomProjection A) m hm (nerveVertex P) =
        strictBETotJointSourceNativeFiberMap A P
```

## 234. 外枠の再見積もりと次の判断点（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。検証済み213e2858e、178本・11,564行。残り枠は3,436行。

### 234.1 残りの規模

§152.4のR04〜R12だけの当初見込みでも下端4,300行で、残り枠を864行超える。さらにR02・R03のnative比較と標準脚が未完了である。これまでのfiber単位の比較を作ったことでその未完箇所を具体化できたが、これをもって全native Hom比較や標準脚の全自然性が済んだとは扱わない。以下は相互に重複しない残りの仕事の紙の見込みであり、新規Lean項目の無条件な追加承認とはしない。

| 残り | 見込み（行） | 再利用と未検証点 |
|---|---:|---|
| R03d内：指定native fiber写像の弱同値 | 600〜1,400 | R03gと§233の厳密な三角形を使用。元の固定始域roofとの照合は未証明 |
| R03d内：全FunctorIsoと固定始域への制限の等式 | 400〜900 | 全要素の同じ延長を使用。点ごとの同値だけでは閉じない |
| R02・R03：指定native錐族と極限性 | 600〜1,200 | 元の重みの比較と指定Hom同型を接続。脚を作り替えない |
| R04・R05：UのTot比較と局所化への輸送 | 500〜1,100 | G10の全図式射と指定錐族、既存forgetの極限保存を再利用 |
| R06〜R08：strict実現の模型と同じ余錐族 | 1,600〜2,800 | §152の見込みを維持。台の通常colimだけで導来実現とはしない |
| R09・R10：実現のU比較と全関手比較 | 1,000〜1,800 | ③-aの全族と指定輸送を使用。まだ実測していない |
| R11・R12：離散制限と既存入口・係数変更 | 500〜900 | ⑤aの欄を変更せず照合。Totと実現の両部分を含む |
| 合計 | **5,200〜10,100** | 完成時 **16,764〜21,664** |

当初§152の全体5,700〜9,800行に対し、現在の完成見込みは下端で+11,064、上端で+11,864行。主な差は、二変数の指定native Homへの全自然性と、元の固定始域roof比較への正規化を、点ごとの同値の存在に弱めず証明するための一般の分類・fiber単位の道具にある。完成時の新しい外枠の提案は22,000行。上端に対する余裕は336行しかなく、再度の上振れを吸収できると保証しない。Tot側の停止点3b-4aと実現側3b-4bの分割は維持する。

### 234.2 止める根拠と現在の状態

coordination.md §2：『上限を超えそうなときは報告して止める（止まる前に、それまでの検証済みの分をコミット）』、夜の進め方も『その線の Lean は止めて決めておいた代わりの紙の作業へ』と指定している。IS-W2 §18は3b-4の外枠15,000行、§19も『外枠15,000行は変えない』。同じまとまり内の1,500行以下の中間定理の追加許可は、この外枠を変更する許可ではない。

したがって、検証済みを213e2858eに保存した上で、この線のLeanの追加を止める。範囲、型、指定脚、全族、固定始域の同型の等式を弱めない。外枠の変更はユーザー判断を要する。停止点3b-4aに達したとの報告ではない。代わりの紙の作業を次節に記録する。

### 234.3 紙：元のnative fiberから元のroofへの未完の橋

次に必要な主張の候補は、既存の指定された写像そのものについての次の型である（ここではLean宣言を追加していない）。

```lean
theorem strictBETotJointSourceNativeFiberMap_isWeakHomotopyEquivalence
    (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceNativeFiberMap A P)
```

この型を示す際、元のsource coefficientの通常の要素圏のnerveと、元のroofで使う逆向きの要素圏のnerveを同一視してはならない。既存のedgewise/opposite比較とterminal augmentationを通した同じ写像で比較し、その上で元のroofの弱同値性とKanHammockHomInfinityの指定Yoneda比較へ接続する。native Homのpullbackのfiberは、同じ元の頂点のtwisted-arrow fiberへ移す。経路修正のexactComponentIso_postcompで指定された底のpathを追跡する必要があり、任意の同型への置換では固定始域の最終等式を保証できない。

この弱同値が示されれば、§233の等式とR03gの同じfiber単位の弱同値から、元の単位を固定する延長のfiber写像を弱同値と判定できる。両側のleft fibrationのKan fiber上で同値に移し、既存isPrecompositionEquivalence_of_leftFibration_nerve_fibersで同じ全延長の前合成同値性を得る。分類の全同型へ移しても、R03dの固定始域へ制限した全FunctorIsoが元のstrictBETotProbeFrameHomInfinityIsoに等しいことは別途残る。

### 234.4 紙：3b-3との境目を維持する

Totのstrict入力の模型、同じHom分類、指定native錐とその極限性は③-bで閉じる。R05でstrict複体図式の局所化上へ全評価・全指定錐族を輸送する部分は③-aの3b-3の指定された比較を使う。実現側R09・R10も、図式ごとの余錐だけではなく③-aの全パラメータの余錐族とその輸送を使う。任意のcoherentなBE図式の厳密化は今回の実装に含めない。既存FramedLimit*とCAlgUnderlyingDerivedComparisonを作り直さず、無条件cAlgForgetDerived_mapJoinCone_isLimitの保存方向を使う。Uが極限を保存することからBE値の極限性を逆に推論しない。

## 235. 外枠判断待ちの紙：既存APIの証明境界を確認（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。Lean追加なし、実測178本・11,564行のまま。前のターンは検証済み保存と再見積もりの進捗であり、検証待ちではない。現mainのIS-W2末尾も§19・外枠15,000行のままで、外枠変更の承認を確認できていない。

次の既存ソースを読み、§234.3の経路のうち使える結論と不足を分けた。

| 既存ソース（SerrePositivity以下） | 実際の結論 | 接続時の注意 |
|---|---|---|
| EInfinity/FrameHom/FrameLeftRoofPrecompose.lean：frameLeftRoofColimitMap_precompose | 指定された始域射・frame比較に沿うanodyneQ.map後の等式 | 生の二変数の自然変換として使わない。定理はinclude hαも要求する |
| InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/VertexFiberPullback.lean：vertexFiberPullbackIso_hom_ι | fiber同型の順射を包含すると元の第一射影になる厳密な等式 | native total spaceの第一射影を元のcorrected pairingへ戻す際の指定された方向が使える |
| EInfinity/FrameHom/RightFrameHomInfinityNormalization.lean：rightFrameTerminalHomIso_hom | 終端の実現比較、原本kanHammockHomInfinityIso、指定homInfinityTransportの順の合成に等しい | 比較二胞体c.triangleも同じ入力として保持する。零単体の共役式だけで全同型の等式を結論しない |
| EInfinity/BarrattEccles/StrictDiagramTotProbeHomInfinityComparison.lean：strictBETotProbeFrameHomInfinityIso | 元のframe比較と、同じprobe源の頂点同型をco-Yonedaで写した全標的同型の合成 | 固定始域への最終制限をこの同じ合成へ合わせる必要がある |
| InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/F1FibrationsLeftFibrationNerveComparison.lean：isPrecompositionEquivalence_of_leftFibration_nerve_fibers | 両射影がleft fibration、底を厳密に保つ全写像について、各対象の指定fiber射がQCat同値なら全射は前合成同値 | native fiber射の弱同値性が未完なのでまだ適用の前提が揃わない |

従って再開時は、元のnative fiber射にvertexFiberPullbackIsoを合成し、包含後の厳密な等式で同じcorrected pairingへの制限を回収する所を最初の検査単位とする。その後、元の指定された底のpathを保持したまま、元のroofとterminal augmentationに沿う比較を組み立てる。anodyneQ上の既存の始域自然性だけで済むと仮定せず、固定始域の全標的同型の合成まで追跡する。この不足を解決したとの数学的主張も、新しい仮定付きのLean入口も追加していない。

今回の紙の整理は§234で指定した代わりの作業。対象ビルド・監査の新しい実行は不要で、鍵は取得していない。外枠変更の質問は一件のまま維持し、重複して送らない。

