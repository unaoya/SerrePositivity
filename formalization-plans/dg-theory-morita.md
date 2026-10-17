# 導来Morita：このチャットのU16a・U16c

## U16a 公開 API（2026-10-17固定）

名前空間は `SerrePositivity.DifferentialGraded.Morita`。
以下は他担当が依存してよい名前・正確な型・仮定の契約であり、実装状態を分けて記す。
**「型のみ確定」は予定宣言であり、現時点でLeanからimportできることや証明済みであることを意味しない。**
未証明のLean宣言・sorry・axiomは作らない。既存公開型を変更する必要があれば変更前に本節へ旧新型と移行方法を書く。

共通の変数は次の通り。`D`・`E`・`F`の対象宇宙は独立である。
型仕様はこの変数文脈で右辺を省略した宣言として記す。共通引数の順はA・D・E・F。

```lean
universe u v w z
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
```

### 1. kernelの型・向き・恒等・合成（KernelBasic.lean）

D→Eのkernelは**右E・左D**。`functorGraph A D E f`と同じ向きであり、
この順序は将来のQuasiEquivalence*・Perfect*側でも保持する。

```lean
abbrev Kernel := DerivedBimoduleCategory A E D
def kernelIdentity : Kernel A D D
def kernelGraph (f : DGFunctor A D E) : Kernel A D E
def kernelCompose (hD : localHomKFlat A D)
  (P : Kernel A D E) (Q : Kernel A E F) : Kernel A D F
def kernelComposeMap (hD : localHomKFlat A D)
  {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
  kernelCompose A D E F hD P Q ⟶ kernelCompose A D E F hD P' Q'
```

共通引数は各型に現れるものだけを抽出する。Kernel自体とkernelGraphはDのSmallを要求せず、
EのSmallだけを保持する（KernelChecksの#check出力で確認）。他の通常作用・合成は両側のSmallを保持する。
Kernelの実体は既存の主bimodule局所化。identityは対角の局所化像。
`kernelCompose A D E F hD P Q`は
`((derivedBimoduleComposeFunctor A F E D hD).obj P).obj Q`。
この合成に必要な局所Hom条件はDだけ。E・Fには追加しない。

### 2. 通常作用（KernelTensor.lean）

```lean
def kernelTensor (P : Bimodule A E D) :
  DGFunctor A (RightModule A D) (RightModule A E)
lemma kernelTensor_value (P : Bimodule A E D)
  (M : RightModule A D) (e : E) :
  ((kernelTensor A D E P).obj M).obj (Opposite.op e) =
    BalancedTensor.obj A D M (P.leftAt e)
lemma kernelTensor_graph (f : DGFunctor A D E) :
  kernelTensor A D E (functorGraph A D E f) = dgModuleExtension A D E f
```

通常作用にlocalHomKFlatは不要。準同型保存は任意入力について主張せず、入力の射影解像度を使う。

### 3. 主導来作用（実装・検証済み、U16a3）

```lean
def kernelDerivedTensorFunctor :
  Kernel A D E ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
def kernelDerivedTensor (P : Kernel A D E) :
  DerivedModuleCategory A D ⥤ DerivedModuleCategory A E
def kernelDerivedTensorComputation (P : Bimodule A E D)
  (M : ModuleCategory A D) (R : ModuleProjectiveResolution A D M) :
  (kernelDerivedTensor A D E
      ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).obj
      ((moduleToDerived A D).obj M) ≅
    (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj)
```

`kernelDerivedTensor A D E P`は`(kernelDerivedTensorFunctor A D E).obj P`と定義する。
主導来作用そのものにはlocalHomKFlatを課さない。右D入力のsemifree射影解像度は
DのHomのA-flat性なしで相対K-flatであり、kernelの準同型に関する不変性をこのモデルで証明する方針。
任意指定射影解像度Rの計算を公開し、単なる対象上の計算で関手・自然性を代用しない。

### 4. 導来右随伴・unit/counit（型のみ確定）

```lean
def kernelDerivedHom (P : Kernel A D E) :
  DerivedModuleCategory A E ⥤ DerivedModuleCategory A D
def kernelDerivedAdjunction (P : Kernel A D E) :
  kernelDerivedTensor A D E P ⊣ kernelDerivedHom A D E P
def kernelDerivedUnit (P : Kernel A D E) :
  𝟭 (DerivedModuleCategory A D) ⟶
    kernelDerivedTensor A D E P ⋙ kernelDerivedHom A D E P
def kernelDerivedCounit (P : Kernel A D E) :
  kernelDerivedHom A D E P ⋙ kernelDerivedTensor A D E P ⟶
    𝟭 (DerivedModuleCategory A E)
lemma kernelDerived_left_triangle (P : Kernel A D E)
  (X : DerivedModuleCategory A D) :
  (kernelDerivedTensor A D E P).map ((kernelDerivedUnit A D E P).app X) ≫
    (kernelDerivedCounit A D E P).app ((kernelDerivedTensor A D E P).obj X) = 𝟙 _
lemma kernelDerived_right_triangle (P : Kernel A D E)
  (Y : DerivedModuleCategory A E) :
  (kernelDerivedUnit A D E P).app ((kernelDerivedHom A D E P).obj Y) ≫
    (kernelDerivedHom A D E P).map ((kernelDerivedCounit A D E P).app Y) = 𝟙 _
```

unit/counitは上の実際の随伴の成分とする。随伴の存在・成分の可逆性を入力仮定として受け取らない。
右随伴の一般kernelに対する構成は残る証明課題。localHomKFlatを列のhomotopically projective性と
同一視しない。一対象Endでの既存随伴を任意kernelの証明の代わりにしない。
この型の確定は右随伴の実装が完成したという意味ではない。
通常Homのdg関手はAdjunctionHom.leanで実装・検証済み（U16a10）。
一般導来右随伴の表現対象構成はAdjunctionBrownSeed.leanの初期被覆まで進んでいるが、存在証明は未完。

### 5. 恒等作用（実装・検証済み、U16a4）・合成比較（実装・検証済み、U16a6）

```lean
def kernelIdentityIso :
  kernelDerivedTensor A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D)
def kernelCompositionIso (hD : localHomKFlat A D)
  (P : Kernel A D E) (Q : Kernel A E F) :
  kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E F Q ≅
    kernelDerivedTensor A D F (kernelCompose A D E F hD P Q)
```

恒等比較にlocalHomKFlatは不要。合成比較はU12e-localの結合子と同じく始域Dだけに条件を置く。
合成比較は入力導来加群と両kernelの任意の主導来射に自然（U16a9）。
kernelComposeMapへの自然性はkernelCompositionIso_naturalityで利用できる。
恒等と三因子の結合比較のcoherenceは未完で、Coherence*で続ける。

```lean
lemma kernelCompositionIso_naturality (hD : localHomKFlat A D)
  {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
  NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
      ((kernelDerivedTensorFunctor A E F).map g) ≫
      (kernelCompositionIso A D E F hD P' Q').hom =
    (kernelCompositionIso A D E F hD P Q).hom ≫
      (kernelDerivedTensorFunctor A D F).map (kernelComposeMap A D E F hD f g)
lemma kernelCompositionIso_kFlat (hD : localHomKFlat A D)
  (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
  kernelCompositionIso A D E F hD ((bimoduleToDerived A E D).obj P.obj)
      ((bimoduleToDerived A F E).obj Q) = kernelCompositionKFlatIso A D E F hD P Q
```
三因子D→E→F→Gで必要なのは既存結合子に現れるD・EのlocalHomKFlat。
同じkernel・固定dg圏の契約とし、中断した一般分解変更のcoherenceを待たない。

### 実装状態と他担当の利用境界

| API群 | 状態 | 他担当の利用 |
| --- | --- | --- |
| Kernel・kernelIdentity・kernelGraph・kernelCompose・kernelComposeMap | 実装・対象ビルド済み | 型・向きは上記で固定 |
| kernelTensor・値・graph一致 | 実装・対象ビルド済み | 同上 |
| 主導来作用・任意解像度計算 | 実装・検証済み（U16a3） | Morita/KernelDerivedFunctor.leanをimportして利用できる |
| 一般右随伴・unit/counit | 型のみ確定 | 同上 |
| 恒等作用比較 | 実装・検証済み（U16a4） | Morita/CoherenceIdentity.leanのkernelIdentityIso |
| 合成の作用比較・全kernel射の自然性 | 実装・検証済み（U16a9）。恒等・結合coherenceは未完 | Morita/CoherenceComposition.leanのkernelCompositionIso・kernelCompositionIso_naturality・kernelCompositionIso_kFlat |

U16b担当が構成するgraph作用と`dgDerivedExtension`の自然同型はQuasiEquivalence*に置く。
このチャットは同ファイルを編集しない。導来作用が未実装の間も、通常graph一致はKernelTensorで提供する。
不足する比較は双方の所有範囲の新規アダプタに置き、既存のDerived/・Endomorphism/等を変更しない。

## 分担と次工程

このチャットはU12e-local受入、U16aの公開API固定、一般経路の棚卸し、U16a証明、U16cの順に進める。
U16b→dはdg-U14チャットのMorita/QuasiEquivalence*・Perfect*・ScalarExtension*・Center*と
`dg-theory-morita-qe.md`、U17c/dの一部は局所K-flat版担当のVerdier/・Quotient/DerivedComparison*。
新しいsorry・axiom・引用は追加しない。DG-MOR等が必要なら採用せず止まって報告する。

U16cではmoduleCompact_iff_perfect、perfectEndomorphismDG_quasiEquivalence、
endomorphismDerivedEquivalence_ofCompactGeneratorを再利用する。
perfect性・全Homの擬同型・compact生成は独立条件であり、局所Hom K-flat性から自動にはしない。
U16a・c全体は未受入。


## U16a1：公開型と通常作用の固定・検証（2026-10-17）

KernelBasic・KernelTensor・KernelChecksを対象ビルドし成功（2607 jobs、警告なし）。
KernelChecksは8宣言の#checkと直接公理監査を再現する。標準3公理以内で、新しいsorry・axiom・引用なし。
主導来作用・一般右随伴・恒等／合成の作用比較は冒頭の型のみ確定であり、U16a全受入ではない。
既存公開APIの型・名前・証明は変更していない。U16b/d担当のMoritaファイルは編集していない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.KernelChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/KernelChecks.lean
```

次は指定の順に従い一般経路の棚卸し・docstring整理を行い、その後主導来作用の証明へ戻る。


## 一般経路の棚卸し完了・U16a証明への復帰（2026-10-17）

指定された順序の棚卸し・docstring整理を実施し、記録をdg-theory-u12e-general-inventory.mdへ保存した。
U12e-generalは中断・未受入のまま。局所入口とKernelTensorのResolution/依存はともに0件。
次は冒頭で型を固定した主導来作用、一般右随伴とunit/counit、恒等・合成の作用比較の証明を進める。
U16a・U16cの全受入を宣言するものではない。既存公開型の変更はない。


## U16a2：任意の通常kernelの導来作用と入力解像度（2026-10-17）

KernelResolution.leanは任意のP : Bimodule A E Dについて、入力右D加群だけを射影解像して
主導来関手kernelDerivedTensorOnBimoduleを構成する。Homの局所K-flat性は要求しない。
U10のmoduleDerivedResolutionFunctor・moduleDerivedResolutionIsoを再利用し、
解像度選択の自己・推移則をそのままtensorのH⁰関手へ送る。

共通変数は冒頭と同じで、以下の追加公開型を固定する。

```lean
variable (P : Bimodule A E D)
def kernelHomotopyToDerived : ModuleHomotopyCategory A D ⥤ DerivedModuleCategory A E
def kernelResolutionDerivedTensor
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
  DerivedModuleCategory A D ⥤ DerivedModuleCategory A E
def kernelDerivedTensorOnBimodule : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E
def kernelResolutionDerivedTensorIso
  (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
  kernelResolutionDerivedTensor A D E P R ≅ kernelResolutionDerivedTensor A D E P S
def kernelDerivedTensorOnBimoduleComputation {M : ModuleCategory A D}
  (R : ModuleProjectiveResolution A D M) :
  (kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M) ≅
    (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj)
lemma kernelDerivedTensorOnBimodule_graph (f : DGFunctor A D E) :
  kernelDerivedTensorOnBimodule A D E (functorGraph A D E f) = dgDerivedExtension A D E f
```

kernelTensorHomotopyComputationとkernelResolutionDerivedTensorComputationはH⁰と指定解像度族での計算。
kernelResolutionDerivedTensorIso_self・_transは二つ／三つの解像度族の比較の整合性。
これらは既存公開型の変更ではなく追加APIである。graph一致は既存導来延長そのものとの等式で、
U16b担当はこの通常kernel版を直接利用できる。

U16a2の時点では、主導来kernel全体のkernelDerivedTensorFunctorは型のみ確定だった。
今回の通常kernel作用をkernelの射に自然な族へまとめ、kernelの準同型を反転して降ろす必要がある。
一般右随伴・恒等／合成の作用比較・U16cも残る。U16a全受入ではない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.KernelResolutionChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/KernelResolutionChecks.lean
```


検証：KernelResolutionChecks・既存kernel型検査・局所受入・General入口検査・Spectra.StageTwoの
合同ビルド成功（3524 jobs、警告なし）。追加10宣言の直接公理監査は標準3公理のみ。
文書検査は24 Markdown・326 exposition参照、失敗0件。新しいsorry・axiom・引用なし。


## U16a3：kernelの射・準同型反転と主導来作用の実装（2026-10-17）

**冒頭§3の三宣言は型を変えずに実装・検証済みへ更新した。**
主導来kernelの利用者は以下をimportする。一般分解の入口は経由しない。

```lean
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor
```

KernelNaturality.leanのkernelClosedFamilyNatTransは、全Hom自然な加群値bimodule射を
閉零関手の自然変換にする。源の全加群型にSmallを要求しない。
kernelTensorMap、kernelTensorHomotopyMapは通常／H⁰の入力上の作用の自然変換で、
_app・_id・_compを証明した。kernelTensorMap_valueは各値のbalanced tensor mapとの一致。
kernelTensorMap_projective_quasiIsoは、任意kernel準同型と射影的右D入力について
出力が準同型になることを示す。射影性⇒相対K-flat性の既存APIを再利用している。

KernelDerivedFunctor.leanでは次の追加公開型を固定した。共通変数は冒頭と同じ。

```lean
def kernelResolutionDerivedTensorMap
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
  {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
  kernelResolutionDerivedTensor A D E (BimoduleCategory.underlying A E D P) R ⟶
    kernelResolutionDerivedTensor A D E (BimoduleCategory.underlying A E D P') R
lemma kernelResolutionDerivedTensorMap_isIso
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
  {P P' : BimoduleCategory A E D} (f : P ⟶ P')
  (hf : BimoduleCategory.quasiIso A E D f) :
  IsIso (kernelResolutionDerivedTensorMap A D E R f)
def kernelDerivedTensorOnBimoduleFunctor :
  BimoduleCategory A E D ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
lemma kernelDerivedTensorFunctor_fac :
  bimoduleToDerived A E D ⋙ kernelDerivedTensorFunctor A D E =
    kernelDerivedTensorOnBimoduleFunctor A D E
def kernelDerivedTensorOnBimoduleIso (P : BimoduleCategory A E D) :
  kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P) ≅
    kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P)
```

作用の準同型反転にはlocalHomKFlatを要求しない。H⁰上の出力準同型を主導来圏で反転し、
任意の導来入力へ既存の入力解像度計算と局所化の本質的全射性で運ぶ。
従って対象だけでなくkernelの任意の導来射に対する作用も同じ主局所化上で定まる。

kernelDerivedTensorOnBimoduleIsoとU16a2のkernelDerivedTensorOnBimodule_graphを合成すれば、
U16b担当は主導来graph kernelの作用を既存のdgDerivedExtensionへ比較できる。
こちらでQuasiEquivalence*の比較を重複実装していない。既存公開型の変更は0件。

KernelDerivedFunctorChecksは任意可換環・独立宇宙、任意指定入力解像度族、標数2で検査する。
同入口とKernelResolutionChecks・U12eLocal・General入口検査・Spectra.StageTwoの合同ビルド成功
（3526 jobs、警告なし）。追加公開22宣言の直接公理監査は重複・欠落なく標準3公理以内。
文書検査は24 Markdown・326 exposition参照、失敗0件。
主導来作用入口の推移的project依存は434ファイル、Resolution/依存0件。
U16a3時点では一般右随伴・unit/counit、恒等と合成の作用比較が型のみ確定であり、U16a全受入ではなかった。
次はこれらを証明し、その後U16cへ進む。DG-MOR等の引用は追加していない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctorChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/KernelDerivedFunctorChecks.lean
```


## U16a4：対角kernelの恒等作用（2026-10-17）

**冒頭§5のkernelIdentityIsoは、公開型を変えず実装・検証済みへ更新した。**

```lean
public import SerrePositivity.DifferentialGraded.Morita.CoherenceIdentity
```

kernelIdentityClosedIsoは、既存の通常左bimodule単位子を全右D加群に評価した自然同型。
kernelIdentityHomotopyIsoは、その同型をMathlibの商の普遍性でH⁰へ降ろす。
全右加群型へのSmall仮定は追加しない。

kernelInputResolutionHomotopyAugmentationは任意の指定入力射影解像度族の増大を自然変換へ束ねる。
kernelInputResolutionDerivedAugmentationIsoは出力局所化で増大を反転した同型、
kernelInputResolutionDerivedCounitIsoはそれを全主導来入力へ延長した比較同型である。
**このCounitIsoは入力解像度の増大比較であり、一般kernelのtensor–Hom随伴の余単位ではない。**

kernelDerivedTensorOnBimoduleIdentityIsoはH⁰単位子と入力解像度比較を合成し、
kernelIdentityIsoはさらに既存kernelDerivedTensorOnBimoduleIsoを前置したもの。
従って主導来対角kernelそのものの作用から恒等関手への自然同型である。
任意可換環・非有界、DのSmall.{u}だけを要求し、localHomKFlatは不要。

CoherenceIdentityChecksは任意の導来入力、任意の指定入力射影解像度族、標数2で型を確認する。
主導来kernel・局所受入・General入口・Spectra.StageTwoとの合同ビルド成功（3527 jobs、警告なし）。
公開7宣言の直接公理監査は重複・欠落なく標準3公理以内。
文書検査は24 Markdown・326 exposition参照、失敗0件。
恒等作用入口の推移的project依存は435ファイル、Resolution/依存0件。
一般右随伴・unit/counit、合成比較および恒等・合成の作用coherenceは未完。U16a全受入ではない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.CoherenceIdentityChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/CoherenceIdentityChecks.lean
```


## U16a5：通常合成・相対K-flat入力での増大比較と自然な計算モデル（2026-10-17）

ユーザーの再開指示に従い、CoherenceCompositionClosedの名前解決・dg関手外延性を修正した。
kernelTensorCompositionClosedIsoは通常作用の合成を通常合成kernelの作用に、
kernelTensorCompositionHomotopyIsoはそのH⁰関手を自然同型で比較する。
KernelAugmentationのkernelDerivedTensorAugmentationは実際の入力増大により自然な比較を作り、
kernelRelativeKFlatComputationは相対K-flat入力でそれを反転する。
KernelResolutionModelのkernelResolutionTensorModelFunctorは任意の入力射影解像度族から
通常tensorの主導来像を値に持つ実際の関手を作る。kernelResolutionTensorModelIsoと
kernelResolutionTensorModelFunctor_mapが全ての通常入力射で計算を保証する。
FubiniによるkernelTensor_relativeKFlatは合成比較の同型性に使う。

いずれにもlocalHomKFlatは不要。kernelTensor_relativeKFlatのkernelには右相対K-flat性を明示する。
主導来kernel全体のkernelCompositionIsoはこの時点ではまだ未実装であり、型のみ確定を維持する。
一般右随伴・unit/counit、kernel射に自然な作用合成のcoherence、U16cも未完。

CoherenceCompositionClosedChecksと既存作用・恒等・局所受入・一般入口・Spectra.StageTwoの
合同ビルド成功（3531 jobs）、追加21公開宣言の直接公理監査は標準3公理以内。
既存の公開APIの型・名前は変更していない。新規sorry・axiom・引用はない。


## U16a6：全導来kernelの作用の合成比較（2026-10-17）

冒頭§5のkernelCompositionIsoを、型を変更せず実装・検証済みに更新した。
利用入口はMorita/CoherenceComposition.lean。必要なlocalHomKFlatは始域Dだけで、E・Fには追加しない。

CoherenceCompositionKFlatのkernelResolutionTensorCompositionIsoは、右相対K-flatな最初のkernelと
任意の後のkernelについて、通常入力射に自然な解像度モデル上の比較を作る。
kernelDerivedTensorOnBimoduleCompositionIsoは主局所化の普遍性から全導来入力へ延長する。
CoherenceCompositionのkernelCompositionKFlatIsoはU12e-localの
 derivedBimoduleComposeKFlatValueIsoと実際の主導来作用を接続する。
kernelCompositionIsoは任意の主導来P・QをそれぞれK-flat代表・通常代表へ比較して運ぶ。
入力導来加群への自然性はこの関手自然同型に含まれる。
**kernel射に対する自然性、代表選択の整合性、恒等・結合coherenceは引き続き未完。**
一般右随伴・unit/counitも型のみ確定であり、U16a全受入はまだ行わない。

CoherenceCompositionChecksは任意可換環・独立宇宙・標数2を検査し、他担当の
kernelCompose_columnsPerfectへ実際のkernelCompositionIsoを渡せることも確認する。
他担当のPerfファイルは変更していない。U16dはeCompの入力をこの公開同型で埋められるが、
hNatを要求する比較にはまだkernel射の自然性の証明が必要。
追加4宣言の直接公理監査は標準3公理のみ。既存基盤・作用・恒等・局所受入・一般入口・
Spectra.StageTwoとの合同ビルド成功（3565 jobs）。新規sorry・axiom・引用なし。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionChecks.lean
```


## U16a7：kernel射に関する増大・計算と通常合成の自然性（2026-10-17）

KernelAugmentationNaturalityは任意の通常kernel射について、H⁰計算・任意入力解像度計算・
主導来増大の自然性を証明する。kernelResolutionTensorModelMapは自然なモデル間の実際の自然変換、
kernelResolutionTensorModelIso_kernel_naturalityは主導来作用の射との比較square。
CoherenceCompositionNaturalityは通常作用射の水平合成を入れ子bimodule射として計算し、
kernelTensorCompositionClosedIso_kernel_naturalityを既存結合子の三変数自然性から証明する。
いずれにもlocalHomKFlatは不要。追加8公開宣言の直接監査は標準3公理以内。
既存kernelCompositionIsoも再監査して同じ。合同ビルド成功（4087 jobs）。

kernelTensorCompositionSourceIsoの公開型は維持し、定義を恒等成分と全Hom map計算による
直接のNatIso.ofComponentsへ変更した。これにより成分の計算を、巨大な関手等式の輸送を展開せず使える。
資源上限の変更・新規sorry・axiom・引用はない。
全導来kernelの合成比較のkernel射自然性はまだ未完で、通常自然性からK-flat計算と
主局所化へ運ぶ必要がある。一般右随伴・unit/counitと作用coherence、U16cも未完。


## U16a8：K-flatモデルのkernel自然性と導来入力での成分計算（2026-10-17）

CoherenceCompositionKFlatNaturalityのkernelResolutionTensorCompositionIso_kernel_naturalityは、
両端が右相対K-flatな最初のkernelの任意射と、後の任意kernel射の作用合成square。
任意の指定入力射影解像度族Rを使い、localHomKFlatは要求しない。
kernelResolutionTensorCompositionIso_hom_appは増大と通常結合子での計算。
kernelDerivedTensorOnBimoduleCompositionIso_hom_appは、全導来入力へ延長した比較を
元の入力でそのモデル比較に計算する。公開名・型の変更はなく追加APIである。

追加全3宣言の直接公理監査は標準3公理のみ。合同ビルド成功（4088 jobs）。
資源上限を変更せず、成分計算を独立補題へ分けて検証した。新規sorry・axiom・引用なし。
全導来kernelのkernelCompositionIsoの射自然性・代表選択の整合性と作用coherenceは未完。
次はモデル比較のkernel自然性と今回の成分計算を主局所化からの自然変換の一意性で接続し、
K-flatkernel局所化と主導来kernel圏の比較へ運ぶ。一般右随伴・unit/counit、U16a全受入とU16cも未完。


## U16a9：積局所化による全導来kernel射の自然性（2026-10-17）

CoherenceCompositionDerivedNaturalityは、通常kernelの導来作用合成比較を両kernel射に自然にした。
KernelComparisonNaturalityは主導来作用と通常代表作用の比較、およびその水平合成の自然性。
CoherenceCompositionValueNaturalityはU12e-localのK-flat値計算を両kernel射に自然な一つのsquareへまとめる。
CoherenceCompositionFamiliesは作用の合成族・合成kernelの作用族、CoherenceCompositionLocalizationは
それらの積圏表示とkernelCompositionModelsを定義する。射のクラスは
rightKFlatQuasiIsoとBimoduleCategory.quasiIsoの積。始域DのlocalHomKFlatの下で積関手が指定局所化になる。
Mathlibの積局所化と既存rightKFlatDerivedEquivalenceを使い、一般の分解経路は経由しない。

CoherenceCompositionNaturalIsoはモデル上の三つの自然な比較を合成し、
kernelCompositionNaturalIsoを積局所化から全導来kernelへ延長する。
CoherenceCompositionのkernelCompositionIsoは、同じ公開型のままこの自然な族の成分へ更新した。
公開名・型・仮定・向きの変更はなく、利用側の移行は不要。
kernelCompositionIso_naturalityは両kernelの任意の主導来射に対する比較square。
kernelCompositionIso_modelは指定モデルでの計算、kernelCompositionIso_kFlatは既存の
kernelCompositionKFlatIsoとの一致。K-flatモデルの既存計算も保持する。

CoherenceCompositionCanonicalChecksは独立宇宙・任意可換環・標数2に加え、
他担当のperfectDerivedKernelCompositionIso_naturalityのhNatをこの実際の定理で埋めて検査する。
担当28宣言を直接監査し、追加26・既存2の再監査に欠落・重複なく標準3公理のみ。
既存自然性・合成・局所受入・一般入口・別担当QuasiEquivalence入口・Spectra.StageTwoとの
合同ビルド成功（4096 jobs、警告0件）。新しいsorry・axiom・引用・資源上限変更なし。
恒等・結合の作用coherenceと一般右随伴・unit/counitは未完。U16a全受入とU16cは継続中。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionCanonicalChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionCanonicalChecks.lean
```


## U16a10：任意kernelの通常Homと表現対象の初期被覆（2026-10-17）

AdjunctionHom.leanのkernelHomModuleはP : Bimodule A E Dに沿って、全右E加群dg圏上の
代表加群Hom(−,N)をDへ制限する。kernelHomParamは既存のパラメータ付きYoneda作用の制限。
kernelHomはこれを全Hom自然なdg関手へまとめる。値はmoduleHom A E (P.rightAt d) Nそのもの。
kernelHom_map_πは全Hom写像を共変representableの写像で計算し、kernelHom_map_evalは
閉零射での出力評価が元の全Hom endの後合成であることを示す。
全右E加群型のSmall、kernelの射影性・局所Hom K-flat性は要求しない。
既存EndomorphismのYoneda・後合成計算を読み取り専用で再利用した。

AdjunctionBrownSeed.leanは任意の指定関手L : D(D) ⥤ D(E)と対象Yに対する初期生成元被覆。
brownSeedRawIndexは全てのp : D × ℤとL(moduleCompactGenerators p) ⟶ Yの対。
既存の主導来圏の局所小性とSmall.{u} Dにより、この添字がSmall.{u}であることを証明し、
brownSeedIndexでShrink.{u}を取って実際のu-small余積brownSeedを構成する。
指定したその余積の保存PreservesColimit (Discrete.functor (brownSeedFamily ...)) Lを明示し、
brownSeedMapと各成分の計算brownSeedMap_ιを与える。
brownSeedMap_generator_surjectiveは各shiftした代表加群のL像からYへの任意射が
L(brownSeed)を経由することを証明する。随伴や表現可能性の存在は入力にしていない。
恒等関手でこの保存仮定が実際に供給できることもChecksで検査する。

これらは一般導来右随伴の構成の部分成果である。kernelDerivedHom・kernelDerivedAdjunction・
unit/counitの公開契約は型のみ確定のまま。後続では次を証明する。

1. 実際のkernelDerivedTensorに対するu-small余積保存：任意J : Type uについて
   PreservesColimitsOfShape (Discrete J) (kernelDerivedTensor A D E K)。
   exact性・shiftは別担当Verdier/KernelActionTrianglesの存在を確認しており、読み取り専用で再利用する。
2. 生成元からのkernelに当たる全射をconeで殺す後続段階を作り、同じ初期射を延長する。
3. 可算telescopeとcompact生成から表現対象と全入力に自然なHom同値を作る。
4. そのHom同値から実際の右随伴・unit/counit・三角恒等式を構成する。

局所K-flat性をhomotopically projective性に置き換えていない。
一般右随伴を射影的な列だけへ縮小して受け入れるものではない。
恒等・結合の作用coherence、U16a全受入とU16cも未完である。

AdjunctionHomChecksの6宣言、AdjunctionBrownSeedChecksの9宣言（instance・abbrevを含む）を
直接監査し、宣言名の欠落・重複なく標準3公理のみ。
新旧合成自然性・別担当QuasiEquivalence入口・局所受入・一般入口・Spectra.StageTwoとの
合同ビルド成功（4097 jobs、警告0件）。新規sorry・axiom・引用・資源上限変更なし。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.AdjunctionHomChecks SerrePositivity.DifferentialGraded.Morita.AdjunctionBrownSeedChecks SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionCanonicalChecks SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence SerrePositivity.DifferentialGraded.Checks.U12eLocal SerrePositivity.DifferentialGraded.Checks.U12eGeneralInventory SerrePositivity.Spectra.StageTwo
lake env lean SerrePositivity/DifferentialGraded/Morita/AdjunctionHomChecks.lean
lake env lean SerrePositivity/DifferentialGraded/Morita/AdjunctionBrownSeedChecks.lean
```
