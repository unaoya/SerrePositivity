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

### 3. 主導来作用（型のみ確定）

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

### 5. 恒等作用・合成比較（型のみ確定）

```lean
def kernelIdentityIso :
  kernelDerivedTensor A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D)
def kernelCompositionIso (hD : localHomKFlat A D)
  (P : Kernel A D E) (Q : Kernel A E F) :
  kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E F Q ≅
    kernelDerivedTensor A D F (kernelCompose A D E F hD P Q)
```

恒等比較にlocalHomKFlatは不要。合成比較はU12e-localの結合子と同じく始域Dだけに条件を置く。
kernelComposeMapへの自然性、恒等と三因子の結合比較のcoherenceはCoherence*で証明する。
三因子D→E→F→Gで必要なのは既存結合子に現れるD・EのlocalHomKFlat。
同じkernel・固定dg圏の契約とし、中断した一般分解変更のcoherenceを待たない。

### 実装状態と他担当の利用境界

| API群 | 状態 | 他担当の利用 |
| --- | --- | --- |
| Kernel・kernelIdentity・kernelGraph・kernelCompose・kernelComposeMap | 実装・対象ビルド済み | 型・向きは上記で固定 |
| kernelTensor・値・graph一致 | 実装・対象ビルド済み | 同上 |
| 主導来作用・任意解像度計算 | 型のみ確定 | この節の型を前提に設計可能。Lean宣言はまだ未実装 |
| 一般右随伴・unit/counit | 型のみ確定 | 同上 |
| 恒等・合成の作用比較 | 型のみ確定 | 同上 |

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
