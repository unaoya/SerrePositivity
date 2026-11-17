# BS-W16 の報告（report-codex-w16.md） — G10 後の紙の一覧 L38〜L44（§209〜§219、2026-11-14）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 209. G10後の紙の一覧：受け渡しの現在地と型の記法

一覧：済み 12／全体 48（うち追加 4）

### 209.1 読んだ現在の証拠

自分の枝の界面とMayの本体に加え、main 753c269b6の
`formalization-plans/stage-ii/inf-supply-b/report-inf-supply-w2.md` §150〜153をread-onlyで確認した。
枝にmainを取り込んだとは扱わない。③-bの**B・C（停止点2a）は完成、Dと停止点2bは未完**。
§153ではG10実測19,901行、残るDは750〜1,350行で外枠20,000行のため停止している。
各図式の錐を未完成と一括りにしたり、逆にG10全体を完成扱いしたりしない。

mainの実際の公開入口は
`InfinityCategories/HA/DerivedCategoryModels/CosimplicialTotalization/StrictDerivedTotCone.lean`。
namespaceは同じパスの`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization`。
次の宣言は既にあり、⑤aで作り直すものではない。

```lean
strictDerivedTotCone (X : CosimplicialObject (Complex A)) :
  JoinCone (strictCosimplicialComplexNerve X ≫ complexOrdinaryDerivedSource A)
strictDerivedTotCone_isLimit (X : CosimplicialObject (Complex A)) :
  IsLimitCone (strictDerivedTotCone X)
strictDerivedTotCone_pullback (X : CosimplicialObject (Complex A)) :
  joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.hom ≫
    (strictDerivedTotCone X).val = (nativeDerivedCone X).val
```

これらは同じ元のstrict複体図式の全join錐と、その極限性を供給する。
全図式射・全錐族を含む`derivedTotVertexFamily`・`derivedTotConeFamily`の最終照合は
G10のDに残る。⑤aでDを新しく作らない。
③-bの§152の3b-4案R01〜R12は紙であり、BE版の完成品とは数えない。

既存のBE側で再利用するものも確認した。

| 現在ある宣言 | この紙での使い方と限界 |
| --- | --- |
| `framedLimitFunctor A K` | 同じ右frameを使う計算全関手。end/frameを再定義しない |
| `carrierFramedLimitComparisonIso` | 台の通常局所化の同型。nativeの全join錐族の比較をこれだけで済ませない |
| `algebraCAlgSource_underlyingDerivedIso A` | 元の`algebraCAlgSource A ≫ cAlgForgetDerived A`の全関手比較 |
| `cAlgForgetDerived_mapJoinCone_isLimit A c hc` | 追加輸送条件なしの既存定理。Uが極限を保つことを使うときの入口 |
| `mayPrimeFieldPowerZero_source` | 同じho(CAlg)のP⁰を、既存νと同じ厳密May演算へ引き戻す等式 |
| `mayNormalizedHomologySourceIso k n` | 元の厳密BE代数のホモロジーとΠの自然比較 |
| `FunctorIso.toNatIso`・`hoMapCompIso`・`ordinaryToHoNerve_naturalIso` | nativeの全比較を通常の全射の自然同型へ運ぶ |

Uが極限を保つことから、任意に作ったBEの錐が極限だとは推論しない。
同じBEのnative錐・普遍性は③-bの3b-4の受け渡しで確認する。
点つきKanのTotは使わず、Sp値のcoherentなP⁰へ戻らない。

### 209.2 以下の紙の記法

以下は**未実装・未elaborationの型案**。新しい`SpecifiedG10Comparison`等の構造を
Leanで作って不足を前提の中へ隠すものではない。
§112のL38〜L44・L43a・L43bを、既存の欄と実際の受け渡しへ結ぶための法則・証明分割で、
一覧の新しい項目数には加えない。元の48項目、完了12のまま。

`p : ℕ`、`[Fact p.Prime]`、`κ := EInfinityPrimeField.{u} p`、
`C := CosimplicialRingAlgebra κ`、`CA := CAlg_R κ`、`HCA := CA.HomotopyCategory`、
`Π n := homotopyGroupsOnHo κ (cAlgForgetDerived κ) n`、
`P n := barrattEcclesPowerOp0 p n`とする。これらの本体・型は現ソースにある。
`B := bfNormalizedAlgebra κ`はまだ未完成のL26の出力で、現時点の既存宣言ではない。
`F := nerveMap B ≫ algebraCAlgSource κ`、
`FHo := ordinaryToHoNerve C ⋙ hoMap F`はその出力を受けたときの紙の記法。

`T : nerve C ⟶ CA`は③-bの3b-4から**同じ指定native Tot・錐族との比較付きで**受け取る
ofCosimplicialの候補。任意の関手にTotでの演算の主張を仮定なしに要求しない。
`THo := ordinaryToHoNerve C ⋙ hoMap T`。
`e : FunctorIso F T`は全関手比較で、対象ごとの同値だけへ弱めない。
`eHo := Functor.isoWhiskerLeft (ordinaryToHoNerve C) e.toNatIso`を使う。
このeの供給と、指定錐族・同じ脚・指定射への適合こそL39の受け渡しの検収対象。

## 210. L38〜L40：native Totへの適用の型と検収

一覧：済み 12／全体 48（うち追加 4）

### 210.1 L38の同じBF模型の錐

L37の同じ標準単体のframe・augmentationからBF模型の錐を作る部分は未完。
既存の一般native錐の代用品を定義しない。紙の要求は§112と同じ。

```lean
bfCosimplicialCone (X : C) :
  JoinCone (cosimplicialNerve X ≫ discreteCAlgUnderEmbedding κ)
bfCosimplicialCone_vertex (X : C) :
  (bfCosimplicialCone X).vertex = atVertex F (nerveVertex X)
```

錐の全join射と、各qの標準の評価脚を同じframeから照合する。
③-bのR11が界面に制限して供給する
`TotalizationCone (cosimplicialNerve X ≫ discreteCAlgUnderEmbedding κ)
  (atVertex T (nerveVertex X))`
の頂点だけをBFの頂点と同一視しない。錐の移送は全join射を保って行う。
G10のstrictDerivedTotConeはUで忘れた加群側の検収に使い、BE錐の構成を肩代わりさせない。

### 210.2 L39の全関手・同じ射の比較

```lean
bfToNativeTotIso : FunctorIso F T

bfToNativeTotIso_naturality (X Y : C) (f : X ⟶ Y) :
  FHo.map f ≫ eHo.hom.app Y = eHo.hom.app X ≫ THo.map f

nativeTotHoMap (X Y : C) (f : X ⟶ Y) :
  THo.map f = SSet.HomotopyCategory.homMk ((nerve.edgeMk f).map T)
```

二番目はeHoの自然性、三番目は既存ordinaryToHoNerve・hoMapの同じ辺への評価の法則。
全native比較を供給したことをこれらの形式的法則だけで済ませない。
③-bからはTと同じ全錐族・指定脚への比較を受け取ってから、eをL39として検収する。
F側のMayの比較は、`ordinaryToHoNerve_naturalIso B`と`hoMapCompIso`で
FHoを`B ⋙ ordinaryAlgebraHoSource κ`へ運び、
`mayPrimeFieldPowerZero_source`と`mayNormalizedHomologySourceIso`を適用する。
L36の同じBF作用・同じFrobeniusの計算を、この成分へ渡す。別のνや作用へ取り替えない。

通常圏へ移した後の必要な係数移送の法則の型は次。

```lean
natTrans_transport_endomorphism {D : Type v} [Category D]
    (L M : D ⥤ AddCommGrpCat.{u}) (a : L ⟶ L) (b : M ⟶ M) (e : L ≅ M)
    (he : a ≫ e.hom = e.hom ≫ b) (X : D) (f : X ⟶ X)
    (hX : a.app X = L.map f) : b.app X = M.map f
```

このeは上の具体的なeHoをΠでwhiskerしたもの。heは既存Pの全ho(CAlg)射に対する
自然性から得る。形式的な移送のための独立の新しい数学の仮定ではない。
指定射fへのeHoの自然性と、同じ比較の逆成分で消去して示す。

### 210.3 L40の界面への最終形

```lean
barrattEcclesPowerOp0_tot
    (X : C) (f : X ⟶ X)
    (hf : ∀ j (a : (X.obj j).right), (f.app j).right.hom a = a ^ p) (n : ℤ) :
  let x := atVertex T (nerveVertex X)
  (barrattEcclesPowerOp0 p n).app (SSet.HomotopyCategory.mk x) =
    (homotopyGroupsOnHo κ (cAlgForgetDerived κ) n).map
      (SSet.HomotopyCategory.homMk ((nerve.edgeMk f).map T))
```

Tとeは上記の実際の受け渡しを前提としており、現在の新規宣言ではない。
L36のBF側の計算とL39を適用してこの型を閉じる。
同じTをAssemblyのofCosimplicialとpowerOp0_totの両方へ渡す。
Assemblyは現在この欄を残り引数に取っており、既証明の零次・正次数・離散の欄を変更しない。
対象ごとのホモロジー同型だけで、Frobeniusを指定した同じTの辺へ同定したとは扱わない。

## 211. L41〜L42：filtered塔の同じ演算とshift（紙の型）

一覧：済み 12／全体 48（うち追加 4）

### 211.1 普通の群の余極限での一意性

§112のL41の数学は可換群の余極限の普遍性。filtered性は実際の利用条件であり、
等式の消去そのものは任意の添字の余極限で成立する既存構成の法則。
この停止中にその容易な部分だけをLeanに新設することもしない。

```lean
filteredOperation_desc {I : Type v} [Category I]
    (D : I ⥤ AddCommGrpCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (P Q : c.pt ⟶ c.pt)
    (h : ∀ i, c.ι.app i ≫ P = c.ι.app i ≫ Q) : P = Q
```

L41のIsFilteredを含む元の型には、そのまま適用できる。
この型の一般化は外部の新しい数学の項目として数えず、既存余極限のhom_extの適用にすぎない。

### 211.2 nativeなfiltered余極限とho(CAlg)を混同しない型

§112のL42の紙では`hc : IsColimit c`をho(CAlg)の通常圏に書いた。
実際のA4のnative余極限から、その通常圏での普遍性まで無条件には使わない。
必要なのは同じ脚を持つcoconeと、Πによる像の可換群の余極限性である。
ネイティブのshiftを表す同じ射sと、その脚の式を入力に明示する。
元のL42でhcから作るcolimitEndomorphismも、この型のsとして適用できる。

```lean
frobeniusTower_powerOp_on_specified_cone
    (D : ℕ ⥤ HCA) (f : D ⟶ D) (c : Cocone D)
    (s : c.pt ⟶ c.pt) (hs : ∀ i, c.ι.app i ≫ s = f.app i ≫ c.ι.app i)
    (n : ℤ) (hπ : IsColimit ((Π n).mapCocone c))
    (hP : ∀ i, (P n).app (D.obj i) = (Π n).map (f.app i)) :
  (P n).app c.pt = (Π n).map s
```

Pの脚への自然性→hP→hsのΠによる像→L41の順。
Πのfiltered余極限保存自体は、忘却のsifted保存とホモロジーの比較、または対応する供給者の
指定した保存の定理として受け取る。M14で証明済みとは数えず、hπを黙って消さない。
Dのnativeな元図式、同じnative余錐の全脚、sの同じ代表辺を受け取ってcとhsを作る。
ho(CAlg)の通常のIsColimitを、nativeなIsColimitConeから無条件に生成する工程を追加しない。

### 211.3 A4の半線形塔への接続

A4の実際の塔は`Δ → φ_*Δ → φ_*²Δ → …`であり、初めから同じR上の自己射の塔とはしない。
mod pの後、κへの制限と、Frobeniusが素体上で恒等であることによる係数制限の指定同型を
使って上のD・fへ送る。`E.restrictD_homologyIso`・`E.restrict_comp`等の同じ係数比較を使い、
頂点を勝手に等しいと置かない。

既存draftsの`prismaticPerfectionFrobenius_leg`の同じ第0脚の式と、その高い項への自然性を、
c・s・hsへ照合する。全塔のshiftの同型はA4側のcofinality・完備化との両立から受け取る。
L42だけでその同型を構成したことにはしない。

```lean
frobeniusTower_powerOp_isIso
    (D : ℕ ⥤ HCA) (f : D ⟶ D) (c : Cocone D)
    (s : c.pt ⟶ c.pt) [IsIso s]
    (hs : ∀ i, c.ι.app i ≫ s = f.app i ≫ c.ι.app i)
    (n : ℤ) (hπ : IsColimit ((Π n).mapCocone c))
    (hP : ∀ i, (P n).app (D.obj i) = (Π n).map (f.app i)) :
  IsIso ((P n).app c.pt)
```

これは上の等式とfunctorが同型を保つことからの法則。
n>0なら既存`barrattEcclesPowerOp0_pos`で同じ成分は零なので、Π_nの可換群は零となる。
n=0は既存`barrattEcclesPowerOp0_zero`を同じπ₀比較で読む。
A4(a)ではH^{-n}の消滅と導来Nakayamaへ、(b)ではC/p→H⁰(X/p)の**単射**へ運ぶ。
この単射を同型として使わず、Xの離散性も仮定しない。

## 212. L43a・L43b・L43・L44：同じ二重模型の比較（紙の型）

一覧：済み 12／全体 48（うち追加 4）

### 212.1 同じ模型と作用を保持する入力

`X : SimplicialObject C`に対し、内側は同じBF正規化模型B、外側は同じ直和実現を使う。
現ソースの
`InfinityCategories/HA/DerivedCategoryModels/SimplicialRealization/DirectSumTotal.lean`
の`directSumTotalFunctor`を、台の図式に適用する。内部次数の有界性を足さない。
項はK^t = ⨁_{s≥0} (B(X_s).carrier)^{t+s}で、通常のcolimや積全複体へ替えない。
微分・shiftのKoszul符号はその既存関手の指定式を保持し、別の符号を選ばない。

`doubleRealizationModel X`、`doubleShuffleAction X`、`finiteMayPrimitive X n a`は
§112の未実装の出力の紙の名前。単に台が擬同型だからBE作用も同じとはしない。
③-bのR06・R09の模型と、同じ直和複体上のshuffle作用との適合がL43aの証明義務。
R09の台の比較だけでは、元のBE代数の射や作用の比較まで得たとは数えない。

### 212.2 固定した一覧の主張の型

```lean
-- L43a：同じ全係数・全射に沿う作用の照合。
doubleRealization_action (X : SimplicialObject C) (r : ℕ) :
  realizationAction X r = doubleShuffleAction X r

-- L43b：同じMay係数・BF切断・外側shuffleによる有限原始元。
finiteMayPrimitive_d (X : SimplicialObject C) (n : ℤ)
    (a : MayClosed (doubleRealizationModel X).carrier (-n)) :
  (doubleRealizationModel X).carrier.d (-n - 1) (-n) (finiteMayPrimitive X n a) =
    mayNormalizedValue p (doubleRealizationModel X) n (ULift.up (mayNu p n : ZMod p)) a -
      (doubleFrobeniusMap X).f (-n) a.val

-- L43：上記の同じ原始元を持つこと。
doubleMayDifferencePrimitive (X : SimplicialObject C) (n : ℤ)
    (a : MayClosed (doubleRealizationModel X).carrier (-n)) :
  ∃ H : (doubleRealizationModel X).carrier.X (-n - 1),
    (doubleRealizationModel X).carrier.d (-n - 1) (-n) H =
      mayNormalizedValue p (doubleRealizationModel X) n (ULift.up (mayNu p n : ZMod p)) a -
        (doubleFrobeniusMap X).f (-n) a.val
```

ここでdoubleFrobeniusMapは、元のXのlevelwise Frobeniusを同じ模型関手で送った複体射。
存在だけの別のFrobenius自己射を取らない。general kでは半線形の係数比較を明記するが、
この本欄の計算はκ上。`mayNormalizedValue`は既存mayDClosedと同じ係数・次数移送から
作る閉元の値の紙の名前であり、現時点の既存公開宣言としては扱わない。
n>0の負の添字の分岐も含め、全整数nを保つ。n<0や有界な入力だけに縮めない。
原始元の式では係数微分・shuffleの全境界・BF切断の境界を保持し、
閉元条件で消える項も境界計算に入れてから消す。

実際のホモロジーへの必要な法則は次（同じ原始元の既存構成への適用）。

```lean
doubleMayClass_frobenius (X : SimplicialObject C) (n : ℤ)
    (a : MayClosed (doubleRealizationModel X).carrier (-n)) :
  mayNormalizedClass p (doubleRealizationModel X) n (ULift.up (mayNu p n : ZMod p)) a =
    mayClosedClass (doubleRealizationModel X).carrier (-n)
      (mayClosedMap (doubleFrobeniusMap X) (-n) a)
```

`mayClosedClass_eq_zero_iff`・`mayClosedClass_naturality`と、既存の代表元の全射性で
閉元から全ホモロジー元へ移す。全整数次数のνは既存mayNuを保持する。

### 212.3 L44とA4-localなnative実現の最終形

紙で`R : nerve (SimplicialObject C) ⟶ CA`を、③-bの指定BE実現と同じnative頂点・
同じ実現余錐に沿う出力とする。
`D := nerveMap doubleRealizationModel ≫ algebraCAlgSource κ`、
`eR : FunctorIso D R`は、同じBE作用・同じ指定図式射を保つ比較として受け取って検収する。
別のstrictificationや一般の実現保存を⑤aで新設しない。

```lean
a4_realization_powerOp
    (X : SimplicialObject C) (f : X ⟶ X)
    (hf : ∀ s j (a : ((X.obj s).obj j).right), ((f.app s).app j).right.hom a = a ^ p)
    (n : ℤ) :
  let x := atVertex R (nerveVertex X)
  (barrattEcclesPowerOp0 p n).app (SSet.HomotopyCategory.mk x) =
    (homotopyGroupsOnHo κ (cAlgForgetDerived κ) n).map
      (SSet.HomotopyCategory.homMk ((nerve.edgeMk f).map R))
```

L43a・L43bの同じ作用と原始元からstrict側を読み、L39と同じ全関手・射の移送を使う。
このA4-localな補題を界面のpowerOp0_totの新しい欄へ広げない。
Totにおけるlevelwise Frobeniusの計算だけで、外側実現でP⁰が可換だとは推論しない。
一般のΠと実現の可換性も仮定せず、実際の同じ二重模型上の計算を保持する。

## 213. 再開時の受け渡し検収表と残作業

一覧：済み 12／全体 48（うち追加 4）

| 固定した項目 | 受け取る具体的なもの | ⑤aが検収・適用すること | 現状態 |
| --- | --- | --- | --- |
| L38 | 同じstrict複体のG10指定錐、BEの同じframeの計算 | BFの同じ全join射と標準脚 | 加群の各図式の錐はmainにある。BFとBEの比較は未完 |
| L39 | G10のDの全族、3b-4のR04・R11の同じnative比較 | F→Tの全関手同型・全射・指定錐族 | 受け渡し未完。図式ごとの錐だけで完了としない |
| L40 | 同じT・e、L36の全整数計算 | 現界面のpowerOp0_totの同じ型 | 未完 |
| L41 | 可換群の指定余極限 | hom_ext | 紙のみ |
| L42 | native塔と同じ脚、同じshift、Πによる像のIsColimit | 脚の自然性からP⁰=shift | Π保存とnative shiftを自分で供給しない。紙のみ |
| L43a | 3b-4の実現模型・指定余錐・全射 | 同じshuffleのBE作用との比較 | 紙のみ |
| L43b・L43 | 同じW係数・BF作用・外側shuffle | 指定有限原始元の微分、全整数の差の境界 | 紙のみ |
| L44 | 同じeRとnative Frobenius辺 | A4-localな実現上の成分の比較 | 紙のみ |

一般G10・strictification・BEのTot/実現の供給者側の証明を、この紙で⑤aの新しいLeanへ
振り替えない。M14本体の外枠25,000行は維持したまま。上の紙を実装・証明済みや
M14完成として数えない。M14のLeanの再開には、§208の外枠超過見込みへの調整役の判断が必要。
判断が来た後の再開箇所は§205で、G10の再実装ではない。

## 214. 紙の型の最終点検：同じ閉元とAssemblyへの渡し方

一覧：済み 12／全体 48（うち追加 4）

### 214.1 既存のMayの値との接続を明示する

現本体の`mayPowerZeroCycle`はZMod p上で定義されている。
κ上の上記二重模型では、一般kで既にある`mayDClosed`・`mayClosedIndex`と
κへ送った同じmayNuを使う。§212の紙のmayNormalizedValueは次の**同じ代表元**の値の略記とする。
別のコホモロジー類の任意の代表元を選ばない。

```lean
doubleMayNormalizedClosed (X : SimplicialObject C) (n : ℤ)
    (a : MayClosed (doubleRealizationModel X).carrier (-n)) :
    MayClosed (doubleRealizationModel X).carrier (-n) :=
  if hn : 0 ≤ mayZeroIndex p n then
    (ULift.up (mayNu p n : ZMod p) : κ) •
      mayClosedIndex (doubleRealizationModel X).carrier (mayPowerZero_degree p n hn)
        (mayDClosed (doubleRealizationModel X) p (mayZeroIndex p n).toNat (-n) a)
  else 0

doubleMayNormalizedClosed_class (X : SimplicialObject C) (n : ℤ)
    (a : MayClosed (doubleRealizationModel X).carrier (-n)) :
  mayClosedClass (doubleRealizationModel X).carrier (-n) (doubleMayNormalizedClosed X n a) =
    mayNormalizedClass p (doubleRealizationModel X) n (ULift.up (mayNu p n : ZMod p)) a
```

`mayNormalizedValue p (doubleRealizationModel X) n (ULift.up (mayNu p n : ZMod p)) a`
という§212の紙の記法は、この`doubleMayNormalizedClosed X n a`のvalを指す。
閉じていることを仮定せずkernelの構成から保持し、classの上式で本体の同じMayの演算へ戻す。
この式を新しい強いSp値の出力や、全複体の線形自己射の存在と混同しない。
この閉元の定義とclassの式も§112のL43の同じ代表元・次数移送の法則の詳細化で、
新しい一覧項目や既に検証したLeanではない。

### 214.2 全係数のTotの欄は供給者の族を受け取る

AssemblyのofCosimplicialは全Sの欄なので、κ上のT一つだけを全欄の実例としない。
③-bから全係数Sの同じTotの族と、係数制限の比較を受け取り、そのκでの制限をTとして
§210のpowerOp0_totへ渡す。ofCosimplicial_restrictその他の残り欄をこの紙で構成したとは数えない。
現`barrattEcclesTheoryOfRemaining`の既証明欄はそのまま保持する。

### 214.3 本ターンの検証と保存範囲

今回の変更は**report-codex-w16.mdのみ**。Leanの追加・編集・下書き、draftsの変更、
ビルド・小監査・共有鍵の取得は行っていない。型は全て紙であり、elaboration済みとは報告しない。
参照した既存宣言の名前と型、mainのG10停止点2aと未完D、界面のpowerOp0_totの実際の型、
既存直和全複体とMayの閉元・classの定義をread-onlyで照合した。git diff --checkを行う。
数学実測は**18,308行**、一覧は**12/48（追加4）**から変わらない。
外枠の超過見込みへの判断を待つ間、この線のLeanの停止を維持する。
M14は未完であり、/goalの完了にはしない。

## 215. 停止後の再確認：判断未更新、代わりの紙の利用側照合

一覧：済み 12／全体 48（うち追加 4）

前ターンは143b2884bで停止判断とG10後の型つき一覧を保存した進捗。
本ターン開始時の枝は同じ143b2884b、作業木は清潔。
mainは2b1085501へ進み、5∞-0のdrafts統合が取り込まれたが、
`bhatt-scholze-codex-w16.md`の末尾は§31で、M14外枠25,000行の判断は未変更だった。
したがって§208のこの線のLeanの停止を維持する。B4のやり直し・mainの取り込みはしていない。

代わりの紙の作業として、§211のfiltered塔の型を実際のA4の完備化の対象へ当て直した。
これは§209〜214の紙を実装や証明済みとして数える作業ではない。
利用側へ渡すための具体的な未供給の入力を下に記録する。

## 216. filtered塔の型の射程：raw余極限と完備化後を分ける

一覧：済み 12／全体 48（うち追加 4）

### 216.1 実際に読んだ定義

枝とmainの両方の`drafts/A4/Perfectoidization.lean`において、
`directPerfectionValue`は`directTowerColimit`の頂点に`prismCAlgCompletion`を施した対象。
`prismaticPerfection`はその対象を使う。従ってLemma 8.4の対象はrawな塔の余極限と同一ではない。
mainの統合後も、この順序は保持されていた。

mainの`prismCAlgCompletion`は、A2の`prismCompleteReflection`による反射と包含の合成。
`prismCompletion`という共通名の定義は現時点では
`drafts/A2/DerivedPrismaticCohomology.lean`にある。
これは反射の共通入口への統合であり、この名前があることだけで、M14に必要な
完備化後のP⁰と指定Frobeniusの一致が本体で証明済みとは扱わない。

読んだ`drafts/DerivedGeneral/CompletionFunctor.lean`の`completion_tensor_koszul`は、
有限Koszul商を適用した完備化単位についての型で、現draftでは証明はsorryのまま。
この型だけでは、完備化単位そのものが全Π_n上で同型・全射だとは結論しない。
また`restrictFrobeniusCompletion`は完備化と係数制限の比較であり、
P⁰と指定Frobeniusの**一致**を直接供給する型ではない。
上は読んだ宣言の型の射程の確認で、関連する一般定理のプロジェクト全体での非存在を
断言するものではない。

### 216.2 §211の適用で追加してはいけない仮定

`frobeniusTower_powerOp_on_specified_cone`は、実際のraw余極限のΠ像の余極限性が
供給されればその対象の成分の等式を与える。
完備化単位を合成した脚を同じcの脚として扱っても、完備化後のΠ像のIsColimitまで
引き継げるとは限らない。そのhπを、実際の完備化済みの対象に無条件に入れない。

§211.3のA4への接続は、完備化後のこの比較も供給されたときの利用側の筋であり、
L42だけで完備化を越えたと読める部分はこの節で明確に限定する。
P⁰が単位に自然であることと、完備化とFrobeniusが可換であることだけでは、
その単位の像での二つの作用の一致から完備化後の全元の一致へ消去できない。

### 216.3 必要な消去の仮定を露出させた、条件つきの型

記法κ・HCA・Π・Pは§209のまま。
raw対象x、完備化後の対象y、実際の単位ηと指定されたFrobenius射sx・syに対し、
自然性からの消去ができる一つの**条件つきの法則**は次。
これは仮定が得られているという主張でも、新しい承認済み一覧項目でもない。

```lean
powerOp_on_completion_of_epi
    (x y : HCA) (η : x ⟶ y) (sx : x ⟶ x) (sy : y ⟶ y)
    (hη : sx ≫ η = η ≫ sy) (n : ℤ) [Epi ((Π n).map η)]
    (hx : (P n).app x = (Π n).map sx) :
  (P n).app y = (Π n).map sy
```

紙の計算は、Pのηへの自然性、hx、hηのΠによる像を順に使い、
`(Π n).map η ≫ (P n).app y = (Π n).map η ≫ (Π n).map sy`
を得て、表示したEpiの仮定で消去するだけ。
肝心の`Epi ((Π n).map η)`を、現時点の完備化反射やKoszul比較から供給済みとは扱わない。
この仮定をAssemblyの欄やLemma 8.4の利用側へ新しく足して完成扱いすることもしない。

## 217. 完備化後の比較の受け渡し：判断が要る境界（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

### 217.1 既存L44へ渡せる場合の入力の型

L44の同じ二重模型が完備化後の対象まで表すなら、その指定Frobeniusとの比較を
**入力として確認する**ことで、§212の計算を利用できる。
以下でxκは実際の`prismaticPerfection/p`をκへ係数制限したCAlgの頂点、
σκは実際の半線形Frobeniusを同じ係数制限の同型で自己辺に移したもの。
単なるraw余極限の頂点に置き換えない。Rは§212.3の指定native実現の関手。

必要な利用側の提示の型案は次。これは新しいM14のLeanとして一覧に足さない。

```lean
a4_completed_model_frobenius_comparison :
  ∃ (M : SimplicialObject C) (ψ : M ⟶ M),
    (∀ s j (a : ((M.obj s).obj j).right), ((ψ.app s).app j).right.hom a = a ^ p) ∧
      ∃ e : SSet.HomotopyCategory.mk (atVertex R (nerveVertex M)) ≅
          SSet.HomotopyCategory.mk xκ,
        SSet.HomotopyCategory.homMk ((nerve.edgeMk ψ).map R) ≫ e.hom =
          e.hom ≫ SSet.HomotopyCategory.homMk σκ
```

このeは対象だけの選択ではなく、同じ完備化と同じFrobeniusから得る比較を表す。
供給側でnativeな全関手・同じ指定錐の比較を要求されている部分はそれを保持し、
M14の演算を読む最後にこの同型と射の式を使う。
この提示が供給されれば、L44とPのe.homへの自然性で実際のxκの成分を照合できる。
しかし、その提示を既存L44の定義だけから新しく構成済みとは扱わない。

### 217.2 別の完備化の検出を使う場合

完備化の商の塔やKoszul商で検出するなら、同じ完成対象と同じFrobeniusの辺への
比較、必要なΠの検出性、逆極限に由来する項の扱いを具体的な型で受け取る必要がある。
各商のΠ上で一致することだけで、全対象のΠ上の一致が無条件に従うとはしない。
同じMayの鎖模型で直接完備化後まで計算する場合も、その比較は現§112のL43a・L43bに
含まれる同じ模型の照合なのか、追加の数学が要るのかを判断する。

今回はどちらの経路も新しく実装しない。完備化後の提示をA4側から受け取れるか、
既存M14の二重模型の範囲にその比較が既に含まれているか、追加の定理を要するかは、
現状の型の照合だけでは確定できなかった。この判断を未証明の前提で隠さず報告する。
§208の外枠の判断に加え、再開時の利用側の検収点として残す。

## 218. 本ターンの保存範囲

一覧：済み 12／全体 48（うち追加 4）

変更はreport-codex-w16.mdだけ。前ターンの紙の一覧を実際のA4の完備化の定義へ
当て直し、raw余極限と完備化後を同一視しないための入力を具体化した。
Lean・drafts・界面・共有入口・mainは変更しない。ビルド・監査・共有鍵の取得もしていない。
数学実測18,308行、完了12/48（追加4）は不変。紙の型をelaboration済みとは扱わない。
外枠25,000行と、完成見込み25,185〜30,745行への判断はまだ未更新で、この線のLeanは停止中。
G10の後の紙の一覧は§209〜214、今回の完備化後の受け渡しの注意は§216〜217。
M14を完了にはしない。

## 219. 再開判断の再確認と /goal の blocked 記録

一覧：済み 12／全体 48（うち追加 4）

本ターンもmain 2b1085501のW16指示書とcoordination.md §2をread-onlyで確認した。
W16の末尾は§31、外枠25,000行と、超過が見込まれたときの停止規則に更新はない。
枝はb3d6bc416から変更なし、未検証のLeanはない。

同じ停止条件の継続は次の3ターンで確認した。

1. §208〜214（143b2884b）：完成見込み25,185〜30,745行を受けてLeanの停止判断を訂正。
   代わりの仕事としてG10後のnative Tot・filtered塔・二重模型の型つき一覧を具体化した。
2. §215〜218（b3d6bc416）：再開判断未更新を確認。紙の一覧を実際のA4の完備化へ照合し、
   raw余極限のΠの余極限性だけでは完備化後へのP⁰の一致を消去できない入力の不足を明示した。
3. 本ターン：再開判断未更新を再確認。指定された代わりの紙の作業は§209〜217に保存済み。
   型や範囲を自己承認で変更せずに進める、次のLeanの工程はない。

従って /goal は **blocked（調整役の判断待ち）** とする。
M14の完了を意味せず、目標・範囲・外枠を縮めない。
必要な判断は、§207〜208の規模見込みへの対応と、§216〜217の完備化後の比較を
既存のM14の模型の受け渡しに含められるか／別の供給が要るか。
その判断の後の実装再開箇所は§205の残り色の全位置・全頂点の順序同値であり、
既に証明した正の全有限対応やB4はやり直さない。

数学実測**18,308行**、一覧**12/48（追加4）**は不変。
本ターンはこの報告だけを保存する。Lean・drafts・界面・共有入口・mainには変更せず、
ビルド・監査・共有鍵の取得も行わない。

