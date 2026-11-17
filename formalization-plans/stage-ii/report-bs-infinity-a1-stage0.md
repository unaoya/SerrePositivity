# ⑤∞ A-1 段0：∞層 S1〜S8（11-12夜、紙）

IS-W1 段3の上限再見積もりに伴う、承認済みの代替作業。実装の承認や完了を主張しない。
正本は `bhatt-scholze/design/infinity-sheaves-design.md` と `drafts/Sheaves/` 全7本。
一般論の骨格を本体へ移す際は KL-W1 後の配置を使う。設計§9の旧F2パスは現行HTT・Kerodonへ読み替える。

## 型・再利用・不足・規模

| 群 | 維持する型と対象 | 本体の再利用・残る証明 | 新規実装の見込み |
| --- | --- | --- | ---: |
| S1 層条件 | `IsInfinitySheaf J F := ∀ U S, S ∈ J U → IsLimitCone (restrictionCone F S)`。小さい通常site、Eは準圏。coverage生成、sup、extensive条件も保持 | Mathlib Sieve/Over/位相。篩の圏と要素の圏の等価、元の制限錐の照合。最大篩の終対象と定値極限は既存。coverageの推移・底変換から全生成位相への閉性は新規で、単なる位相の単調性からは出ない | 700〜1,200行 |
| S2 Γ・RΓ | `globalSections F h := h.choose.vertex`、`RΓ(J,F) := Γ(sheafify J F)`。任意の前層に定義、錐と単位・射も保持 | `IsPresentable.hasLimit`、指定極限錐の一意比較、reflective subcategoryの単位を再利用。層ならRΓとΓの同じ単位からの比較、粗い位相との比較。値の対象の等号ではなく可逆な辺 | 500〜900行 |
| S3 弱終Čech | `IsLimitCone c ↔ IsLimitCone (restrictJoinCone c (cechShape d))`、逆向きは同じ頂点の錐の延長を結論にする | `CategoryTheory/CechNerveData` と BS-W17 の具体的Čech部品。G9-1〜3のleft cofinalityを使い、通常commaを非空な射集合の縮約で閉じる。存在の同値だけで指定錐の輸送を済ませない | 600〜1,000行 |
| S4 層化 | 任意presentable Eと小さいsite。`Sheafification J E` は層充満部分圏への実際の反射 | presentable関手圏、Bousfield局所置換・反射は既存。G8の正本の篩四角形は完了。G14のType uの検出族が不足。生成辺Wは(U,被覆篩,生成対象)で小さい。局所性⇔層条件を全写像空間で証明して反射へ渡す | G14を除き600〜1,000行 |
| S5 安定性・左完全性 | 安定presentable Eに対して層の部分圏の安定性、層化の有限極限保存 | 層条件を与える極限の交換、零対象・fiberでの閉性と安定部分圏の極限。左随伴一般から有限極限保存とは言わず、まず両側の安定性と有限余極限保存を示す | 600〜1,100行 |
| S6 小ささ | κで切り落としたsiteと元の構成の比較。宇宙を無条件に一段上げない | 一般の小さいsiteの層論とBS固有の濃度評価を分離する。任意κの切り落としが全siteのRΓと等しい型にはしない。閉性とcofinalな比較の仮定を個別に要する。BS固有構成の全濃度評価は未照合 | 一般比較400〜800行、BS固有は別見積もり |
| S7 CAlg値 | 忘却の極限保存・反映、`isSheaf_iff_forget`、層化・RΓとの比較 | `drafts/Sheaves/CAlgValued.lean` と既存EInfinity忘却の保守性・極限保存を使う。忘却した層化単位がD(A)値の局所同値であることは独立に必要。単にpresentableかつ極限保存・保守的な関手だから層化と可換、とする一般定理は作らない | モデル接続を除き600〜1,000行 |
| S8 空間値重み | `weightedSectionsData`、離散重みとの全関手比較、余極限→極限、`sections_localEquiv_iso` | G8の離散重み比較と元の指定錐を再利用。一般の空間値重みの右Kan拡張、単射に沿う離散押し出し、局所同値の強飽和性を別々に示す。篩四角形の完成だけで一般の重み比較の完成とはしない | 1,300〜2,300行 |

合計5,300〜9,300行。G14・G9の残り、EInfinity/Derivedのモデル固有の接続、S6のBS固有濃度評価を含まない。
これは紙の分解の見込みであり、実装開始前に各段の本体APIをもう一度型で照合する必要がある。

## drafts の確認と判断が要る点

- 層はČech層（D-S1）。hypercompletionを結論に加えない。原典のhypercompleteなRΓとの比較は、
  bounded-below等の係数条件と具体的siteでの降下を使う別の主張。一般のČech層のRΓと無条件に同一視しない。
- `CechConerveLimit.lean` のsorryコメントは効果的エピ・Bousfield–Kanを挙げるが、現行の決定は
  Quillen Aのleft版である。実装時のdocstringは現行経路に合わせる。`cechShape`はN(Δ)からの射。
- 大きいsite版は対象Type(u+1)・射Type u、Čech側は小さい。小さいsite版を宇宙を上げて適用するだけでは
  元の小さいEの極限を与えない。小さいČech形状へのcofinal性と同じ頂点の延長を証明する。
- S2の`derivedGlobalSections_of_le`は、両位相で層である同じ係数Fに対する比較の仮定を保持する。
  任意の前層の異なる層化のRΓが等しいという型にしない。
- S7の`forget_sheafify`には、単位の忘却が局所同値であることの具体的な証明が必要。
  入力のpresentable性だけで足りると扱わず、既存CAlgモデルがこの条件を供給するかを実装前に確認する。
- S6は一般論とprismatic site固有の閉性の境界を調整役に確定してもらう必要がある。
  紙の段階ではdraftsの型を変えない。

## 配置と順序

S1/S2/S4のsite共通部分は設計§9の`InfinityCategories/Sheaves/`を候補とする。
一般のcofinal性・弱可縮性は現行Kerodon、反射・presentableの検出族は現行HTT/Kerodon。
S6のprism・κの具体的条件は`BhattScholze/`、S7のdg固有接続はDerived/EInfinity側。
新しい層・入口・監査登録は調整役の判断に委ねる。

順序は G14/G9 → S1とSetSectionsの元の錐の接続 → S4 → S2 → S3 → S5、
S7はCAlg側の単位比較を確認後、S8は一般重みG8の残りと強飽和APIを確認後。
S6は必要なBS固有の閉性の表を作った後に独立の段として進める。

この紙の作業ではLeanの実装・draftsの変更・ビルドはしていない。


## 調整役判断（11-13）

上のS6のκ切り落とし・BS固有閉性の提案は取り下げる。prismatic siteの本質的小ささは5∞-0で本体化される。
S6はsiteの同値（小さい模型への置換）に沿い、層・層化・RΓを運ぶ一般補題だけを扱う。
S7の`forget_sheafify`の単位条件が⑤aのCAlg模型から供給されるかは、5∞-1段0で確認する。
配置は案どおり、入口・監査は5∞-1開始時に調整役が決める。現在の担当作業はIS-W1 G14の再開。


## 11-15朝：5∞-1の型つき一覧とS7の先行判定

一覧：済み 0／全体 8（うち追加 0）。R2：済み 1／全体 13（うち追加 11）。

ユーザー承認済みのS1〜S8を次の8個のIDとして追跡する。各ID内の構成・法則・証明分割は
数に加えない。以下は紙の型（draftsの宣言名・記法を使用）、Lean検証済みの型ではない。
全IDの完了には表の全出力が必要であり、代表の一つだけで済みにしない。
外枠18,600行、約9,300行で途中報告。既存のR2の行数はこの外枠に加算しない。

共通記法：Cは小さい通常site、JはGrothendieckTopology C、Eはquasicategory、
`Presheaf C E = ulift (nerve Cᵒᵖ) ⟶ E`。`hE : IsPresentable E` は必要箇所だけ。

| ID | 出力の型（主張の束） | 再利用と見込み |
|---|---|---|
| S1 | `IsSheaf J F := ∀ U S, S ∈ J U → IsLimitCone (restrictionCone F S)`；`IsSheaf J F ↔ ∀ U S, S ∈ J U → IsInvertibleEdge (sectionsOf_map S.functorInclusion F _ _)`；`IsSheaf (K.toGrothendieck) F ↔ ∀ U S, S ∈ K U → IsLimitCone (restrictionCone F S)`；`IsSheaf (J ⊔ J') F ↔ IsSheaf J F ∧ IsSheaf J' F`；extensive位相と有限積保存の同値 | drafts SheafCondition/SetSections、G8の元の篩錐比較。700〜1,200行 |
| S2 | `globalSectionsCone F h : JoinCone F` と `IsLimitCone`；`derivedGlobalSectionsCone J hJ hE F : JoinCone (sheafify J hJ F)` と `IsLimitCone`；`IsSheaf J F → ∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = derivedGlobalSections J hJ hE F`；射・位相比較は同じ単位と指定錐を保つ全族 | drafts GlobalSections、反射の単位と指定極限比較。500〜900行 |
| S3 | `IsLimitCone c ↔ IsLimitCone (restrictJoinCone c (cechShape d))`；逆向き `∃ c, IsLimitCone c ∧ c.vertex = c₀.vertex`（制限後の錐とc₀の指定同値を保持、11-15調整役承認）。大きいsite版も同じ頂点 | G9のleft cofinality、CategoryTheory/CechNerveData。600〜1,000行 |
| S4 | `∃ (I : Type u) (edges : I → (PresheafCat C E) _⦋1⦌), ∀ F, IsLocalObject (Set.range edges) F ↔ sheafProperty J F`；`Sheafification J E`（反射そのもの）；層化単位・層での可逆性 | G14検出族・G8・presentable関手圏のBousfield反射。600〜1,000行 |
| S5 | `[IsStable E] → IsStable (SheafCat J E)`；`[IsStable E] → PreservesFiniteLimits (sheafificationFunctor J hJ)`（記法は既存native極限条件へ展開して固定する）。零・fiberでの閉性と有限余極限保存から結ぶ | 安定部分圏と極限交換。600〜1,100行。一般のPostnikov左完全性はこの型からは結論しない |
| S6 | site同値 `e : C ≌ D` と対応する位相 `J,K` に対し `IsSheaf J (e.op.functor ⋆ F) ↔ IsSheaf K F`；反射・単位の全関手同型の輸送；`VertexIso (derivedGlobalSections J ... (e.op.functor ⋆ F)) (derivedGlobalSections K ... F)` | `⋆`はnerve/uliftによる前合成の略記。一般のsite同値と指定錐の輸送のみ。mainのPrismatic/Site/PrismOverSmallにEssentiallySmallの入力あり。κの新切り落としなし。400〜800行 |
| S7 | `IsSheaf J F ↔ IsSheaf J (F ≫ U)`；`forget_sheafify : FunctorIso (sheafify J hD ((sheafify J hC F) ≫ U)) (sheafify J hD (F ≫ U))`；`VertexIso (U(RΓ_CAlg F)) (RΓ_D (F ≫ U))` | CAlgの保守性・極限保存、単位の局所同値は独立。600〜1,000行、模型接続を除く |
| S8 | `weightedSectionsData O hE`；`weightedSections_discrete` は離散重みとの全関手同型；`IsColimitCone c → IsLimitCone (mapJoinCone (weightedSections O hE) (coconeReverseCone c))`；単射に沿う離散押し出し；`IsLocalEquivSet J φ → IsSheaf J O → IsInvertibleEdge (sectionsOf_map φ O _ _)` | G8の離散重み、右Kan拡張と強飽和API。1,300〜2,300行 |

合計5,300〜9,300行は承認済み段0を維持。未検証の略記を本体の新たな界面としない。
実装時は各束の全宣言をdraftsの元の型へ展開して記録する。S5の安定性・有限極限保存を
無条件のPostnikov左完全性に広げない。S6のPrismOverSmall入力はmainには存在するが、
現枝への未取り込みを理由にそのコードを複製しない。

### S7先行判定：単位の条件が未供給のため停止

今回読んだ本体：
`EInfinity/BarrattEccles/FreeProbeDerivedFreeForget.lean` の
`cAlgFreeForgetDerivedAdjunction` は実際のQCatAdjunction、
`cAlgForgetDerived_mapJoinCone_isLimit` は任意の指定極限錐の保存を無条件で結論する。
これらの型はサイトJ・前層F・層化単位を量化せず、局所同値を結論しない。
本体EInfinity以下の `sheafif`・`localEquiv`・`LocalEquiv` の検索でも、この接続を与える
宣言は見つからなかった。検索だけで数学的不可能性とはしないが、適用可能な証明は未供給。

必要な条件を層化の辺の型で固定すると、次である（紙）。

```lean
-- η : F → sheafify_CAlg F は指定した反射の単位
-- U_* : PSh(C,CAlg_A) → PSh(C,D(A)) は後合成
-- L_D はD(A)値の指定層化
IsInvertibleEdge (mapEdge L_D (mapEdge U_* η)).toTruncated
```

この条件は局所化がU_*ηを反転することそのもの。保守性・極限保存から得られる
「忘却した層が層」という対象側の条件と取り違えない。
局所化の普遍性で可換性を得るにも、まずこの反転性または生成局所同値のU像の反転性が必要。
free–forget随伴を使う候補では、D(A)値の層化と自由代数モナドの両立、または
代数的層化の構成が追加で必要になる。現在の随伴だけをその証明としない。

指示書11-15朝の「供給できなければ止まって報告」に従い、ここで5∞-1のLean開始を止める。
S7の型へこの条件を新たな入力として足して済ませたり、既に層であるFだけへ範囲を狭めたりしない。
選択肢は、⑤a等でこの具体的な単位条件を供給するか、S7を別の停止点に分けてS1〜S6/S8を
先行する範囲変更を調整役が決めること。どちらも今回こちらで承認済みとは扱わない。
本体Lean・drafts・他レーンのコードの変更、ビルド、鍵取得はしていない。
配置はInfinityCategories/Sheaves。実装するdocstringのHTT/Kerodon番号・Tagは各原典を照合して
記入する（今回は新規Leanのdocstringなし）。

## 11-15：S7分離後の再開

一覧：済み 0／全体 8（うち追加 0、S7は後続の停止点）。

調整役の承認に従いS1〜S6・S8を先行する。外枠18,600行、約9,300行で途中報告。
S7の単位条件は5a-4mの後とし、前節の停止を解除する。R2は停止、R3は未着手。
main `f116dfeeb` を指定枝へfast-forwardで取り込んだ。

S1の最初の証明分割を `InfinityCategories/Sheaves/SheafCondition.lean` に置く。
型はdraftsの同名宣言を保持し、現在の配置のnerveCone・JoinCone.ulift・postcompを再利用。

```lean
abbrev presheafShape (C : Type u) [SmallCategory C] : SSet.{u+1}
abbrev Presheaf (C : Type u) [SmallCategory C] (E : SSet.{u+1}) := presheafShape C ⟶ E
def sieveCategory (S : Sieve U) : Type u
def sieveDiagram (S : Sieve U) : (sieveCategory S)ᵒᵖ ⥤ Cᵒᵖ
def sieveCone (S : Sieve U) : Cone (sieveDiagram S)
def restriction (F : Presheaf C E) (S : Sieve U) : presheafShape (sieveCategory S) ⟶ E
def restrictionCone (F : Presheaf C E) (S : Sieve U) : JoinCone (restriction F S)
def IsSheaf (J : GrothendieckTopology C) (F : Presheaf C E) : Prop :=
  ∀ U S, S ∈ J U → IsLimitCone (restrictionCone F S)
lemma IsSheaf.of_le (h : J ≤ J') (hF : IsSheaf J' F) : IsSheaf J F
```

HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）はdraftsと本体の指定錐の対応をdocstringに記録。
S1のcoverage・sup・extensive・篩切断比較は未完なので、この分割でS1を完了には数えない。
初回検証ログ `/tmp/is-w1/sheaf-condition/build.log`。共有の鍵の整理券は一枚のみ。

### S1の要素圏の比較と次の接続（下書き）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`Sheaves/SieveElements.lean` に次を準備。まだ検証済みではない。

```lean
def sieveElementsToCategory (S : Sieve U) : S.functor.Elements ⥤ (sieveCategory S)ᵒᵖ
def sieveCategoryToElements (S : Sieve U) : (sieveCategory S)ᵒᵖ ⥤ S.functor.Elements
def sieveElementsEquivalence (S : Sieve U) : S.functor.Elements ≌ (sieveCategory S)ᵒᵖ
lemma sieveCategoryToElements_comp_π (S : Sieve U) :
  sieveCategoryToElements S ⋙ Functor.Elements.π S.functor = sieveDiagram S
```

S4の再利用先は現在の配置の
`Kerodon/LargeInfinityCategories/PresentableInfinityCategories/DetectingFamily` と
`BousfieldReflection`。S1の指定制限錐の極限性をG8の元の篩切断写像の可逆性へ結び、
この可逆性を小さい検出族で試して被覆篩・検出対象からなる生成辺へ渡す。
単なる対象ごとの同値を、全族の比較や層化の反射と読み替えない。

### S1の基礎の検証結果

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`SheafCondition.lean` 100行の対象ビルド成功（1,739 jobs）、11宣言の小監査は
標準三公理のみ。ログ `/tmp/is-w1/sheaf-condition/build.log`。計算上限変更なし。
S1の残りを完了扱いにしない。

次の保存則を `SieveSectionsDiagram.lean` に追加（未検証）。

```lean
abbrev sectionsOfDiagram (P : Cᵒᵖ ⥤ Type u) (F : Presheaf C E) := SetWeight.diagram P F
lemma sieveCategoryToElements_inclusion_comp_π (S : Sieve U) :
  sieveCategoryToElements S ⋙ S.functorInclusion.mapElements ⋙
    Functor.Elements.π (yoneda.obj U) = sieveDiagram S
lemma sieveSectionsDiagram_reindex (S : Sieve U) (F : Presheaf C E) :
  (SSet.uliftFunctor.map (nerveMap (sieveCategoryToElements S))) ≫
    sectionsOfDiagram S.functor F = restriction F S
```

基礎・要素圏・この再添字の3本の再検証を同じworktreeの一枚の整理券で実行中。
ログ `/tmp/is-w1/sheaf-condition/build-2.log`。元の旧E01の未検証4本は対象外。

### 最大篩の終対象（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

```lean
def topSieveIdentity (U : C) : sieveCategory (⊤ : Sieve U)
def topSieveIdentityIsTerminal (U : C) : IsTerminal (topSieveIdentity U)
```

S1の `isSheaf_bot` の証明分割。元のOver.mkIdTerminalの射と一意性を
同じ充満部分圏に読み替える。これだけでnative制限錐の極限性が済んだとはしない。

### Γの既存小極限への接続（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`Sheaves/GlobalSections.lean` にS2の最初の証明分割を準備。

```lean
def globalSectionsCone (F : Presheaf C E) (h : HasLimit F) : JoinCone F
lemma globalSectionsCone_isLimit (F : Presheaf C E) (h : HasLimit F) :
  IsLimitCone (globalSectionsCone F h)
def globalSections (F : Presheaf C E) (h : HasLimit F) : E _⦋0⦌
lemma hasLimit_presheaf (hE : IsPresentable E) (F : Presheaf C E) : HasLimit F
```

presentable係数の小極限の既存定理の適用。層化を仮定として束ねず、
後続の反射と指定単位の比較をS2の未完部分として残す。

### 指定制限錐の頂点の計算（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`RestrictionConeVertex.lean`：
```lean
lemma restrictionCone_vertex (F : Presheaf C E) (S : Sieve U) :
  (restrictionCone F S).vertex =
    F.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Opposite.op U)))
```
既存のnerveCone・ulift・後合成の頂点の計算則のみ。S1の指定錐と
G8の表現可能評価錐の頂点を同じ評価値として照合するために使う。

### S4の既存反射への接続（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`SheafificationReflection.lean` に、draftsと同じ次の型を準備。

```lean
abbrev PresheafCat C E := (ihom (presheafShape C)).obj E
def vertexToPresheaf (F : (PresheafCat C E) _⦋0⦌) : Presheaf C E
def sheafProperty J : (PresheafCat C E) _⦋0⦌ → Prop
abbrev Sheafification J E := IsReflectiveSubcategory (PresheafCat C E) (sheafProperty J)
theorem sheafification_of_generatingEdges (hE : IsPresentable E)
  (edges : I → (PresheafCat C E) _⦋1⦌)
  (hW : ∀ F, IsLocalObject (Set.range edges) F ↔ sheafProperty J F) : Sheafification J E
```

既存の一般の反射の適用の分割。`hW`を仮定にまとめたものを最終結果にはせず、
S4の本体の結論は小さい生成辺の存在とこの同値を証明した後に得る。

### 指定反射の像（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`Sheafify.lean`：
```lean
def sheafificationFunctor (hJ : Sheafification J E) : PresheafCat C E ⟶ PresheafCat C E
def sheafify (hJ : Sheafification J E) (F : Presheaf C E) : Presheaf C E
lemma isSheaf_sheafify (hJ : Sheafification J E) (F : Presheaf C E) :
  IsSheaf J (sheafify J hJ F)
```
既存の反射のlocalization_memを同じ前層圏で読む。反射の存在はまだ仮定で、
S4の生成辺の存在証明に付け替える部分は未完として保持する。

### 元の生成辺族（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`SheafGeneratingEdges.lean`：
```lean
def sheafGeneratingEdges (J : GrothendieckTopology C) (hE : IsPresentable E)
    (M : ι → E _⦋0⦌) :
  (Σ U : C, {S : Sieve U // S ∈ J U} × ι) → (PresheafCat C E) _⦋1⦌
```

各辺はG8の `SetWeight.sieveTensorEdge` そのもの。生成性の定理は未完。

### 最大篩の始対象の点（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`TopSieveInitialPoint.lean`：
```lean
def topSieveInitialPoint (U : C) : Δ[0] ⟶ presheafShape (sieveCategory (⊤ : Sieve U))
lemma topSieveInitialPoint_leftAnodyne (U : C) :
  leftAnodyneExtensions (topSieveInitialPoint U)
```
最大篩の終対象の反対と既存のnervePoint_leftAnodyneの適用。
残るのは元の制限錐をこの点へ制限した全射が定値（元の恒等脚）になる計算と、極限性の輸送。

### 最大篩と最小位相（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`TopSieveLimit.lean`：
```lean
lemma topSieveInitialPoint_eq : topSieveInitialPoint U = yonedaEquiv.symm (ULift.up (nerveVertex (op (topSieveIdentity U))))
lemma topSieveRestrictionCone_point_val :
  (restrictJoinCone (restrictionCone F (⊤ : Sieve U)) (topSieveInitialPoint U)).val =
    SSet.const (F.app _ (ULift.up (nerveVertex (Opposite.op U))))
lemma topSieveRestrictionCone_isLimit : IsLimitCone (restrictionCone F (⊤ : Sieve U))
lemma isSheaf_bot (F : Presheaf C E) : IsSheaf ⊥ F
```
既存の一点錐・left anodyne制限の極限性判定と最大篩の射の計算の適用。

### S3の指定Čech形状（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`CechShape.lean`：
```lean
def cechShape (d : CategoryTheory.CechNerveData U) : ulift (nerve SimplexCategory) ⟶ presheafShape D
def cechShapeLarge (d : CategoryTheory.CechNerveData U) : ulift (nerve SimplexCategory) ⟶ nerve Dᵒᵖ
```

単体的対象のrightOpを元の小さいΔから読む。小さいsiteと大きいsiteのサイズの差を保つ。
S3の極限性・同じ頂点での延長は、弱終性と必要な積からcommaの縮約を作った後に示す。

### 指定切断錐と層条件の比較（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

drafts `SetSections.lean` の証明済みの形の本文を、既存宣言と重複しない3本へ移した。
本体の型検証・監査はまだで、draftsの本文があることを完成の証拠とはしない。

- `SectionsOf`：`sectionsOfDiagram_hasLimit`、`sectionsOfCone`、`sectionsOf`、
  `sectionsOfCone_isLimit`、`sectionsOf_map`（選んだ錐に既存G8を適用）。
- `RepresentableSections`：`representableElementsCone` と篩への制限の一致、
  `representableSectionsCone`、頂点計算、始対象の点とleft anodyne性、
  点に制限した錐の全射の定値性、指定錐の極限性、`sectionsOf_representable`。
- `SieveSectionsCriterion`：`coneComparison_isInvertible_iff`、
  `sectionsMap_isInvertible_iff`、`uliftNerveCone_whisker_val`、
  `sieveRestrictCanonicalCone_reindex_val`、`sieveRestrictCone_isLimit_iff`、
  `sieveSectionsMap_isInvertible_iff`、`isSheaf_iff_sieveSectionsMap_isInvertible`。

主要な結論の型は次。
```lean
lemma sieveRestrictCone_isLimit_iff (cU : JoinCone (sectionsOfDiagram (yoneda.obj U) F))
  (hcU : IsLimitCone cU) :
  IsLimitCone (SetWeight.restrictSectionsCone S.functorInclusion F cU) ↔
    IsLimitCone (restrictionCone F S)
lemma sieveSectionsMap_isInvertible_iff (cS : JoinCone (sectionsOfDiagram S.functor F))
  (hcS : IsLimitCone cS) (cU : JoinCone (sectionsOfDiagram (yoneda.obj U) F))
  (hcU : IsLimitCone cU) :
  IsInvertibleEdge (SetWeight.sectionsMap S.functorInclusion F cS hcS cU hcU).toTruncated ↔
    IsLimitCone (restrictionCone F S)
```

S1の指定錐とS4のG8の元の辺を接続する証明分割。同値な頂点だけで全錐を置き換えない。

### G8の一辺の局所性（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`SieveProbeLocality.lean` の型：
```lean
lemma sieveTensorEdge_locality_iff (S : Sieve U) (hE : IsPresentable E) (M : E _⦋0⦌)
  (F : Presheaf C E) (cS : JoinCone (SetWeight.diagram S.functor F)) (hcS : IsLimitCone cS)
  (cU : JoinCone (SetWeight.diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
  IsQCatEquivalence (precompose (functorVertex F) (homMk (SetWeight.sieveTensorEdge S hE M).toTruncated)) ↔
  IsQCatEquivalence (postcompose M (homMk (SetWeight.sieveSectionsMap S F cS hcS cU hcU).toTruncated))
```
G8の指定四角形と同値の左右の消去を使うS4の照合。検出族の存在・生成性はこの後。

### 検出族での層条件の判定（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`SheafProbeCriterion.lean`：
```lean
lemma isSheaf_iff_probe_locality (J : GrothendieckTopology C) (hE : IsPresentable E)
  (M : ι → E _⦋0⦌) (hM : IsDetectingFamily M) (F : Presheaf C E) :
  IsSheaf J F ↔ ∀ U S, S ∈ J U → ∀ i,
    IsQCatEquivalence (precompose (functorVertex F)
      (homMk (SetWeight.sieveTensorEdge S hE (M i)).toTruncated))
```
S4の証明分割。G14の元の後合成による検出性と、指定切断錐の比較を直接合成する。

### 基礎11本の検証完了（11-15）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

11本・582行の対象ビルド7,187 jobs成功。65宣言の小監査は標準三公理のみ。
ログ `/tmp/is-w1/sheaf-condition/build-5.log`。プロセス終了・鍵解放確認済み。
計算上限変更なし。既存本体の変更なし。

今回の検証済み：SheafCondition、SieveElements、SieveSectionsDiagram、
TopSieveTerminal、TopSieveInitialPoint、TopSieveLimit、RestrictionConeVertex、
GlobalSections、SheafificationReflection、Sheafify、SheafGeneratingEdges。
最大篩の元の制限錐の極限性と `isSheaf_bot` を含む。
S1のcoverage/sup/extensiveと指定切断比較、S2の単位とRΓ、S4の生成性はまだ未完。
未検証のSectionsOf・RepresentableSections・SieveSectionsCriterion・SieveProbeLocality・
SheafProbeCriterion・CechShapeは作業木に置く。旧E01の四本も対象外のまま。

### S4の生成性と反射の結論（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`Sheafification.lean`：
```lean
lemma isLocalObject_sheafGeneratingEdges_iff (hE : IsPresentable E)
  (M : ι → E _⦋0⦌) (hM : IsDetectingFamily M) (F : (PresheafCat C E) _⦋0⦌) :
  IsLocalObject (Set.range (sheafGeneratingEdges J hE M)) F ↔ sheafProperty J F
theorem exists_sheafGeneratingEdges (hE : IsPresentable E) :
  ∃ (I : Type u) (edges : I → (PresheafCat C E) _⦋1⦌),
    ∀ F, IsLocalObject (Set.range edges) F ↔ sheafProperty J F
theorem sheafification_exists (hE : IsPresentable E) : Sheafification J E
```
S4の元の結論へG8・G14・Bousfield反射を合成する下書き。局所性を入力として残さない。
端点の定義上の照合を含め、Lean検証はこの後。

### 辺の代表の照合（未検証）

一覧：済み 0／全体 8（うち追加 0、S7は後続）。

`LocalEdgeRepresentative.lean`：
```lean
lemma localForEdgeRepresentative_iff (e : X.Edge x y) (z : X _⦋0⦌) :
  IsLocalForHom (homMk (edgeOfSimplex e.edge)) z ↔ IsLocalForHom (homMk e.toTruncated) z
```
S4の最後の辺族の照合でのwhnf時間切れを避ける計算の分割。端点の等式を除去するだけ。
上限は変更しない。前段の切断錐比較・一辺局所性・検出族判定はbuild-7まで対象ビルド成功、
反射存在の最後の組み立てと全体の監査は未完。

## S4完了：生成辺から実反射へ（11-15）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

19本・1207行、対象ビルド7,316 jobs成功。107宣言の小監査で標準三公理のみ。
ログ `/tmp/is-w1/sheaf-condition/build-9.log`。プロセス終了・鍵解放確認済み。
計算上限変更なし。本体の既存宣言の変更なし。

S4の完了証拠：`Sheafification.lean` の
`isLocalObject_sheafGeneratingEdges_iff`、`exists_sheafGeneratingEdges`、
`sheafification_exists` が、生成性を仮定せず任意の小さいsite・presentable係数に対して成立。
G8の元の篩辺、指定切断錐との一致、G14のType uの検出族を実際に合成した。
最後の辺の端点のwhnf時間切れは、任意の辺で端点の等式を除去する
`localForEdgeRepresentative_iff` に分割して解消。

今回追加検証された束は、CechShape、SectionsOf、RepresentableSections、
SieveSectionsCriterion、SieveProbeLocality、SheafProbeCriterion、
LocalEdgeRepresentative、Sheafification。S1のcoverage/sup/extensive、
S2の単位とRΓ、S3のcofinality、S5、S6、S8は引き続き未完。
S1の指定切断錐と篩切断写像の可逆性の同値も検証済みだが、
これをS1全体の完了には数えない。S8の一般重み・局所同値も未完。
次はS2の同じ反射の単位とRΓ、S1の生成位相の判定に進む。

### S2：同じ反射の単位（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`SheafifyUnit.lean`：
```lean
lemma functorVertex_sheafify : functorVertex (sheafify J hJ F) = (sheafificationFunctor J hJ).app _ (functorVertex F)
def sheafifyUnitHom : FunctorHom F (sheafify J hJ F)
def sheafifyUnit : SSet.Homotopy F (sheafify J hJ F)
lemma sheafifyUnitHom_isIso_of_isSheaf (hF : IsSheaf J F) : IsIso (sheafifyUnitHom J hJ F)
lemma sheafifyUnit_isEquivalence_of_isSheaf (hF : IsSheaf J F) :
  IsInvertibleEdge (functorEdgeOfSimplicialHomotopy (sheafifyUnit J hJ F))
```
反射単位の成分と、前層の頂点の往復の等式による移送。層ではisLocal_inclusionを適用する。

### S2：単位の検証と RΓ の定義（11-15）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

SheafifyUnit の対象ビルド7,163 jobs成功、6宣言の標準三公理のみの監査成功。
ログ `/tmp/is-w1/sheaf-unit/build-2.log`。鍵解放確認済み。

次の証明分割（未検証）：`DerivedGlobalSections.lean`。
```lean
def derivedGlobalSectionsCone J hJ hE F : JoinCone (sheafify J hJ F)
lemma derivedGlobalSectionsCone_isLimit : IsLimitCone (derivedGlobalSectionsCone J hJ hE F)
def derivedGlobalSections J hJ hE F : E _⦋0⦌
lemma derivedGlobalSectionsCone_vertex :
  (derivedGlobalSectionsCone J hJ hE F).vertex = derivedGlobalSections J hJ hE F
```

### S2：単位に沿う指定錐の輸送（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`SheafUnitConeTransport.lean` は次の証明分割。
```lean
def sheafifyUnitPrism J hJ F : Δ[1] ⊗ presheafShape C ⟶ E
lemma sheafifyUnitPrism_zero : prismEndpoint 0 _ ≫ sheafifyUnitPrism J hJ F = F
lemma sheafifyUnitPrism_one : prismEndpoint 1 _ ≫ sheafifyUnitPrism J hJ F = sheafify J hJ F
lemma sheafifyUnitPrism_vertex_isInvertible (hF : IsSheaf J F) (x : (presheafShape C) _⦋0⦌) :
  IsInvertibleEdge (edgeOfSimplex ((sheafifyUnitPrism J hJ F).app _ (id₁, constant x 1)))
def sheafUnitLimitConeTransport (hF : IsSheaf J F) (d : JoinCone (sheafify J hJ F))
  (hd : IsLimitCone d) : SpecifiedLimitConeTransport (p := F) (sheafifyUnitPrism J hJ F) d
lemma derivedGlobalSections_isLimitVertex_of_isSheaf (hF : IsSheaf J F) :
  ∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = derivedGlobalSections J hJ hE F
```
元の単位とそのホモトピー代表を固定。既存の specifiedLimitConeTransport の
境界と全頂点の可逆性も返す。単なる独立な対象同型への置換はしない。

### S2：射と全パラメータの関手（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`GlobalSectionsFunctor.lean` の証明分割：
```lean
lemma exists_globalSectionsFunctor hE :
  ∃ R : PresheafCat C E ⟶ E, Nonempty (QCatAdjunction (constantFunctorMap (presheafShape C) E) R)
def globalSectionsFunctor hE : PresheafCat C E ⟶ E
def globalSectionsAdjunction hE :
  QCatAdjunction (constantFunctorMap (presheafShape C) E) (globalSectionsFunctor hE)
def derivedGlobalSectionsFunctor J hJ hE : PresheafCat C E ⟶ E
def globalSectionsToDerivedHom J hJ hE :
  FunctorHom (globalSectionsFunctor hE) (derivedGlobalSectionsFunctor J hJ hE)
```
右随伴は既存の定値図式の余極限保存と presentable 随伴関手定理から得る。
Γ・RΓの選択済み頂点との比較はまだ残る。

### S2：選んだ頂点と全 Γ 関手の比較（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`GlobalSectionsConeComparison.lean` の法則：
```lean
def globalSectionsConeFamilyIso hE s hs :
  FunctorIso (s ≫ evaluateFunctorAt apex) ((s ≫ coneRestriction _ E) ≫ globalSectionsFunctor hE)
def globalSectionsConeValueIso hE (c : JoinCone F) (hc : IsLimitCone c) :
  VertexIso c.vertex ((globalSectionsFunctor hE).app _ (functorVertex F))
```
既存の limitConeFamily_apexIso_of_constantAdjunction を同じ右随伴へ適用し、
一つの錐は定値の全族から回収する。法則・証明分割として扱う。

### S2 の今回の検証済み部分（11-15）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

4本・275行を追加検証、全体23本・1482行。
SheafifyUnit 6宣言、DerivedGlobalSections 5宣言、
SheafUnitConeTransport と GlobalSectionsFunctor 計14宣言の小監査は標準三公理のみ。
対象ビルド7,167 jobs成功、ログ `/tmp/is-w1/sections-transport/build-3.log`。
すべてプロセス終了・鍵解放確認済み。計算上限・既存宣言は変更なし。

単位の可逆性、RΓの指定極限錐、同じ単位による頂点を固定した全錐の輸送、
Γ・RΓの全関手と同じ単位からの全自然変換まで検証した。
S2は全Γ関手と選択済み頂点の比較・位相比較が残るため完了には数えない。
GlobalSectionsConeComparison は作業木の未検証下書き。

### S2：層と位相の比較（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`DerivedGlobalSectionsComparison.lean` の法則：
```lean
theorem derivedGlobalSections_of_isSheaf (hF : IsSheaf J F) :
  ∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = derivedGlobalSections J hJ hE F
def derivedGlobalSectionsSheafIso (hF : IsSheaf J F) :
  VertexIso (derivedGlobalSections J hJ hE F) (globalSections F (hasLimit_presheaf hE F))
def derivedGlobalSectionsTopologyIso (h : J ≤ J') (hF : IsSheaf J' F) :
  VertexIso (derivedGlobalSections J hJ hE F) (derivedGlobalSections J' hJ' hE F)
theorem derivedGlobalSections_of_le (h : J ≤ J') (hF : IsSheaf J' F) :
  ∃ e : E.Edge (derivedGlobalSections J hJ hE F) (derivedGlobalSections J' hJ' hE F),
    IsInvertibleEdge e.toTruncated
```
単位で輸送した指定極限錐と同じ右随伴を用いる。

### S8：離散前層の入口（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`DiscretePresheaf.lean` の証明分割：
```lean
def discretePresheaf (P : Cᵒᵖ ⥤ Type u) : Presheaf C SpaceInfinity
lemma discretePresheaf_vertex (P : Cᵒᵖ ⥤ Type u) (U : C) :
  (discretePresheaf P).app _ (ULift.up (nerveVertex (op U))) =
    coherentNerveVertex (setsToKan.obj (P.obj (op U)))
theorem sheafification_exists_spaces J : Sheafification J SpaceInfinity
```
S8の一般重みの構成・離散重みの全関手比較・局所同値の主張はまだ未完。

### S2：選択済み RΓ 頂点の射（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`DerivedGlobalSectionsMap.lean` の法則：
```lean
def derivedGlobalSectionsValueIso J hJ hE F :
  VertexIso (derivedGlobalSections J hJ hE F) ((derivedGlobalSectionsFunctor J hJ hE).app _ (functorVertex F))
def derivedGlobalSectionsHom J hJ hE (α : FunctorHom F G) : hE(RΓ F, RΓ G)
lemma derivedGlobalSectionsHom_id : derivedGlobalSectionsHom J hJ hE (𝟙 _) = 𝟙 _
lemma derivedGlobalSectionsHom_comp α β :
  derivedGlobalSectionsHom J hJ hE (α ≫ β) = derivedGlobalSectionsHom J hJ hE α ≫ derivedGlobalSectionsHom J hJ hE β
def derivedGlobalSections_map J hJ hE (η : SSet.Homotopy F G) : E.Edge (RΓ F) (RΓ G)
lemma derivedGlobalSections_map_hom η : homMk (derivedGlobalSections_map J hJ hE η).toTruncated =
  derivedGlobalSectionsHom J hJ hE (homMk (functorEdgeOfSimplicialHomotopy η))
```
辺の代表を選ぶ前の全関手・指定比較・射の類を保持する。

### S2：層の全族の単位と位相（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`SheafGlobalSectionsFamily.lean` の既存の反射と係数移送の法則：
```lean
abbrev SheafCat J E := fullSubcomplexOnVertices (PresheafCat C E) (sheafProperty J)
def sheafInclusion J : SheafCat J E ⟶ PresheafCat C E
def sheafGlobalSectionsUnitIso J hJ hE (s : A ⟶ SheafCat J E) :
  FunctorIso ((s ≫ sheafInclusion J) ≫ globalSectionsFunctor hE)
    ((s ≫ sheafInclusion J) ≫ derivedGlobalSectionsFunctor J hJ hE)
def sheafTopologyInclusion (h : J ≤ J') : SheafCat J' E ⟶ SheafCat J E
lemma sheafTopologyInclusion_comp : sheafTopologyInclusion J J' h ≫ sheafInclusion J = sheafInclusion J'
def derivedGlobalSectionsTopologyFamilyIso (h : J ≤ J') (s : A ⟶ SheafCat J' E) :
  FunctorIso ((s ≫ sheafInclusion J') ≫ derivedGlobalSectionsFunctor J hJ hE)
    ((s ≫ sheafInclusion J') ≫ derivedGlobalSectionsFunctor J' hJ' hE)
```
任意のパラメータA、実際の全射・高次単体を保持し、比較は元の反射単位の制限から作る。

### S8：離散前層の全埋め込み（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`DiscretePresheafInclusion.lean` の既存の構成の合成と値の法則：
```lean
def kanDiscretePresheafFunctor C : (Cᵒᵖ ⥤ Type u) ⥤ KanDiagramObject Cᵒᵖ
def kanDiscretePresheafMap C : nerve (Cᵒᵖ ⥤ Type u) ⟶ PresheafCat C SpaceInfinity
lemma kanDiscretePresheafMap_vertex P : kanDiscretePresheafMap C (nerveVertex P) = functorVertex (discretePresheaf P)
lemma kanDiscretePresheafMap_edge φ : (nerve.edgeMk φ).map (kanDiscretePresheafMap C) |₁ =
  kanDiagramNaturalTransformationEdge (whiskerRight (whiskerRight φ setsToKan) kanObjectForget) |₁
def kanDiscretePresheafInclusion C : { I // 頂点と辺の上記二仕様 }
```
既存の kanDiagramBundle・nerveToCoherent・kanDiagramRealization を合成し、
同じ自然変換・高次単体を再構成しない。報告中の `|₁` は辺の一単体の略記。

### S3：指定有限冪の座標計算（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`CechPowerMaps.lean` は既存の CechNerveData の積の普遍性の法則：
```lean
def cechPowerLift d (g : Fin (n+1) → (V ⟶ U)) : V ⟶ d.obj.obj (op ⦋n⦌)
lemma cechPowerLift_proj : cechPowerLift d g ≫ d.proj n i = g i
lemma cechPower_hom_ext (h : ∀ i, f ≫ d.proj n i = g ≫ d.proj n i) : f = g
lemma cechPowerLift_proj_eq f : cechPowerLift d (fun i ↦ f ≫ d.proj n i) = f
lemma cechPowerLift_precomp : f ≫ cechPowerLift d g = cechPowerLift d (fun i ↦ f ≫ g i)
lemma cechPowerLift_map : cechPowerLift d g ≫ d.obj.map θ.op = cechPowerLift d (fun i ↦ g (θ.toOrderHom i))
```
S3の comma の点・座標・収縮を元の有限冪のまま作るための前提計算。

### S8：右 Kan 拡張の指定 Yoneda 射（未検証）

一覧：済み 1／全体 8（うち追加 0、済み：S4、S7は後続）。

`SpacePresheafYoneda.lean` は既存の構成の合成・評価の法則：
```lean
def discretePresheafInclusion C : { I // 元の頂点仕様 ∧ 各対象で集合の射を離散化する辺の仕様 }
def liftedSetYoneda C : ulift (nerve C) ⟶ nerve (Cᵒᵖ ⥤ Type u)
def oppositeSpaceYoneda C : presheafShape C ⟶ (PresheafCat C SpaceInfinity).op
```
S8の主張の型の元の指定 Yoneda 射を固定する。一般重みの右 Kan 拡張の存在と保存性はまだ残る。

## S2 完了・S3/S8 の検証済み入口（11-15）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

検証済みは全体30本・1952行、190宣言、小監査は標準三公理のみ。
追加ログ `/tmp/is-w1/sections-comparison/build-2.log`（9宣言）、
`/tmp/is-w1/sections-maps/build.log`（22宣言）、
`/tmp/is-w1/sheaf-families/build-2.log`（27宣言）。対象ビルド7,318 jobs成功。
すべてプロセス終了・鍵解放確認済み。計算上限は変更なし。

S2 完了の証拠：
- Γ と RΓ の指定極限錐・極限性、元の単位を保つ全錐の輸送。
- Γ・RΓ の実全関手、同じ反射単位からの全自然変換。
- `globalSectionsConeFamilyIso` と `globalSectionsConeValueIso` による指定錐との比較。
- `derivedGlobalSections_map` と元の射の類の回収、恒等・合成則。
- `derivedGlobalSections_of_isSheaf`、`derivedGlobalSections_of_le` は元の drafts の仮定・結論を維持。
- `sheafGlobalSectionsUnitIso`・`derivedGlobalSectionsTopologyFamilyIso` は任意のパラメータの全族に対し、
  同じ反射単位の制限から作った関手同型。独立な頂点の同型に縮めない。

S3 は CechPowerMaps の座標計算だけ、S8 は離散前層・その全埋め込み・空間値層化の存在だけ。
S3 の cofinality、S8 の一般重み・余極限を極限へ送る性質・局所同値、S1 の残り・S5・S6 は未完。
SpacePresheafYoneda は未検証の作業木に残す。

### S3：元の Čech comma の収縮関手（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`CechCommaPrefix.lean`、S3の cofinality の証明分割：
```lean
abbrev CechComma d V := CostructuredArrow d.obj.rightOp (op V)
def cechCommaPrefixLift d (r : V ⟶ U) (a : CechComma d V) : V ⟶ d.obj.obj (op ⦋a.left.len+1⦌)
lemma cechCommaPrefixLift_proj : cechCommaPrefixLift d r a ≫ d.proj _ i = Fin.cons r (fun j ↦ a.hom.unop ≫ d.proj _ j) i
lemma cechCommaPrefixLift_map : cechCommaPrefixLift d r b ≫ d.obj.map (simplexPrefixMap f.left).op = cechCommaPrefixLift d r a
def cechCommaPrefix d (r : V ⟶ U) : CechComma d V ⥤ CechComma d V
```
③-b の既存の simplexPrefixMap・恒等・合成則を再利用する。
次は恒等・根からの二つの自然変換、既存の contractionCospan、Quillen A に接続する。
対象・射の宇宙は切り離したまま。cofinalityの原典の結論を仮定に追加しない。

### S3：同じ comma の収縮の二変換（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`CechCommaContraction.lean`、S3の証明分割：
```lean
def cechCommaRoot d (r : V ⟶ U) : CechComma d V
def cechCommaToPrefix d r : 𝟭 (CechComma d V) ⟶ cechCommaPrefix d r
def cechCommaRootToPrefix d r : (Functor.const _).obj (cechCommaRoot d r) ⟶ cechCommaPrefix d r
```
weak contractibility には既存の contractionCospan を使う。
同じ宇宙を要求する nerve API への接続では AsSmall へ輸送し、
C の対象・射の宇宙を暗黙に同一視しない。

### S3：収縮の小さい模型への輸送（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`CechCommaSmallContraction.lean`、同じ収縮と二変換の係数移送・S3の証明分割：
```lean
abbrev CechCommaSmall d V := AsSmall.{max u v} (CechComma d V)
def cechCommaSmallPrefix d r : CechCommaSmall d V ⥤ CechCommaSmall d V
def cechCommaSmallToPrefix d r : 𝟭 (CechCommaSmall d V) ⟶ cechCommaSmallPrefix d r
def cechCommaSmallRootToPrefix d r : (Functor.const _).obj (AsSmall.up.obj (cechCommaRoot d r)) ⟶ cechCommaSmallPrefix d r
lemma cechCommaSmall_isWeaklyContractible (r : V ⟶ U) : IsWeaklyContractible (nerve (CechCommaSmall d V))
```
既存の contractionCospan を実際に使う。まだ原典の cofinality 自体は未完。

### S3：Quillen A の小さい模型（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`CechCofinalityModel.lean`、同じ図式の宇宙比較と S3 の証明分割：
```lean
def cechSmallFunctor d : AsSmall.{max u v} SimplexCategory ⥤ AsSmall.{0} Cᵒᵖ
lemma cechSmallFunctor_nerve_isLeftCofinal (hU : CategoryTheory.IsWeaklyTerminal U) :
  IsLeftCofinal (nerveMap (cechSmallFunctor d))
```
既存の AsSmallComma.equivalence、nerveQCatEquivalence、NerveLeftQuillenA を使用。
元の cechShape・cechShapeLarge に戻す厳密な形状の照合と指定錐への適用は後続。

### S3：共通模型の持ち上げ先（未検証の一般化）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

小さい模型での cofinality は build.log（2,123 jobs、2宣言の小監査）で一度通った。
元の E の宇宙の形状へ戻すため、未コミットの CechCommaSmallContraction と
CechCofinalityModel の共通持ち上げ先を `max u v w` に一般化して再検証する。
元の対象・射の小ささは追加せず、CechSmallFunctor は
`AsSmall.{max u v w} SimplexCategory ⥤ AsSmall.{w} Cᵒᵖ`、
`cechSmallFunctor_nerve_isLeftCofinal` も同じ任意 w の型とする。
既存の本体・コミット済み宣言は変更しない。

### S3：元の二つの Čech 形状へ戻す（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`CechShapeCofinality.lean`、同じ図式の宇宙比較とS3の証明分割：
```lean
def nerveAsSmallMaxIso (D : Type u) [Category.{v} D] : nerve D ≅ nerve (AsSmall.{max u v} D)
lemma cechShape_isLeftCofinal (hU : CategoryTheory.IsWeaklyTerminal U) : IsLeftCofinal (cechShape d)
lemma cechShapeLarge_isLeftCofinal (hU : CategoryTheory.IsWeaklyTerminal U) : IsLeftCofinal (cechShapeLarge d)
```
同じ矢の同型で戻し、旧模型の cofinality を入力には残さない。

### S3 の型の照合で見つかった段0の表の誤り（11-15、判断待ち）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

段0の S3 の表で、元 drafts より強い等式を私が書いていた。
元 `drafts/Sheaves/CechConerveLimit.lean` の `exists_limitCone_of_cech` と large 版は
```lean
∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = t.vertex
```
だが、段0の表は `restrictJoinCone c (cechShape d) = t` という厳密な延長を要求していた。
一般の cofinality は錐圏の同値を与えるが、非単射の形状に沿う任意の錐の厳密な延長は与えない。
元 drafts の同じ頂点の型へ訂正し、制限した錐と t の比較は同値で保持する案について
調整役へ確認を出した。厳密な等号を結論する部分は保留。S3 は完了に数えない。

判断によらない前向きの残り `CechLimitRestriction.lean`（未検証）：
```lean
theorem isLimitCone_iff_restrict_cech hU d F c :
  IsLimitCone c ↔ IsLimitCone (restrictJoinCone c (cechShape d))
theorem hasLimit_iff_cech hU d F : HasLimit F ↔ HasLimit (cechShape d ≫ F)
theorem isLimitCone_iff_restrict_cech_large hU d F c :
  IsLimitCone c ↔ IsLimitCone (restrictJoinCone c (cechShapeLarge d))
theorem hasLimit_iff_cech_large hU d F : HasLimit F ↔ HasLimit (cechShapeLarge d ≫ F)
```

### S8：同値な局所形状への移送の法則（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`Kerodon/LimitsAndColimits/LimitsAndColimits/EquivalentShapeLimitExistence.lean`：
```lean
lemma hasLimit_of_equivalentRestriction (f : A ⟶ B) (hf : IsQCatEquivalence f)
  (F : B ⟶ X) (hF : HasLimit (f ≫ F)) : HasLimit F
```
既存の余極限側の法則の双対。既存の因子分解・同値な単射への制限定理を使い、
添字に単射性を足さない。S8の小さい元の圏と右 Kan 局所形状の移送に使う。

### S8：一般重みの右 Kan 局所極限（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`NativeWeightedSections.lean`、S8の一般重みの存在の証明分割：
```lean
lemma nativeWeightedSectionsDiagram_hasLimit hE O P :
  HasLimit (rightKanDiagram (opFunctor.map (yonedaInfinityMap A)) O (opObjEquiv.symm (functorVertex P)))
lemma exists_nativeWeightedSections hE O :
  ∃ G ε, IsRightKanExtension (opFunctor.map (yonedaInfinityMap A)) O G ε
```
既存の小さい元の圏との比較 presheafElementsRightKanComparison、
PresentableSmallLimits、RightExistence を使う。原典の右 Kan 延長を入力にしない。
この後、固定した oppositeSpaceYoneda への全関手比較と離散重み・保存性へつなぐ。

### S3 の検証済み部分と S8 の追加入口（11-15）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

検証済み全体38本・2399行、233宣言、標準三公理のみ。
追加の SpacePresheafYoneda 5宣言、Čechの収縮と共通宇宙模型25宣言、
元の形状の cofinality 7宣言、指定極限の制限と同値な添字での存在6宣言。
ログ `/tmp/is-w1/space-yoneda/build.log`、`/tmp/is-w1/cech-cofinality/build-2.log`、
`/tmp/is-w1/cech-native/build.log`、`/tmp/is-w1/cech-limits/build.log`。
すべて対象ビルド・小監査成功、プロセス終了・鍵解放確認済み。
既存宣言・計算上限の変更なし。

S3 の未完は上記の型の確認と、確認後の同じ頂点をもつ逆向きの錐・比較。
一般の cofinality を仮定に残さず、弱終性と指定 CechNerveData から両方の元の形状の
cofinality を実際に証明した。S8 の NativeWeightedSections は未検証の作業木に残す。

### S8：同じ全切断関手の選択と値（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`NativeWeightedSectionsData.lean` の既存の構成の選択・値の法則：
```lean
def nativeWeightedSectionsData O hE : Σ G, {ε // IsRightKanExtension (opFunctor.map (yonedaInfinityMap A)) O G ε}
abbrev nativeWeightedSections O hE := (nativeWeightedSectionsData O hE).1
lemma nativeWeightedSections_isRightKanExtension :
  IsRightKanExtension (opFunctor.map (yonedaInfinityMap A)) O (nativeWeightedSections O hE) (nativeWeightedSectionsData O hE).2.val
lemma nativeWeightedSections_limitValue P : ∃ c,
  IsLimitCone c ∧ c.vertex = (nativeWeightedSections O hE).app _ P
```
局所図式は本文に固定し、一つの選択で元の全関手・変換と値を保持する。

### S1/S6：同じ全関手同型による層条件の移送（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`SheafEquivalence.lean`、元の全錐比較の法則：
```lean
lemma IsSheaf.of_functorIso (hF : IsSheaf J F) (e : FunctorIso F G) : IsSheaf J G
lemma isSheaf_iff_of_functorIso (e : FunctorIso F G) : IsSheaf J F ↔ IsSheaf J G
lemma sheafProperty_iff_of_vertexIso (e : VertexIso F G) : sheafProperty J F ↔ sheafProperty J G
```
指定篩錐の同じ全同型を使い、頂点だけの同型を層の全同型と取り違えない。

### S6：同じ site 関手の全前層圏への再添字（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`SiteReindex.lean`、既存の nerve・前合成の法則：
```lean
def siteShapeMap (f : C ⥤ D) : presheafShape C ⟶ presheafShape D
def reindexPresheaf f F : Presheaf C E
def reindexPresheafFunctor f : PresheafCat D E ⟶ PresheafCat C E
lemma siteShapeMap_isQCatEquivalence (e : C ≌ D) : IsQCatEquivalence (siteShapeMap e.functor)
lemma reindexPresheafFunctor_isQCatEquivalence (e : C ≌ D) :
  IsQCatEquivalence (reindexPresheafFunctor (E := E) e.functor)
```
S6の被覆位相・層・層化・RΓの移送はまだ未完。前層圏だけの比較でS6完了とはしない。

### S6：引き戻した篩の元の圏（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`SieveSiteComparison.lean`、既存の Over.post の制限・係数移送の法則：
```lean
def sieveSiteFunctor F S : sieveCategory (S.functorPullback F) ⥤ sieveCategory S
instance sieveSiteFunctor_faithful [F.Faithful] : (sieveSiteFunctor F S).Faithful
instance sieveSiteFunctor_full [F.Faithful] [F.Full] : (sieveSiteFunctor F S).Full
instance sieveSiteFunctor_essSurj [F.IsEquivalence] : (sieveSiteFunctor F S).EssSurj
def sieveSiteEquivalence (e : C ≌ D) S : sieveCategory (S.functorPullback e.functor) ≌ sieveCategory S
lemma sieveSiteFunctor_diagram : (sieveSiteFunctor F S).op ⋙ sieveDiagram S = sieveDiagram (S.functorPullback F) ⋙ F.op
```
元の実際の比較関手を使い、前層の頂点の対応だけで篩錐の比較を代用しない。

### S6：元の篩錐の制限比較（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`SieveSiteConeComparison.lean` の同じ指定錐の係数移送の法則：
```lean
lemma sieveSiteFunctor_cone : F.op.mapCone (sieveCone (S.functorPullback F)) = (sieveCone S).whisker (sieveSiteFunctor F S).op
lemma sieveSiteFunctor_restrictionCone_val :
  (restrictJoinCone (restrictionCone O S) (ulift.map (nerveMap (sieveSiteFunctor F S).op))).val =
    (restrictionCone (reindexPresheaf F O) (S.functorPullback F)).val
lemma isLimit_restrictionCone_site_iff (e : C ≌ D) :
  IsLimitCone (restrictionCone (reindexPresheaf e.functor O) (S.functorPullback e.functor)) ↔
    IsLimitCone (restrictionCone O S)
```
対象の対応ではなく、元の篩錐全体を同じ比較関手で制限する。

### S6：対応する被覆位相での層条件（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`SheafSiteInvariance.lean` の元の再添字と単位・余単位の法則：
```lean
def reindexPresheaf_inverseFunctorIso e O : FunctorIso (reindexPresheaf e.inverse (reindexPresheaf e.functor O)) O
lemma IsSheaf.reindex_of_equivalence (hcov : CoverPreserving J K e.functor) (hO : IsSheaf K O) :
  IsSheaf J (reindexPresheaf e.functor O)
theorem isSheaf_reindex_equivalence_iff (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse) :
  IsSheaf J (reindexPresheaf e.functor O) ↔ IsSheaf K O
theorem isSheaf_inducedTopology_equivalence_iff :
  IsSheaf J (reindexPresheaf e.functor O) ↔ IsSheaf (e.inverse.inducedTopology J) O
```
元の指定篩錐で証明する。反射の全比較・RΓの輸送、大きい元の site への接続はまだ残る。

### S8 の全右 Kan 関手と S6 の前層圏の検証（11-15）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

追加の検証済み4本・216行、全体42本・2615行、249宣言。
NativeWeightedSections 2宣言、NativeWeightedSectionsData 6宣言、
SheafEquivalence 3宣言、SiteReindex 5宣言。すべて小監査で標準三公理のみ。
対象ビルドは順に5,897・5,898・7,162・7,162 jobs成功。
ログ `/tmp/is-w1/native-weights/build.log`、`/tmp/is-w1/native-weight-data/build.log`、
`/tmp/is-w1/sheaf-equivalence/build.log`、`/tmp/is-w1/site-reindex/build.log`。
プロセス終了・鍵解放確認済み。既存宣言・計算上限の変更なし。

S8の元の反対 Yoneda に沿う一般重みの全右 Kan 関手・指定変換・各値の極限錐まで検証。
固定した離散 Yoneda 表示との全比較、余極限→極限、離散押し出しと局所同値は未完。
S6の全前層圏の比較は検証済みだが、篩錐・層・層化・RΓ・大きい模型の輸送は未完。
SieveSiteComparison・SieveSiteConeComparison・SheafSiteInvariance は未検証の作業木。
S3の型の訂正案は判断待ち。S1の残り・S5も未完。S7は後続。

### S6：全 Γ 比較の指定極限錐族（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`GlobalSectionsFamilyData.lean` の既存の極限錐の選択・全族の制限の法則：
```lean
def globalSectionsFamilyData hE : {s // s ≫ coneRestriction _ E = 𝟙 _ ∧ ∀ v, IsLimitCone (functorVertexCone (s.app _ v))}
lemma globalSectionsFamilyData_restrict : (globalSectionsFamilyData hE).val ≫ coneRestriction _ E = 𝟙 _
lemma globalSectionsFamilyData_isLimit v : IsLimitCone (functorVertexCone ((globalSectionsFamilyData hE).val.app _ v))
```
既存の exists_pointwiseLimitConeFamily を使う。
site 同値の後の全 Γ 比較では、この族を同じ形状写像で制限し、
S2の globalSectionsConeFamilyIso の二つの全比較を合成する予定。

### S6：指定 Γ 錐の値の比較（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`GlobalSectionsSiteComparison.lean` の同じ錐の移送・単位の法則：
```lean
def globalSectionsReindexIso e hE O : VertexIso (globalSections (reindexPresheaf e.functor O) _) (globalSections O _)
def derivedGlobalSectionsReindexIso_of_isSheaf (hO : IsSheaf K O) :
  VertexIso (derivedGlobalSections J hJ hE (reindexPresheaf e.functor O)) (derivedGlobalSections K hK hE O)
```
後者は S2 の単位を使う層での中間の系。S6全体の任意の前層の RΓ 比較・反射と単位の全関手比較は未完。
この中間の系で S6 の元の範囲を狭めない。

### S6：全錐族の再添字の三法則（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`Kerodon/LimitsAndColimits/LimitsAndColimits/EquivalentShapeConeFamilies.lean`：
```lean
lemma isLimitCone_functorVertexCone_reindex_iff_of_equivalence (hf : IsQCatEquivalence f) v :
  IsLimitCone (functorVertexCone (((pre (joinMap (𝟙 _) f)).app X).app _ v)) ↔ IsLimitCone (functorVertexCone v)
lemma coneReindex_precomp_restriction : (pre (joinMap (𝟙 _) f)).app X ≫ coneRestriction J X = coneRestriction K X ≫ (pre f).app X
lemma coneReindex_precomp_apex : (pre (joinMap (𝟙 _) f)).app X ≫ evaluateFunctorAt apexJ = evaluateFunctorAt apexK
```
既存の全錐の読み戻し、同値な添字の制限、join の両端自然性による前提計算。
S6の全 Γ 関手比較はこの三法則と、既存の S2 の全錐比較を組み合わせる。

### S6：全 Γ 関手の比較（未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

`GlobalSectionsSiteFamilyComparison.lean` の指定極限錐族による全係数移送：
```lean
def globalSectionsReindexFunctorIso (e : C ≌ D) hE :
  FunctorIso (reindexPresheafFunctor e.functor ≫ globalSectionsFunctor hE) (globalSectionsFunctor (C := D) hE)
```
同じ全錐族を e の元の形状写像で制限し、S2 の globalSectionsConeFamilyIso を二回使う。
射・高次単体も全前層圏上で比較する。

### S3 の訂正承認と指定比較の回収（11-15、未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7は後続）。

調整役より、型の正本は drafts/Sheaves なので、同じ頂点の元の型への訂正を承認された。
制限した錐と t の比較は指定同値として保持する。元の段0の表も訂正した。

`Kerodon/LimitsAndColimits/Cofinality/SpecifiedCofinalLimitLift.lean`：
```lean
structure CofinalLimitLiftData f F t where
  cone : JoinCone F
  isLimit : IsLimitCone cone
  vertex_eq : cone.vertex = t.vertex
  comparison : VertexIso (X := sliceOver (f ≫ F)) (restrictJoinCone cone f) t
def specifiedCofinalLimitLift f hf F t ht : CofinalLimitLiftData f F t
```
既存の cofinal 極限存在・可逆頂点への輸送・錐圏内の極限錐の一意比較を合成する。
安定性や追加の極限の存在は仮定しない。

`CechLimitLift.lean`：
```lean
def cechLimitLift hU d F t ht : CofinalLimitLiftData (cechShape d) F t
theorem exists_limitCone_of_cech hU d F t ht : ∃ c, IsLimitCone c ∧ c.vertex = t.vertex
def cechLimitLiftLarge hU d F t ht : CofinalLimitLiftData (cechShapeLarge d) F t
theorem exists_limitCone_of_cech_large hU d F t ht : ∃ c, IsLimitCone c ∧ c.vertex = t.vertex
```
全ての docstring に「制限の厳密な等号は要求しない」と明記。
`cechLimitLift.comparison` / `cechLimitLiftLarge.comparison` で指定した同値を実際に返し、
存在命題だけにはしない。

### S6：層の全部分準圏への制限（11-15、未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7 は後続）。

既存の `isQCatEquivalence_fullSubcomplexRestriction` を使い、新しい一般の同値判定は作らない。
`SheafSiteEquivalence.lean` の型：
```lean
def reindexSheafFunctor e J K hf : SheafCat K E ⟶ SheafCat J E
lemma reindexSheafFunctor_comp e J K hf :
  reindexSheafFunctor e J K hf ≫ sheafInclusion J =
    sheafInclusion K ≫ reindexPresheafFunctor e.functor
theorem reindexSheafFunctor_isQCatEquivalence e J K hf hg :
  IsQCatEquivalence (reindexSheafFunctor e J K hf)
```
前提計算は再添字の頂点における層条件の同値。全単体の再添字を包含へ制限する。
S6 の残りは層化・任意の前層の RΓ の単位を保つ比較、大きい site の小さい模型への適用。

### S6 の検証済みの区切り（11-15）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7 は後続）。

今回の7本419行・45宣言が対象ビルドと新しい環境の小監査に成功。
- `sieve-site/build-3.log`：2本14宣言、7,189 jobs。
- `sheaf-site-invariance/build-2.log`：2本13宣言、7,251 jobs。
- `global-site-families/build-2.log`：3本18宣言、7,256 jobs。
いずれも標準三公理のみ、計算上限は変更なし。検証済み全体49本3,034行・294宣言。
層条件の輸送と全 Γ 関手の比較まで。層化・任意の前層の RΓ・大きい site の比較は未完。
S3 の追加2本と S6 の `SheafSiteEquivalence` はまだコミットに含めない。
S3 初回は Prop から Type への除去制限で失敗。`Classical.choice` を明示して再検証中。

### S6：反射の輸送の前提計算（11-15、未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7 は後続）。

既存の同値の法則として、次の随伴表示を固定する。新しい逆関手を作るものではない。
```lean
def equivalenceAdjunction (e : QCatEquivalence X Y) : QCatAdjunction e.hom e.inv
```
`e.homInvIso.symm.hom` を指定単位にし、既存の全パラメータ単位 Hom 判定を使う。
逆射の充満忠実性と単位の可逆性だけで全単射を証明する。200行未満。

同じ前提計算について Mathlib の `Bicategory.Equivalence.mkOfAdjointifyCounit` が見つかったため、
Hom 全単射の証明を重ねず、同じ指定単位を持つ既存の補正を使う。
```lean
def functorIsoToQcatIso (e : FunctorIso F G) : qcatMap F ≅ qcatMap G
def adjointFunctorIsoOfRightIso (a : QCatAdjunction F G) (b : QCatAdjunction F' G')
  (e : FunctorIso G G') : FunctorIso F F'
```
後者は既存の mate 同型による係数移送。いずれも既存構成の表示・法則で、200行未満。

### S6：指定反射の全関手比較（11-15、未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7 は後続）。

`functorIsoInverseSquare` と既存の mate 同型を再利用し、任意前層上の比較を書く。
```lean
def sheafificationReindexFunctorIso e J K hf hg hJ hK :
  FunctorIso (sheafificationFunctor K hK ≫ reindexPresheafFunctor e.functor)
    (reindexPresheafFunctor e.functor ≫ sheafificationFunctor J hJ)
```
ここでは全関手同型の構成まで。元の指定単位との可換性は未検証の残りとして保持し、
これだけで S6 全体の完成とはしない。

### S6：任意前層の全 RΓ 比較（11-15、未検証）

一覧：済み 2／全体 8（うち追加 0、済み：S2・S4、S7 は後続）。

```lean
def derivedGlobalSectionsReindexFunctorIso e J K hf hg hJ hK hE :
  FunctorIso (reindexPresheafFunctor e.functor ≫ derivedGlobalSectionsFunctor J hJ hE)
    (derivedGlobalSectionsFunctor K hK hE)
```
上の層化比較を Γ で送り、検証済みの `globalSectionsReindexFunctorIso` を前合成する。
任意の前層が源で、層であるという余分な仮定は加えない。

### S3 完了：頂点の等号と指定した制限錐の同値（11-15）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

承認された訂正後の型で、S3 の逆向きを小さい site と大きい site の両方で閉じた。
- `SpecifiedCofinalLimitLift` の元の全錐 `cone` は `vertex_eq` を厳密な等号で保持。
- `comparison` は制限後の錐から指定錐への、同じ slice 圏内の指定同値。存在だけにしない。
- `CechLimitLift` の存在命題は drafts の `∃ c, IsLimitCone c ∧ c.vertex = t.vertex`。
- module docs と各宣言の docstring に「制限の厳密な等号は要求しない」を記載。

`/tmp/is-w1/cech-lift/build-2.log`：対象2本114行、5,700 jobs成功。
新しい環境の27宣言の小監査も成功、標準三公理のみ。計算上限は変更なし。
検証済み全体51本3,148行・321宣言。外枠18,600行内。
S6 の新しい4本（層圏同値・随伴表示・層化比較・任意前層RΓ比較）は別の対象検証中で、
本コミットには含めない。S1・S5・S6・S8 は継続中、S7 は指示どおり後続。

### S5：極限閉性と係数移送（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

```lean
theorem sheafProperty_limitCone J hE (c : JoinCone D) (hc : IsLimitCone c)
  (hD : ∀ k, sheafProperty J (D.app _ k)) : sheafProperty J c.vertex
lemma IsSheaf.postcomp_of_preservesSmallLimits hF G (hG : PreservesSmallLimits G) :
  IsSheaf J (F ≫ G)
lemma IsSheaf.postcomp_of_equivalence hF (e : QCatEquivalence E B) : IsSheaf J (F ≫ e.hom)
```
最初は S4 の既存生成辺と `isLocalObject_limitCone` の合成。後二つは同じ篩錐に
既存の極限保存を適用する係数移送の法則。S5 の安定性・層化の有限極限保存はまだ未完。

### S6 対象検証の修正（11-15）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

`EquivalenceAdjunction` はビルド成功。層圏への制限は層条件全体の `change` で
既定200,000 heartbeatsの `whnf` 上限に到達。上限は変えず、次の表示の法則へ分割する。
```lean
lemma vertexToPresheaf_reindex f v :
  vertexToPresheaf ((reindexPresheafFunctor f).app _ v) =
    reindexPresheaf f (vertexToPresheaf v)
lemma sheafProperty_reindex_of_equivalence e J K hf v (hv : sheafProperty K v) :
  sheafProperty J ((reindexPresheafFunctor e.functor).app _ v)
```
最初は既存の `functorVertexMap_precomp` そのもの。後者はこの等式による書き換え。
`fullSubcomplexLift` の証明引数にはコンパイルした頂点条件を渡し、巨大な条件を一度に展開しない。

### S6・S5 再検証の結果（11-15）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

`SheafSiteEquivalence` と `SheafLimitClosure` は対象ビルド成功。
S6 の既定 `whnf` 時間切れは、小さい読み戻しの等式と明示した係数引数により解消した。
層化比較の末尾では `s.hom` のままでは自動書き換えが合わないため、
元の `reindexSheafFunctor_comp` を `s.hom ≫ iJ = iK ≫ t.hom` として明示して使う。
これは既存構成の包含との可換則の再表示。5本の対象ビルドと小監査を再検証中。

### S5：周囲の前層圏の安定性の回収（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

S5 の証明を、周囲の関手圏・層の零/fiber/cofiber閉性・反射の完全性に分ける。
既存の `FunctorLoopEquivalence` と `isStable_of_loopEquivalence` をつなぐ部分：
```lean
theorem isStable_functorCategory (K X : SSet) [Quasicategory X] [IsStable X] :
  IsStable ((ihom K).obj X)
```
`HA/StableInfinityCategories/FunctorStability.lean`。既存の零対象と有限極限、
loop の全族の評価式と同値性を使う。点ごとの cofiber 選択を全族とみなす工程は作らない。
S5 の証明分割であり、一覧のIDは増やさない。

### S5：有限極限と零対象の持ち上げ（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

既存 `fullSubcomplex_hasLimit_of_apex` と空図式の指定極限錐を使う証明分割。
```lean
lemma sheafProperty_of_isTerminalVertex J hE x (hx : IsTerminalVertex x) : sheafProperty J x
theorem sheaf_hasFiniteLimits [IsStable E] J hE : HasFiniteLimits (SheafCat J E)
theorem sheaf_hasZeroVertex [IsStable E] J hE : HasZeroVertex (SheafCat J E)
```
始対象性の反映は、既存の全頂点の延長則を同じ境界へ適用する法則として分ける。
```lean
lemma fullSubcomplexOnVertices_isInitialVertex_of_image P x
  (hx : IsInitialVertex x.val) : IsInitialVertex x
```
新しい零対象の選択を仮定せず、周囲の元の零頂点を使う。各補題は200行未満。
S5 の fiber/cofiber、loop の制限、安定性と反射の有限極限保存は後続。

S6 の `SheafificationSiteComparison` は対象ビルド成功。RΓ 比較の `.postcomp` 直前の
改行が Lean の field notation の構文エラーになったため修正した。
次は S6・極限閉性の5本を先に対象ビルド・小監査し、その後 S5 の持ち上げ3本を検証する。
双方とも同じ鍵の間の検証のみで、編集は鍵を取る前に済ませる。

### S5：係数の同値を層圏へ制限（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

loop の係数同値を層圏へ制限するため、元の係数同値についての移送を分ける。
```lean
lemma vertexToPresheaf_postcomp G v :
  vertexToPresheaf (((ihom (presheafShape C)).map G).app _ v) = vertexToPresheaf v ≫ G
lemma isSheaf_postcomp_equivalence_iff J (e : QCatEquivalence E B) F :
  IsSheaf J (F ≫ e.hom) ↔ IsSheaf J F
def postcomposeSheafFunctor J (e : QCatEquivalence E B) : SheafCat J E ⟶ SheafCat J B
lemma postcomposeSheafFunctor_comp J e :
  postcomposeSheafFunctor J e ≫ sheafInclusion J =
    sheafInclusion J ≫ (ihom (presheafShape C)).map e.hom
theorem postcomposeSheafFunctor_isQCatEquivalence J e :
  IsQCatEquivalence (postcomposeSheafFunctor J e)
```
元の全後合成を既存の全部分圏の同値判定へ入れる法則。各頂点での所属の計算は
`sheafProperty_postcomp_equivalence_iff` に分ける（200行未満）。
S5 の loop の証明分割であり、S7 の忘却・層化の単位条件には使わない。

### S5：loop 図式の所属の反映（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

元の全部分複体への制限の法則：
```lean
lemma fullSubcomplexOnVertices_isZeroVertex_of_image P x
  (hx : IsZeroVertex x.val) : IsZeroVertex x
lemma fullSubcomplexOnVertices_isPullbackSquare_of_image P R
  (hR : IsPullbackSquare (R ≫ (fullSubcomplexOnVertices X P).ι)) : IsPullbackSquare R
lemma isLoopDiagramVertex_of_fullSubcomplex P v
  (hv : IsLoopDiagramVertex (((ihom square).map inclusion).app _ v)) : IsLoopDiagramVertex v
```
既存の同じ錐の反映を用いる。最後は零角二つと引き戻しの三条件への分割。
各補題は200行未満。持ち上げた全 loop 族の頂点条件の確認で使う。

### S6 全関手比較・S5 極限閉性の検証済みの区切り（11-15）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

`/tmp/is-w1/s6-s5-sequence.log` の前半：対象5本279行、7,383 jobs成功。
`/tmp/is-w1/sheaf-site-equivalence/target-audit-result.json`：25宣言、標準三公理のみ。
計算上限は変更なし。検証済み全体56本3,427行・346宣言。

S6 は層条件・層圏・層化の全関手・任意の前層の全 RΓ の比較まで検証済み。
指定単位との照合と、大きい site の小さい模型への適用は残す。S6 完成とは数えない。
S5 は局所対象の極限閉性と係数移送まで検証済み。

後半の S5 は `FunctorStability`・`FullSubcomplexInitialReflection` がビルド成功。
`SheafFiniteLimits` の空頂点の除去で `simpa` の型不一致が一つ残ったため、
空部分複体の所属の証明を直接 `False.elim` に渡す形へ直して再検証する。
この3本と係数同値・loop条件反映の2本は未検証で、コミットに含めない。

### S5：全 loop 族の四つの角（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

```lean
def sheafAmbientLoopFamily J s : SheafCat J E ⟶ loopDiagrams (PresheafCat C E)
lemma sheafAmbientLoopFamily_evaluation J s i j :
  sheafAmbientLoopFamily J s ≫ loopDiagramEvaluation (PresheafCat C E) i j =
    sheafInclusion J ≫ (ihom (presheafShape C)).map (s ≫ loopDiagramEvaluation E i j)
lemma sheafAmbientLoopFamily_target J s hs :
  sheafAmbientLoopFamily J s ≫ loopDiagramEvaluation (PresheafCat C E) 1 1 = sheafInclusion J
lemma sheafAmbientLoopFamily_corner_isSheaf J hE s hs hΩ x i j :
  sheafProperty J ((loopDiagramEvaluation (PresheafCat C E) i j).app _
    ((sheafAmbientLoopFamily J s).app _ x))
lemma sheafAmbientLoopFamily_vertices J hE s hs hΩ x :
  FunctorVertexSatisfies square (PresheafCat C E) (sheafProperty J)
    ((sheafAmbientLoopFamily J s).app _ x).val
```
前提は係数の指定 loop 切断 `s`、終点の等式 `hs`、その loop の同値性 `hΩ`。
これらは安定係数から既存の普遍四角形の族で供給する。四つの角の確認は
終点の等式・零頂点二つ・係数 loop 同値の保存に分ける。各補題は200行未満。

### S5：全 loop 族の持ち上げと元の評価の等式（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

```lean
lemma evaluateFunctorAt_postcomp F k :
  (ihom K).map F ≫ evaluateFunctorAt k = evaluateFunctorAt k ≫ F
def sheafLoopSquareFamily J hE s hs hΩ : SheafCat J E ⟶ (ihom square).obj (SheafCat J E)
lemma sheafLoopSquareFamily_comp ... :
  sheafLoopSquareFamily ... ≫ (ihom square).map (sheafInclusion J) =
    sheafAmbientLoopFamily J s ≫ loopInclusion
def sheafLoopSection J hE s hs hΩ : SheafCat J E ⟶ loopDiagrams (SheafCat J E)
lemma sheafLoopSection_comp ... : sheafLoopSection ... ≫ loopInclusion = sheafLoopSquareFamily ...
lemma sheafLoopSection_evaluation ... i j :
  (sheafLoopSection ... ≫ loopDiagramEvaluation (SheafCat J E) i j) ≫ sheafInclusion J =
    sheafAmbientLoopFamily J s ≫ loopDiagramEvaluation (PresheafCat C E) i j
lemma sheafLoopSection_target ... :
  sheafLoopSection ... ≫ loopDiagramEvaluation (SheafCat J E) 1 1 = 𝟙 (SheafCat J E)
lemma sheafLoopSection_source ... :
  sheafLoopSection ... ≫ loopDiagramEvaluation (SheafCat J E) 0 0 = postcomposeSheafFunctor J hΩ.choose
lemma sheafLoopSection_loop_isQCatEquivalence ... :
  IsQCatEquivalence (sheafLoopSection ... ≫ loopDiagramEvaluation (SheafCat J E) 0 0)
```
全族を既存の `fullSubcomplexInternalHomBackward` で移す。包含後の写像の等号を
保持し、その等号と評価の後合成則で終点と loop 関手を照合する。
いずれも既存構成の持ち上げ・係数移送・評価の法則。各補題は200行未満。

### S5：層圏の安定性への最終接続（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

```lean
theorem sheaf_isStable [IsStable E] (J : GrothendieckTopology C) (hE : IsPresentable E) :
  IsStable (SheafCat J E)
```
S5 の型は維持する。有限極限と零頂点を持ち上げ、係数の既存の全 loop 切断の
持ち上げを `isStable_of_loopEquivalence` に入れる証明分割である。
元の有限極限と同値な loop 判定を使うため、fiber/cofiber の点ごとの選択を
追加の自然性の仮定にしない。層化の有限極限保存はこの後の残り。

### S5 の入力5本の検証済みの区切り（11-15）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

`/tmp/is-w1/s5-inputs-sequence.log`：
- 関手圏の安定性・始対象の反映・層の有限極限と零対象：3本154行、7,675 jobs、5宣言の小監査成功。
- 係数同値の層圏への制限・loop条件の反映：2本152行、7,321 jobs、10宣言の小監査成功。
いずれも標準三公理のみ、計算上限変更なし。空部分複体の所属は直接 False.elim に渡した。
検証済み全体61本3,733行・361宣言。

S5 の残りは、四つの角の確認・全 loop 族の持ち上げ・層圏の安定性の接続（新しい4本、未検証）と、
指定層化の有限極限保存。S5 完成とはまだ数えない。S6 の残りは指定単位の照合と大きい site の比較。

### S5：指定反射の有限極限保存への前提計算（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

既存随伴の始終対象・極限・余極限の保存を、安定圏の完全性へつなぐ法則：
```lean
lemma QCatAdjunction.left_preservesInitialVertex a x hx : IsInitialVertex (F.app _ x)
lemma QCatAdjunction.right_preservesTerminalVertex a y hy : IsTerminalVertex (G.app _ y)
lemma adjunction_left_preservesZeroVertices a : PreservesZeroVertices F
lemma adjunction_right_preservesZeroVertices a : PreservesZeroVertices G
theorem isExactFunctor_leftAdjoint [IsStable X] [IsStable Y] a : IsExactFunctor F
theorem isExactFunctor_rightAdjoint [IsStable X] [IsStable Y] a : IsExactFunctor G
lemma isLimitCone_iff_terminal_of_initialShape (hK : Limits.IsInitial K) (c : JoinCone p) :
  IsLimitCone c ↔ IsTerminalVertex c.vertex
```
始終対象は既存の随伴の同じ写像空間比較と可縮性で判定する。零対象は既存の一意比較。
cofiber/fiber は同じ随伴の元の全錐の保存を適用する。空形状は初期対象間の
一意同型で既存の空錐へ戻す係数・形状移送である。各補題は200行未満。
S5 の既存構成の法則・証明分割で、一覧IDは増やさない。

### S5 の全 loop 族の対象検証（11-15、修正中）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

`FunctorEvaluationPostcomp` と `SheafLoopCorners` は対象ビルド成功。
`SheafLoopFamily` は、内部 Hom の法則を `rw` で当てる際の `loopDiagrams`・
`sheafInclusion` の表現の不一致と、包含の `Mono` の推論の2箇所で止まった。
法則を同じ包含の型の命題 `hb` として明示して合成し、`Mono` は元の全部分複体の
包含へ局所的に戻して供給する。計算上限は変更しない。
次は独立な随伴・空形状の3本を先に検証し、その後この4本を再検証する。

### S5：任意有限形状の指定極限錐の保存（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

```lean
lemma isExactFunctor_map_isLimit_cospan F [IsExactFunctor F] (c : JoinCone p)
  (hc : IsLimitCone c) : IsLimitCone (mapJoinCone F c)
theorem isExactFunctor_map_isLimit_finite F [IsExactFunctor F]
  {K : SSet} [K.Finite] (c : JoinCone p) (hc : IsLimitCone c) : IsLimitCone (mapJoinCone F c)
theorem sheafification_isExactFunctor [IsStable E] J hJ hE :
  IsExactFunctor (sheafificationFunctor J hJ)
theorem sheafification_map_isLimit_finite [IsStable E] J hJ hE
  {K : SSet.{u+1}} [K.Finite] {p : K ⟶ PresheafCat C E}
  (c : JoinCone p) (hc : IsLimitCone c) :
  IsLimitCone (mapJoinCone (sheafificationFunctor J hJ) c)
```
一般の完全関手の計算は、元の cospan 錐と四角形の既存の比較、空形状の判定、
`map_isLimit_finite_of_empty_pointCospan` を使用する。反射・包含は両圏の安定性の下で完全、
同じ指定自己関手への合成とする。S5 の元の有限極限保存の型を全錐で展開した最終出力。
各補題は200行未満。これらを対象ビルドと小監査で検証するまでは S5 を完成としない。

### S5 の随伴・空形状の3本の検証済みの区切り（11-15）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

`/tmp/is-w1/adjunction-loop-sequence.log` の前半と
`/tmp/is-w1/adjunction-exactness/target-audit-result.json`：
対象3本153行のビルドと7宣言の小監査に成功。標準三公理のみ、計算上限変更なし。
検証済み全体64本3,886行・368宣言。

後半の loop 族は、包含後の全写像の等式と四つの角の反映まで通った。
終点の書き換えは既知の `hs` を明示し、始点は `hΩ.choose.hom` の元の射との
定義の照合を rfl で閉じる二箇所を修正する。新しい仮定・構成は加えない。
次はこの4本の後に、層化の任意有限形状の極限保存の2本を対象ビルド・小監査する。

### S6：大きい site の同じ宇宙での形状比較（11-15、未検証）

一覧：済み 3／全体 8（うち追加 0、済み：S2・S3・S4、S7 は後続）。

`C : Type (u+1)`、射 `Type u`、小さい模型 `D : Type u`、係数 `E : SSet.{u+1}`：
```lean
def siteSmallModelShapeEquivalence (e : D ≌ C) :
  QCatEquivalence (presheafShape D) (nerve Cᵒᵖ)
lemma siteSmallModelShapeEquivalence_hom_app e σ :
  (siteSmallModelShapeEquivalence e).hom.app _ σ = σ.down ⋙ e.functor.op
def reindexSmallModelPresheafFunctor e E : (ihom (nerve Cᵒᵖ)).obj E ⟶ PresheafCat D E
lemma reindexSmallModelPresheafFunctor_isQCatEquivalence e :
  IsQCatEquivalence (reindexSmallModelPresheafFunctor e E)
lemma hasLimit_largePresheaf_of_smallModel e hE (F : nerve Cᵒᵖ ⟶ E) : HasLimit F
def essentiallySmallSiteShapeEquivalence C [EssentiallySmall.{u} C] :
  QCatEquivalence (presheafShape (SmallModel C)) (nerve Cᵒᵖ)
```
S3 の検証済み `nerveAsSmallIso`・`nerveAsSmallMaxIso` と既存の通常圏の同値を
再利用する。全 n 単体の順射の式も保持する。係数を SSet(u+2) へ上げる操作はしない。
`PrismOverSmall` は EssentiallySmall の入力を既に供給するため、BS 固有の濃度条件や
κ の切り落としは新設しない。この部品だけで層化・単位・RΓ の全輸送の完成とはしない。

### S5 完了：安定な層圏と指定層化の任意有限極限保存（11-15）

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

最終出力は、元の `SheafCat J E` の `sheaf_isStable` と
`sheafification_map_isLimit_finite`。後者は同じ `sheafificationFunctor J hJ` について
任意の `K : SSet.{u+1}`・`[K.Finite]`・元の図式 `p`・指定全錐 `c` を量化する。
終対象と引き戻しの二形状だけを最終出力とせず、既存の有限極限生成を使って閉じた。
前提は原案どおり、小さい通常 site と安定な presentable 係数。Postnikov 左完全性は追加しない。

`/tmp/is-w1/s5-final-sequence.log`：
- 全 loop 族・同じ角の等式・層圏の安定性：4本297行、7,683 jobs、21宣言の小監査成功。
- 完全関手の任意有限極限保存・指定層化への適用：2本123行、7,694 jobs、4宣言の小監査成功。
いずれも新しい環境で標準三公理のみ。sorry・新しい公理はなく、計算上限変更なし。

S5 の証明分割は極限閉性からの15本931行。段0見込み600〜1,100行の範囲内。
検証済み全体70本4,306行・393宣言、外枠18,600行内。
S1・S6・S8 は継続、S7 は指示どおり後続。S6 の新しい大きい site の形状比較は未検証。

### S6：係数と同じ宇宙での篩錐の比較（11-15、未検証）

`NativeSiteDescent.lean` に、`C : Type u`・`E : SSet.{u}` の補助表示を置く。
`nativeRestrictionCone` は既存の `sieveCone` の nerve を元の前層で後合成した指定錐。
`NativeIsSheaf J O := ∀ U S, S ∈ J U → IsLimitCone (nativeRestrictionCone O S)`。
型つきの接続は
`NativeIsSheaf J (nerveMap e.functor.op ≫ O) ↔ NativeIsSheaf K O`
（`e : C ≌ D`、両向きの被覆保存性）で、実際の篩圏の同値と錐全体の等式から証明する。
既存の `sieveSiteFunctor`・`sieveSiteEquivalence` を再利用する。
大きい site はその AsSmall 表示をこの補助表示に入れ、係数を上げずに比較する予定。
既存の層条件との接続と指定単位の照合は残り、S6 完成とは数えない。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：AsSmall 表示の篩の全射比較（11-15、未検証）

`AsSmallSieveComparison.lean` の比較は、`S : Sieve (AsSmall.up.obj U)` に対して
`AsSmall (sieveCategory (S.functorPullback AsSmall.up)) ≌ sieveCategory S`。
対応する形状比較は
`QCatEquivalence (presheafShape (sieveCategory (S.functorPullback AsSmall.up)))
  (nerve (sieveCategory S)ᵒᵖ)`。
既存の `Over.post`・充満部分圏の lift・`nerveAsSmallIso` の移送であり、
新しい被覆条件や濃度条件を追加しない。指定錐の比較を次に接続する。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：指定単位の比較に使う conjugate の法則（11-15、未検証）

既存の構成の法則として、`ConjugateUnit.lean` に次の型を書く：
`a.unit ≫ l₁ ◁ conjugateEquiv a b α = b.unit ≫ α ▷ r₂`
（任意の双圏、`a : l₁ ⊣ r₁`・`b : l₂ ⊣ r₂`・`α : l₂ ⟶ l₁`）。
逆 conjugate の型も同じ指定単位で保持する。証明は交換則二回と三角恒等式。
これは層化比較の mate の指定単位への接続の前提計算で、S6 の新しい定理としては数えない。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：既存の左随伴比較の指定単位法則（11-15、未検証）

`AdjointComparisonUnit.lean` の型は、既存の比較 `i := adjointFunctorIsoOfRightIso a b e` に対して
`a.unit ≫ qcatMap F ◁ (functorIsoToQcatIso e).hom =
 b.unit ≫ (functorIsoToQcatIso i).inv ▷ qcatMap G'`。
全二胞体の等式であり、頂点ごとの等式へ忘却しない。
S6 の検証済み層化比較で実際に用いた同じ構成の法則として接続する。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：残る同じ宇宙の指定錐・単位の接続（紙）

次の既存構成の法則を、篩固有の比較に先行させる。
`I,C : Type u`・`[SmallCategory I]`・`[SmallCategory C]`・`F : I ⥤ C`、
`c : CategoryTheory.Limits.Cone F` に対して、
`cA := (AsSmall.up.mapCone c).whisker AsSmall.down` とおく。
必要な全錐の式は
```lean
joinMap (𝟙 _) (nerveAsSmallIso I).hom ≫ (nerveCone cA).val =
  (nerveCone c).ulift.val ≫ (nerveAsSmallIso C).hom
```
である。右辺・左辺の係数となる nerve はすべて SSet(u+1)。
これを `AsSmallSieveComparison` の形状同値に適用し、元の
`restrictionCone` と `nativeRestrictionCone` の極限性を比較する。
大きい site は AsSmall 表示を経由するが、元のすべての被覆篩を用いる。

単位は、検証済み層化比較で使った同じ `t,s,rC,rD,hright` について、
`a := (equivalenceAdjunction t).comp rC.adjunction` と
`b := rD.adjunction.comp (equivalenceAdjunction s)` の
`adjointFunctorIsoOfRightIso_unit a b hright` を使う。
`functorIsoInverseSquare` の元の等式と同じ指定同値の単位を相殺し、
元の層化単位の全関手の正方形へ戻す。別の比較同型を選び直して代用しない。
S6 はこの二つの接続を終えるまで未完とする。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：錐の宇宙表示の法則の下書き（11-15、未検証）

上の紙の全錐の式を `ConeUniverseNaturality.lean` に書いた。
証明は `nerve_joinPoint_hom_ext` による点・図式・すべての脚の三つの照合。
頂点だけの比較を結論にせず、元の全錐の射の等式を保つ。
既存の構成の宇宙移送の法則として扱い、S6 の一覧の項目は追加しない。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6 の元の大きい形状の検証済みの区切り（11-15）

`SiteSmallModelShape.lean`：1本73行、対象ビルド 7,176 jobs と
10宣言の小監査成功（`/tmp/is-w1/native-site-shape-only/target-audit-result.json`）。
元の `nerve Cᵒᵖ` と小さい模型の持ち上げた nerve の同値、全単体の順射の式、
同じ係数の全前層圏の同値と極限の存在の回収、EssentiallySmall 入力まで検証した。
標準三公理のみ、計算上限変更なし。

篩錐・AsSmall 篩圏・単位法則2本・錐の宇宙表示の5本は未検証のまま作業木に残す。
今回の検証で、逆同値の型を先に明示する箇所と、合成の括弧・単位子・
ComposableArrows の脚の照合を修正している。
S6 は元の指定錐と指定単位の全比較が残るため未完。
検証済み全体71本4,379行・403宣言。S1・S6・S8 は継続、S7 は後続。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の restrictionCone への全錐の比較（11-15、未検証）

`AsSmallSiteShape.lean` に、`presheafShape C ≅ nerve (AsSmall C)ᵒᵖ` の同じ全単体の同型を置く。
`AsSmallSieveConeComparison.lean` の型は、元の `S : Sieve (AsSmall.up.obj U)` に対し
```lean
(restrictJoinCone (nativeRestrictionCone O S) (asSmallSieveShapeEquivalence S).hom).val =
  (restrictionCone ((asSmallSiteShapeIso C).hom ≫ O) (S.functorPullback AsSmall.up)).val
```
および、この等式と篩形状の同値による極限性の同値。
前の錐の宇宙表示の法則・既存の `nerveCone_whisker`・`nerveCone_mapCone` を使う。
係数は SSet(u+1) のまま、元のすべての被覆篩と指定錐を保持する。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の指定錐の宇宙表示の法則の検証済みの区切り（11-15）

`ConeUniverseNaturality.lean`：1本73行、対象ビルドと2宣言の小監査成功
（`/tmp/is-w1/native-site-universe-cone/target-audit-result.json`、標準三公理のみ）。
点・図式・全ての脚の比較により、紙に書いた `uliftNerveCone_asSmall_val` の
元の全錐の等式を証明した。計算上限変更なし。

conjugate の単位法則はビルドを通過したが、小監査はその適用ファイルの
構文の不足（Bicategory の notation）と分けて再検証する。
篩の比較は型の読み戻しを先に明示し、不要な dsimp を change に直している。
元の制限錐への比較2本は未検証のまま。
検証済み全体72本4,452行・405宣言、S6 全体は未完。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の全被覆篩の層条件への接続（11-15、未検証）

`AsSmallSiteInvariance.lean` の型は
`IsSheaf J ((asSmallSiteShapeIso C).hom ≫ O) ↔
 NativeIsSheaf ((AsSmall.down : AsSmall C ⥤ C).inducedTopology J) O`。
前提は元の `C : Type u`・`E : SSet(u+1)` の準圏性だけで、係数を上げない。
任意の AsSmall 表示の被覆篩は元の引き戻し篩へ移し、逆向きは元の篩の順像を用いる。
Mathlib の元の誘導位相の判定を再利用し、新しい被覆条件を仮定しない。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：既存の随伴比較の指定単位法則の検証済みの区切り（11-15）

`ConjugateUnit.lean`・`AdjointComparisonUnit.lean` の2本82行、
対象ビルドと4宣言の小監査成功
（`/tmp/is-w1/native-site-unit/target-audit-result.json`、標準三公理のみ）。
二度の交換則と三角恒等式から、任意の双圏での conjugate の単位法則を示し、
S6 の元の `adjointFunctorIsoOfRightIso` へ同じ全二胞体の等式として接続した。

NativeSiteDescent はビルドを通過した。AsSmall の篩比較は一般の lift の
充満忠実性の型クラスの探索を、元の Over.post の射の全射・単射の明示的適用に直す。
元の被覆篩の層条件の同値まで、残りは再検証中。
検証済み全体74本4,534行・409宣言。S6 全体の指定層化単位の照合はなお残る。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の随伴の正方形の単位法則（11-15、未検証）

`MateUnit.lean` の型は一般の双圏の `s : l₁ ⊣ r₁`・`t : l₂ ⊣ r₂`、
`α : g ≫ l₂ ⟶ l₁ ≫ h` について
```lean
𝟙 g ⊗≫ s.unit ▷ g ⊗≫ l₁ ◁ mateEquiv s t α ⊗≫ 𝟙 ((l₁ ≫ h) ≫ r₂) =
  𝟙 g ⊗≫ g ◁ t.unit ⊗≫ α ▷ r₂ ⊗≫ 𝟙 ((l₁ ≫ h) ≫ r₂)
```
（結合子・単位子は型に自動挿入される）。逆 mate の同じ単位法則も保持する。
S6 の元の層化単位の正方形へ直接接続するための、既存の構成の法則。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：同じ宇宙の層条件・AsSmall の篩形状の検証済みの区切り（11-15）

`NativeSiteDescent.lean`・`AsSmallSieveComparison.lean` の2本188行、
それぞれ対象ビルドと小監査成功（合わせて23宣言、標準三公理のみ）。
記録は `/tmp/is-w1/native-site-cones/target-audit-result.json` と
`/tmp/is-w1/native-site-assmall-comparison/target-audit-result.json`。
元の指定錐の再添字と両向きの被覆保存性により、係数と同じ宇宙で層条件を比較した。
AsSmall の篩圏の充満忠実性は、元の Over.post の射の全射・単射へ直接戻して閉じた。

元の restrictionCone への比較は、単体記法のスコープを補って再検証する。
`AsSmallSiteShape` はビルド通過、全3本を合わせた小監査はまだ通っていない。
検証済み全体76本4,722行・432宣言。S6 の元の層化単位の照合は未完。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：指定二胞体を保つ横の mate への接続（11-15、未検証）

指定単位の比較は、縦の同値の随伴表示の単位・余単位が可逆であることを使い、
Mathlib の `mateEquiv`・`conjugateIsoEquiv`・二重 mate の等式を直接組み合わせる。
`EquivalenceAdjunctionIsoData.lean` で元の同じ equivalenceAdjunction の可逆性を読み、
`EquivalenceSquareMate.lean` の型を次に固定する。
```lean
equivalenceSquareMateIso s t p q β : f₁ ≫ l₂ ≅ l₁ ≫ f₂
mateEquiv s t (equivalenceSquareMateIso s t p q β).hom = β.hom
```
縦の `p : f₁ ⊣ u₁`・`q : f₂ ⊣ u₂` の単位・余単位が可逆、
`β : r₁ ≫ f₁ ≅ f₂ ≫ r₂` は元の指定正方形。
同じ `β` と `s.unit`・`t.unit` に対する全二胞体の単位法則も結論に保持する。
これを層の包含の厳密な可換式に適用する。元の hJ・hK・指定単位を変更しない。

既存の `functorIsoOfPrecompEquivalence` の存在比較には、前合成後の二胞体を
指定値に保つ法則がない。単位の照合には上の直接の mate を用い、既存の存在比較の
宣言・型・結論は保つ。充満忠実な逆像を別途導入する案は使わず、未検証の2本は削除した。
必要な構成は既存の二重 mate と同型の全単射の合成だけである。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の全制限錐・元の位相の層条件の検証済みの区切り（11-15）

`AsSmallSiteShape`・`AsSmallSieveConeComparison`・`AsSmallSiteInvariance` の
3本193行、対象ビルドと14宣言の小監査成功
（`/tmp/is-w1/native-site-original-cone/target-audit-result.json`、標準三公理のみ）。
元の restrictionCone の全射の等式、全被覆篩での極限性の同値、
AsSmall.down による元の誘導位相での層条件の同値まで閉じた。
係数は SSet(u+1) のまま、計算上限変更なし。

mate の単位法則の内部の計算では `g ◁ t.unit` の始域が `g ≫ 𝟙 c` なので、
その直前の whiskering に右単位子を保持する形へ修正する。公開の型は保つ。
検証対象の組は次回から実行ごとに別の出力先で固定し、実行開始後に追加しない。
S6 は指定単位を保つ層化比較と、本質的小さい site の最終適用が残る。
検証済み全体79本4,915行・446宣言。S1・S6・S8 は継続、S7 は後続。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：指定正方形を mate として保つ層化比較（11-15、未検証）

`SheafificationSiteSpecifiedComparison.lean` に、元の包含の正方形を
`sheafInclusionReindexIso` として固定し、同じ hJ・hK の横の比較 α を構成する。
保持する型は
```lean
mateEquiv (Classical.choice hK).adjunction (Classical.choice hJ).adjunction
  (sheafificationReindexSpecifiedMateIso e J K hf hg hJ hK).hom =
    (functorIsoToQcatIso (sheafInclusionReindexIso e J K hf)).hom
```
および、元の全前層の層化関手間の `sheafificationReindexSpecifiedFunctorIso`。
後者は元の包含の正方形を reflector で前合成し、同じ α の逆を包含で後合成する。
一般の逆 mate の単位法則とまさに同じ二胞体の合成を使うので、指定単位の照合へ接続する。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：一般の正方形の元の単位法則の検証済みの区切り（11-15）

`MateUnit.lean`：1本56行、対象ビルド 1,580 jobs と2宣言の小監査成功
（`/tmp/is-w1/s6-mate-canonical-1/mate-unit/target-audit-result.json`、標準三公理のみ）。
元の s.unit・t.unit と正方形の mate の全二胞体の等式、逆 mate の法則を閉じた。
内側の普通の合成では `g ◁ t.unit` の始域 `g ≫ 𝟙 c` を保持し、
外側の結合子・単位子は元の型に残した。計算上限変更なし。

同値の随伴表示は端点と一胞体を明示して型探索を局所化する。
二重 mate の可逆性は自動挿入される合成の定義だけを開き、既存の IsIso の合成へ渡す。
検証済み全体80本4,971行・448宣言。S6 の適用と大きい site の最終接続は残る。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の層化単位の全正方形と同じ全 RΓ 比較（11-15、未検証）

`SheafificationSiteSpecifiedUnit.lean` は、元の `rK.adjunction.unit` を再添字で送り、
包含の指定正方形と同じ横の mate の逆を合成したものが、元の
`rJ.adjunction.unit` の再添字と等しい、という全二胞体の等式。
この二胞体の合成が `sheafificationReindexSpecifiedFunctorIso` の本文そのものである。
元の単位を複合随伴の別の単位に取り替えない。
`DerivedGlobalSectionsSiteSpecifiedComparison.lean` はこの同じ比較に Γ を後合成し、
任意の前層の全 RΓ 同型を与える。既存の Γ の指定全錐族の比較を再利用する。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：指定二胞体を保つ可逆な mate の検証済みの区切り（11-15）

`EquivalenceAdjunctionIsoData`・`EquivalenceSquareMate` の2本120行、
それぞれ対象ビルドと合わせて10宣言の小監査成功（標準三公理のみ）。
`/tmp/is-w1/s6-mate-canonical-2/{equivalence-iso-data,square-mate}/target-audit-result.json`。
指定した正方形そのものへ戻る mate の等式、元の二つの単位の正方形、
横の比較の逆を合成した単位の可換式まで閉じた。計算上限変更なし。
検証済み全体82本5,091行・458宣言。層化への適用は明示した可逆性を
補題の呼び出しにも渡して再検証する。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：大きい site の元の全被覆篩の同じ宇宙での表示（11-15、未検証）

`LargeSiteAsSmall.lean` は元の `nerve Cᵒᵖ` と `nerve (AsSmall C)ᵒᵖ` の厳密な同型を用い、
元のすべての被覆篩 S の AsSmall 表示の指定錐 `largeRestrictionCone F S` を作る。
型は
`LargeIsSheaf J F ↔ ∀ U S, S ∈ J U → IsLimitCone (largeRestrictionCone F S)`。
元の被覆篩の順像・逆像が一致する Mathlib の同値の法則を用いる。
対象 Type(u+1)・射 Type u・係数 SSet(u+1) を保ち、位相や κ の条件を新設しない。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の EssentiallySmall 入力から元の層条件の小さい模型比較（11-15、未検証）

`SiteAsSmallEquivalence` は、元の圏同値と被覆保存性を共通の宇宙の
AsSmall 表示へ移す。`LargeSiteSmallModel` の型は
```lean
IsSheaf J ((siteSmallModelShapeEquivalence e).hom ≫ F) ↔ LargeIsSheaf K F
```
（`e : D ≌ C`、元の両向きの被覆保存性）。
さらに `[EssentiallySmall.{u} C]` だけから、元の誘導位相を持つ
`SmallModel.{u} C` の同じ `IsSheaf` との同値を結論する。
`PrismOverSmall` が供給する入力をそのまま入れられ、係数は SSet(u+1) のまま。
新しい site 固有条件や κ の切り落としを作らない。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：指定単位の式の型の局所化（11-15、再検証中）

指定比較そのものと元の正方形への mate の等式はビルドを通過。
単位式では `qcatMap (F ≫ G)` を一つの原子として読む coherence の探索を避け、
元の二つの随伴と β・α の端点を、構成因子ごとの一胞体で明示した。
元の単位・指定二胞体・全比較の論理的な型は保ち、計算上限は変更しない。
次の検証は各組を固定し、指定比較1本、指定単位とRΓ2本、大きいsiteの3本を分ける。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の大きい層圏と大域切断の同じ universe の接続（11-15、未検証）

`LargeSheafSmallModel` は、元の大きい層の全部分準圏から小さい模型の層圏への
全再添字を作り、包含との厳密な可換式と `IsQCatEquivalence` を結論する。
`LargeGlobalSections` は同じ全前層圏の presentable 性を元の全同値で回収し、
`∃ R, Nonempty (QCatAdjunction (constantFunctorMap (nerve Cᵒᵖ) E) R)` を結論する。
元の定値関手を変えず、係数は SSet(u+1) のまま。小さい模型はこの存在の証明だけに用いる。
このため、選んだ元の大きい Γ 全関手は模型によらず等しいことも保持する。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の大きい Γ と模型の Γ の全関手比較（11-15、未検証）

`LargeGlobalSectionsSiteComparison` は、元の nerve Cᵒᵖ の上の全極限錐族を保持し、
`FunctorIso (reindexSmallModelPresheafFunctor e E ≫ globalSectionsFunctor hE)
 (largeGlobalSectionsFunctor e hE)` を結論する。
元の全錐族の極限性と厳密な図式の回収も保持する。点ごとの同型だけで代用しない。
小さい模型の Γ と元の大きい site の Γ の二つの定値随伴を、
検証済みの元の形状同値に沿う全錐の制限で比較する。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：元の層化単位を保つ全層化・RΓ 比較の検証済みの区切り（11-15）

`SheafificationSiteSpecifiedComparison`・`SheafificationSiteSpecifiedUnit`・
`DerivedGlobalSectionsSiteSpecifiedComparison` の3本と `LargeSiteAsSmall` の
合わせて4本285行、対象ビルド・31宣言の小監査成功（標準三公理のみ）。
記録：`/tmp/is-w1/s6-sheaf-and-large-1/` の specified-comparison・specified-unit・large-as-small。
元の hJ・hK の単位を、同じ指定正方形と横の mate の逆で保つ全二胞体の等式が通った。
元の全前層の全 RΓ 比較も同じ比較から構成した。
大きい site の元の全被覆篩での指定錐の極限性の判定まで通った。

AsSmall の site 同値の被覆保存性は、依存する篩の型を rewrite せず、
元の定義的に同じ合成関手へ change してから順像の合成則を用いる形へ修正する。
検証済み全体86本5,376行・489宣言、外枠18,600行内。
S6 は小さい模型への最終接続と大きい Γ・RΓ の同じ全比較が残る。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：大きい全前層の RΓ と元の Γ・同じ層化単位の比較（11-15、未検証）

`LargeDerivedGlobalSections` は、元の大きい全前層を小さい模型へ再添字し、
同じ `derivedGlobalSectionsFunctor J hJ hE` を合成する。
元の大きい Γ から RΓ への全自然変換は、同じ模型の `globalSectionsToDerivedHom` を使う。
元の大きい全層圏では、同じ指定層化単位を用いる全関手同型を得る。
`[EssentiallySmall.{u} C]` と係数の presentable 性だけから、元の
SmallModel と誘導位相に対する全 RΓ を定義し、元の大きい層の上で Γ との同型まで保持する。
層化を小さい模型で行うという設計を保ち、係数の universe や定義域を変えない。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：本質的小さい入力の最終適用の型クラスを明示（11-15、再検証中）

一般の site 同値から大きい層条件を小さい模型へ移す証明はビルドを通過。
最後の canonical SmallModel への適用で、逆関手という表示だけからは
Mathlib の同値の連続性が探索されなかったため、元の `(equivSmallModel C).functor` が
元の誘導位相の dense subsite である既存の instance を名前どおり明示する。
新しい仮定を追加しない。Γ・RΓ の比較でも同じ入力を明示して再検証する。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6：SmallModel の小ささの universe の明示（11-15、再検証中）

canonical SmallModel の適用では、小ささの universe を `equivSmallModel.{u} C` と
すべて明示する。dense subsite の被覆保存性を Mathlib の元の補題で直接渡す。
元の `[EssentiallySmall.{u} C]` を使い、より大きい自己模型の入力を選ばない。
型・範囲・係数の universe と計算上限は変更しない。

一覧：済み 4／全体 8（うち追加 0、済み：S2・S3・S4・S5、S7 は後続）。

### S6 完了：元の大きい site と小さい模型の比較（11-15）

最終6本428行・56宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録は `/tmp/is-w1/s6-large-model-3/` の4組。ビルド前の source SHA と
監査後・報告時のソースが一致することも検査した。

元の全被覆篩での層条件と SmallModel の層条件の同値、元の大きい層圏と
小さい層圏の全同値、元の定値関手への右随伴 Γ、全前層上の Γ・RΓ の全関手比較を得た。
指定した層化単位を保持する比較は既検証の指定 mate を使う。
`EssentiallySmall.{u}` からの適用では `equivSmallModel.{u}` と誘導位相を明示し、
係数 SSet(u+1) と元の大きい前層圏を保つ。

検証済み全体92本5,804行・545宣言、外枠18,600行内。
S6 は当初の400〜800行より増えた。元の大きい site の universe の接続、
全錐族による Γ の比較、元の層化単位を保つ mate の法則が主な増分。
S1 の被覆生成・上限位相・extensive の判定、S8 の全比較が残る。

一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：二つの篩の交叉と二段分解の比較（11-15）

`SieveFactorization` 82行・17宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-factorization-1/`。

型は `sieveFactorizationSection R S ⊣ sieveFactorizationComposite R S`。
分解の圏は Over U の充満部分圏の comma として、合成射が R ⊓ S に属し、
中間の射が R に属する二段の射を保持する。恒等分解の後の合成は厳密に恒等。
随伴の Hom 同値は全射を明示して証明した。
これを反変図式の initial な比較に使い、各中間射の fiber と
S の引き戻しの比較、さらに局所右 Kan 拡張による降下の合成へ進む。
この段階で被覆生成・上限位相・extensive の判定が済んだとはしない。

検証済み全体93本5,886行・562宣言。係数への極限存在の追加仮定は置かない。
S3 の逆向きは drafts の `∃ c, IsLimitCone c ∧ c.vertex = t.vertex` と一致し、
`cechLimitLift.comparison` に指定同値を保持している。
「制限の厳密な等号は要求しない」の docstring も確認した。

一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：引き戻し篩の全 fiber と元の指定図式（11-15）

`SieveFactorizationFiber`・`SieveFactorizationDiagram` の2本168行・27宣言が
対象ビルド・小監査成功（標準三公理のみ）。記録：
`/tmp/is-w1/s1-fiber-and-diagram-7/`。採取は今回の対象ビルド後の環境から行い、
記録の source SHA と現在の2本も一致する。

主な型：
```lean
sieveCategory (S.pullback t.obj.hom) ≌ sieveFactorizationFiber R S t

(pullbackSieveToFactorizationFiber R S t).op ⋙
  (sieveFactorizationFiberInclusion R S t).op ⋙ sieveFactorizationDiagram R S =
    sieveDiagram (S.pullback t.obj.hom)

(sieveFactorizationCone R S).π =
  Functor.whiskerLeft (sieveFactorizationOuter R S).op (sieveCone R).π ≫
    sieveFactorizationTriangle R S
```

fiber の比較は対象だけでなく全射を保持する充満忠実・本質的全射の比較。
元の図式は厳密に回収し、錐の比較も元の三角形の自然変換を明示した。
係数への極限存在の追加仮定はない。

次の芯の型（未証明）は次のとおり。
```lean
(∀ t : sieveCategory R,
  IsLimitCone (restrictionCone F (S.pullback t.obj.hom))) →
(IsLimitCone (restrictionCone F (R ⊓ S)) ↔
 IsLimitCone (restrictionCone F R))
```
各 fiber の比較を局所右 Kan の形状へ移し、指定三角形に沿う
極限の合成を示してから、普遍的降下篩の位相を構成する。
被覆生成・上限位相・extensive の判定、S8 は未完。
検証済み全体95本6,054行・589宣言、外枠18,600行内。

一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：局所 comma の随伴と実 nerve の cofinal 性（11-15）

3本162行・21宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-local-cofinal-3/`。source SHA も一致。

```lean
sieveFactorizationLocalPush R S t ⊣ sieveFactorizationLocalInclusion R S t
IsLeftCofinal (nerveMap (sieveFactorizationComposite R S).op)
IsLeftCofinal (nerveMap (sieveFactorizationLocalInclusion R S t).op)
```

一般の通常の左随伴の実 nerve が left cofinal である補題は
`Kerodon/LimitsAndColimits/Cofinality/NerveAdjunction` に置いた。
既存の各左 comma による Quillen A と終対象での収縮を使い、
S1 の中へ一般の補題を埋め込まない。

局所 comma から固定 fiber への押し出しは三角形の合成。
Hom 同値と自然性は元の全射の式で証明した。
既存の構成の法則・証明分割として S1 内で進めており、一覧の追加はない。
次はこの cofinal 比較と引き戻し篩の全同値で、元の制限錐を局所 comma 上で回収する。
極限の合成には既存の `coneTransformationMap_isQCatEquivalence` を再利用できる。
これは任意の形状と追加パラメータの元の錐を、定値始域からの変換へ比較する。
被覆生成の最終結論そのものはまだ未証明。

検証済み全体98本6,216行・610宣言、外枠18,600行内。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：元の引き戻し篩の指定錐と局所 comma の極限条件（11-15）

`SieveFactorizationLocalCone` 100行・9宣言の対象ビルドと小監査が成功
（標準三公理のみ）。記録：`/tmp/is-w1/s1-local-cone-2/`。source SHA も一致。

```lean
IsLimitCone (sieveFactorizationLocalRestrictionCone R S t F) ↔
  IsLimitCone (restrictionCone F (S.pullback t.obj.hom))
```

通常の全錐の制限が元の篩錐に等しいこと、nerve・宇宙持ち上げ・
元の係数前層への後合成後の全射が同じであることを証明した。
引き戻し篩から局所 comma への比較を、一つの右随伴の反転として
left cofinal にしたため、二重の制限による頂点の選び直しはない。
元の係数には準圏性だけを仮定する。

次の接続には `NerveComparison/RightConeTransport` の
`nerveRightConeTransport` と、その元の指定局所錐との比較を再利用する。
`RightPointwise` は通常の係数圏の極限を前提とする結果なので、
そのまま適用して一般の係数を縮めることはしない。
元の輸送を係数前層へ後合成する法則と、反転した局所 comma の形状の比較をつなぐ。
極限の合成では `ConeCounitHomUniversal`・`ConeFamilyHomUniversal` の
指定余単位による Hom 全単射を使える。いずれも元の準圏の錐の定理で、
presentable な係数への制限はない。

検証済み全体99本6,316行・619宣言、外枠18,600行内。
S1 の交叉降下の同値と被覆生成の結論、S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：指定右 Kan 局所輸送の係数前層への後合成（11-15）

`KanExtensions/RightTransportPostcomp` 59行・10宣言の対象ビルドと
小監査が成功（標準三公理のみ）。記録：`/tmp/is-w1/s1-right-postcomp-2/`。
source SHA も一致。

```lean
kanRightTransportPostcomp (t : RightKanConeTransport δ F₀ F α c) (U : D ⟶ E) :
  RightKanConeTransport δ (F₀ ≫ U) (F ≫ U) (kanRightCounitPostcomp α U) c

(kanRightTransportPostcomp t U).cone.val = t.cone.val ≫ U
```

元の右 Kan 輸送の円柱全体に同じ係数射を合成する法則。
右輸送は始端を標準錐に固定し、終端を比較錐とする元の定義のまま。
極限の保存性を新しい仮定として追加せず、極限性は各像の指定錐で別途示す。
これは既存の構成の係数移送の法則として数える。

検証済み全体100本6,375行・629宣言、外枠18,600行内。
S1 の交叉降下の同値・生成系・上限位相・extensive の判定と、S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：実右 Kan の局所形状への指定比較（11-15）

3本180行・12宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-native-shape-5/`。source SHA も一致。

```lean
sieveFactorizationRightKanShapeComparison R S t :
  presheafShape (sieveFactorizationLocalComma R S t) ⟶
    rightKanShape (nerveMap (sieveFactorizationRightKanFunctor R S))
      (nerveVertex (AsSmall.up.obj (Opposite.op t)))

IsQCatEquivalence (sieveFactorizationRightKanShapeComparison R S t)
```

元の局所 comma の反転から右 comma への同値は、Mathlib の
`costructuredArrowOpEquivalence` を直接再利用した。
これと重なる未コミットの再実装 `CostructuredOpposite` は採用せず、作業木から除いた。
宇宙の接続には、Mathlib の `StructuredArrow.post`・`pre` と AsSmall の
既存同値だけを合成し、元の局所射影を全関手として厳密に保持する。
最後に既存の `nerveRightKanShapeIso` を合成した同じ実写像の同値性を証明した。

`RightConeTransportPostcomp` は、通常の指定余単位の実輸送を任意の準圏値へ写した
場合に、元の通常の局所錐の像との全射の等式と極限性の同値を示す。
通常の係数圏での極限性・係数射の極限保存性は仮定しない。

次は、元の三角形 `sieveFactorizationTriangle` を AsSmall の係数圏へ写した
同じ余単位の輸送を固定し、この指定形状比較の下で局所錐の全射を照合する。
既検証の `uliftNerveCone_asSmall_val` で元の係数前層への後合成へ戻す。
ここまでで極限の合成自体が済んだとはしない。

検証済み全体103本6,555行・641宣言、外枠18,600行内。
S1 の交叉降下の同値・生成系・上限位相・extensive の判定と、S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：元の各引き戻し篩の降下から、指定余単位による実右 Kan 条件（11-15）

4本253行・14宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-right-kan-5/`。source SHA も一致。

```lean
(∀ t : sieveCategory R, IsLimitCone (restrictionCone F (S.pullback t.obj.hom))) →
IsRightKanExtension (nerveMap (sieveFactorizationRightKanFunctor R S))
  (nerveMap (sieveFactorizationRightKanSource R S) ≫ sieveFactorizationRightKanCoefficient F)
  (nerveMap (sieveFactorizationRightKanTarget R) ≫ sieveFactorizationRightKanCoefficient F)
  (sieveFactorizationRightKanCounitHomotopy R S F)
```

`SieveFactorizationRightKanData` は元の三角形の同じ指定余単位と実輸送を固定。
`RightKanLocalCone` は通常の右 comma 上の局所錐を制限すると元の局所錐の
AsSmall 表示そのものであることを証明した。
`RightKanConeComparison` は既検証の実形状比較で全錐を引き戻すと、
元の局所制限錐と全射が等しいことを証明し、各引き戻し篩の降下との極限性の同値を得た。
`SieveFactorizationRightKan` は全頂点を元の中間射へ戻して上の指定右 Kan 条件を結論する。
係数の universe は下げず、準圏性以外の極限存在は仮定しない。
計算上限は変更せず、nerve の合成則は元の型で明示した等式を使った。

次の芯は、この指定右 Kan 条件と元の錐の余単位の Hom 普遍性をつなぎ、
交叉篩と元の篩の降下の同値を導く部分。
任意の追加パラメータの定値族へ同じ指定輸送を写す法則は、
`kanRightTransportPostcomp` と `kanIsLimitCone_constantFamily` から作れる。
写像空間を π₀ だけで代用せず、全パラメータを保持して極限性へ戻す。

検証済み全体107本6,808行・655宣言、外枠18,600行内。
S1 の交叉降下の同値・生成系・上限位相・extensive の判定と、S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：指定右 Kan の全パラメータの Hom 普遍性（11-15）

`KanExtensions/RightKanConstantFamily` 48行・2宣言の対象ビルドと小監査が成功
（標準三公理のみ）。記録：`/tmp/is-w1/s1-right-family-1/`。source SHA も一致。

```lean
IsRightKanExtension δ F₀ F α →
  IsRightKanExtension δ (F₀ ≫ constantFunctorMap A D) (F ≫ constantFunctorMap A D)
    (kanRightCounitPostcomp α (constantFunctorMap A D))
```

A は任意の単体集合。準圏性や有限性は課さない。元の指定輸送を同じ定値族へ
後合成し、元の局所極限錐の像の極限性で判定した。
さらに同じ後合成した指定余単位の `RightKanHomUniversal` を任意の A で結論する。
π₀ の一つの Hom 全単射だけで全写像空間の同値を代用しないための入力になる。
既存の構成の係数移送の法則として S1 内で扱う。

極限の合成の次の証明では、元の錐の余単位の比較が必要。
`coneCounitHom_bijective`・`coneFamilyCounitHom_bijective` は必要条件で、
それだけから任意の係数圏の極限性を主張しない。
全パラメータの比較を元の錐の極限性へ戻す判定、または小極限が存在する係数での
比較を証明したうえで全共変表現可能関手による極限の検出へ運ぶ経路を接続する。
後者を用いる場合も、最終の S1 の係数に presentable 性や極限存在は追加しない。

検証済み全体108本6,856行・657宣言、外枠18,600行内。
S1 の交叉降下の同値・生成系・上限位相・extensive の判定と、S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：錐の射の余単位の自然性と全関手への射影（11-15）

6本283行・19宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-cone-apex-10/`。source SHA も一致。

```lean
constantFunctorHomMap K (functorHomEvaluate α apex) ≫ coneCounitHom d =
  coneCounitHom c ≫ kanFunctorHomCongr c.property d.property
    ((hoFunctor.map ((pre (joinInr Δ[0] K)).app X)).toFunctor.map α)

functorHomEvaluate (coneHoMorphismValue β) apex =
  (hoFunctor.map (sliceOverProjection p)).toFunctor.map β
```

`ConeCounitMorphismNaturality` は任意の全錐間の変換について元の余単位の自然性を証明。
`ConeValueProjection` は元の錐圏から全関手への写像と、頂点・底の全写像の等式を固定。
`ConeMorphismApex` は元の錐圏の射の頂点評価を同じ頂点射影の作用として回収した。
`HoHomVertexTransport`・`Congr` は端点の等式での移送の合成則・同一視、
`HoConstantMap` は任意のホモトピー圏の射が定値写像で恒等射になる法則。
大きい本文の展開で起きた kernel の時間切れは、一般の端点移送の公開定義に分割して解消。
計算上限は変更していない。

次は底の恒等射の式を接続し、極限が存在する場合に限った余単位の Hom 判定を作る。
この中間の存在仮定を最終の S1 へ追加せず、全表現可能関手での検出へ戻す。
S3 の承認済みの型（頂点の等号と指定比較同値、制限の厳密な等号は不要）は保持。

検証済み全体114本7,139行・676宣言、外枠18,600行内。
S1 の交叉降下の同値・生成系・上限位相・extensive の判定と、S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：元の錐の射の底と、極限が存在する場合の判定（11-15）

2本131行・4宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-cone-boundary-5/`。source SHA 一致。

```lean
constantFunctorHomMap K ((hoFunctor.map (sliceOverProjection p)).toFunctor.map β) ≫
  coneCounitHom d = coneCounitHom c

HasLimit p → (IsLimitCone c ↔ ∀ y, Function.Bijective
  (fun β : Hom (Ho.mk y) (Ho.mk c.vertex) =>
    constantFunctorHomMap K β ≫ coneCounitHom c))
```

`ConeMorphismBoundary` は元の錐圏の射の底が恒等射であることを示し、
同じ頂点射が元の指定余単位を可換にする式を得た。
`ConeCounitCriterionWithLimit` は実際の極限錐への比較辺を選び、二つの Hom 全単射で
頂点射の逆射を作り、元の右ファイブレーションで反映した。
極限の存在を明示する中間補題であり、最終の S1 にこの仮定は追加しない。
計算上限は変更していない。次は形状制限・指定三角形との余単位の式を接続する。

検証済み全体116本7,268行・680宣言、外枠18,600行内。
S1・S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：形状制限と指定右 Kan の余単位との合成則（11-15）

3本157行・8宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-counit-composition-1/`。source SHA 一致。

```lean
kanFunctorHomCongr (SSet.comp_const i c.vertex) rfl
  ((hoFunctor.map ((pre i).app X)).toFunctor.map (coneCounitHom c)) =
kanFunctorHomCongr (congrArg SSet.const (restrictJoinCone_vertex c i)) rfl
  (coneCounitHom (restrictJoinCone c i))
```

`FunctorHomCongrArrow` は端点の移送を Arrow の対象として相殺する法則。
`ConeCounitShapeRestriction` は元の円柱の自然性を使い、元の錐を制限した同じ余単位を比較。
`RightKanCounitHomComposition` は指定右 Kan 射の元の Hom 全単射を定値始域へ
正規化し、その余単位との合成が Hom 判定を保ち反映することを証明した。
計算上限は変更せず、全図式・指定変換を保持した。

次の接続は、通常の `sieveFactorizationCone_triangle` の同じ三角形を
既存の `nerveConePostcomposeHomotopy` で写し、頂点で恒等な全錐の変換を使う部分。
この構成は既存の `ConePostcomposeHomotopy` を再利用し、作り直さない。
その後、極限存在下の判定を完全な空間値で使い、任意の係数へ表現可能関手で反映する。
S1 の交叉降下自体を閉じたとはしていない。

検証済み全体119本7,425行・688宣言、外枠18,600行内。
S1・S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：極限存在下の指定右 Kan の合成と、元の通常の全錐の変換（11-15）

5本297行・9宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-right-kan-limit-3/`。source SHA 一致。

```lean
(hp : HasLimit p) → (hq : HasLimit q) →
(α : FunctorHom (restrictJoinCone c δ).val d.val) →
[IsIso (functorHomEvaluate α apex)] →
RightKanHomUniversal δ (kanFunctorHomCongr
  (restrictJoinCone c δ).property d.property ((hoFunctor.map (pre inr)).toFunctor.map α)) →
(IsLimitCone c ↔ IsLimitCone d)
```

`ConeCounitMorphismHomUniversal` は元の全錐間の変換を保持し、頂点で可逆なら
その底の変換との合成が元の余単位の Hom 判定を与える法則。
`RightKanLimitComposition` はこれを形状制限と指定右 Kan の Hom 全単射へ接続した。
**両図式の極限が存在する場合の中間補題**であり、最終の S1 に存在仮定は追加しない。
`FixedHomotopyEvaluation` は既存の時間に定値なホモトピーの類と評価の自然性を接続。
`ConePostcomposeComponent` は既存の `nerveConePostcomposeHomotopy` を再利用し、
同じ係数で写した後も頂点成分が可逆であることを証明した。
`ConePostcomposeBoundary` は、その全錐の変換の底が元の指定自然変換の像である厳密な等式。
新しい全錐のホモトピーは作らず、既存の構成の法則として扱った。
計算上限は変更していない。

次は通常の `nerveCone_whisker` に沿って同じ全変換の始域を制限錐へ移し、
二段分解の元の三角形へこの判定を適用する。任意の係数へ戻すには、
全共変表現可能関手の保存・検出と宇宙変更を接続する必要がある。
既存の `UniverseRightKanShape`・`UniverseRightKanCanonical` は実形状と標準全錐を
保持するが、任意の指定余単位の全輸送への接続はまだ未検証。
この部分を元の指定輸送の法則として作り、存在を仮定して済ませない。

検証済み全体124本7,722行・697宣言、外枠18,600行内。
S1 の交叉降下・生成系・上限位相・extensive の判定と、S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：通常の元の三角形へ、制限錐からの全変換として接続（11-15）

2本135行・10宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-ordinary-triangle-1/`。source SHA 一致。

```lean
(hp : HasLimit (nerveMap P ≫ U)) →
(hq : HasLimit (nerveMap Q ≫ U)) →
RightKanHomUniversal (nerveMap δ) (normalizedNerveClass η U) →
(IsLimitCone (mapJoinCone U (nerveCone c)) ↔
 IsLimitCone (mapJoinCone U (nerveCone ((Cone.postcompose η).obj (c.whisker δ)))))
```

`FunctorHomCongrEvaluation` は全関手の端点の等式による表示変更が、同じ頂点成分の
可逆性を変えない法則。`NerveConeWhiskerPostcompose` は既存の `nerveCone_whisker` と
既検証の後合成ホモトピーを使用し、元の制限錐から元の後合成錐への全変換を固定した。
頂点での可逆性と、底が元の三角形の同じ指定変換に一致する式を証明。
この同じ変換に極限存在下の合成補題を適用する判定まで閉じた。
`normalizedNerveClass η U` は本文では `nerveWhiskerCoefficient_eq` による
`kanFunctorHomCongr` と元の `nerveNatTransHomotopy η` の後合成を明記している。
計算上限は変更していない。

次の接続の再利用を確認：
- 実右 Kan 形状：`UniverseRightKanShape.rightKanShapeUniverseIso`。
- 実標準錐：`UniverseRightKanCanonical.rightKanCanonicalCone_universe_val`。
- 全円柱の宇宙移送：既存 `simplexTensorMap_source`・`target`・`constant`
  （`Project/SimplicialCombinatorics/Subdivision/UniverseLiftTensor`）。
  同じ原始的な宇宙移送の自然性は作り直さず、指定右 Kan 輸送の全族へ接続する。
- 全表現可能関手の極限保存・検出：`RepresentableLimitCharacterization`。
まだ任意の係数での交叉降下は閉じておらず、上の存在仮定を最終型へ追加しない。

検証済み全体126本7,857行・707宣言、外枠18,600行内。
S1 の交叉降下・生成系・上限位相・extensive の判定と、S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：指定右 Kan 輸送の実宇宙移送と全表現可能関手への接続（11-15）

5本330行・25宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-right-universe-4/`。source SHA 一致。

```lean
IsRightKanExtension δ F₀ F α → ∀ x : D₀,
  IsRightKanExtension (uliftFunctor.map δ)
    (uliftFunctor.map F₀ ≫ covariantRepresentableInfinity x)
    (uliftFunctor.map F ≫ covariantRepresentableInfinity x)
    (kanRightCounitPostcomp (kanRightCounitUlift α) (covariantRepresentableInfinity x))
```

`UniverseTensorEndpoints` は既存 `simplexTensorMap` が元の端点の全射を保つ法則。
`RightCounitUniverse` はその同じ全円柱の移送で指定余単位を正規化。
`RightKanConeUniverseShape` は既存の join と実右 Kan 形状の宇宙同型を合成し、
元の両包含と実標準全錐を同じ写像で保つことを証明した。
`RightKanTransportUniverse` はその同じ逆比較で元の全輸送を移し、
始端・図式・固定頂点・終端の全射の式を証明した。
`RightKanTransportUniverseLimit` は、同じ再添字付けの下で後合成した元の全錐との
極限性の同値を示し、既存の共変表現可能関手の極限保存を適用して上の指定右 Kan 条件を得た。
任意の大きい図式の極限保存は追加仮定にせず、元の小さい局所全錐への保存だけを使った。
既存の構成の宇宙・係数移送の法則として S1 内で扱う。計算上限は変更していない。

次は元の全錐間の指定ホモトピーにも同じ宇宙移送を適用し、
同じ底の指定余単位と固定頂点を保持する。全表現可能関手で検出し、
これまでの中間補題の極限存在の仮定を最終の係数から取り除く。

検証済み全体131本8,187行・732宣言、外枠18,600行内。
S1 の交叉降下・生成系・上限位相・extensive の判定と、S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：極限存在を仮定しない元の指定右 Kan 比較（11-15）

6本453行・29宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-cone-universe-4/`。source SHA 一致。

```lean
(α : SSet.Homotopy (δ ≫ p) q) → IsRightKanExtension δ q p α →
(H : SSet.Homotopy (restrictJoinCone c δ).val d.val) →
((inr ▷ Δ[1]) ≫ H.h = α.h) →
((inl ▷ Δ[1]) ≫ H.h = fst Δ[0] Δ[1] ≫ inl ≫ (restrictJoinCone c δ).val) →
(IsLimitCone c ↔ IsLimitCone d)
```

I・K・D は準圏。係数 D に極限存在・presentable 性を仮定しない。
`ConeHomotopyUniverse` は元の全錐間の同じ円柱の宇宙移送と、底・固定頂点の法則。
`FixedHomotopyEndpoints` は固定した全円柱から、その部分の厳密な端点一致を回収。
`ConeHomotopyUniverseComponents`・`RightKanComparisonUniverse` は同じ係数で後合成し、
実制限錐の表示へ始域だけを揃えた同じ射の頂点可逆性と底の指定射の一致を証明した。
`RightKanLimitCompositionArbitrary` は全共変表現可能関手への同じ移送を使い、
空間値の小極限存在下で判定してから元の全錐へ反映した。
`NerveTriangleLimitComposition` は元の通常の三角形にこれを適用し、
同じ通常の全ホモトピーの始端だけを実制限錐へ揃えた場合の極限性の同値を得た。

一括した最初の証明は kernel の既定の計算上限で時間切れ。
同じ指定射を公開の名前付き定義へ固定し、頂点・底・係数移送下の比較を
別々の法則へ分割して通した。計算上限は変更していない。

次は既存の篩の指定三角形にこの無条件の係数の比較を適用し、
AsSmall の表示から元の制限錐へ戻して交叉降下を閉じる。
この段階で元の係数に極限存在を追加して済ませる部分はなくなったが、
S1 の交叉・生成系・上限位相・extensive の判定全体はまだ未完。

検証済み全体137本8,640行・761宣言、外枠18,600行内。
S1・S8 は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：元の交叉篩の降下の同値を閉じた（11-15）

3本142行・5宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-intersection-1/`。source SHA 一致。

```lean
(∀ t : sieveCategory R, IsLimitCone (restrictionCone F (S.pullback t.obj.hom))) →
(IsLimitCone (restrictionCone F (R ⊓ S)) ↔ IsLimitCone (restrictionCone F R))
```

任意の準圏係数 E に対し、元の restrictionCone のまま上の同値を証明した。
`AsSmallCoefficientCone` は元の全錐の同じ AsSmall 表示から係数前層へ戻す法則。
`SieveFactorizationLimitComparison` は既存の元の指定右 Kan 条件を、
同じ元の二段分解の三角形・全錐へ適用した。
`SieveIntersectionDescent` は既存の合成射影の left cofinal 性と同じ全錐の制限の等式を
合成し、元の交叉篩の降下を結論した。係数の極限存在・presentable 性は仮定していない。
計算上限は変更していない。

次は全引き戻しで降下する篩の推移性を、この同値の両順序での適用から示す。
その篩の位相を用いて位相の上限の層条件を閉じる。
生成 coverage は refine の条件しか持たないので、一つの生成篩での降下を
全引き戻しの降下と混同せず、元の drafts の仮定からの接続を別に残す。
S1 の生成系・extensive の判定と S8 は未完。

検証済み全体140本8,782行・766宣言、外枠18,600行内。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S1：降下位相と、元の上限位相の層条件（11-15）

3本163行・16宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s1-descent-topology-6/`、source SHA 一致。

```lean
IsSheaf (J ⊔ J') F ↔ IsSheaf J F ∧ IsSheaf J' F
```

`UniversalSieveDescent` は交叉降下を両順序で使って全引き戻しの降下の推移性を証明。
`DescentTopology` はその篩の位相を構成し、元の層条件を位相の包含へ同定して上の型を閉じた。
`CoverageUniversalDescent` は生成篩の**全引き戻し**での降下を明示した中間判定。
これは drafts の生成篩そのものだけで足りる最終定理の代用ではない。
計算上限は変更していない。

S1 の残りの芯は次の元の入力からの接続：
```lean
(K : Coverage C) → (F : Presheaf C E) →
(∀ U (R : Presieve U), R ∈ K.coverings U →
  IsLimitCone (restrictionCone F (Sieve.generate R))) →
∀ U (R : Presieve U), R ∈ K.coverings U →
  UniversallyDescendingSieve F (Sieve.generate R)
```
coverage の refine の条件を、実際の引き戻し篩そのものが生成系に属する条件と
取り違えない。この接続と extensive の有限積判定、S8 の全重みの比較等は未完。
新しい一まとまりや外枠超過が必要と判明した時点で、共通の停止規則に従う。

検証済み全体143本8,945行・782宣言、外枠18,600行内。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S8：元の集合の押し出し余錐を保持する（11-15）

2本153行・16宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s8-discrete-pushout-4/`、source SHA 一致。

```lean
{F : AsSmall WalkingSpan ⥤ KanObject} →
(c : Cocone F) → IsColimit (kanObjectForget.mapCocone c) →
[Mono ((F ⋙ kanObjectForget).map (AsSmall.up.map WalkingSpan.Hom.fst))] →
IsColimitCone (strictNativeCocone c)

{F : AsSmall WalkingSpan ⥤ Type u} →
(c : Cocone F) → IsColimit c →
[Mono (F.map (AsSmall.up.map WalkingSpan.Hom.fst))] →
IsColimitCone (discreteSpaceCocone c)
```

`KanPushoutCocones` は既存の反変 Hom の極限性と一脚 fibration の cospan 判定の接続。
`DiscretePushoutCocones` は同じ集合の余錐の定値単体集合への像を使う。
`discreteSpaceCocone_vertex` は元の `c.pt` の離散空間との頂点の等号。
Kan 置換へ頂点や脚を移して済ませず、元の全余錐を保持した。
計算上限は変更していない。前層の元の押し出し四角形との接続はまだ残る。

検証済み全体145本9,098行・798宣言、外枠18,600行内。
S1 の生成 coverage・extensive の判定と、S8 の全重み比較・局所同値は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S8：離散前層の全埋め込みと評価の可換則（11-15）

2本93行・5宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s8-discrete-evaluation-2/`、source SHA 一致。

```lean
kanDiscretePresheafFunctor C ⋙
    coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched U) =
  (evaluation Cᵒᵖ (Type u)).obj U ⋙ setsToKan

kanDiscretePresheafMap C ≫ evaluateFunctorAt (ULift.up (nerveVertex U)) =
  nerveMap ((evaluation Cᵒᵖ (Type u)).obj U) ≫ discreteSpaceInclusion
```

`DiscreteSpaceCoherentRepresentation` は、元の離散埋め込みが同じ `setsToKan` の nerve の
coherent 表示と全次数で一致する法則。
`DiscretePresheafEvaluation` は束縛された元の図式の評価と、この全埋め込みの評価の法則。
既存の `kanDiagramBundle_evaluation` と `nerveToCoherent_postcomp` を再利用した。
前層の射も高次の族も同じ等式に含み、対象ごとの比較だけで全関手比較を代用しない。
計算上限は変更していない。

次の接続では元の全余錐の評価を、上の集合の同じ余錐の離散表示へ移す。
元の `strictNativeCocone` と豊穣後合成の法則が必要なので、反対の coherent nerve の
既存の自然性（`coherentNerveOppositeInverse_post`）と `strictCoherentCone_postcomp` を使う。
この接続と元の押し出し四角形の同定はまだ未完で、S8 完了には数えない。

検証済み全体147本9,191行・803宣言、外枠18,600行内。
S1 の生成 coverage・extensive の判定と、S8 の全重み比較・局所同値は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S8：前層の同じ全余錐の押し出し判定・中間実測（11-15）

2本148行・10宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s8-presheaf-essential-1/`、source SHA 一致。

```lean
(mapJoinCocone (evaluateFunctorAt (ULift.up (nerveVertex U)))
  (discretePresheafCocone c)).val =
(discreteSpaceCocone (((evaluation Cᵒᵖ (Type u)).obj U).mapCocone c)).val

(c : Cocone F) → IsColimit c →
[Mono (F.map (AsSmall.up.map WalkingSpan.Hom.fst))] →
IsColimitCone (discretePresheafCocone c)

(discretePresheafCocone c).vertex = functorVertex (discretePresheaf c.pt)

(d : JoinCocone (strictCoherentDiagram (F ⋙ kanDiscretePresheafFunctor C) ≫
  kanDiagramRealization Cᵒᵖ)) → IsColimitCone d → Is0Truncated d.vertex
```

最後の型では同じ c の通常の余極限性と一脚の単射性を引数に取る。
`DiscretePresheafPushoutCocones` は全余錐を点ごとに評価して元の集合の同じ余錐へ照合し、
点ごとの余極限判定を適用した。`DiscretePresheafEssentialImage` の `Is0Truncated` は
元の drafts の本質像の存在型で、指定した頂点同型で任意の余極限へ運ぶ。
元の押し出し四角形はまだ同定していないため、その型の最終定理の完成とはしない。

照合中、一般の全余錐の後合成則が既存の
`IndCompletionsOfInfinityCategories/StrictCoconePostcomposition` にあることを確認した。
試作した反転・帰還の重複2本は作業木から除き、この既存の宣言を直接再利用した。
計算上限は変更していない。

中間実測：検証済み全体149本9,339行・813宣言。目安9,300行を超えた。
元の四角形への接続は現時点で200〜400行程度を見込む。
残りの S1 の生成 coverage・extensive、S8 の一般重みの全比較・連続性・局所同値は未完。
一般重み側の依存照合が未確定なので、全残量の確定見積もりは保留する。
外枠18,600行は維持し、新しい一まとまりや上限超過の必要が判明したら共通の規則で止める。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S8：全余錐の制限則と三角形の反転の法則（11-15）

4本298行・12宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s8-cocone-triangle-laws-8/`、source SHA 一致。

```lean
ulift.map (nerveMap G) ≫ (strictCoconeIndexIso I).hom =
  (strictCoconeIndexIso J).hom ≫ opFunctor.map (ulift.map (nerveMap G.op))

joinMap (ulift.map (nerveMap G)) (𝟙 Δ[0]) ≫
  (strictNativeCocone c).val = (strictNativeCocone (c.whisker G)).val

coherentOppositeSimplex ((nerveToCoherent C).app (op ⦋n⦌) A) =
  (nerveToCoherent Cᵒᵖ).app (op ⦋n⦌)
    ((ComposableArrows.opEquivalence C n).functor.obj (op A))

((joinStdSimplexIso 1 0).inv ≫
  joinMap ((stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map a) (𝟙 Δ[0])) ≫
  c.reverseCocone.val =
(stdSimplex.opIso ⦋2⦌).inv ≫ opFunctor.map
  ((pointJoinStdSimplexIso 1).inv ≫ joinMap (𝟙 Δ[0]) a ≫ c.val)
```

`StrictCoconeShapeRestriction` は既存の全錐の再添字則と反転の制限則を再利用。
`OrdinaryCoherentReversal` は Mathlib の射列の反対同値と既存の coherent 反転の法則。
`CoconeTriangleReverseShape` は固定した三頂点で順方向の同型を比較してから逆射へ戻す。
`StrictCoconeEdgeReflection` は添字同型の指定辺での評価の法則。
全て既存の構成の自然性・計算則で、型つき ID の追加はない。

全余錐の制限則の推論で既定の計算上限の時間切れを確認した。
反対の錐側の式へ証明分割し、指定した部分だけを rw して通した。上限は変更していない。
途中の commentary の「制限則が通った」は添字の自然性だけの検証と取り違えたもので、訂正済み。

直近の四角形への接続の再見積もり：当初200〜400行に対し、上の法則298行、
係数を含む全二単体の照合の下書き約126行、四角形への同定を更に100〜200行程度とみる。
再添字・有限反転の全射の法則を分割する必要があり、合計約524〜624行へ増えた。
この下書きは未検証なのでコミットせず、完成とは数えない。

検証済み全体153本9,637行・825宣言、外枠18,600行内。
S1 の二判定、S8 の元の四角形・全重みの比較・連続性・局所同値は未完。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S8-3：元の押し出し四角形と任意の余極限の離散性を閉じた（11-15）

4本405行・25宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s8-pushout-square-5/`、source SHA 一致。

```lean
strictCoconeLegTriangleShape f ≫ (strictNativeCocone c).val =
  SSet.yonedaEquiv.symm ((nerveToCoherent C).app (op ⦋2⦌)
    (ComposableArrows.mk₂ (F.map f) (c.ι.app j)))

((discretePushoutCocone f g).restrict strictSpanHornIso.inv).val =
  (pushoutCocone (discretePushoutSquare f g)).val

-- [Mono f]
IsPushoutSquare (discretePushoutSquare f g) ∧
  ∀ c : JoinCocone (pushoutSpan (discretePushoutSquare f g)),
    IsColimitCone c → Is0Truncated c.vertex
```

`StrictNativeCoconeTriangles` は反対の錐の全単体の式と既存の反転 Yoneda の法則を使い、
元の通常の合成二単体そのものを回収する。`StrictSpanHornEdges` は元の二辺を宇宙移送する法則。
`DiscretePushoutSquareData` の四角形は drafts と同じ二つの合成二単体の貼り合わせを
同じ `discretePresheafInclusion` で送った式（通常の四角形の式だけ名前に切り出した）。
`DiscretePushoutSquareComparison` は元の全余錐を形状同型で制限し、上の二単体の等式を
左右で使って同じ四角形の全余錐へ一致させた。
最後に、元の前層の離散表示との指定した頂点同型を、任意の余極限へ移した。

第一成分だけや、別の頂点を選んだ押し出しの存在へ弱めていない。
S8-3 のこの最終型は本体で完成。S8 全体の完了とはしない。
計算上限は変更していない。既存の宣言は変更せず、新規ファイルのみ。

実測の差：前節の反転・制限298行と今回405行で、四角形への接続は703行。
再見積もり524〜624行に対して79〜179行増えた。
主な追加は持ち上げた span の指定二辺の厳密な移送58行と、元の二三角形の表示・比較の分割。
新しい数学のまとまりや型つき ID は追加していない。

検証済み全体157本10,042行・850宣言、外枠18,600行内。
残りは S1 の生成 coverage・extensive の判定、S8 の固定した元の Yoneda に沿う一般重み、
離散重みとの全関手比較、一般余極限を極限へ送る性質、離散層化の通常層化との比較・局所同値。
S7 は指示どおり後続。S8-3 の成功だけで他の未供給入力を済んだものとはしない。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S8：通常の Hom の両変数を同時に保持する射列（11-15）

3本201行・17宣言の対象ビルドと小監査が成功（標準三公理のみ）。
記録：`/tmp/is-w1/s8-ordinary-hom-chains-2/`（2本13宣言）、
`/tmp/is-w1/s8-hom-join-reindex-2/`（1本4宣言）、source SHA 一致。

```lean
ordinaryHomBifunctor C : Cᵒᵖ × C ⥤ Type u := Functor.uncurry.obj coyoneda
OrdinaryHomElements C := (ordinaryHomBifunctor C).Elements

h.hom.1.unop ≫ x.val ≫ h.hom.2 = y.val

ordinaryHomJoinChain s :
  CategoryTheory.Join (Fin (n + 1))ᵒᵖ (Fin (n + 1)) ⥤ C

(ordinaryHomCrossChain s).app (op i, i) = (s.obj i).val

Join.mapPair α.toFunctor.op α.toFunctor ⋙ ordinaryHomJoinChain s =
  ordinaryHomJoinChain (α.toFunctor ⋙ s)
```

元の圏は既存の Hom 関手の Elements そのもので、新しい圏構造は作らない。
join 図式も Mathlib の `Join.mkFunctor` に同じ二つの端点の射列と交差射を入れたもの。
`α 0 ≠ 0` でも元の可換四角形を使って交差射を照合したので、全ての面・退化を含む。
対象ごとの表現可能前層の同値だけで全関手比較を代用しない。

原典の確認：[Kerodon Remark 8.1.0.3（03JC）](https://kerodon.net/tag/03JC) は
Hom の元の圏による表示を述べ、[Proposition 8.1.1.10（03JN）](https://kerodon.net/tag/03JN) は
両端射影を保持した nerve と twisted arrow の同型を、同じ射列の連結から構成している。
ここではまだ後者の単体的同型を完成していない。

次は既存の通常圏の join と単体的 join の模型を同じ切断・全射列で接続し、
この再添字の法則を単体的比較へ送る。型の形は次のとおり（S8 の比較の証明分割）：
```lean
nerveJoinComparison C D : join (nerve C) (nerve D) ⟶ nerve (CategoryTheory.Join C D)
-- この比較と同じ両端射影を保つ：
nerve (OrdinaryHomElements C) ≅ TwistedArrow (nerve C)
-- 全分類図式の同型を curry し、固定した元の oppositeSpaceYoneda へ戻す。
```
これらの模型比較・分類図式への接続がなお残り、元の `weightedSectionsData` の完成には数えない。
一般重み側の局所的な見込み：nerve と join の比較の自然性・両端・射列の復元で約500〜900行、
その後の指定分類図式・元の Yoneda への接続は既存の全族の API の照合が要る。
全残量の確定見積もりは依然未確定で、外枠18,600行は維持する。

検証済み全体160本10,243行・867宣言。未検証の `NerveJoinChains`・`NerveJoinNaturality` は作業木のみ。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：nerve と join の全単体的比較

`NerveJoinChains`（116行）・`NerveJoinNaturality`（154行）の2本270行・39宣言を検証した。
対象ビルドと小監査は成功、標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-nerve-join-natural-3/target-audit-result.json`。

```lean
nerveJoinComparison C D : join (nerve C) (nerve D) ⟶ nerve (CategoryTheory.Join C D)
nerveJoinChain (Join.simplexMap _ _ α s) = α.toFunctor ⋙ nerveJoinChain s
```

全順序写像で対象と射を比較し、面・退化を含む自然性を閉じた。
この段階では比較射の可逆性と係数関手に関する自然性はまだ示していない。
次は係数関手による後合成の法則を新規ファイルで示す。
検証済み全体162本10,513行・906宣言。S1・S8 の完成にはまだ数えない。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：模型比較の後合成と両側の制限

`NerveJoinPostcomposition`（116行11宣言）と `NerveJoinBoundaries`（81行10宣言）の
対象ビルド・小監査が成功した（標準三公理のみ、source SHA 一致）。
記録：`/tmp/is-w1/s8-nerve-join-postcomp-2/`、`/tmp/is-w1/s8-nerve-join-boundaries-3/`。
法則の型は以下のとおり。いずれも既存の比較射の法則で、追加 ID はない。

```lean
joinMap (nerveMap F) (nerveMap G) ≫ nerveJoinComparison C' D' =
  nerveJoinComparison C D ≫ nerveMap (CategoryTheory.Join.mapPair F G)

joinInl (nerve C) (nerve D) ≫ nerveJoinComparison C D =
  nerveMap (CategoryTheory.Join.inclLeft C D)
joinInr (nerve C) (nerve D) ≫ nerveJoinComparison C D =
  nerveMap (CategoryTheory.Join.inclRight C D)
```

後合成は空単体を含む全射列の対象・射から、制限は元の左右の全射列から証明した。
計算上限は変更していない。検証済み全体164本10,710行・927宣言。
逆比較は、既存の `initialNerveCut` を通常圏の join に適用して切断を復元するところを検証待ち。
左右の射列の復元、twisted arrow との両端射影を保持する同型、元の固定 Yoneda の全族比較は残る。
S1 と S8 は引き続き未完成。S7 は後続とし、R2・R3 は再開しない。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：同じ切断の復元

`NerveJoinCut`（63行8宣言）の対象ビルド・小監査が成功した。
標準三公理のみ、source SHA 一致。記録：`/tmp/is-w1/s8-nerve-join-cut-2/`。

```lean
nerveJoinCollapseLeft C D : CategoryTheory.Join C D ⥤ WithInitial D
nerveJoinCut s := initialNerveCut (s ⋙ nerveJoinCollapseLeft C D)
nerveJoinCut (nerveJoinChain s) = s.1.val
```

最初の関手は既存 `Join.mkFunctor` に左の定値関手・右の包含・始対象の射を入れた特殊化。
切断の等式は既存 `Join.cut_ext` と `initialNerve_lt_cut_iff` から出した。
新しい独立の定理の ID は足していない。検証済み全体165本10,773行・935宣言。

次の接続の注意：edgewise の始域は標準単体の join なので、既存の
`joinStdSimplexIso` と `stdSimplex.isoNerve` を使う経路を先に照合する。
一般の `nerveJoinComparison` の逆比較を全て作ることが必要かは、その照合で判断する。
元の Hom の元の圏から twisted arrow への比較と、固定した Yoneda への全族比較は未完成。
S1・S8 は未完成、外枠18,600行を維持する。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：Hom の元の圏から実際の twisted arrow への全単体的比較

`OrdinaryHomLiftedChains`（75行8宣言）と `OrdinaryHomTwistedSimplex`（93行8宣言）の
対象ビルド・小監査が成功した。標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-hom-lifted-chains-1/`、`/tmp/is-w1/s8-hom-twisted-simplex-2/`。

```lean
ordinaryHomLiftedJoinChain s :
  CategoryTheory.Join (ULift (Fin (n + 1)))ᵒᵖ (ULift (Fin (n + 1))) ⥤ C

ordinaryHomTwistedSimplex s : edgewiseWeight.obj ⦋n⦌ ⟶ nerve C
edgewiseWeight.map α ≫ ordinaryHomTwistedSimplex s =
  ordinaryHomTwistedSimplex (α.toOrderHom.toFunctor ⋙ s)

ordinaryHomTwistedComparison C : nerve (OrdinaryHomElements C) ⟶ TwistedArrow (nerve C)
```

添字の移送は順序同型の下降を左右に前合成するだけで、元の Hom の射列を作り直していない。
実際の edgewise 重みから、既存の反対 nerve と join の比較を通す。
面・退化を含む全自然性まで証明した。可逆性や指定 Yoneda の全族比較は未完成。
左右の制限と射影の保持は続く新規ファイルで検証中。

逆向きには既存 `edgewiseSimplexEquiv` と `edgewiseWeightReindexOrderHom_left/right` が使える。
特に長い射列の左頂点・右頂点を同じ添字で評価し、両端間の射を読むことで、
一般の nerve–join 比較の全単体の逆を先に作らずに済む見込み。
検証済み全体167本10,941行・951宣言。外枠18,600行を維持する。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：両端射影の保持と長い射列からの読み戻し

`OrdinaryHomTwistedRestrictions`（88行6宣言）、`OrdinaryHomTwistedLeftProjection`（64行）、
`OrdinaryHomFromLongChain`（113行）の対象ビルド・小監査が成功した。
後二本は合わせて20宣言。標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-hom-twisted-restrictions-2/`、
`/tmp/is-w1/s8-hom-twisted-left-and-long-3/`。

```lean
ordinaryHomTwistedComparison C ≫ edgewiseRight (nerve C) =
  nerveMap (ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.snd Cᵒᵖ C)
ordinaryHomTwistedComparison C ≫ edgewiseLeft (nerve C) ≫ nerveOppositeMap =
  nerveMap (ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.fst Cᵒᵖ C)

ordinaryHomFromLongChain (L : ComposableArrows C (n + n + 1)) :
  ComposableArrows (OrdinaryHomElements C) n
```

両端は全単体的射の等式。左側は反対圏と単体集合の反転を指定した比較で接続する。
長い射列の各左・右頂点を結ぶ射をそのまま元とし、合成則で可換四角形を証明した。
恒等・合成も検証済み。まだ逆関係は証明しておらず、比較の可逆性の完成には数えない。

次は既存 `edgewiseSimplexEquiv` にこの読み戻しを適用し、長い射列の左右の制限を照合する。
全体167本から3本265行26宣言増え、検証済み全体170本11,206行・977宣言。
S1・S8 は未完成、外枠18,600行を維持する。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：実際の単体の読み戻しと両端射影

`OrdinaryHomTwistedRead`（114行11宣言）の対象ビルド・小監査が成功した。
標準三公理のみ、source SHA 一致。記録：`/tmp/is-w1/s8-hom-twisted-read-2/`。

```lean
ordinaryHomTwistedRead f : ComposableArrows (OrdinaryHomElements C) n

ordinaryHomTwistedRead f ⋙ ordinaryHomElementsProjection C ⋙
  CategoryTheory.Prod.snd Cᵒᵖ C = (edgewiseRight (nerve C)).app _ f
ordinaryHomTwistedRead f ⋙ ordinaryHomElementsProjection C ⋙
  CategoryTheory.Prod.fst Cᵒᵖ C = nerveOppositeMap.app _ ((edgewiseLeft (nerve C)).app _ f)
```

読み戻しは既存 `edgewiseSimplexEquiv` の長い射列へ `ordinaryHomFromLongChain` を適用したもの。
既存の左右の包含の座標式と Yoneda の自然性から両端の全射列を比較した。
左の添字の二つの自然数式は命題の等式で移送した（計算上限の変更なし）。
まだ往復の逆関係・可逆性は未完成。零次の単位則と各対象の全再添字則は検証待ち。
検証済み全体171本11,320行・988宣言。S1・S8 は未完成。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：全次数の単位と比較の単射性

`OrdinaryHomTwistedReadPoint`（31行）、`OrdinaryHomTwistedReadReindex`（81行）は合わせて6宣言、
`OrdinaryHomTwistedUnit`（71行）は4宣言の対象ビルド・小監査が成功した。
標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-hom-twisted-point-reindex-3/`、`/tmp/is-w1/s8-hom-twisted-unit-1/`。

```lean
(ordinaryHomTwistedRead (ordinaryHomTwistedSimplex (ComposableArrows.mk₀ x))).obj 0 = x

(ordinaryHomTwistedRead (edgewiseWeight.map α ≫ f)).obj i =
  (ordinaryHomTwistedRead f).obj (α.toOrderHom i)

ordinaryHomTwistedRead (ordinaryHomTwistedSimplex s) = s
Function.Injective ((ordinaryHomTwistedComparison C).app (Opposite.op ⦋n⦌))
```

各対象の単位を零次と全再添字から出し、射の二成分は既に検証した両端射影の一致で比較した。
単位は全対象・全射を含む。零次では Hom 関手の恒等射の法則を先に書き換えた。
計算上限は変更していない。全て既存構成の法則・証明分割で、追加 ID はない。

逆向きの往復（余単位）、比較射の可逆性、指定分類図式と固定 Yoneda の全族比較は残る。
余単位は、長い射列の左右の制限と中央の隣接射で全射列を比較する筋を次に進める。
単位や単射性だけで可逆性・S8 の完成を代用しない。
検証済み全体174本11,503行・998宣言。S1・S8 は未完成、S7 は後続。
外枠18,600行を維持する。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：同じ両端を保持する Hom–twisted arrow の指定同型

`OrdinaryHomLongChainExt`（76行18宣言）、`OrdinaryHomTwistedCounitPoint`（34行1宣言）、
`OrdinaryHomTwistedIso`（104行7宣言）の対象ビルド・小監査が成功した。
標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-hom-long-ext-2/`、`/tmp/is-w1/s8-hom-counit-point-1/`、
`/tmp/is-w1/s8-hom-twisted-iso-1/`。

```lean
ordinaryHomTwistedSimplex (ordinaryHomTwistedRead f) = f
IsIso (ordinaryHomTwistedComparison C)
ordinaryHomTwistedIso C : nerve (OrdinaryHomElements C) ≅ TwistedArrow (nerve C)
```

余単位は長い射列の左右の制限を既存の両端保持の法則で比較し、中央の隣接射を
零次の余単位と全再添字から比較した。これを `ComposableArrows.ext` の証明分割に入れた。
順射は同じ `ordinaryHomTwistedComparison` なので、前に証明した両端射影の等式をそのまま保つ。
この模型比較は可逆性まで完成した（Kerodon Proposition 8.1.1.10、Tag 03JN）。
一般の nerve–join 比較の全単体の逆を別に作らず、既存の edgewise の標準単体同型を再利用した。

次は底 `nerve (Cᵒᵖ × C)` と `(nerve C).op ⊗ nerve C` を既存の積・反対の同型で揃え、
射の同型として分類図式の全族比較へ渡す。固定 Yoneda への全族比較と S8 の層化・局所同値はまだ残る。
検証済み全体177本11,717行・1,024宣言。S1・S8 は未完成、外枠18,600行を維持する。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：底を含む Hom 比較から全分類図式、固定 Yoneda の全族実現へ

`OrdinaryHomTwistedArrowIso`（71行5宣言）、`LeftStraighteningOverIso`（45行5宣言）、
`OrdinaryHomTwistedClassification`（71行11宣言）、`OrdinaryHomJointRealization`（52行6宣言）の
対象ビルド・小監査が成功した。標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-hom-twisted-arrow-iso-2/`、`/tmp/is-w1/s8-left-straightening-over-iso-1/`、
`/tmp/is-w1/s8-hom-twisted-classification-1/`、`/tmp/is-w1/s8-hom-joint-realization-1/`。

```lean
ordinaryHomTwistedArrowIso C :
  Arrow.mk (nerveMap (ordinaryHomElementsProjection C)) ≅
    Arrow.mk (twistedArrowProjection (nerve C))

leftStraighteningInfinityDiagram_overIso p q (e : Over.mk p ≅ Over.mk q) :
  FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q)

ordinaryHomJointRealizationIso C :
  FunctorIso
    ((SSet.uliftFunctor.map (ordinaryHomBaseIso C).hom) ≫ twistedArrowHomInfinity (nerve C))
    (spaceDiagram (ordinaryHomBifunctor C))
```

積・組紐・反対の既存同型で底を揃えた。底上の同型保存則を共同分類関手で送り、
引き戻しの既存の普遍性と straightening の底変換を合成した。
最後の比較は既存の自然な `SetWeight.elementsComparisonNatural` と分類の余単位を再利用した。
全底上の一つの関手同型で、対象ごとの同型を集めた仮定にしていない。
既存構成の同型保存・係数移送・底変換の法則であり追加 ID はない。

検証済み全体181本11,956行・1,051宣言。この後の固定 Yoneda の全族の実現の照合は別記する。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。


### S8 続報：固定した元の Yoneda 射と実際の Yoneda の全族比較

`SpacePresheafYonedaRealization`（62行5宣言）、`SpacePresheafYonedaJointHom`（63行3宣言）、
`SpacePresheafYonedaComparison`（68行7宣言）の対象ビルド・小監査が成功した。
標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-set-yoneda-realization-1/`、`/tmp/is-w1/s8-set-yoneda-joint-hom-2/`、
`/tmp/is-w1/s8-set-yoneda-comparison-1/`。

```lean
liftedSetYoneda C ≫ (discretePresheafInclusion C).val =
  curry (ordinaryHomFamilyBase C ≫ spaceDiagram (ordinaryHomBifunctor C))

nativeSetShapeYoneda C := yonedaInfinityMap (nerve C) ≫
  (pre ((SSet.uliftFunctor.map (nerveOppositeIso (C := C)).inv))).app SpaceInfinity

fixedSetYoneda_nativeIso C :
  FunctorIso (nativeSetShapeYoneda C)
    (liftedSetYoneda C ≫ (discretePresheafInclusion C).val)
```

元の射を既存の `kanFamily_realization_curry` により全族の実現に戻し、Hom の変数交換を
同じ通常の二変数関手の等式として照合した。共同 Hom の指定同型を底の移送で制限して curry したので、
全対象・全射・全高次を含む関手同型である。表現可能値だけの比較で代用していない。
新しい数学の ID は追加せず、既存構成の係数移送・curry・合成則の証明分割のみ。

残り：この指定同型を反転し、前層形状の指定同型とともに右 Kan 拡張へ運んで、
元の `oppositeSpaceYoneda` を使う `weightedSectionsData` を作る。
その後、離散重みの比較と射の自然性、一般の余極限から極限、層化・局所同値への接続が必要。
S1 の残りも維持し、S7 は後続とする。今回の Yoneda 比較だけで S8 完成とは数えない。
検証済み全体184本12,149行・1,066宣言。外枠18,600行を維持する。

運用記録：先行する小監査のプロセス終了確認前に次の待ちを一度出した。
先行の終了コード0を確認後は待ちを一つに戻した。以後は終了コードを確認してから次を出す。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S8 続報：元の反対 Yoneda に沿う全重みの右 Kan 延長

新規9本477行37宣言の対象ビルド・小監査が完了した。標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-left-limit-transport-2/`（2本5宣言）、
`/tmp/is-w1/s8-right-kan-fixed-yoneda-4/`（3本11宣言）、
`/tmp/is-w1/s8-right-kan-shape-iso-3/`（1本11宣言）、
`/tmp/is-w1/s8-original-weighted-sections-3/`（3本10宣言）。全runnerの終了コード0を確認した。

```lean
hasLimit_iff_of_leftStraighteningIso p q e O :
  HasLimit (p ≫ O) ↔ HasLimit (q ≫ O)

hasLimit_rightKanDiagram_iff_of_functorIso e O c :
  HasLimit (rightKanDiagram δ O c) ↔ HasLimit (rightKanDiagram δ' O c)

-- a : K ≅ K', b : C ≅ C', hw : δ ≫ b.hom = a.hom ≫ δ'
exists_rightKanExtension_iff_of_isoSquare a b hw O :
  (∃ G ε, IsRightKanExtension δ (a.hom ≫ O) G ε) ↔
    (∃ G ε, IsRightKanExtension δ' O G ε)

weightedSectionsData (O : Presheaf C E) (hE : IsPresentable E) :
  Σ G : (PresheafCat C SpaceInfinity).op ⟶ E,
    {ε : SSet.Homotopy (oppositeSpaceYoneda C ≫ G) O //
      IsRightKanExtension (oppositeSpaceYoneda C) O G ε}

weightedSections_limitValue O hE P :
  ∃ c : JoinCone (rightKanDiagram (oppositeSpaceYoneda C) O P),
    IsLimitCone c ∧ c.vertex = (weightedSections O hE).app _ P
```

分類図式の指定同型、復元、小さい unstraightening の既存の比較を使い、同じ底からの係数を保つ。
一般の同値な添字に Mono を追加せず、実際の同型の場合だけ同型の単射性を使った。
反対 nerve の指定同型を内部 Hom の第一変数で送り、前層そのものの同型を構成した。
元の Yoneda の全族比較とこの形状同型で、native な存在定理を元の `oppositeSpaceYoneda` に戻した。
`weightedSectionsData` は drafts の元の型どおり、一つの全関手と指定した変換を保持する。
新しい数学の ID は追加せず、既存の分類・同型保存・係数移送・合成則の証明分割のみ。

S3 の承認された逆向きは本体 `CechLimitLift` のとおりで、頂点の等号と指定した錐比較同値を保持する。
docstring に「制限の厳密な等号は要求しない」を記載済み。今回変更していない。

残り：離散重みと `sectionsOf` の指定比較・射の自然性、任意の小さい余極限を極限に送ること、
層化・局所同値への接続。S1 の coverage・extensive の残りも維持する。
今回の全関手の存在だけで S8 完成とは数えない。
検証済み全体193本12,626行・1,103宣言。外枠18,600行。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S8 続報：元の全切断関手の値と指定した native 局所極限の比較

新規6本313行49宣言の対象ビルド・小監査が完了した。標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-equivalent-limit-vertex-1/`、`s8-left-straightening-vertex-1/`、
`s8-right-kan-limit-vertex-1/`、`s8-local-limit-comparison-1/`（2本）、
`s8-native-limit-comparison-2/`。いずれも全runnerの終了コード0を確認した。

```lean
limitVertexIsoOfEquivalentRestriction a ha O c d hc hd :
  VertexIso c.vertex d.vertex
-- c : JoinCone (a ≫ O), d : JoinCone O, ha : IsQCatEquivalence a

limitVertexIsoOfLeftStraighteningIso p q e O c d hc hd :
  VertexIso c.vertex d.vertex
-- c : JoinCone (p ≫ O), d : JoinCone (q ≫ O)
-- e : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q)

rightKanLimitVertexIsoOfFunctorIso e O v c d hc hd :
  VertexIso c.vertex d.vertex
-- c : JoinCone (rightKanDiagram δ O v), d : JoinCone (rightKanDiagram δ' O v)
-- e : FunctorIso δ δ'

rightKanLimitVertexIsoOfIsoSquare a b hw O v c d hc hd :
  VertexIso c.vertex d.vertex
-- hw : δ ≫ b.hom = a.hom ≫ δ'
-- c : JoinCone (rightKanDiagram δ (a.hom ≫ O) v)
-- d : JoinCone (rightKanDiagram δ' O (b.hom.app _ v))

weightedSections_nativeLimitIso O hE P d hd :
  VertexIso ((weightedSections O hE).app _ P) d.vertex
-- d は実際の反対 Yoneda の局所図式の指定極限錐。
-- 係数は (fixedYonedaDomainIso C).inv ≫ O、重みは
-- (opFunctor.mapIso (fixedPresheafShapeIso C)).inv.app _ P。
```

同値な添字への既存の錐制限と、同じ図式の極限の一意性を合成した。
分類図式の同型の場合も既存の二つの復元と小さい unstraightening の比較を使った。
元の全切断関手の選択を変えず、その同じ値から指定した native 局所極限へ比較を構成する。
局所極限の存在だけの比較から、指定錐の頂点の比較まで進んだ。
全て既存構成の係数・形状移送と合成則で、追加 ID はない。200行を超える補題はない。

残りは離散重みと `sectionsOf` の指定比較・射の自然性、一般の余極限の反転、層化・局所同値、
S1 の coverage・extensive の残り。元の圏から Kan 局所形状への既存の射の射影則を次に検証する。
検証済み全体199本12,939行・1,152宣言。外枠18,600行。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### S8 続報：元の離散重みでの指定切断との比較（停止・再見積もり）

新規7本452行45宣言の対象ビルド・小監査が完了。標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-native-left-limit-2/`（2本14宣言）、
`s8-unstraightening-base-iso-1/`（2本7宣言）、`s8-fixed-left-limit-2/`（1本9宣言）、
`s8-discrete-weighted-sections-2/`（2本15宣言）。全runnerの終了コード0を確認。

```lean
weightedSections_discrete (O : Presheaf C E) (hE : IsPresentable E)
    (P : Cᵒᵖ ⥤ Type u) (hP : HasLimit (sectionsOfDiagram P O)) :
  VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm
    ((discretePresheafInclusion C).val.app _ (nerveVertex P)))) (sectionsOf P O hP)
```

これは drafts の元の型。既存の **自然な** `SetWeight.elementsComparisonNatural` とその射影・同値性を使う。
古い `elementsComparison` を使った初回も検証は通ったが、自然な既存比較へ揃えて再検証した。
指定した元の `sectionsOfCone` を保持する。射の自然性 `weightedSections_discrete_map` はまだ未完成。

既存の密度比較の射影を反転・宇宙変更で計算し、小さい left 全空間上の指定極限へ接続した。
`smallLeftUnstraighteningBaseIso` は既存の引き戻し比較射を `asIso` として読むだけで、
新しい持ち上げやホモトピーを構成していない。元の前層形状へ戻す同じ底同型で錐を制限した。
全て既存構成の射影・評価・係数移送・同型保存・合成則の証明分割。追加 ID なし。
200行を超える補題はない。計算上限は変更していない。

検証済み全体 **206本13,391行・1,197宣言**。今回の一連の追加は22本1,242行131宣言。
入口・監査登録は調整役に委ねる。S1・S8 全体は未完成、S7 は後続のまま。

#### 残りの型の照合と見込み

元の drafts を再照合した。点ごとの0切り捨て判定と離散層化の比較も未供給であり、
今回の離散重みの値比較だけでは埋まらない。既存の `Sheafification` は反射のデータで、
左完全性や集合値層化との自然な一致を結論として取り出せる型ではない。
一般の余極限についても、右 Kan 延長の存在と点ごとの値だけでは保存定理の証明は完結しない。

| 残り | 再利用と必要な接続 | 追加見込み |
|---|---|---:|
| S1 coverage・extensive | `CoverageUniversalDescent`・`DescentTopology`、元の生成篩の降下から全引き戻しへの接続、空族を含む有限積判定 | 900〜1,600行 |
| S8 離散重みの射の自然性 | 今回の同じ指定比較、`elementsComparisonNatural` の全自然性、元の `sectionsOf_map`、右 Kan の指定変換との全族照合 | 800〜1,400行 |
| S8 任意の小さい余極限の反転 | 元の全関手 `weightedSections`、密度比較、同じ全余錐の普遍性。指定余錐を仮定した条件付き保存では閉じない | 900〜1,500行 |
| S8 点ごとの0切り捨て・離散層化 | `Is0Truncated` の本質像、G13、集合値層化。反射の存在から0切り捨て保存・同じ単位の自然な比較への接続 | 1,000〜1,800行 |
| S8 局所同値 | S4 の生成篩辺と層化単位、上の全余極限の反転・離散比較から元の指定射の可逆性へ | 600〜1,000行 |
| S8 押し出し・同値な元の圏 | 検証済みの `discretePushout_isDiscrete` と任意余極限の反転、同値な添字の指定極限比較 | 100〜200行 |
| **追加合計** | S7 を含めない | **4,300〜7,500行** |

全体の見込みは **17,691〜20,891行**。上端が外枠18,600行を超える見込みになった。
`inf-supply-w1.md` の外枠・共通停止規則に従い、検証済みをコミットし、この線の Lean の追加を止める。
これは不可能性の主張ではなく、現在の残りの接続を含めた見積もり。外枠を自分で上げない。

型の正本は引き続き drafts/Sheaves。残りの型を以下に保持する（名前の省略は open namespace のみ）。

```lean
-- S1：元の生成篩だけの降下を入力にする。
isSheaf_toGrothendieck_iff (K : Coverage C) (F : Presheaf C E) :
  IsSheaf K.toGrothendieck F ↔
    ∀ U (R : Presieve U), R ∈ K.coverings U →
      IsLimitCone (restrictionCone F (Sieve.generate R))

isSheaf_extensive_iff_preservesFiniteProducts [FinitaryExtensive C] (F : Presheaf C E) :
  IsSheaf (extensiveTopology C) F ↔ PreservesFiniteProductsOnSite F

-- S8：以下は元の単位と選択した比較を使用する。
weightedSections_discrete_map (O : Presheaf C E) (hE : IsPresentable E)
    {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q)
    (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)) :
  let e := (nerve.edgeMk φ).map (discretePresheafInclusion C).val
  let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
  Truncated.HomotopyCategory.homMk r ≫ (weightedSections_discrete O hE P hP).hom =
    (weightedSections_discrete O hE Q hQ).hom ≫
      Truncated.HomotopyCategory.homMk (sectionsOf_map φ O hP hQ).toTruncated

sectionsOf_colimit (O : Presheaf C E) (hE : IsPresentable E) {K : SSet.{u}}
    {D : (SSet.uliftFunctor.{u+1,u}).obj K ⟶ PresheafCat C SpaceInfinity.{u}}
    (c : JoinCocone D) (hc : IsColimitCone c) :
  IsLimitCone (mapJoinCone (weightedSections O hE) (coconeReverseCone c))

is0Truncated_iff_pointwise (x : (PresheafCat C SpaceInfinity.{u}) _⦋0⦌) :
  Is0Truncated x ↔ ∀ U : C,
    Is0TruncatedSpace ((vertexToPresheaf x).app _ (ULift.up (nerveVertex (Opposite.op U))))

sheafify_discrete_eq (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
    (P : Cᵒᵖ ⥤ Type u) :
  FunctorIso (sheafify J hJ (discretePresheaf P))
    (discretePresheaf (((presheafToSheaf J (Type u)).obj P).obj))

-- IsLocalEquivSet J φ := IsIso ((presheafToSheaf J (Type u)).map φ)
localEquiv_of_sheafifyIso (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
    {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ) :
  IsInvertibleEdge ((nerve.edgeMk φ).map
    ((discretePresheafInclusion C).val ≫ sheafificationFunctor J hJ)).toTruncated

sections_localEquiv_iso (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
    (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ) (O : Presheaf C E) (hO : IsSheaf J O)
    (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)) :
  IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated

sectionsOf_pushout {P Q R : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : P ⟶ R) [Mono f]
    (O : Presheaf C E) (hE : IsPresentable E) :
  IsLimitCone (mapJoinCone (weightedSections O hE)
    (coconeReverseCone (pushoutCocone (discretePushoutSquare f g))))

sectionsOf_eq_limit_elements (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
    (h : HasLimit (sectionsOfDiagram P O)) {D : Type u} [SmallCategory D]
    (e : D ≌ P.Elements)
    (c : JoinCone ((SSet.uliftFunctor.{u+1,u}).map
      (nerveMap (e.functor ⋙ Functor.Elements.π P)) ≫ O)) (hc : IsLimitCone c) :
  VertexIso (sectionsOf P O h) c.vertex
```

一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### 停止後の照合：右 Kan の大域的一意性の再利用（紙、11-16）

作業枝 `142826a1a` と main `a4388efc9` の現状を確認した。
main の指示書でも S1〜S6・S8 の外枠18,600行は変更されていない。
共通規則の正しい場所は `formalization-plans/coordination.md` §2。
「上限を超えそうなときは報告して止める（止まる前に、それまでの検証済みの分をコミット）」
に従い、Lean の追加・ビルドは行っていない。直前の22本は全てコミット済み。

`Kerodon/LimitsAndColimits/KanExtensions/RightHomUniversal.lean` には、点ごとの値の一意性より強い、
指定変換を保つ大域的な比較がすでにある。再開時に点ごとの同型を集める構成を新しく作らない。

```lean
-- [Quasicategory K] [Quasicategory C] [Quasicategory D]
-- δ : K ⟶ C, F₀ : K ⟶ D, F G : C ⟶ D
-- α : SSet.Homotopy (δ ≫ F) F₀, β : SSet.Homotopy (δ ≫ G) F₀
-- hα : IsRightKanExtension δ F₀ F α
-- hβ : IsRightKanExtension δ F₀ G β
kanRightKanExtensionIso δ α β hα hβ : FunctorIso F G

kanRightKanExtensionIso_hom_fac δ α β hα hβ :
  rightKanHomMap δ
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) F
    (kanRightKanExtensionIso δ α β hα hβ).hom =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)
```

再利用の境目：

- **自然性**：全関手・指定変換を持つ第二の模型を用意できれば、上の同型と射の一意性を使う。
  現在の `sectionsOf`・`sectionsOf_map` の値と辺だけを、その第二の全関手とみなしてはいけない。
  もう一つの候補は G8 の `SetWeight.tensorSpaceFunctor_setWeightHomNatural` の全パラメータの比較で
  元の指定射を検出し、今回の `weightedSections_discrete` の評価と照合する道。
  いずれも今回の比較の頂点成分だけから自然性が自動で出るとは数えない。
- **一般余極限**：`kanRightKanExtensionIso` は全関手の比較を与えるが、右 Kan 条件の入力自体は
  余極限を極限に送ることを仮定・結論にしていない。任意の小さい形状での同じ全余錐の保存の証明は残る。
- **離散層化**：既存の `Sheafification` は反射の型。集合値層化の単位と同じ指定単位の比較、
  または0切り捨て保存の証明を別に要する。一般の反射の一意性だけではその入力を置き換えられない。
- **main の再利用**：最終の未完宣言名（`weightedSections_discrete_map`、`sectionsOf_colimit`、
  `is0Truncated_iff_pointwise`、`sheafify_discrete_eq`、`sections_localEquiv_iso`、
  `isSheaf_toGrothendieck_iff`）について、本体の供給済みの宣言を main から拾うことはできなかった。
  これは別名の定理がないことの証明ではなく、上の具体的 API の型の確認と合わせた現状の照合である。

この再利用を考慮しても、前節の残りの上端を外枠内まで下げる根拠は得ていない。
見込み17,691〜20,891行、検証済み13,391行は維持する。R2・R3・S7 は再開しない。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### 22,000行で再開：S8 の点ごとの離散性・同値な元の圏・大域比較（11-16）

ユーザー承認 `cae591fa4` を含む main を作業枝へ取り込んだ（merge `687f2db8c`）。
外枠を22,000行へ変更し、約18,000行の途中報告を保持する。S7・R2・R3 は再開しない。

新規5本316行21宣言の対象ビルド・小監査が完了。標準三公理のみ、source SHA 一致。
記録：`/tmp/is-w1/s8-resume-global-comparison-1/`（新規2本10宣言と既存 `WeightedSectionsDiscrete` の回帰）、
`s8-small-nerve-diagram-2/`（1本6宣言）、`s8-pointwise-discrete-2/`（1本4宣言）、
`s8-presheaf-left-kan-colimits-2/`（1本1宣言）。全runnerの終了コード0を確認済み。

```lean
-- β : Homotopy (oppositeSpaceYoneda C ≫ G) O,
-- hβ : IsRightKanExtension (oppositeSpaceYoneda C) O G β
weightedSections_comparison O hE β hβ : FunctorIso (weightedSections O hE) G
-- 本文は kanRightKanExtensionIso の特殊化。
-- hom_fac・hom_unique も既存の同名の分解則・一意性をそのまま使う。

sectionsOf_eq_limit_elements P O h e c hc : VertexIso (sectionsOf P O h) c.vertex
-- e : D ≌ P.Elements、c は e.functor ⋙ Elements.π P に沿う元の指定極限錐。

is0Truncated_iff_pointwise (x : (PresheafCat C SpaceInfinity) _⦋0⦌) :
  Is0Truncated x ↔ ∀ U : C,
    Is0TruncatedSpace ((vertexToPresheaf x).app _ (ULift.up (nerveVertex (Opposite.op U))))

-- β : Homotopy F₀ (yonedaInfinityMap A ≫ L),
-- hβ : IsLeftKanExtension (yonedaInfinityMap A) F₀ L β,
-- p : (SSet.uliftFunctor.{u+1,u}).obj I ⟶ PresheafInfinity A
presheafYonedaLeftKan_map_isColimit β hβ (c : JoinCocone p) (hc : IsColimitCone c) :
  IsColimitCone (mapJoinCocone L c)
```

点ごとの離散性は既存の `exists_diagram_in_fullyFaithful_source` を離散埋め込みへ適用した。
小さい nerve の図式は元の頂点・辺・三角形から通常前層へ戻し、strict Segal 則で全次数を照合した。
元の離散前層の埋め込みとの全単体の等式も証明した。点ごとの同型を集める新しい構成は作っていない。
この判定と S8-6 は drafts の元の型を閉じたが、S8 全体の完了とは数えない。

全前層 Yoneda 左 Kan 延長の任意小余極限保存には、既存の
`presheafExtensionHom_liftedIso` と `fullPresheafHomWeightFamily_map_isLimit` を合成した。
前者は既存の大域的右 Kan 比較を使う。後者の元の任意余錐を保持して co-Yoneda で反映する。
sifted 性を追加していない。これを元の反対 Yoneda に沿う `weightedSections` へ戻す接続は残る。

検証済み全体211本13,707行・1,218宣言。追加 ID なし、200行超の補題なし、計算上限変更なし。
残り：元の離散比較の射の自然性、元の全切断関手の一般余極限の反転・押し出し、離散層化・局所同値、
S1 coverage・extensive。承認された同じ範囲で続ける。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### 反対 Yoneda の全関手を保つ接続（11-16）

新規3本189行17宣言を対象ビルド・小監査で確認した。
記録 `/tmp/is-w1/s8-kan-shape-data-2/target-audit-result.json`、runner 終了0、
標準三公理のみ、source SHA 一致。検証済み全体214本13,896行・1,235宣言。

```lean
-- a : K ≅ K', b : C ≅ C', hw : δ ≫ b.hom = a.hom ≫ δ'
kanRightKanExtension_of_isoSquare a b hw α hα :
  IsRightKanExtension δ (a.hom ≫ O) (b.hom ≫ F)
    (rightKanCounitIsoSquare a b hw α)

-- hU は同じ rightKanDiagram の各極限錐の保存
kanRightKanExtension_postcomp_of_localLimits δ α hα U hU :
  IsRightKanExtension δ (F₀ ≫ U) (F ≫ U) (kanRightCounitPostcomp α U)
```

これらは既存の構成の同型移送・後合成の法則。指定変換と全輸送族を保存し、
点ごとの頂点同型を集める大域比較を作っていない。追加 ID なし、200行超の補題なし。
反転した実 Yoneda からの任意小余極限の極限への変換を次に検証中。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### 文献属性の追加の作業（11-16、検証中）

追加指示 `8522e6b3b` を確認。Sheaves の既存112本と新規検証中1本で、
出典番号を「使われ方」から「方針」の文献対応へ移した。主な宣言へ18属性を追加。
HTT 6.2.2.6・6.2.2.7・5.5.4.15、Čech の HTT 4.1.3.1 と双対の4.1.1.8、
重み付き切断の5.1.5.6、右 Kan の一意性の4.3.2.15、安定性のHA1.1.3.2に対応。
原典の型を公式PDFと照合した。小さい通常 site・Čech 層・反射だけの結論・
反転した特殊化である理由を `(partial := special)` に明記した。
Kerodon の02NY・02Y9・06VH等は一般の判定・定義・Bousfield反射であり、
ここでの宣言はその特殊化なので、partialへの属性は付けずdocstringに保つ。

コメント・文献属性・そのmeta importを除いたコードの一致をPythonで全113本確認。
主張・証明を変更していない（新規未検証 NativeRightKanContinuity の修正は別）。
属性・docstring の行数差は外枠に数えない。対象ビルドと小監査は
`/tmp/is-w1/s8-sheaves-citations-1/` の一枚の整理券で待っている。
完了・コミット済みとはまだ報告しない。

実 Yoneda の反転の初回対象ビルドでは、二重反転の等式移送の向きだけが不一致だった。
Eqの後合成で向きを揃える修正を行い、上の対象ビルドに含めた。計算上限変更なし。
同じ形状同型に沿って実際の全関手と指定余単位を運ぶ68行の接続も作業木で準備中。
全関手の比較は引き続き既存の kanRightKanExtensionIso と hom_fac を使う。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### 文献属性・docstring の対象検証（11-16）

既存112本の文献整理と、新規の接続2本の計114本の対象ビルド、小監査726宣言、
属性18件の新しい環境での登録確認が終了0で通った。記録：
`/tmp/is-w1/s8-sheaves-citations-2/`（target-audit-result.json、citations-registered.json）。
標準三公理のみ、source SHA一致。初回の二つの連続属性ブロックの構文エラーは、
同じ一つのブロックの二属性へ直した。未解決のビルドエラーなし。style警告は残る。

既存112本では、コメント・文献属性・必要なmeta importを除いた宣言・証明コードの一致を
改めて確認した。主張・証明の変更なし。文献整理の行数は外枠に数えない。
Kerodon の一般定理に対する特殊化には属性を付けず、既存のdocstringで対応を保持した。
新規の実 Yoneda の余極限反転と形状移送にも同じ理由付き属性を足し、2本の最終検証中。
これは5∞-1の完成の報告ではない。S1とS8の残りを継続する。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### 実 Yoneda の余極限反転・文献属性の最終確認（11-16）

新規2本152行（文献属性・docstringの差分は除外）4宣言の最終対象ビルド・小監査が
終了0で通った。記録 `/tmp/is-w1/s8-native-continuity-final/target-audit-result.json`。
標準三公理のみ、source SHA一致。新規の接続2本の属性を含めて、
Sheaves の20件すべてが新しい環境で登録され、special の理由を持つことも確認した
（`/tmp/is-w1/sheaves-citations-registered.json`）。既存112本の属性・docstringだけの
変更は `cd65864e0` に分けた。計算上限変更なし、200行を超える補題なし。

```lean
-- α : Homotopy (opFunctor.map (yonedaInfinityMap A) ≫ G) O
-- hα : IsRightKanExtension (opFunctor.map (yonedaInfinityMap A)) O G α
nativeRightKan_map_colimit_isLimit α hα
  (c : JoinCocone p) (hc : IsColimitCone c) :
  IsLimitCone (mapJoinCone G (coconeReverseCone c))

-- O : Presheaf C E、hE : IsPresentable E
exists_nativeShapeSections_continuous O hE :
  ∃ (H : (PresheafCat C SpaceInfinity).op ⟶ E)
    (ε : Homotopy (nativeSetShapeOppositeYoneda C ≫ H) O),
    IsRightKanExtension (nativeSetShapeOppositeYoneda C) O H ε ∧
    ∀ {I : SSet.{u}} {p : (SSet.uliftFunctor.{u+1,u}).obj I ⟶ PresheafCat C SpaceInfinity}
      (c : JoinCocone p), IsColimitCone c →
        IsLimitCone (mapJoinCone H (coconeReverseCone c))
```

前者は既存の指定左 Kan の全 Hom 比較を反転し、二重反転の等式の後合成で
元の全関手・余錐に戻す。後者は実際の始域・終域の同型の可換四角形で、
同じ全関手と指定余単位を移す。点ごとの同型を集める大域比較は作っていない。

**残る接続を区別する**：このHは `nativeSetShapeOppositeYoneda` に沿う模型。
元の `oppositeSpaceYoneda` への関手同型の移送で、Hと指定余単位の類を保つ法則が残る。
既存の `exists_rightKanExtension_iff_of_functorIso` は存在だけを運び、
その証明をHの保存に読み替えてはいけない。次の既存構成の法則を閉じてから、
`kanRightKanExtensionIso`・`kanRightKanExtensionIso_hom_fac` を元の全関手へ適用する。

```lean
-- {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
-- {δ δ' : K ⟶ C} (e : FunctorIso δ δ') {O : K ⟶ D} {G : C ⟶ D}
-- (α : Homotopy (δ' ≫ G) O) (hα : IsRightKanExtension δ' O G α)
∃ β : Homotopy (δ ≫ G) O,
  IsRightKanExtension δ O G β ∧
  Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β) =
    (e.postcomp G).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)
```

検証済み全体216本14,048行・1,239宣言（文献整理の行数は除外）。
S8の残りはこの元の全関手への接続、指定離散比較の射の自然性、押し出し、
離散層化と局所同値。S1の元のcoverage・extensiveも残る。停止点にはまだ届いていない。
S7・R2・R3は再開していない。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### 元の全切断の小余極限・押し出し（11-16）

調整役の承認 `6ea430827` に従い、既存の `rightKanHomUniversalIso` と
`rightKanHomUniversalIso_hom_fac` を直接使った。両方のHom普遍性は
既存の指定Kan延長から証明し、片側は添字同型で移送した。
前節の、Hを保った点ごとの右Kan条件そのものの添字同型移送を経由する必要はなくなった。
元の主張の型と指定変換の類を保持する同じ大域比較で結論に達する。

新規3本212行（うち文献属性・必要なmeta import10行、外枠計202行）13宣言。
対象ビルド・小監査は `/tmp/is-w1/s8-weighted-pushout-1/`、終了0、
標準三公理のみ、source SHA一致。既存Cat包装を`Functor.toCatHom_toFunctor`で
明示的に簡約し、計算上限は変えていない。200行超の補題なし。
元draftsと同じ余極限・押し出しの型と引数順もLeanで確認した。
記録 `/tmp/is-w1/s8-weighted-original-types/check.lean`・`check.log`、終了0。
同じ新環境でSheavesの理由付き文献属性23件の登録も確認した。

```lean
rightKanHomMap_indexIso e α G η :
  rightKanHomMap δ ((e.postcomp F).hom ≫ α) G η =
    (e.postcomp G).hom ≫ rightKanHomMap δ' α G η

-- hα : RightKanHomUniversal δ' α（呼び出し側で指定Kan延長から証明）
RightKanHomUniversal.indexIso e hα :
  RightKanHomUniversal δ ((e.postcomp F).hom ≫ α)

weightedSections_nativeShape_comparison O hE α hα :
  FunctorIso (weightedSections O hE) G
-- hom_fac は元の指定余単位の類への分解則。仮定を新設してはいない。

sectionsOf_colimit O hE (c : JoinCocone p) (hc : IsColimitCone c) :
  IsLimitCone (mapJoinCone (weightedSections O hE) (coconeReverseCone c))

sectionsOf_pushout (f : P ⟶ Q) (g : P ⟶ R) [Mono f] O hE :
  IsLimitCone (mapJoinCone (weightedSections O hE)
    (coconeReverseCone (pushoutCocone (discretePushoutSquare f g))))
```

押し出しの形状は既存の `strictSpanHornIso` で実際の小さい形状へ制限し、
`coconeReverseCone_restrict_val` と同型での極限性の反映で元の全錐へ戻した。
指定辺や二単体を別々に選ぶ構成は追加していない。

検証済み全体219本14,250行・1,252宣言（文献整理の差分は除外）。
S8の元の二つの結論が閉じた。指定離散比較の射の自然性、離散層化、
局所同値と切断の比較、およびS1のcoverage・extensiveは残る。
Mathlibの局所全単射判定と同じ層化単位への接続を次に対象検証する。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### 集合値局所同値の元の入口（11-16）

`SetLocalEquivalence` 1本42行（文献属性・meta import4行を除く外枠計38行）
4宣言を対象ビルド・小監査で確認した。記録 `/tmp/is-w1/s8-set-local-equivalence-1/`、
終了0、標準三公理のみ、source SHA一致。定義はdraftsと同じ層化の同型の逆像。
局所全単射の判定と単位の性質は、既存Mathlibの同じ層化・単位から証明した。

```lean
IsLocalEquivSet J φ := IsIso ((presheafToSheaf J (Type u)).map φ)

isLocalEquivSet_iff_locallyBijective J φ :
  IsLocalEquivSet J φ ↔
    CategoryTheory.Presheaf.IsLocallyInjective J φ ∧
    CategoryTheory.Presheaf.IsLocallySurjective J φ

isLocalEquivSet_toSheafify J P :
  IsLocalEquivSet J (CategoryTheory.toSheafify J P)
```

この通常の集合値の判定を、空間値層化での可逆性の結論としてはまだ数えない。
次の離散層化の比較では、元の集合値単位と同じ射を使う。
必要な切り分けは、まず
`IsSheaf J (discretePresheaf P) ↔ CategoryTheory.Presheaf.IsSheaf J P`
の元の制限全錐での比較、その後、同じ単位を保つ空間値反射との全自然な比較。
既存の反射の存在だけから0切り捨ての保存を推論してはいけない。
任意の通常の添字を持つ離散空間値図式の極限比較を、既存の全Hom判定から調べる。

検証済み全体220本14,288行・1,256宣言（文献整理は外枠外）。
今回閉じた元の結論は `sectionsOf_colimit`・`sectionsOf_pushout`（`5318de01c`）。
未完：S8の `weightedSections_discrete_map`・`sheafify_discrete_eq`・
`localEquiv_of_sheafifyIso`・`sections_localEquiv_iso`、S1の元のcoverage・extensive。
目標全体は継続中で、完成停止点ではない。追加IDなし、計算上限変更なし。
一覧：済み 5／全体 8（うち追加 0、済み：S2・S3・S4・S5・S6、S7 は後続）。

### 離散係数の任意小極限（11-16）

`DiscreteAnodyneExtensions`・`DiscreteSpaceLimits` の2本118行（文献整理4行を除く114行）、
6宣言を対象ビルド・小監査で確認した。記録 `/tmp/is-w1/s8-discrete-limits-2/`、
終了0、標準三公理のみ、source SHA一致。

```lean
discrete_precomp_injective_of_anodyne i hi T :
  Function.Injective (fun f : B ⟶ discrete T => i ≫ f)
existsUnique_discrete_extension i hi T a : ∃! b, i ≫ b = a
discreteDiagram_anodyne_extensions F ι hι a : ∃ b, ι ≫ b = a
discreteSpaceCone_isLimit (c : Cone F) (hc : IsLimit c) :
  IsLimitCone (discreteSpaceCone c)
```

anodyneに沿う一意な延長は既存の相対ホモトピーと定値空間への射の判定から導き、
その図式での自然性を経て、既存の全Hom極限判定に渡した。添字は任意の小さい通常の圏で、
離散な添字に制限していない。これはS8の証明の分割で追加IDなし。
次は同じ通常錐を元の層条件の指定制限錐へ比較する。
検証済み全体222本14,402行・1,262宣言（文献整理は外枠外）。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 元の指定錐での離散層条件の比較（11-16）

4本262行（文献属性・meta import4行を除く258行）、13宣言の対象ビルド・小監査が成功。
記録 `/tmp/is-w1/s8-cone-initial-9/`、終了0、標準三公理のみ、source SHA一致。

```lean
nerveInitialCone_leg hi j :
  (nerveInitialCone hi).app _ (coneLegSimplex j) = ComposableArrows.mk₁ (hi.to j)
initialJoinNerveMap_eq_initialCone I :
  initialJoinNerveMap I = joinMap (𝟙 _) (nerveMap WithInitial.incl) ≫
    nerveInitialCone (WithInitial.starInitial (C := I))
nerveCone_val_initial c :
  (nerveCone c).val = joinMap (𝟙 _) (nerveMap WithInitial.incl) ≫
    nerveInitialCone (WithInitial.starInitial (C := I)) ≫
    nerveMap (coneWithInitialFunctor c)
strictConeFunctor_mapCone c G :
  coneWithInitialFunctor (asSmallCone c) ⋙ AsSmall.down ⋙ G =
    strictConeFunctor (G.mapCone c)
strictCoherentConeMap_mapCone c G :
  strictCoherentConeMap (G.mapCone c) =
    (nerveCone c).ulift.val ≫ kanDiagramCoherentNerve G
smallNerveDiagram_reflects_limit c P
    (hc : IsLimitCone (((nerveCone c).ulift).postcomp (smallNerveDiagram P))) :
  Nonempty (IsLimit (P.mapCone c))
sieveCone_eq_presieveCone S : sieveCone S = S.arrows.cocone.op
restrictionCone_discrete_val P S :
  (restrictionCone (discretePresheaf P) S).val =
    (discreteSpaceCone (P.mapCone (sieveCone S))).val
isSheaf_discretePresheaf_iff J P :
  IsSheaf J (discretePresheaf P) ↔ CategoryTheory.Presheaf.IsSheaf J P
```

前半は既存の始対象錐・AsSmall・coherent 表示の構成の法則。
逆向きは既存の `nerveAsSmallMaxIso`、通常の極限比較、充満忠実な離散埋め込みによる
全錐の反映を使った。対象宇宙とHom宇宙を同一視していない。
制限錐の頂点だけでなく全射が一致し、通常の層条件はMathlibの同じ篩の錐で得ている。
独立の追加IDなし、200行を超える法則の補題なし、計算上限変更なし。
主な層条件比較に HTT 6.2.2.7 の属性（小さい通常site・離散係数の特殊化）を付けた。

検証済み全体226本14,660行・1,275宣言（文献整理は外枠外）。
これは離散層化の比較の前提までであり、`sheafify_discrete_eq` そのものは未完。
残りは同じ層化単位を保つ全比較、指定した `weightedSections_discrete` の射の自然性、
`localEquiv_of_sheafifyIso`・`sections_localEquiv_iso`、S1の元のcoverage・extensive。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 局所単射の像篩と元の局所 comma（11-16）

3本216行、21宣言を対象ビルド・小監査で確認した。記録 `/tmp/is-w1/s8-image-sieve-7/`、
終了0、標準三公理のみ、source SHA一致。S8の局所同値の証明の分割で、追加IDなし。

```lean
imageSieveCommaFunctor φ q :
  StructuredArrow q φ.mapElements ⥤ (sieveCategory (Presheaf.imageSieve φ q.val))ᵒᵖ
imageSieveCommaFunctor_projection φ q :
  imageSieveCommaFunctor φ q ⋙ sieveDiagram (Presheaf.imageSieve φ q.val) =
    StructuredArrow.proj q φ.mapElements ⋙ Functor.Elements.π P
imageSieveCommaEquivalence φ [Mono φ] q :
  StructuredArrow q φ.mapElements ≌ (sieveCategory (Presheaf.imageSieve φ q.val))ᵒᵖ
-- 比較の忠実性・単射での充満性・本質的全射性を個別に確認。
-- imageSieveCommaEquivalence_projection は上と同じ射影の等式。
imageSieveCommaCone_eq φ q :
  imageSieveCommaCone φ q =
    (sieveCone (Presheaf.imageSieve φ q.val)).whisker (imageSieveCommaFunctor φ q)
imageSieveCommaRestrictionCone_val φ q O :
  (restrictJoinCone (restrictionCone O (Presheaf.imageSieve φ q.val))
    (uliftFunctor.map (nerveMap (imageSieveCommaFunctor φ q)))).val =
      (imageSieveCommaRestrictionCone φ q O).val
imageSieveCommaRestrictionCone_isLimit_iff φ [Mono φ] q O :
  IsLimitCone (imageSieveCommaRestrictionCone φ q O) ↔
    IsLimitCone (restrictionCone O (Presheaf.imageSieve φ q.val))
imageSieveCommaRestrictionCone_isLimit J φ [Mono φ]
    [Presheaf.IsLocallySurjective J φ] q O (hO : IsSheaf J O) :
  IsLimitCone (imageSieveCommaRestrictionCone φ q O)
```

既存の `StructuredArrow`・`imageSieve`・右延長の `coneAt` の表示を照合した。
層条件を頂点の存在へ弱めず、元の射影と全脚を保持している。
局所全射な単射という途中の場合であり、一般の局所同値の完了には数えない。
次は既存の `asSmallStructuredArrowFunctor` と
`nerveRightConeTransportPostcomp_isLimit_iff` による宇宙移送を接続する。
後者と `isLimitCone_asSmallCoefficient_iff` の合成則は、
`AsSmallRightConeTransport` として未検証の作業木に準備した。

検証済み全体229本14,876行・1,296宣言（文献整理は外枠外）。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 局所単射の指定右 Kan 条件（11-16）

`AsSmallRightConeTransport`・`MonoLocalRightKan` の2本118行、4宣言を確認。
記録 `/tmp/is-w1/s8-as-small-right-cone-2/`、対象ビルド・小監査とも終了0、
標準三公理のみ、source SHA一致。既存の構成の宇宙移送とS8の証明分割、追加IDなし。

```lean
asSmallRightCounit L α :
  asSmallLocalFunctor L ⋙ asSmallLocalFunctor F ⟶ asSmallLocalFunctor F₀
asSmallRightCounit_cone L α j :
  ((Functor.RightExtension.mk (asSmallLocalFunctor F) (asSmallRightCounit L α)).coneAt
    (AsSmall.up.obj j)).whisker (asSmallStructuredArrowFunctor L j) =
      asSmallCone ((Functor.RightExtension.mk F α).coneAt j)
asSmallRightConeTransportPostcomp_isLimit_iff L α j U :
  IsLimitCone (nerveRightConeTransportPostcomp (asSmallLocalFunctor L)
    (asSmallRightCounit L α) (AsSmall.up.obj j) ((nerveAsSmallIso D).inv ≫ U)).cone ↔
  IsLimitCone (((nerveCone ((Functor.RightExtension.mk F α).coneAt j)).ulift).postcomp U)

-- V := (nerveAsSmallIso Cᵒᵖ).inv ≫ O
-- η := asSmallRightCounit φ.mapElements φ.mapElementsCompπIso.hom
monoLocal_isRightKanExtension J φ [Mono φ] [Presheaf.IsLocallySurjective J φ]
    O (hO : IsSheaf J O) :
  IsRightKanExtension (nerveMap (asSmallLocalFunctor φ.mapElements))
    (nerveMap (asSmallLocalFunctor (Functor.Elements.π P)) ≫ V)
    (nerveMap (asSmallLocalFunctor (Functor.Elements.π Q)) ≫ V)
    (kanRightCounitPostcomp (nerveNatTransHomotopy η) V)
```

最後の右 Kan 条件は、全頂点を同じ元の圏の元に戻し、直前の局所錐の極限性から証明した。
仮定として置いていない。点ごとの同型を集めて大域同型にする構成も追加していない。
一般の局所全単射の切断不変性への次の接続は、指定恒等余単位の法則と
`isLimitCone_iff_of_rightKan_comparison` から、制限した元の指定極限錐の極限性を戻すもの。
実際の `sectionsOf_map` との同定を飛ばして、任意の頂点同型で完了とはしない。
単射でない場合、同じ層化単位の比較、指定した `weightedSections_discrete` の自然性は残る。
S1の元のcoverage・extensiveも未完。S7・R2・R3は再開していない。

検証済み全体231本14,994行・1,300宣言（文献整理は外枠外）。
今回の継続分は計11本706行・44宣言。外枠22,000行以内、完成停止点ではない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 恒等余単位での極限比較（11-16、検証済み）

`RightKanLimitRestriction` 1本40行・1宣言。記録 `/tmp/is-w1/s8-right-kan-restrict-1/`、
対象ビルド・小監査の終了0、標準三公理のみ、source SHA一致。既存の右 Kan 合成則の特殊化。

```lean
isLimitCone_iff_restrict_of_rightKan_refl δ p
    (h : IsRightKanExtension δ (δ ≫ p) p
      (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (δ ≫ p))))
    (c : JoinCone p) :
  IsLimitCone c ↔ IsLimitCone (restrictJoinCone c δ)
```

`isLimitCone_iff_of_rightKan_comparison` に元の錐の恒等円柱を渡した。
追加IDなし。検証済み全体232本15,034行・1,301宣言（文献整理は外枠外）。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 指定切断射へ戻す続き（11-16、未検証の作業木）

次の4本を作業木に準備した。これらは未検証で、検証済みの実測にはまだ数えていない。
いずれもS8の既存の構成の法則・証明の分割で、追加IDなし、200行を超える補題なし。

`MonoLocalRightKanRestriction`：
```lean
asSmallSectionsDiagram P O :=
  nerveMap (asSmallLocalFunctor (Functor.Elements.π P)) ≫ (nerveAsSmallIso Cᵒᵖ).inv ≫ O
-- monoLocalRightKanCounit φ O は、元の恒等余単位を同じ係数 O へ送った円柱。
monoLocalRightKanCounit_h φ O :
  (monoLocalRightKanCounit φ O).h = fst _ _ ≫ asSmallSectionsDiagram P O
monoLocal_restrict_isLimit J φ [Mono φ] [Presheaf.IsLocallySurjective J φ]
    O (hO : IsSheaf J O) (c : JoinCone (asSmallSectionsDiagram Q O)) (hc : IsLimitCone c) :
  IsLimitCone (restrictJoinCone c (nerveMap (asSmallLocalFunctor φ.mapElements)))
```

`MonoLocalSections`：
```lean
asSmallSectionsDiagram_eq P O :
  asSmallSectionsDiagram P O = (nerveAsSmallIso P.Elements).inv ≫ sectionsOfDiagram P O
asSmallSectionsCone P O (c : JoinCone (sectionsOfDiagram P O)) :
  JoinCone (asSmallSectionsDiagram P O)
asSmallSectionsCone_isLimit P O c (hc : IsLimitCone c) :
  IsLimitCone (asSmallSectionsCone P O c)
asSmallSectionsCone_restrict_val φ O c :
  ((restrictJoinCone (asSmallSectionsCone Q O c)
    (nerveMap (asSmallLocalFunctor φ.mapElements))).reindexIso
      (nerveAsSmallIso P.Elements)).val = (SetWeight.restrictSectionsCone φ O c).val
restrictSectionsCone_isLimit_of_localMono J φ [Mono φ] [Presheaf.IsLocallySurjective J φ]
    O (hO : IsSheaf J O) c (hc : IsLimitCone c) :
  IsLimitCone (SetWeight.restrictSectionsCone φ O c)
sections_localMono_iso J φ [Mono φ] [Presheaf.IsLocallySurjective J φ]
    O (hO : IsSheaf J O) hP hQ : IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated
```
最後は元の `sectionsMap_isInvertible_iff` で同じ指定辺へ戻す。一般形の代用にはしない。

`SetSectionsRestriction`：
```lean
sliceOver_diagramEq_val (h : p = q) n s :
  ((eqToHom (congrArg sliceOver h)).app n s).val = s.val
restrictSectionsFunctor φ F : sliceOver (diagram Q F) ⟶ sliceOver (diagram P F)
restrictSectionsFunctor_val φ F n s :
  ((restrictSectionsFunctor φ F).app n s).val = joinMap (𝟙 _) (elementsMap φ) ≫ s.val
restrictSectionsFunctor_vertex φ F c :
  (restrictSectionsFunctor φ F).app (op ⦋0⦌) c = restrictSectionsCone φ F c
restrictSectionsFunctor_projection φ F :
  restrictSectionsFunctor φ F ≫ sliceOverProjection (diagram P F) =
    sliceOverProjection (diagram Q F)
elementsMap_comp φ ψ : elementsMap (φ ≫ ψ) = elementsMap φ ≫ elementsMap ψ
restrictSectionsCone_comp φ F ψ c :
  restrictSectionsCone φ F (restrictSectionsCone ψ F c) = restrictSectionsCone (φ ≫ ψ) F c
restrictSectionsFunctor_comp φ F ψ :
  restrictSectionsFunctor (φ ≫ ψ) F = restrictSectionsFunctor ψ F ≫ restrictSectionsFunctor φ F
```
これは元の制限の全関手・全錐の法則で、点ごとの同型を集める構成ではない。

`LocalInjectiveDiagonal`：
```lean
presheafDiagonal_fst_apply φ U p :
  (pullback.fst φ φ).app U ((pullback.diagonal φ).app U p) = p
presheafDiagonal_snd_apply φ U p :
  (pullback.snd φ φ).app U ((pullback.diagonal φ).app U p) = p
imageSieve_diagonal φ q :
  Presheaf.imageSieve (pullback.diagonal φ) q =
    Presheaf.equalizerSieve ((pullback.fst φ φ).app _ q) ((pullback.snd φ φ).app _ q)
diagonal_isLocallySurjective J φ [Presheaf.IsLocallyInjective J φ] :
  Presheaf.IsLocallySurjective J (pullback.diagonal φ)
```
対角はMathlibの同じ核対の射で、単射でない場合の入力を保持する。
一般の局所同値は、核対・Čech解消と指定射の自然性との接続がまだ必要。
層化単位の比較・`weightedSections_discrete_map`・S1のcoverageとextensiveも残る。
S7・R2・R3は再開していない。

検証の順序：現在の `/tmp/is-w1/s8-right-kan-restrict-2/`（2本）の終了を確認し、
誤りを修正した後に上の4本をまとめて対象ビルド・小監査。待ちは一枚。
05:42 UTCの時点でセッション18959の生存を再確認、共有鍵で調整役のrootビルドの後を待機中。
古い索引や未検証の結果を監査の証拠に流用しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 鍵待ちの紙の照合：S1 extensive の元の型（11-16）

未実装。範囲・型の変更ではなく、元の有限積判定を閉じるための証明の分割。
有限非空族 B と余極限 cofan c、生成篩 S に対し、次の添字の表示を使う案。

```lean
-- S := Sieve.generate (Presieve.ofArrows B c.inj)
extensiveSieveIndexFunctor c (hc : IsColimit c) [Nonempty ι] :
  WithTerminal (Discrete ι) ⥤ (sieveCategory S)ᵒᵖ
-- of i ↦ (B i ⟶ c.pt), star ↦ (⊥_ C ⟶ c.pt)
-- 各 i → star は元の initial.to (B i) の反転。

extensiveSieveIndexFunctor_hasTerminalComma c hc (s : (sieveCategory S)ᵒᵖ) :
  HasTerminal (CostructuredArrow (extensiveSieveIndexFunctor c hc) s)
```

像が初対象の射である star の membership は、非空族の一本の脚と篩の下方閉性から作る。
篩の対象 s の始域 V が初対象なら、この comma の終対象は star から作る。
V が初対象でなければ、S の元であることから V→B i の分解を一本選ぶ。
別の脚 j への分解があれば、交叉の非交叉性と初対象の厳密性から V は初対象となり矛盾。
同じ脚への分解の一意性は脚の単射性で示す。
**C の任意の V→c.pt が一本の脚を通るとは仮定しない**。ここで分解を使うのは S の対象だけ。

照合した既存Mathlibの入力：
- `Mono.of_coproductDisjoint`、`IsInitial.ofCoproductDisjointOfCommSq`
  （`Limits/Shapes/DisjointCoproduct.lean`）。
- `FinitaryExtensive.isVanKampen_finiteCoproducts`、有限 cofan の脚の単射性と交叉の初対象性
  （`CategoryTheory/Extensive.lean`）。
- `Adjunction.isLeftAdjoint_of_costructuredArrowTerminals`
  （`CategoryTheory/Adjunction/Comma.lean`）。
これで添字比較を左随伴とし、既存の adjunction からの nerve の left cofinality を使う。
新しい一般の Quillen A を作らない。

係数側：WithTerminal (Discrete ι) の star の値 F(⊥) が終対象なら、元の全錐の極限性は
脚だけの指定積錐の極限性と同値。離散添字の包含に沿う恒等余単位の右 Kan 条件を、
star では空の局所図式、of i では恒等射の局所図式で示す方針。
`isLimitCone_iff_of_rightKan_comparison` へ同じ全錐を渡す。
空族は star の篩 membership を作れないので別の枝にし、底篩の制限錐と終対象の判定へ渡す。

元の広い篩への方向には、被覆篩が有限 colimit cofan の脚を含むという
`extensiveTopology.mem_sieves_iff_contains_colimit_cofan` と、既検証の descentTopology を使う。
引き戻した有限 cofan も colimit であることを extensivity から示し、
生成篩の**全引き戻し**で降下を供給する（S1の一般coverageの未完部分を仮定しない）。

これは紙の接続案までであり、S1の完成には数えない。既検証の実測15,034行は変わらない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 鍵待ちの紙の照合：S8 の非単射の場合（11-16）

未実装の残りの接続。`CechCommaPrefix`・`CechCommaContraction` は既に
`{C : Type u} [Category.{v} C]` と二宇宙で定義され、与えた一本の根 `r : V ⟶ U` だけから
`cechCommaPrefix` と二つの自然変換を作る。一般の弱終対象性を仮定する前の部品である。
非単射の場合の各点の Čech の収縮を新しく作り直す前に、この指定収縮を再利用する。
`CechCommaSmallContraction` は `max u v w` へ持ち上げているので、
点の根の商で実際に必要な小さい comma の宇宙への接続は別途照合する。
小さい型であることを、まだ証明したとはしない。

既存 `bousfieldKanCoherentCocone_isColimit` は一般の小さい通常の Kan 値図式を扱う。
集合値の Čech 解消を使う際は、同じ元の増大余錐について余極限性を示す必要がある。
各点で根を選べることだけから、前層の自然な大域切断を仮定してはいけない。
また、生の集合の余極限を空間値の余極限と同一視しない。

元の `sections_localEquiv_iso` は係数 E の presentable 性を要求していない。
したがって、E 上の `weightedSections O hE` をそのまま使うために hE を足してはいけない。
必要なら、既存の `covariantRepresentableInfinity` が同じ指定極限錐を保つことを使って
空間値へ移し、指定辺の比較と宇宙移送を示してから反映する。
`SetWeight.sectionsEquivalenceNatural` と既検証の
`setWeightSectionsEquivalenceNatural_shapeIso` は、元の pinched Hom と切断制限の
同じ全族を比較するので、空間値の局所性から同じ層化単位の比較への接続でも再利用する。
指定した `weightedSections_discrete` の自然性を、存在だけの別の頂点同型で代用しない。

06:09 UTCに鍵保持者の親PID30580と直接の子PID31284（lake）の生存を確認。
このレーンの検証セッション18959も生存中で、同じ整理券一枚を保持して待機している。
検証済み実測は15,034行のまま。S8・S1の未完を完成とは数えない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### Čech comma の Hom 宇宙の移送（11-16、未検証）

`CechCommaLocalContraction` 56行を作業木に追加した。新しい収縮は作らず、
既存の `cechCommaPrefix`・`cechCommaToPrefix`・`cechCommaRootToPrefix` をそのまま包む。
Mathlibの `CostructuredArrow` は `Functor.fromPUnit.{0}` を使い、commaの対象宇宙は
二つの始域の対象宇宙と標的のHom宇宙のmaxで、標的の対象宇宙は含めない。
したがって、次の Hom 宇宙の表示を試す。Leanでの検証はまだなので完了とは数えない。

```lean
CechCommaLocal (d : CechNerveData U) (V : C) : Type v := AsSmall.{v} (CechComma d V)
cechCommaLocalPrefix d (r : V ⟶ U) : CechCommaLocal d V ⥤ CechCommaLocal d V
cechCommaLocalToPrefix d r : 𝟭 (CechCommaLocal d V) ⟶ cechCommaLocalPrefix d r
cechCommaLocalRootToPrefix d r :
  (Functor.const (CechCommaLocal d V)).obj (AsSmall.up.obj (cechCommaRoot d r)) ⟶
    cechCommaLocalPrefix d r
cechCommaLocal_isWeaklyContractible d r : IsWeaklyContractible (nerve (CechCommaLocal d V))
```

5本の未検証を含む次の対象一覧は `/tmp/is-w1/s8-local-sections-next/files.json` に準備したが、
実行していない。現在のセッション18959が終端を返してから、この束に切り替える。
現セッションの観測待ちが満了しただけでは、別の整理券を発行しない。
検証済み全体232本15,034行・1,301宣言は変わらない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 同じ余錐・単位を保つための続きの照合（11-16、紙）

非単射の場合の Čech 解消について、既存の native 余極限模型は
`bousfieldKanCoherentCocone`・`kanReflectedBousfieldKanColimitObject`。
後者の元の coend は、係数を変えず、重みを
`bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor` としたもの。
coend 全体を反転する式と混同しない。
集合値係数 P の場合は、この coend と `nerve P.Elements` の係数計算の比較を調べる。
次数ごとには under の射列と一点から、元の圏の射列と先頭の点へ戻す co-Yoneda の計算になる。
この比較はまだ作っていないので、余極限性が済んだとは数えない。

各点での surjection の根を一本選ぶのは、同じ元の増大余錐の点ごとの余極限性を
G14 の検出へ渡すためだけ。前層としての自然な切断や、点ごとの同型の大域への貼り合わせを
仮定しない。既存の Čech prefix の収縮への入力は、その固定した点での根である。

同じ層化単位の比較の順序も保持する：
(1) 元の `sectionsOf_map` で一般の局所全単射の切断の不変性を閉じる。
(2) 既存G8の `sectionsEquivalenceNatural` とその全族自然性で、
    離散重みから任意の空間値層への元の pinched Hom の局所性へ戻す。
(3) Mathlibの同じ `toSheafify J P` の局所全単射性と、検証済みの
    `isSheaf_discretePresheaf_iff` で、その単位の標的が空間値層であることを使う。
(4) 与えられた同じ hJ の反射・単位の普遍性に沿って全族の mate を取り、
    その可逆性を既存の全族の判定で示す。任意の点ごとの頂点同型から新たな全自然同型を作らない。
これにより、hJ に未証明の左完全性や0切り捨ての保存を追加仮定に置かず、
元の `sheafify_discrete_eq`・`localEquiv_of_sheafifyIso` へ接続する方針。
指定された `weightedSections_discrete_map` 自体の証明も省略しない。

上は再利用の照合であり、型の変更・独立の追加ID・検証済み行数の追加ではない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 整理券の待ち時間満了（11-16 15:25 JST）

セッション18959（`s8-right-kan-restrict-2`）が終了75を返した。
これは観測の待ち時間だけの満了ではなく、`with_build_lock --wait 3600` の終端。
対象ビルド・小監査は未開始で、検証の成功・失敗としては数えない。
`--status` で旧整理券が列から消えたことを確認した。
新たに準備済み6対象（うち検証済み1本、未検証5本）を
`/tmp/is-w1/s8-local-sections-next/` にまとめ、`--class impl --wait 3600` で一枚だけ待ち直す。
鍵保持者は引き続き調整役のrootビルド。他レーンの実行は中断せず、鍵の規則も変更しない。
検証済み実測15,034行・1,301宣言は変わらない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S1 の元の生成篩への添字比較（11-16、未検証の型）

`ExtensiveSieveIndex` 77行・`ExtensiveSieveCofinality` 109行を作業木に追加した。
既存の `WithTerminal.lift` と comma の終対象からの指定随伴を使う。
型の引数を省略していない主要部は次のとおり（`C : Type u`, `[SmallCategory C]`）：

```lean
cofanSieveIndex [HasInitial C] [Nonempty ι] (c : Cofan B) :
  WithTerminal (Discrete ι) ⥤ (sieveCategory (cofanGeneratedSieve c))ᵒᵖ
cofanFactorization_label_unique [FinitaryExtensive C] [Finite ι]
  (c : Cofan B) (hc : IsColimit c) {V : C} (hV : ¬ Nonempty (IsInitial V))
  {i j : ι} (f : V ⟶ B i) (g : V ⟶ B j)
  (h : f ≫ c.inj i = g ≫ c.inj j) : i = j
cofanSieveIndex_hasTerminalComma [FinitaryExtensive C] [Finite ι] [Nonempty ι]
  (c : Cofan B) (hc : IsColimit c)
  (s : (sieveCategory (cofanGeneratedSieve c))ᵒᵖ) :
  HasTerminal (CostructuredArrow (cofanSieveIndex c) s)
cofanSieveIndex_isLeftCofinal [FinitaryExtensive C] [Finite ι] [Nonempty ι]
  (c : Cofan B) (hc : IsColimit c) : IsLeftCofinal (nerveMap (cofanSieveIndex c))
```

任意の射が一本の脚を通るとは主張しない。分解を使うのは、生成篩の対象に限る。
その始域が初対象なら comma の終対象は star、そうでなければ有限余積の
非交叉性と各脚の単射性から一意な脚の三角形を終対象にする。
これは既に報告した S1 の有限被覆の比較の証明分割で、追加IDなし、200行超の補題なし。

残りは同じ錐の係数・添字移送、初対象の値が終対象であることを使う star の除去、
空族、有限余積被覆の引き戻しと extensive 位相への接続。
元の一般 `Coverage` の型も保持し、普遍降下を追加仮定に置いて済ませない。

現在の対象ビルドのセッション18673は整理券一枚で待機中。
上記2本は実行中の6対象から import されず、次の束の一覧にだけ準備した。
未検証の Lean はコミットしない。検証済み232本・15,034行・1,301宣言は変わらない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S1 の指定された star の除去（11-16、未検証）

前節の有限添字の係数計算を、新規3本176行で下書きした。
`ExtensiveTerminalComma` 31行、`ExtensiveLegRightCone` 65行、
`ExtensiveIndexRightKan` 80行。既存の完全忠実包含の恒等三角形、
`initialValueCone_isLimit`、`isLimitCone_iff_terminal_of_initialShape`、
`nerveRightConeTransportPostcomp` を使う。
主張は既存の指定局所錐と添字の法則で、新しいIDは足さない。

```lean
extensiveTerminalComma_isEmpty (I : Type u) [SmallCategory I] :
  IsEmpty (StructuredArrow (WithTerminal.star : WithTerminal I)
    (WithTerminal.incl : I ⥤ WithTerminal I))
extensiveLegComma_isInitial (I : Type u) [SmallCategory I] (i : I) :
  IsInitial (StructuredArrow.mk (T := (WithTerminal.incl : I ⥤ WithTerminal I))
    (𝟙 (WithTerminal.of i)))
extensiveLegRightCone_postcomp_isLimit {E : SSet.{u}} [Quasicategory E]
  (H : nerve (WithTerminal I) ⟶ E) (i : I) :
  IsLimitCone ((nerveCone (extensiveLegRightCone I i)).postcomp H)
extensiveIndex_isRightKanExtension {E : SSet.{u}} [Quasicategory E]
  (H : nerve (WithTerminal I) ⟶ E)
  (hH : IsTerminalVertex (H.app _ (nerveVertex (WithTerminal.star : WithTerminal I)))) :
  IsRightKanExtension (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I))
    (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ H) H
    (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm
      (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ H)))
extensiveIndex_restrict_isLimit_iff H hH (c : JoinCone H) :
  IsLimitCone c ↔ IsLimitCone
    (restrictJoinCone c (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I)))
```

`extensiveLegRightCone_val` は元の通常の右 Kan 局所錐の nerve の全射が、
同じ comma の初対象からの錐と等しいことを、両境界と各混合辺で比較する。
star の空形状でも元の頂点を保つ。右 Kan 条件や係数の極限保存性は仮定しない。
点ごとの同型を集める構成ではなく、指定された全錐の制限の法則を使う。
200行超の補題なし。Leanではまだ未検証なので、S1完了とは数えない。

現在のセッション18673の対象6本と依存は凍結したまま。
新規S1計5本362行は次の未実行一覧
`/tmp/is-w1/s8-all-local-sections-next-1/files.json` に追加した（全11対象）。
検証済み全体232本・15,034行・1,301宣言は変わらない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S1 の元の fan への双対・全錐の照合（11-16、未検証）

`ExtensiveCofanDuality` 56行と `ExtensiveSieveCone` 56行を追加した下書き。
既存の通常の積・余積の普遍射と nerve の錐の法則だけを使う。
S1 の証明の分割で、追加IDなし、200行超の補題なし。

```lean
cofanToOppositeFan {B : ι → C} (c : Cofan B) : Fan (fun i => Opposite.op (B i))
fanToUnopCofan {B : ι → Cᵒᵖ} (c : Fan B) : Cofan (fun i => (B i).unop)
cofanToOppositeFan_isLimit c (hc : IsColimit c) : IsLimit (cofanToOppositeFan c)
fanToUnopCofan_isColimit c (hc : IsLimit c) : IsColimit (fanToUnopCofan c)
cofanSieveIndexCone [HasInitial C] [Nonempty ι] (c : Cofan B) :=
  (sieveCone (cofanGeneratedSieve c)).whisker (cofanSieveIndex c)
cofanSieveIndex_legs [HasInitial C] [Nonempty ι] (c : Cofan B) :
  WithTerminal.incl ⋙ cofanSieveIndex c ⋙ sieveDiagram (cofanGeneratedSieve c) =
    Discrete.functor (fun i => Opposite.op (B i))
cofanSieveIndexCone_legs_val [HasInitial C] [Nonempty ι] (c : Cofan B) :
  (nerveCone ((cofanSieveIndexCone c).whisker WithTerminal.incl)).val =
    (nerveCone (cofanToOppositeFan c)).val
```

双対の2本は有限性も非空性も仮定しない。同じ脚を保ったまま、元の積錐を余積被覆へ
移すための法則。後半は元の篩錐を実際に whisker し、指定 fan の頂点と各脚を比較する。
実行中の6対象には触れず、次の未実行一覧を全13対象へ更新した。
新規S1は計7本474行が未検証。検証済み15,034行は変わらない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S1 の引き戻しの宇宙の照合（11-16、紙）

`FinitaryPreExtensive.isIso_sigmaDesc_fst` の添字は `{α : Type}`（Type 0）である。
元の `PreservesFiniteProductsOnSite` の `ι : Type u` に、そのまま一般版として適用しない。
同じ Mathlib の `FinitaryPreExtensive.isUniversal_finiteCoproducts hc` と
`IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left` は一般の有限添字を扱う。
必要な引き戻しは `hasPullbacks_of_is_coproduct hc (Discrete.mk i) f` から得る。
生成篩の引き戻しとの同じ等式は
`Sieve.ofArrows_eq_pullback_of_isPullback` を使い、作り直さない。

もう一つの許される移送は、有限添字を有限の Type 0 の模型に移し、同じ全 fan を
添字同値で運ぶこと。`extensiveCoverage` の定義と
`extensiveTopology.mem_sieves_iff_contains_colimit_cofan` 自体も Type 0 の有限族で書かれる。
どちらの場合も元の任意の有限 `Type u` の量化と、空族を含む指定錐を保持する。
この照合で元の型を狭めたり、引き戻しの降下を追加仮定にしたりしない。
未検証の Lean の数、検証済み15,034行はいずれも変わらない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S1 の空族の同じ頂点の比較（11-16、未検証）

`ExtensiveEmptySieve` 55行を追加した下書き。元の空族の枝を省略しない。
既存の空形状の判定を同じ指定制限錐へ適用する証明分割で、追加IDなし。

```lean
bottomSieveShape_isInitial (U : C) :
  IsInitial (presheafShape (sieveCategory (⊥ : Sieve U)))
restrictionCone_bot_isLimit_iff (F : Presheaf C E) (U : C) :
  IsLimitCone (restrictionCone F (⊥ : Sieve U)) ↔
    IsTerminalVertex (F.app _ (ULift.up (nerveVertex (Opposite.op U))))
cofanGeneratedSieve_eq_bot {ι : Type u} [IsEmpty ι] {B : ι → C} (c : Cofan B) :
  cofanGeneratedSieve c = ⊥
```

底篩の元の圏に対象がないことから、同じ持ち上げた形状の初期対象性を得る。
`restrictionCone_vertex` と `isLimitCone_iff_terminal_of_initialShape` を合成し、
頂点を新しい終対象に取り替えない。非空族の star の membership は使わない。

新規S1の未検証は8本・物理530行（前の双対ファイルの文献番号を方針へ移す1行増を含む）。
次の未実行一覧は全14対象。現セッション18673は整理券一枚で生存中。
検証済み232本15,034行・1,301宣言は変わらない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 対象ビルド再開と S1 の恒等余単位の簡約の分割（11-16 夕）

調整役の16:25の伝達に従い、停止点までは main を取り込まない。
Citation の略号表の変更による再コンパイルを、この作業木へ導入していない。
旧セッション18673は終了1で終端を確認した。前の6対象のビルドが実行され、
`MonoLocalRightKanRestriction`・`MonoLocalSections`・`CechCommaLocalContraction` が通った。
その後の束で `SetSectionsRestriction`・`LocalInjectiveDiagonal` も通った。
小監査がまだなので、検証済み行数とコミット済み本数には加算しない。

S1は `ExtensiveSieveIndex`・`ExtensiveSieveCofinality`・`ExtensiveTerminalComma`・
`ExtensiveCofanDuality`・`ExtensiveLegRightCone`・`ExtensiveEmptySieve` が対象ビルドを通った。
`ExtensiveSieveCone` の Functor の外延性は、型クラス Functor との名前の混同と
外延性の引数の順序を直した。`ExtensiveIndexRightKan` は、実際の指定輸送の
`nerveMap (𝟭 _) ≫ H` を H と直接定義上比較するところで whnf が時間切れになった。
上限を上げず、113行の同じ新規ファイルの中で次に分割した（未検証）：

```lean
extensiveIndexRightKanCounit I H :
  SSet.Homotopy
    (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ nerveMap (𝟭 (WithTerminal I)) ≫ H)
    (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ H)
extensiveIndexRightKanCounit_h I H :
  (extensiveIndexRightKanCounit I H).h =
    fst _ _ ≫ (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ H)
extensiveIndexRightKan_data I H hH :
  IsRightKanExtension (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I))
    (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ H)
    (nerveMap (𝟭 (WithTerminal I)) ≫ H) (extensiveIndexRightKanCounit I H)
-- 以下は同じファイルの private な移送の法則。
rightKan_refl_of_counit {δ : A ⟶ B} {p q : B ⟶ X} (hp : p = q)
  (α : SSet.Homotopy (δ ≫ p) (δ ≫ q)) (hα : α.h = fst _ _ ≫ (δ ≫ q))
  (hk : IsRightKanExtension δ (δ ≫ q) p α) :
  IsRightKanExtension δ (δ ≫ q) q
    (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (δ ≫ q)))
```

最後の元の型への接続は `nerveFunctor.map_id (Cat.of (WithTerminal I))` から得た
命題的な等式を使う。新しいIDは足さず、既存の構成の法則・証明の分割として扱う。
200行超の補題なし。元の右 Kan 条件を仮定にせず、局所輸送から証明する。

現在の再検証は `/tmp/is-w1/s8-all-local-sections-next-6/`、セッション25070。
同じ14対象でビルド後に新しい環境からの所有宣言の小監査・SHA確認を行う束。
待ちは一枚。実行中の対象と依存は変更しない。未検証の Lean は作業木に残す。
検証済み232本・15,034行・1,301宣言は変わらない。S1・S8は未完。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 13本の対象ビルド・小監査の完了（11-16 夕、途中の検証済み点）

数学のコミット：`9e7b918c2`。新規13本937行・93宣言。
既検証の `RightKanLimitRestriction` 1本を含めた14対象のビルドが成功し、
新しい環境から採取した所有94宣言の小監査（標準三公理のみ）と、
全14ソースのSHA一致が通った。セッション25070の終了0も確認した。
証拠：`/tmp/is-w1/s8-all-local-sections-next-6/target-audit-result.json`、
同じディレクトリの `catalog-after.json`・`audit-after.log`・`build.log`。

S8側：5本372行。局所全射な単射に対する**元の** `sectionsOf_map` の可逆性、
同じ制限の全関手の自然性・合成則、局所単射の核対の対角射の局所全射性、
元のČech prefixの収縮のHom宇宙への移送。任意の存在だけの同型に置き換えていない。
S1側：8本565行。脚と初対象の添字の共終性、同じ局所右Kan錐の輸送、
終点の値が終対象であるときの指定全錐の制限の極限性、元のfanへの全錐の比較、
空族の底篩の指定制限錐と元の頂点の終対象性の同値。

whnfの時間切れは、実際の輸送で得た右Kan条件と、恒等関手の命題的な等式による
移送を分けることで通った。maxHeartbeats・maxRecDepthは上げていない。
新しいIDなし。既存の構成の法則・証明分割のみ、200行超の補題なし。
新規ファイルは物理行で保守的に計数し、検証済み全体245本・15,971行・1,394宣言。
既存112本の文献属性・docstringだけの整理は引き続き外枠に数えない。

これは完成停止点ではない。S1は係数の宇宙移送を含む有限積判定の組み立て、
有限余積被覆の引き戻しと元のextensive位相、元の一般coverageの型への接続が残る。
S8は一般の局所全単射の不変性、同じ層化単位の比較、指定した
`weightedSections_discrete` の射の自然性、元の層化による局所同値の判定が残る。
既存の大域の右Kan比較の再利用を保ち、点ごとの同型を新しく集めない。
S7・R2・R3は再開せず、mainも停止点までは取り込まない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S1 の終点付き添字の宇宙移送（11-16 夕、検証中の型）

既存の構成の法則として、新規2本に分けた。追加IDなし、200行超の補題なし。
`Project/LocalizationAndKanExtensionAuxiliaries/NerveComparison/AsSmallWithTerminal` は
既存 `WithTerminal.map` を `AsSmall.up`・`down` へ適用し、その順序交換を全単体で示す。
`Sheaves/ExtensiveIndexUniverseRestriction` は同じ指定錐をこの添字同型で運び、
検証済み `extensiveIndex_restrict_isLimit_iff` へ渡す。

```lean
nerveWithTerminalAsSmallIso (I : Type u) [SmallCategory I] :
  (SSet.uliftFunctor.{u + 1, u}).obj (nerve (WithTerminal I)) ≅
    nerve (WithTerminal (AsSmall.{u + 1} I))
nerveWithTerminalAsSmallIso_incl I :
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I)) ≫
    (nerveWithTerminalAsSmallIso I).hom =
      (nerveAsSmallIso I).hom ≫
        nerveMap (WithTerminal.incl : AsSmall.{u + 1} I ⥤ WithTerminal (AsSmall.{u + 1} I))
extensiveIndex_ulift_restrict_isLimit_iff (I : Type u) [SmallCategory I]
  {E : SSet.{u + 1}} [Quasicategory E]
  (H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (WithTerminal I)) ⟶ E)
  (hH : IsTerminalVertex
    (H.app _ (ULift.up (nerveVertex (WithTerminal.star : WithTerminal I)))))
  (c : JoinCone H) :
  IsLimitCone c ↔ IsLimitCone (restrictJoinCone c
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I))))
```

両逆の前提計算は `WithTerminal.map up ⋙ WithTerminal.map down = 𝟭 _` と
逆順の等式の2本。頂点の標準終点も同じ頂点へ戻す法則を明示した。
比較するのは全錐の射であり、同じ指定右Kan条件の後に、制限錐の全射の等式で戻す。
点ごとの同型から新たな自然同型を作らず、係数 E の極限保存性も仮定しない。

現在の対象は `/tmp/is-w1/s1-extensive-universe-1/`、セッション57886、2本。
結果と小監査の終端を確認するまで、検証済み245本15,971行・1,394宣言には加算しない。
mainは取り込まない。S1・S8の元の残りの型を保って継続する。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S1 の元の有限被覆比較と有限積保存への方向（11-16 夕、検証中）

新規 `ExtensiveCofanRestriction`・`ExtensiveCofanCover`・`ExtensiveFiniteProducts`。
既存の承認された S1 の証明分割と、通常の再添字・双対・係数移送の法則のみ。
追加IDなし、200行超の補題なし。主な型：

```lean
cofanRestriction_isLimit_iff [FinitaryExtensive C] [Finite ι] [Nonempty ι]
  (F : Presheaf C E)
  (h0 : IsTerminalVertex (F.app _ (ULift.up (nerveVertex (Opposite.op (⊥_ C))))))
  (c : Cofan B) (hc : IsColimit c) :
  IsLimitCone (restrictionCone F (cofanGeneratedSieve c)) ↔
    IsLimitCone (((nerveCone (cofanToOppositeFan c)).ulift).postcomp F)
cofanGeneratedSieve_mem_extensiveTopology [FinitaryExtensive C] [Finite ι]
  (c : Cofan B) (hc : IsColimit c) :
  cofanGeneratedSieve c ∈ (extensiveTopology C) c.pt
isTerminal_initial_of_isSheaf_extensive [FinitaryExtensive C]
  (F : Presheaf C E) (hF : IsSheaf (extensiveTopology C) F) :
  IsTerminalVertex (F.app _ (ULift.up (nerveVertex (Opposite.op (⊥_ C)))))
PreservesFiniteProductsOnSite (F : Presheaf C E) : Prop :=
  ∀ (ι : Type u) [Finite ι] (B : ι → Cᵒᵖ) (c : Fan B), Nonempty (IsLimit c) →
    IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} (nerveCone c)))
IsSheaf.preservesFiniteProductsOnSite [FinitaryExtensive C]
  (F : Presheaf C E) (hF : IsSheaf (extensiveTopology C) F) :
  PreservesFiniteProductsOnSite F
```

定義は元 drafts と同じ型。任意の有限 Type u の量化と、空族の元の指定 fan を保つ。
通常の被覆性には `Cofan.isColimitEquivOfEquiv` と `Fintype.equivFin` を使う。
元の位相の被覆判定が Type 0 の有限表示であることを、量化を狭めずに処理する。
空の cofan は同じ初対象の普遍射で作り、底篩の指定錐の終対象判定へ渡す。

元の fan の双対の往復の全射を `nerve_joinPoint_hom_ext` で比較し、
その同じ等式を宇宙移送・係数の後合成へ渡す。
非空族では共終性と指定右Kanによる制限を合成する。
空族では同じ F(c.pt) を頂点とする空形状の錐の判定を使い、別の終対象へ置換しない。

`ExtensiveCofanCover` と先の2本の宇宙比較は対象ビルドを通ったが、小監査はまだ。
現在 `/tmp/is-w1/s1-extensive-products-1/` の5対象、セッション43099で検証中。
未検証のため検証済み245本15,971行・1,394宣言へ加算しない。
逆向きは元の有限余積被覆の引き戻しと descentTopology への接続が残る。
一般coverageとS8の元の残りも保持する。mainは停止点まで取り込まない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 有限被覆比較と有限積保存への方向の検証完了（11-16 夕）

数学：`5d0c7990c`。新規5本416行・27宣言。
`/tmp/is-w1/s1-extensive-products-2/target-audit-result.json` で5対象のビルド成功、
新しい環境の所有27宣言が標準三公理のみ、全ソースのSHA一致を確認。
セッション72071の終了0も確認した。検証済み全体250本16,387行・1,421宣言。
元の `PreservesFiniteProductsOnSite` の型と、空族を含む元の fan での
`IsSheaf.preservesFiniteProductsOnSite` まで通った。S1全体の完成とは数えない。

逆向きに、新規 `ExtensiveCofanPullback` に既存の底変換の法則を下書きした：
```lean
cofanPullbackHasPullback [FinitaryPreExtensive C] [Finite ι]
  (c : Cofan B) (hc : IsColimit c) {V : C} (f : V ⟶ c.pt) (i : ι) :
  HasPullback f (c.inj i)
cofanPullback (c : Cofan B) {V : C} (f : V ⟶ c.pt)
  [∀ i, HasPullback f (c.inj i)] : Cofan (fun i => pullback f (c.inj i))
cofanPullback_isColimit [FinitaryPreExtensive C] [Finite ι]
  (c : Cofan B) (hc : IsColimit c) {V : C} (f : V ⟶ c.pt)
  [∀ i, HasPullback f (c.inj i)] : IsColimit (cofanPullback c f)
cofanPullback_generatedSieve (c : Cofan B) {V : C} (f : V ⟶ c.pt)
  [∀ i, HasPullback f (c.inj i)] :
  cofanGeneratedSieve (cofanPullback c f) = (cofanGeneratedSieve c).pullback f
```

普遍性は `FinitaryPreExtensive.isUniversal_finiteCoproducts hc` と
`nonempty_isColimit_of_pullbackCone_left`、生成篩の等式は
`Sieve.ofArrows_eq_pullback_of_isPullback` を再利用する。
追加IDなし、200行超の補題なし。元の一般coverageの未完の型を仮定に置かない。
この1本を次に対象ビルド・小監査する。停止中のR2下書き・S7・R3は触らない。
mainは停止点まで取り込まない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S1 の有限積判定の逆向きの型（11-16 夕、検証中）

`ExtensiveCofanPullback` は1本の対象ビルド・小監査（所有10宣言、標準三公理のみ、
SHA一致）とセッション60481の終了0を確認した。逆向きの組み立てとまとめてコミットする。
証拠は `/tmp/is-w1/s1-extensive-pullback-1/target-audit-result.json`。

新規 `ExtensiveProductDescent` は、同じ元の有限積判定の逆向きの証明分割：
```lean
PreservesFiniteProductsOnSite.initial_isTerminal (F : Presheaf C E)
  (hF : PreservesFiniteProductsOnSite F) :
  IsTerminalVertex (F.app _ (ULift.up (nerveVertex (Opposite.op (⊥_ C)))))
PreservesFiniteProductsOnSite.cofanRestriction_isLimit (F : Presheaf C E)
  (hF : PreservesFiniteProductsOnSite F) {ι : Type u} [Finite ι]
  {B : ι → C} (c : Cofan B) (hc : IsColimit c) :
  IsLimitCone (restrictionCone F (cofanGeneratedSieve c))
PreservesFiniteProductsOnSite.universallyDescending_cofan (F : Presheaf C E)
  (hF : PreservesFiniteProductsOnSite F) {ι : Type u} [Finite ι]
  {B : ι → C} (c : Cofan B) (hc : IsColimit c) :
  UniversallyDescendingSieve F (cofanGeneratedSieve c)
isSheaf_extensive_of_preservesFiniteProducts (F : Presheaf C E)
  (hF : PreservesFiniteProductsOnSite F) : IsSheaf (extensiveTopology C) F
isSheaf_extensive_iff_preservesFiniteProducts (F : Presheaf C E) :
  IsSheaf (extensiveTopology C) F ↔ PreservesFiniteProductsOnSite F
```
ここでは `[FinitaryExtensive C]`、`E : SSet.{u+1}`、`[Quasicategory E]`。
追加IDなし、200行超の補題なし。最後の型は元draftsの型のまま。
最後の主な宣言に `@[cite HTT "6.2.2.6" (partial := special) "理由"]` を付けた。
小さい通常の finitary extensive site の Čech 層と、空族を含む指定有限積への特殊化を明示する。

各 cofan の全引き戻しの同じ篩錐の極限性から降下位相の所属を得る。
任意の extensive 被覆篩は Type 0 の有限余積 cofan を含むという Mathlib の判定を使い、
その cofan を ULift の添字同値で Type u へ移す。生成篩の包含と降下位相の上方閉性で戻す。
一般coverageの未検証の判定を使わず、普遍降下を入力へ追加して済ませることもしない。

現在はこの2本の対象ビルド・小監査を `/tmp/is-w1/s1-extensive-descent-1/`、
セッション61077で待機中。対象と依存を固定し、mainを取り込まない。
検証済みコミットの実測250本16,387行・1,421宣言は、まだ増やしていない。
S1の一般coverageとS8の元の一般の局所同値・指定比較は残る。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S1-E の元の両方向の検証完了、S8 の反転重みへの接続（11-16 夕）

数学：`065539cb0`、新規2本169行・17宣言。
`/tmp/is-w1/s1-extensive-descent-1/target-audit-result.json` で、2対象のビルド、
新しい環境の所有17宣言の小監査（標準三公理のみ）、全ソースのSHA一致を確認した。
セッション61077の終了0も確認した。検証済み全体252本16,556行・1,438宣言。
`isSheaf_extensive_iff_preservesFiniteProducts` は元の型で両方向が完了し、文献属性も通った。
S1は元の一般 `Coverage` の判定が残るので、一覧全体の完了数は増やさない。

S8 の非単射の場合のČech解消をつなぐための追加の照合：
既存の `SetWeightedTensors.elementsToReplacement P` は、
`nerve P.Elements` と `simplicialReplacement (coefficients P)` の同型であり、
`elementsToReplacement_naturality` もある。同じ元の圏の比較を新しく作り直さない。
native BK余極限は **反転した重み** のcoendを使うので、未反転の模型と混同しない。
まず新規 `Project/HomotopyDiagramComparison/KanExtensions/ReflectedBousfieldKanUnderWeight` に
既存のOver・Under反転と `nerveUnopIso` の係数移送の法則を書いた：

```lean
overUnderOppositeCatIso (I : Type u) [SmallCategory I] (i : I) :
  Cat.of (Over (Opposite.op i)) ≅ Cat.of ((Under i)ᵒᵖ)
reflectedBousfieldKanUnderIso (I : Type u) [SmallCategory I] (i : I) :
  ((bousfieldKanWeight Iᵒᵖ).obj (Opposite.op i)).op ≅ nerve (Under i)
reflectedBousfieldKanUnderWeightIso (I : Type u) [SmallCategory I] :
  bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor ≅ Under.mapFunctor I ⋙ nerveFunctor
```

Overの後合成とUnderの前合成の同じ四角形の法則も明示する。
Mathlib の `Over.opEquivOpUnder` の単位・余単位が `Iso.refl` であることを使い、
その既存の通常圏の同型をnerveと反転に移す。任意の点ごとの頂点同型を集めない。
追加IDなし。既存模型の係数移送の法則、200行超の補題なし。
この1本を `/tmp/is-w1/s8-reflected-under-weight-1/` で対象ビルド・小監査する。
S8の元の一般の局所同値、指定離散比較の射の自然性、同じ層化単位の比較はまだ残る。
mainは停止点まで取り込まない。S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S8 の coend 比較に使う既存の全射列の法則（11-16 夕）

`SimplicialReplacementUnderEvaluation` に、必要な普遍評価と自然性だけでなく、
`scaffoldUnderChain`、`simplicialReplacementUnderEvaluation_scaffold`、
`scaffoldUnderChain_forget_factorization`、`scaffoldUnderChain_restriction` が既にある。
同じ射列の根への正規化を新しく作り直さない。

新規 `UnderWeightedColimitComparison` に、次の既存構成の比較の法則を書いた（未検証）：
```lean
underNerveWeight (I : Type u) [SmallCategory I] := Under.mapFunctor I ⋙ nerveFunctor
underWeightedColimitLeg (F : I ⥤ SSet.{u}) (i : I) :
  F.obj i ⊗ nerve (Under i) ⟶ simplicialReplacement F
underWeightedColimitLeg_condition (F : I ⥤ SSet.{u}) {i j : I} (f : i ⟶ j) :
  F.obj i ◁ (underNerveWeight I).map f.op ≫ underWeightedColimitLeg F i =
    F.map f ▷ nerve (Under j) ≫ underWeightedColimitLeg F j
underWeightedColimitToReplacement (F : I ⥤ SSet.{u}) :
  weightedColimit (underNerveWeight I) F ⟶ simplicialReplacement F
underWeightedColimitToReplacement_ι (F : I ⥤ SSet.{u}) (i : I) :
  weightedColimitι (underNerveWeight I) F i ≫ underWeightedColimitToReplacement F =
    underWeightedColimitLeg F i
```
各脚の底への射影は、元の Under の射列の忘却であることも保持する。
評価は既存 `simplicialReplacementUnderEvaluation` に因子の順序交換を合成しただけ。
coendのdinaturalityは既存 `simplicialReplacementUnderEvaluation_naturality` をそのまま使う。
追加IDなし、既存の模型の係数移送の法則、200行超の補題なし。

逆向きの接続に残る計算も、同じ既存射列を使う：replacementの単体 (σ,x) を、
最初の頂点 σ(0) の普遍脚に `(yonedaEquiv x, scaffoldUnderChain σ)` として送る。
任意の Under の射列 τ は最初の構造射でこの標準射列を前合成したもの、という既存の
`scaffoldUnderChain_forget_factorization` と coend のdinaturalityで正規化する。
単体作用素で最初の頂点が変わることは `scaffoldUnderChain_restriction` で扱う。
この計算を終えてから既存 `elementsToReplacement` の同型へつなぐ。
未証明の正規化・余極限性を仮定には置かない。

現在は反転重みの自然性の参照を明示して、上記との2対象を
`/tmp/is-w1/s8-under-comparison-1/`、セッション58077で検証中。
元のS8の一般の局所同値や指定離散比較の射の自然性が完成したとはしない。
検証済み252本16,556行・1,438宣言、main未取り込み、S7・R2・R3停止を保持する。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S8 の同じ coend 比較の正規化が通った（11-16 夕）

`97888df36`：反転重みの自然同型と元の Under 評価からの coend 比較の2本137行・15宣言。
`75ee8f812`：同じ比較射の正規化の1本98行・7宣言。
証拠は `/tmp/is-w1/s8-under-comparison-1/target-audit-result.json` と
`/tmp/is-w1/s8-under-normalization-1/target-audit-result.json`。
各対象ビルド、新しい環境の所有宣言の小監査（標準三公理のみ）、SHA一致と
セッション58077・50921の終了0を確認した。検証済み全体255本16,791行・1,460宣言。

正規化の型は次のとおり（既存の構成の法則、追加IDなし）：
```lean
underWeightedColimit_normalize (F : I ⥤ SSet.{u}) {i : I} {n : ℕ}
  (τ : ComposableArrows (Under i) n) (x : (F.obj i) _⦋n⦌) :
  (weightedColimitι (underNerveWeight I) F (τ.obj 0).right).app (op ⦋n⦌)
    ((F.map (τ.obj 0).hom).app (op ⦋n⦌) x,
      scaffoldUnderChain (τ ⋙ Under.forget i)) =
    (weightedColimitι (underNerveWeight I) F i).app (op ⦋n⦌) (x, τ)
replacementUnderWeightedPoint F n :
  simplicialReplacementSimplex F n → (weightedColimit (underNerveWeight I) F) _⦋n⦌
replacementUnderWeightedPoint_rightInverse F n :
  Function.RightInverse (replacementUnderWeightedPoint F n)
    ((underWeightedColimitToReplacement F).app (op ⦋n⦌))
replacementUnderWeightedPoint_leftInverse F n :
  Function.LeftInverse (replacementUnderWeightedPoint F n)
    ((underWeightedColimitToReplacement F).app (op ⦋n⦌))
underWeightedColimitToReplacement_isIso F : IsIso (underWeightedColimitToReplacement F)
underWeightedColimitReplacementIso F :
  weightedColimit (underNerveWeight I) F ≅ simplicialReplacement F
```

大域の射は、先に coend の普遍性と既存の全自然性から作った
`underWeightedColimitToReplacement F` のまま。点の公式はその射の全単射性の検証だけに使う。
無指定な成分同型を集めて大域の射を作らず、元の射に既存の同型性の判定を適用して
`asIso` を取る。指定右Kan比較についての禁止も変更していない。
200行超の補題なし。計算上限の変更なし。

次の接続は既存 `coendFunctor` の同型の像で行う。新規2本を下書きした：
```lean
weightedColimitWeightFunctor (F : I ⥤ SSet.{u}) : (Iᵒᵖ ⥤ SSet.{u}) ⥤ SSet.{u}
weightedColimitWeightIso (e : W ≅ V) (F : I ⥤ SSet.{u}) :
  weightedColimit W F ≅ weightedColimit V F
weightedColimitWeightIso_ι_hom e F i :
  weightedColimitι W F i ≫ (weightedColimitWeightIso e F).hom =
    F.obj i ◁ e.hom.app (op i) ≫ weightedColimitι V F i
reflectedBousfieldKanReplacementIso F :
  reflectedBousfieldKanColimit F ≅ simplicialReplacement F
reflectedBousfieldKanElementsIso (P : I ⥤ Type u) :
  reflectedBousfieldKanColimit (coefficients P) ≅ nerve P.Elements
```

最後は検証済みの重みの同型・比較射と、既存の同じ `elementsToReplacement` の同型の合成。
反転していないcoendや生の集合の余極限との同一視はしていない。
現在 `/tmp/is-w1/s8-reflected-elements-1/`、セッション43321で2対象を検証中。
S8 の元の一般の局所同値と指定自然性・層化の同じ単位への接続はまだ残る。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S8 の反転 BK と元の圏の比較を保存（11-16 夕）

`a051e090a`：2本76行・6宣言。対象ビルド、小監査（新しい環境、標準三公理のみ）、
SHA一致とセッション43321の終了0を確認した。
証拠 `/tmp/is-w1/s8-reflected-elements-1/target-audit-result.json`。
検証済み全体257本16,867行・1,466宣言。元の coend から先に作った同じ大域比較の同型性を使う。
11-16 16:25の指示どおり、main cd79e9cc5 は取り込んでいない。

次の既存構成の自然性・評価の法則を下書きし、順に検証中（追加IDなし、200行超なし）：
```lean
underWeightedColimitLeg_naturality (η : F ⟶ G) (i : I) :
  η.app i ▷ nerve (Under i) ≫ underWeightedColimitLeg G i =
    underWeightedColimitLeg F i ≫ simplicialReplacementMap η
underWeightedColimitToReplacement_naturality (η : F ⟶ G) :
  weightedColimitMap (underNerveWeight I) η ≫ underWeightedColimitToReplacement G =
    underWeightedColimitToReplacement F ≫ simplicialReplacementMap η
weightedColimitWeightIso_naturality (e : W ≅ V) (η : F ⟶ G) :
  weightedColimitMap W η ≫ (weightedColimitWeightIso e G).hom =
    (weightedColimitWeightIso e F).hom ≫ weightedColimitMap V η
reflectedBousfieldKanReplacementIso_naturality (η : F ⟶ G) :
  weightedColimitMap (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) η ≫
    (reflectedBousfieldKanReplacementIso G).hom =
    (reflectedBousfieldKanReplacementIso F).hom ≫ simplicialReplacementMap η
reflectedBousfieldKanElementsIso_comp_elements (P : I ⥤ Type u) :
  (reflectedBousfieldKanElementsIso P).hom ≫ elementsToReplacement P =
    (reflectedBousfieldKanReplacementIso (coefficients P)).hom
reflectedBousfieldKanElementsIso_naturality (φ : P ⟶ Q) :
  weightedColimitMap (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) (SetWeight.coefficientsMap φ) ≫
    (reflectedBousfieldKanElementsIso Q).hom =
    (reflectedBousfieldKanElementsIso P).hom ≫ nerveMap φ.mapElements
weightedColimitWeightIso_augmentation (e : W ≅ V) (c : Cocone F) :
  (weightedColimitWeightIso e F).hom ≫ weightedColimitAugmentation V c =
    weightedColimitAugmentation W c
replacementCoconeAugmentation (c : Cocone F) : simplicialReplacement F ⟶ c.pt
underWeightedColimitLeg_augmentation (c : Cocone F) (i : I) :
  underWeightedColimitLeg F i ≫ replacementCoconeAugmentation c =
    fst (F.obj i) (nerve (Under i)) ≫ c.ι.app i
underWeightedColimitToReplacement_augmentation (c : Cocone F) :
  underWeightedColimitToReplacement F ≫ replacementCoconeAugmentation c =
    weightedColimitAugmentation (underNerveWeight I) c
reflectedBousfieldKanReplacementIso_augmentation (c : Cocone F) :
  (reflectedBousfieldKanReplacementIso F).hom ≫ replacementCoconeAugmentation c =
    weightedColimitAugmentation (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) c
setCoconeCoefficients (c : Cocone P) : Cocone (coefficients P)
elementsCoconeFunctor (c : Cocone P) : P.Elements ⥤ Discrete c.pt
elementsCoconeAugmentation (c : Cocone P) :
  nerve P.Elements ⟶ (setCoconeCoefficients c).pt
elementsToReplacement_augmentation (c : Cocone P) :
  elementsToReplacement P ≫ replacementCoconeAugmentation (setCoconeCoefficients c) =
    elementsCoconeAugmentation c
reflectedBousfieldKanElementsIso_augmentation (c : Cocone P) :
  (reflectedBousfieldKanElementsIso P).hom ≫ elementsCoconeAugmentation c =
    weightedColimitAugmentation (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor)
      (setCoconeCoefficients c)
```

`elementsCoconeFunctor c` は (i,x) を c.ι_i(x) へ送る元の関手。
replacement の評価は (σ,x) を yonedaEquiv(x ≫ c.ι_(σ0)) へ送るだけ。
元の Čech 増大を別の頂点や別の射へ取り替えていない。
セッション34045・74044・92350は対象ビルドの書き換えの失敗で終了1。
現在セッション83986、`/tmp/is-w1/s8-elements-naturality-4/` の9対象で検証中。
計算上限を変更していない。未検証分はコミットしない。
一般の局所同値、同じ離散比較の射の自然性、同じ層化単位への接続は引き続き未完。
S1の一般Coverageの判定も未完。S7・R2・R3は停止を保持する。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 同じ増大の照合の検証完了（11-16 夕）

`39b6088a2`：7本340行・23宣言。9対象（既存2本を含む）の対象ビルドと
新しい環境の29宣言の小監査、SHA一致、セッション83986の終了0を確認。
証拠 `/tmp/is-w1/s8-elements-naturality-4/target-audit-result.json`。
上の自然性・元の増大の型はすべてこの束で検証済み。
検証済み全体264本17,207行・1,489宣言。main未取り込みを保持する。
S8全体や一般Coverageの完成を意味しない。

次の同じ表示の法則を `CechPointElements` に書いた（未検証、追加IDなし）：
```lean
cechPointDiagram (d : CategoryTheory.CechNerveData U) (V : C) :
  AsSmall.{v} SimplexCategoryᵒᵖ ⥤ Type v
cechPointElementsToComma d V :
  (cechPointDiagram d V).Elementsᵒᵖ ⥤ CechCommaLocal d V
cechPointElementsFromComma d V :
  CechCommaLocal d V ⥤ (cechPointDiagram d V).Elementsᵒᵖ
cechPointElementsCommaEquivalence d V :
  (cechPointDiagram d V).Elementsᵒᵖ ≌ CechCommaLocal d V
cechPointElements_isWeaklyContractible (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
  IsWeaklyContractible (nerve (cechPointDiagram d V).Elements)
```
同じ Hom 値を同じ次数と射として取り出す順逆だけ。大きい C の Hom 宇宙 v で計算し、
既存 `cechCommaLocal_isWeaklyContractible` の収縮を再利用する。200行超なし。
根一本は各評価で使い、関手に自然な根の選択を要求しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 同じ Čech 収縮から native 余錐判定への接続（11-16 夕、検証中）

`CechPointElements` 単独は対象ビルド、小監査17宣言（標準三公理のみ）、SHA一致、
セッション85424の終了0を確認。証拠 `/tmp/is-w1/s8-cech-point-elements-2/target-audit-result.json`。
この次の束にまとめるため、この時点では未コミット。

既存構成の法則の型（追加IDなし、200行超の補題なし）：
```lean
cechPoint_reflectedBousfieldKan_isWeaklyContractible
  (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
  IsWeaklyContractible (reflectedBousfieldKanColimit (coefficients (cechPointDiagram d V)))
cechPoint_kanReflectedBousfieldKan_isWeaklyContractible
  (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
  IsWeaklyContractible
    (kanReflectedBousfieldKanColimitObject (cechPointDiagram d V ⋙ setsToKan)).obj
strictSetCocone_isColimit_of_elementsAugmentation_weak (c : Cocone P)
  (hc : IsWeakHomotopyEquivalence (elementsCoconeAugmentation c)) :
  IsColimitCone (strictNativeCocone (setsToKan.mapCocone c))
strictSetCocone_isColimit_of_contractible_comma (c : Cocone P)
  (hc : ∀ q : Discrete c.pt,
    IsWeaklyContractible (nerve (CostructuredArrow (elementsCoconeFunctor c) q))) :
  IsColimitCone (strictNativeCocone (setsToKan.mapCocone c))
CategoryTheory.CechNerveData.ofFiniteProducts (U : C) [HasFiniteProducts C] : CechNerveData U
```

ここで native の判定は、既存の
`strictNativeCocone_isColimit_of_reflectedAugmentation_weak` と
`nerveMap_isLeftCofinal_of_weaklyContractible_comma` を合成するだけ。
同じ全余錐の普遍性を使い、頂点の同値や余極限の存在だけで済ませない。
`ofFiniteProducts` は Mathlib `cechNerveTerminalFrom` の同じ有限冪・射影・単体作用素を
既存 `CechNerveData` に包むだけ。新しい Čech 構成を重ねて作らない。

セッション76859は coend に準圏性の instance がないこと、94464は積の計算則名と
定値単体集合の準圏性の推論の失敗により終了1。準圏性を追加仮定にせず、既存
`isPrecompositionEquivalence_of_iso` の弱ホモトピー同値性で修正した。
現在セッション79847、`/tmp/is-w1/s8-cech-point-native-2/` の4対象を検証中。
計算上限を変更せず、mainも取り込んでいない。

次は P→Q の同じ相対Čech図式を Over Q の有限冪で読み、各評価 q の上の comma を
同じ Hom 値図式の要素圏へ移す。局所的な根ではなく、各点の像への全射の根で
収縮を使う。P→Q の像の包含は既証の局所単射の判定へつなぐ。
この全余錐の各点での照合が終わるまでは、一般の `sections_localEquiv_iso` を完了扱いしない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### Čech の収縮と native 判定への接続の検証完了（11-16 夕）

`ab9a40aec`：4本189行・24宣言。対象ビルド、新しい環境の所有宣言の小監査
（標準三公理のみ）、SHA一致、セッション79847の終了0を確認。
証拠 `/tmp/is-w1/s8-cech-point-native-2/target-audit-result.json`。
直前の型つき一覧はすべてこの束で検証済み。
検証済み全体268本17,396行・1,513宣言。追加IDなし、計算上限変更なし。

main cd79e9cc5 は未取り込み。現在の停止点までは取り込まず、取り込む場合は
調整役の夜のrootビルドの成功を待つ。自レーンの対象検証と小監査だけを行った。
自分の鍵の待ちはすべて終了し、未検証のS8ソースは残っていない。
R2の停止中の4本の未追跡下書きは変更していない。

これは5∞-1の完成停止点ではない。S8の元の一般局所同値と同じ離散比較の射の自然性、
同じ層化単位の比較、およびS1の一般Coverage判定は未完。
次は上記の相対Čech図式の同じ各点のcommaの比較から続ける。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S8 の相対 Čech の各点の照合（11-16 夕、検証中）

前ターンは13本を検証・コミットし、権威あるソースと証拠が増えたため「進捗」。
作業木は `math/inf-supply`、検証済み全体268本17,396行・1,513宣言。
mainを取り込まず、停止中R2の4下書きも変更していない。

同じ既存構成の表示・係数移送の法則の型（追加IDなし、200行超なし）：
```lean
relativeCechData (f : P ⟶ Q) [HasFiniteProducts (Over Q)] :
  CategoryTheory.CechNerveData (Over.mk f)
relativeCechDiagram f : AsSmall.{v} SimplexCategoryᵒᵖ ⥤ C
relativeCechCocone f : Cocone (relativeCechDiagram f)
relativeCechHomCocone f (V : C) :
  Cocone (relativeCechDiagram f ⋙ coyoneda.obj (Opposite.op V))
RelativeCechPointComma f (r : V ⟶ Q) :=
  CostructuredArrow (elementsCoconeFunctor (relativeCechHomCocone f V)) (Discrete.mk r)
relativeCechPointCommaToElements f r : RelativeCechPointComma f r ⥤
  (cechPointDiagram (relativeCechData f) (Over.mk r)).Elements
relativeCechPointCommaFromElements f r :
  (cechPointDiagram (relativeCechData f) (Over.mk r)).Elements ⥤ RelativeCechPointComma f r
relativeCechPointCommaEquivalence f r : RelativeCechPointComma f r ≌
  (cechPointDiagram (relativeCechData f) (Over.mk r)).Elements
relativeCechPointComma_isWeaklyContractible (a : V ⟶ P) (ha : a ≫ f = r) :
  IsWeaklyContractible (nerve (RelativeCechPointComma f r))
relativeCechHomCocone_isColimit
  (hlift : ∀ r : V ⟶ Q, ∃ a : V ⟶ P, a ≫ f = r) :
  IsColimitCone (strictNativeCocone (setsToKan.mapCocone (relativeCechHomCocone f V)))
presheafSurjective_yoneda_lift (f : P ⟶ Q)
  (hf : ∀ X : Cᵒᵖ, Function.Surjective (f.app X)) (U : C) (r : yoneda.obj U ⟶ Q) :
  ∃ a : yoneda.obj U ⟶ P, a ≫ f = r
presheafRelativeCechHomCocone_isColimit (f : P ⟶ Q)
  (hf : ∀ X : Cᵒᵖ, Function.Surjective (f.app X)) (U : C) :
  IsColimitCone (strictNativeCocone
    (setsToKan.mapCocone (relativeCechHomCocone f (yoneda.obj U))))
weightedAugmentation_weak_of_iso_square (W : Iᵒᵖ ⥤ SSet.{u})
  (cF : Cocone F) (cG : Cocone G) (e : F ≅ G) (b : cF.pt ≅ cG.pt)
  (he : ∀ i, cF.ι.app i ≫ b.hom = e.hom.app i ≫ cG.ι.app i)
  (hc : IsWeakHomotopyEquivalence (weightedColimitAugmentation W cF)) :
  IsWeakHomotopyEquivalence (weightedColimitAugmentation W cG)
mappedSetCocone_isColimit_of_contractible_comma_and_iso {D : I ⥤ C} (c : Cocone D)
  {F G : C ⥤ Type u} (e : F ≅ G)
  (hc : ∀ q : Discrete (F.obj c.pt), IsWeaklyContractible
    (nerve (CostructuredArrow (elementsCoconeFunctor (F.mapCocone c)) q))) :
  IsColimitCone (strictNativeCocone (setsToKan.mapCocone (G.mapCocone c)))
presheafRelativeCechEvaluation_isColimit (f : P ⟶ Q)
  (hf : ∀ X : Cᵒᵖ, Function.Surjective (f.app X)) (U : C) :
  IsColimitCone (strictNativeCocone (setsToKan.mapCocone
    (((evaluation Cᵒᵖ (Type u)).obj (Opposite.op U)).mapCocone (relativeCechCocone f))))
```

相対Čechは `Over Q` での Mathlib の同じ有限冪。元の構造射を脚として忘却し、
点の条件 h ≫ 構造射 = r を同じ Over の射として読む。根の選択は各点の収縮の証明内だけ。
commaの表示の単位は、離散標的の射の証明項が異なるため厳密な等式でなく
明示的な自然同型にした。元の次数と元の射はそのまま。

`RelativeCechDiagram` と `RelativeCechPointComma` の2本は対象ビルド・小監査・SHA一致、
セッション64741の終了0を確認（`/tmp/is-w1/s8-relative-cech-point-3/`）。
現在セッション67688、`/tmp/is-w1/s8-presheaf-relative-hom-1/` に3対象の整理券一枚で待機。
後半3本は下書き、まだ検証していない。

Homの評価を元の点の評価へ戻す比較には、既存 `curriedYonedaLemma` の成分を
全自然同型としてそのまま入れる。各点の存在同型を集めて大域比較を作らない。
同じ全余錐と増大の可換四角形は、その全自然性と既存の増大の自然性から出す。
局所全射を各点全射と仮定しない。後で像への全射に適用するための入力であり、
一般の `sections_localEquiv_iso` が完成したという主張ではない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 表現可能 Hom 値までの接続を保存（11-16 夜）

`a46b584f9`：3本172行・31宣言。対象ビルド、小監査（標準三公理のみ）、SHA一致、
セッション67688の終了0を確認。証拠 `/tmp/is-w1/s8-presheaf-relative-hom-1/target-audit-result.json`。
検証済み全体271本17,568行・1,544宣言。

同じ既存構成の法則の続きを下書きした（追加IDなし、200行超なし）：
```lean
presheafRelativeCechCocone_isColimit (f : P ⟶ Q)
  (hf : ∀ X : Cᵒᵖ, Function.Surjective (f.app X)) :
  IsColimitCone (discretePresheafCocone (relativeCechCocone f))
relativeCechDiagonal (f : P ⟶ Q) :
  (Functor.const (AsSmall.{v} SimplexCategoryᵒᵖ)).obj P ⟶ relativeCechDiagram f
relativeCechDiagonal_proj f (n : AsSmall.{v} SimplexCategoryᵒᵖ)
  (i : Fin ((AsSmall.down.obj n).unop.len + 1)) :
  (relativeCechDiagonal f).app n ≫
    ((relativeCechData f).proj (AsSmall.down.obj n).unop.len i).left = 𝟙 P
relativeCechDiagonalSplitMono f (n : AsSmall.{v} SimplexCategoryᵒᵖ) :
  SplitMono ((relativeCechDiagonal f).app n)
relativeCechDiagonal_isSplitMono f (n : AsSmall.{v} SimplexCategoryᵒᵖ) :
  IsSplitMono ((relativeCechDiagonal f).app n)
relativeCech_proj_hom_ext f (n : ℕ) {V : C}
  {h k : V ⟶ ((relativeCechData f).obj.obj (Opposite.op ⦋n⦌)).left}
  (he : ∀ i : Fin (n + 1), h ≫ ((relativeCechData f).proj n i).left =
    k ≫ ((relativeCechData f).proj n i).left) : h = k
```

前層の全余錐へ戻す際は、既存 `discretePresheafCocone_evaluate_val` が
全ての余錐に使えるため、元の全余錐の評価を作り直さない。
`isColimitCone_of_pointwise` と、元の単体集合の射を保つ図式等式の移送だけを使う。
対角は既存の有限冪への恒等射の束ね。忘却後の座標の外延性は、
第0座標の Over の可換式と既存 `cechPower_hom_ext` を使う。
局所全射性や局所単射性を仮定として補う法則ではない。

係数移送の検証のセッション59368は `Functor.isoWhiskerRight` の名前空間、
39703は自然性の自動書き換えで終了1。
後者は既存の自然性の等式に H.map の congrArg を適用する形へ修正し、
計算上限を上げていない。現在セッション12725、
`/tmp/is-w1/s8-presheaf-relative-eval-3/` の8対象の整理券一枚で検証中。
mainを取り込まない方針と S7・R2・R3 停止を保持する。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 同じ Čech 対角の局所全射性（11-16 夜、検証中）

既存構成の法則の型（追加IDなし、200行超なし）：
```lean
presheafRelativeCech_proj_app_ext (f : P ⟶ Q) (n : ℕ) (U : C)
  {x y : (((relativeCechData f).obj.obj (Opposite.op ⦋n⦌)).left).obj (Opposite.op U)}
  (he : ∀ i : Fin (n + 1), ((relativeCechData f).proj n i).left.app (Opposite.op U) x =
    ((relativeCechData f).proj n i).left.app (Opposite.op U) y) : x = y
finiteSieveIntersection_mem (J : GrothendieckTopology C) (U : C)
  {ι : Type*} [Fintype ι] (R : ι → Sieve U) (hR : ∀ i, R i ∈ J U) :
  (⨅ i, R i) ∈ J U
relativeCechDiagonal_isLocallySurjective (J : GrothendieckTopology C) (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallyInjective J f] (j : AsSmall.{u} SimplexCategoryᵒᵖ) :
  CategoryTheory.Presheaf.IsLocallySurjective J ((relativeCechDiagonal f).app j)
```

最初は元の Yoneda 対応で既証の全座標の外延性へ戻す。
有限交叉は既存 `GrothendieckTopology.intersection_covering` の有限回の合成で、
添字の宇宙をsiteの対象の宇宙から独立にする私有補題。
対角の像を覆う篩は、第0座標と各座標の等化篩の有限交叉。
局所単射性から各等化篩が被覆であることを `Presheaf.equalizerSieve_mem` で示し、
元の制限した第0座標を同じ対角の前像にする。各点での単射を追加仮定にしない。

セッション12725は単体記法のscopeと全余錐比較の名前空間、25560は標準図式への
等式の暗黙の推論、91766は有限交叉の添字の宇宙で終了1。
いずれも既存の等式と名前空間・宇宙引数を明示して直し、計算上限を上げていない。
現在セッション14451、`/tmp/is-w1/s8-presheaf-relative-eval-6/` の10対象を検証中。
最後の差分を除く9対象は直前の対象ビルドが通ったが、束の小監査はまだ未完。
7本346行の未コミット分は監査が通ってから保存する。
検証済みの累計は引き続き271本17,568行・1,544宣言。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 約18,000行の中間報告：Čech 余錐と局所対角の検証完了（11-16 夜）

`f7066e36d`：7本346行・15宣言。既存3本を含む10対象のビルドと、
新しい環境での46所有宣言の小監査（標準三公理のみ）、SHA一致、セッション14451の終了0を確認。
証拠 `/tmp/is-w1/s8-presheaf-relative-eval-6/target-audit-result.json`。
直前の未検証の型の一覧は、すべてこの束までで検証済みとなった。

検証済み全体278本17,914行・1,559宣言。外枠22,000行まで残り4,086行。
古い文献メタデータのみの変更はこの数に含めない。追加IDなし。
ここは約18,000行での途中報告であり、停止点や全体の完成ではない。

今回閉じたこと：各点で全射な前層の元の相対Čech増大が、同じ空間値前層の
余極限余錐であること。局所単射な前層の元の全有限次数のČech対角が、
分裂単射であり、局所全射であること。前者は各点の comma の既存の収縮と
元の全余錐の評価、後者は各等化篩の有限交叉と同じ全座標の外延性から出した。
局所全射を各点全射にしたり、局所単射を各点単射にしたりしていない。
元の重みの反転、同じ増大の全族、零次の枝を保っている。

残る元の主張は変えない：
1. S8 `sections_localEquiv_iso`：像への全射とそのČech解消、像の包含への既証の局所単射の場合を
   同じ指定切断の射へ接続する。最終の型にpresentable係数の仮定を追加しない。
2. S8 `weightedSections_discrete_map`：現在の固定された値の同型のまま、元の射の類を照合する。
   新しい自然な値の同型への取り替えはしない。
3. S8 `sheafify_discrete_eq`・`localEquiv_of_sheafifyIso`：同じordinary sheafificationの単位と
   同じ∞層化の指定普遍性を使う。別の反射や無指定な対象同型に替えない。
4. S1：元の任意Coverageから生成位相の判定。普遍的に降下することを追加仮定にして代替しない。

S7・R2・R3は停止を保持する。main cd79e9cc5 は取り込んでいない。
自分の整理券・検証セッションはすべて終了。未検証のS8のLeanソースは残っていない。
次も新しい数学は新規ファイルだけに書き、外枠を超えそうなら検証済みを保存して止める。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### S8 の像への分解と固定比較の法則を保存（11-16 夜）

`dfed35d90`：5本280行・19宣言。対象ビルド、小監査（新しい環境・標準三公理のみ）、
SHA一致、セッション42632の終了0を確認。
証拠 `/tmp/is-w1/s8-image-reduction-4/target-audit-result.json`。
`da618f38f`：1本46行・2宣言。同じ検証とセッション97591の終了0を確認。
証拠 `/tmp/is-w1/s8-sections-cone-composition-2/target-audit-result.json`。
検証済み全体284本18,240行・1,580宣言。外枠まで残り3,760行。
追加IDなし、いずれも既存構成の法則・S8内の証明分割。200行超の補題なし。

型つきの法則の一覧（以下すべて検証済み）：
```lean
toRange_app_surjective (f : P ⟶ Q) (X : Cᵒᵖ) :
  Function.Surjective ((Subfunctor.toRange f).app X)
toRange_isLocallyInjective (J : GrothendieckTopology C) (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallyInjective J f] :
  CategoryTheory.Presheaf.IsLocallyInjective J (Subfunctor.toRange f)
rangeInclusion_isLocallySurjective (J : GrothendieckTopology C) (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallySurjective J f] :
  CategoryTheory.Presheaf.IsLocallySurjective J (Subfunctor.range f).ι
rangeCechCocone_isColimit (f : P ⟶ Q) :
  IsColimitCone (discretePresheafCocone (relativeCechCocone (Subfunctor.toRange f)))
rangeCechDiagonal_isLocallySurjective (J : GrothendieckTopology C) (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallyInjective J f] (j : AsSmall.{u} SimplexCategoryᵒᵖ) :
  CategoryTheory.Presheaf.IsLocallySurjective J
    ((relativeCechDiagonal (Subfunctor.toRange f)).app j)
rangeInclusion_restrictSectionsCone_isLimit (J : GrothendieckTopology C) (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallySurjective J f] (O : Presheaf C E) (hO : IsSheaf J O)
  (c : JoinCone (sectionsOfDiagram Q O)) (hc : IsLimitCone c) :
  IsLimitCone (SetWeight.restrictSectionsCone (Subfunctor.range f).ι O c)
relativeCechDiagonal_sections_isInvertible (J : GrothendieckTopology C) (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallyInjective J f]
  (j : AsSmall.{u} SimplexCategoryᵒᵖ) (O : Presheaf C E) (hO : IsSheaf J O)
  (hP : HasLimit (sectionsOfDiagram P O))
  (hD : HasLimit (sectionsOfDiagram ((relativeCechDiagram f).obj j) O)) :
  IsInvertibleEdge (sectionsOf_map ((relativeCechDiagonal f).app j) O hP hD).toTruncated
cechReverseIndex : SSet.{u + 1} :=
  ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} SimplexCategoryᵒᵖ))).op
cechReverseIndex_isWeaklyContractible : IsWeaklyContractible cechReverseIndex.{u}
cechConstantCone_isLimit (E : SSet.{u + 1}) [Quasicategory E] (x : E _⦋0⦌) :
  IsLimitCone (constantDiagramCone cechReverseIndex.{u} E x)
limitConeIso_hom_refl (c : JoinCone p) (hc : IsLimitCone c) :
  (limitConeIso c c hc hc).hom = 𝟙 _
limitConeIso_hom_comp (c d e : JoinCone p)
  (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
  (limitConeIso c d hc hd).hom ≫ (limitConeIso d e hd he).hom =
    (limitConeIso c e hc he).hom
limitVertexIso_hom_refl (c : JoinCone p) (hc : IsLimitCone c) :
  (limitVertexIso c c hc hc).hom = 𝟙 _
limitVertexIso_hom_comp (c d e : JoinCone p)
  (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
  (limitVertexIso c d hc hd).hom ≫ (limitVertexIso d e hd he).hom =
    (limitVertexIso c e hc he).hom
limitConeIso_restrict_hom (f : A ⟶ K) (c d : JoinCone p)
  (hc : IsLimitCone c) (hd : IsLimitCone d)
  (hcf : IsLimitCone (restrictJoinCone c f)) (hdf : IsLimitCone (restrictJoinCone d f)) :
  (hoFunctor.map (sliceOverRestrict p f)).toFunctor.map (limitConeIso c d hc hd).hom =
    (limitConeIso (restrictJoinCone c f) (restrictJoinCone d f) hcf hdf).hom
vertexIso_transport_target_hom (h : b = c) (e : VertexIso a b) :
  (h ▸ e).hom = e.hom ≫ eqToHom (congrArg HomotopyCategory.mk h)
vertexIso_transport_source_hom (h : a = b) (e : VertexIso a c) :
  (h ▸ e).hom = eqToHom (congrArg HomotopyCategory.mk h.symm) ≫ e.hom
limitVertexIsoOfDiagramEq_hom (h : F = G) (c : JoinCone F) (d : JoinCone G)
  (hc : IsLimitCone c) (hd : IsLimitCone d) :
  (limitVertexIsoOfDiagramEq h c d hc hd).hom =
    (limitVertexIso (c.cast h) d (hc.cast h) hd).hom
limitVertexIsoOfEquivalentRestriction_hom (a : A ⟶ B) (ha : IsQCatEquivalence a)
  (O : B ⟶ X) (c : JoinCone (a ≫ O)) (d : JoinCone O)
  (hc : IsLimitCone c) (hd : IsLimitCone d) (hda : IsLimitCone (restrictJoinCone d a)) :
  (limitVertexIsoOfEquivalentRestriction a ha O c d hc hd).hom =
    (limitVertexIso c (restrictJoinCone d a) hc hda).hom ≫
      eqToHom (congrArg HomotopyCategory.mk (restrictJoinCone_vertex d a))
SetWeight.elementsMap_comp (φ : P ⟶ Q) (ψ : Q ⟶ R) :
  elementsMap (φ ≫ ψ) = elementsMap φ ≫ elementsMap ψ
SetWeight.restrictSectionsCone_comp (φ : P ⟶ Q) (ψ : Q ⟶ R) (O : Presheaf C E)
  (c : JoinCone (sectionsOfDiagram R O)) :
  restrictSectionsCone (φ ≫ ψ) O c =
    restrictSectionsCone φ O (restrictSectionsCone ψ O c)
```

定値錐は既存の汎用
`Project/DerivedCategories/MappingAndStability/Homotopies/HomotopyModels/WeaklyContractibleConstantLimit`
を再利用した。依存は共終性・恒等錐の一般論だけで、G10や停止中R2の結果には依存しない。
主な計算の失敗は名前空間・始対象保存の明示引数・mapの合成の書き換えの形であり、
固定値の比較や元の普遍性は変更していない。計算上限も変更していない。

### 22,000行の外枠に対する再見積もりと停止（11-16 夜）

11-16の指示「22,000行を超えそうなら、検証済みの分をコミットして報告して止まる」に従う。
上の6本を保存した時点で、残りの見込みの上端が外枠を超えるため、Leanの追加をここで止める。

| 残り（元の一覧の証明分割。追加IDではない） | 見込み |
| --- | ---: |
| 固定された `weightedSections_discrete_map`：右Kanの指定錐の射の比較、元の分類・底変換・形状比較と指定同型の自然性、最後の合成 | 1,010〜1,710行 |
| 元のČech対角と定値錐、余極限の反転を全族でつなぎ、presentable係数で一般の局所同値を閉じる | 380〜650行 |
| `sections_localEquiv_iso` の元の任意係数 E：表現可能な写像空間による検査と必要な宇宙の移送、同じ hP・hQ と指定射への復帰 | 350〜600行 |
| `sheafify_discrete_eq`・`localEquiv_of_sheafifyIso`：元のordinary層化単位の∞局所性、同じ反射の大域的な指定単位との比較・自然性 | 550〜950行 |
| S1 の元の一般Coverage判定（普遍降下性を追加仮定にしない） | 450〜800行 |
| **残り合計** | **2,740〜4,710行** |
| **検証済み18,240行との合計** | **20,980〜22,950行** |

上端は外枠を950行超える見込み。表の上端を実装で使ってよいという意味ではない。
固定された比較の自然性は、`WeightedSectionsDiscrete` の値の同型が
`OriginalLeftLimit` → `LeftLimit` → `NativeLimit` → `NativeShapeLimit` と
分類・復元の形状比較を合成するため、辺の可逆性だけを示して代替できない。
途中の `limitVertexIsoOfLeftStraighteningIso` も三つの指定極限頂点比較を合成している。
元の全族を保ってこれらの自然性を照合する分を、前の見積もりで小さく見ていた。
分類の底変換の貼り合わせは、本体の既存 `leftStraightening_baseChange_pasting_iso` などを使う。
R2を再開したり、その新しい部分を作る予定ではない。

また任意Eの元の型にpresentable性を足す、固定された値の同型を別物に替える、
`RightKanHomUniversal` やČech増大の余極限性を未証明の仮定にする、Coverageの型を
普遍降下性付きに替える、といった短縮はしない。

未完の正本は drafts の元の5宣言：
`SpaceValued.weightedSections_discrete_map`、`SpaceValued.sections_localEquiv_iso`、
`SpaceValued.sheafify_discrete_eq`、`SpaceValued.localEquiv_of_sheafifyIso`、
`SheafCondition.isSheaf_toGrothendieck_iff`。S7は別停止点であり再開しない。
元の型は変更していない。

自分の整理券・ビルドは終了し、未検証のS8のLean下書きはない。
停止中R2の4下書きは未変更。main cd79e9cc5 は未取り込み。
これは完成停止点ではなく、外枠の指示による中間停止。目標は未完のまま保持する。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：外枠24,000行で再開、指定極限の比較の合成則

ユーザー承認により外枠を24,000行に変更。0cde9bbd3の残り5群を元の型のまま進める。
約22,000行で止まらずに中間報告、上端が24,000行を超える見込みになったら検証済みを
コミットして停止する。S7・R2・R3は再開しない。mainは引き続き取り込まない。

`SectionsConeLimitComparison`（新規1本）の次の2法則を検証した。
これは既存の錐・指定極限の比較の合成則で、追加IDではない。

```lean
sectionsConeMap_limitConeIso_hom (φ : P ⟶ Q) (O : ULiftNerveI ⟶ E)
  (c d : JoinCone (SetWeight.diagram P O)) (hc : IsLimitCone c) (hd : IsLimitCone d)
  (q : JoinCone (SetWeight.diagram Q O)) :
  homMk (sectionsConeMap φ O c hc q).toTruncated ≫ (limitConeIso c d hc hd).hom =
    homMk (sectionsConeMap φ O d hd q).toTruncated
sectionsConeMap_limitVertexIso_hom (φ : P ⟶ Q) (O : ULiftNerveI ⟶ E)
  (c d : JoinCone (SetWeight.diagram P O)) (hc : IsLimitCone c) (hd : IsLimitCone d)
  (q : JoinCone (SetWeight.diagram Q O)) :
  (hoFunctor.map (sliceOverProjection (SetWeight.diagram P O))).toFunctor.map
    (homMk (sectionsConeMap φ O c hc q).toTruncated) ≫ (limitVertexIso c d hc hd).hom =
  (hoFunctor.map (sliceOverProjection (SetWeight.diagram P O))).toFunctor.map
    (homMk (sectionsConeMap φ O d hd q).toTruncated)
```

ここで `ULiftNerveI := (SSet.uliftFunctor.{u+1,u}).obj (nerve I)`、`homMk`は
`Truncated.HomotopyCategory.homMk` の略記。完全な型は新規ファイルにある。
終対象への射の一意性を同じ頂点射影に写し、指定された辺を変更していない。
対象ビルド・新鮮な環境の所有モジュール別2宣言の小監査が完了、終了コード0。
証拠：`/tmp/is-w1/s8-sections-limit-comparison-1/target-audit-result.json`。
標準三公理のみ、対象ソースのSHA一致を確認した。

続いて、図式等式と指定極限比較の合成則、および
`nativeWeightedSections_leftLimitIso`の標的比較との可換性を新規ファイルで検証中。
最初の後者の型の推論は合成記号の箇所で `whnf` の200,000 heartbeat上限に達した。
上限は上げず、合成の圏と3頂点を明示して再検証する。
いずれも200行を超える法則ではない。元の値の同型・主張は変更していない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：固定値の比較で、指定余単位との両立を失う選択についての確認点

`weightedSections_discrete_map`の固定値比較を調べ直したところ、時間切れとは別に、
指定余単位との両立を補題で回収する前に確認すべき選択が3箇所ある。
これは元の固定値比較の反例をLeanで証明したという報告ではない。

* `WeightedSectionsLocalComparison.lean:33`：
  `Classical.choose (weightedSections_limitValue O hE P)`。
* `NativeWeightedSectionsLeftLimit.lean:71`：
  `Classical.choose (nativeWeightedSections_limitValue O hE v)`。
* `WeightedSectionsLeftLimit.lean:44`：
  `Classical.choose (nativeWeightedSections_limitValue O' hE v)`。

`IsRightKanExtension.limitValue`（KanExtensions/Definition.lean:167）の結論は
次の存在命題だけで、選んだ余単位αと錐を結ぶデータは含まない。

```lean
∃ c : JoinCone (rightKanDiagram δ O v), IsLimitCone c ∧ c.vertex = G.app _ v
```

この命題からの`Classical.choose`は、αに沿う`RightKanConeTransport`を選ぶ操作とは違う。
命題の証明の無関係性があるため、`limitValue`の証明中でαの輸送を使っていることだけを
根拠に、選ばれたcがその輸送の終端だとは言えない。元の定理のdocstringも
「自然性の組み立て…は主張しない」と明記している。

一般に、指定頂点を持つ極限錐という条件だけから、元の関手の射と両立する比較は出ない。
通常の圏の例では、[1]上の定値図式を一対象の非自明な群のgroupoidへ取り、二つの
頂点で極限錐の脚をそれぞれ恒等と非自明な自己同型にすれば、どちらも指定頂点を持つ
極限錐だが、それらの頂点比較は定値図式の恒等射と自然にはならない。
この例は不足する条件の説明であり、現在の`Classical.choose`の値を計算した反例ではない。

検討する差分案は次のとおり（まだ既存宣言には反映しない）。新規ファイルに、
元の同じ`weightedSectionsData`と`nativeWeightedSectionsData`の余単位の
輸送を選ぶdefとその2法則を置く。

```lean
-- δ、G、αは元の同じデータ。hαも既存のIsRightKanExtensionの証明。
def valueTransport (v : K _⦋0⦌) : RightKanConeTransport δ O G α v :=
  Classical.choose (hα v)
-- IsLimitCone (valueTransport v).cone := Classical.choose_spec (hα v)
-- (valueTransport v).cone.vertex = G.app _ v := (valueTransport v).cone_vertex
```

その後、上の3箇所だけ、`let c := (valueTransport ...).cone`、極限性と頂点等式は
この同じ輸送の法則から取る形へ置き換える。全関手・元の余単位・sectionsOfの選択、
公開の名前・型は保つ。元の`weightedSections_discrete`の本文自体も保つが、参照する
比較の本文が変わるため、その定義を展開した値は変わりうる。rflによる旧値との一致は
主張しない。この点は単なる計算法則の追加ではなく、既存本文の変更の承認が要る。

この差分なら、自然性を任意の点ごとの同型から組み立てず、同じ指定余単位に両立する
大域的な`rightKanHomUniversalIso`とその`hom_fac`に照合する道を保てる。
その後の照合の証明はなお必要で、この提案だけで自然性が完成したとはしない。
輸送のdefと3箇所の差分は80〜140行程度を見込む。前節の見込みの上端22,950行と
合わせても24,000行の中だが、実装・検証前の見込みである。

指示書§2の「既存の宣言の本文・型・名前は変えない（どうしても要るときは止めて報告）」
により、既存の3本文は変更していない。この判断の間は、既にコンパイルを通過した
Čechの極限性と比較の法則の小監査を閉じる。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：Čech増大の極限性と比較の法則を検証、3本文の修正の承認

`/tmp/is-w1/s8-cech-and-comparison-laws-3/target-audit-result.json`で追加4本・6宣言の
対象ビルドと小監査が完了し、監視していたプロセスも終了コード0を確認した。
新鮮な環境のモジュール所有権、標準三公理のみ、対象ソースのSHA一致を確認。

| 新規ファイル | 行数 | 宣言数 | 検証した内容 |
| --- | ---: | ---: | --- |
| DiagramEqLimitVertexComposition | 39 | 2 | 図式等式による頂点比較と標準極限比較の前後の合成則 |
| EquivalentRestrictionLimitComposition | 36 | 1 | 同値な添字への比較の前に標準極限比較を合成する法則 |
| WeightedSectionsRelativeCech | 45 | 2 | 元の点ごとに全射な射と像への全射の全Čech増大を、元のweightedSectionsで極限に送る |
| FunctorHomEdgeNaturality | 32 | 1 | 元の全関手間の二胞体の成分と、指定辺の像の類の自然性 |

既存の構成の法則・承認済み一覧の証明分割で、追加IDはない。
各法則は200行未満。既にコミットした51行・2宣言と合わせて、この再開の検証済みは
5本・203行・8宣言。通算は289本・18,443行・1,588宣言。
Čechの同じ全余錐の余極限反転までは閉じたが、局所同値の結論をまだ主張しない。

`NativeWeightedSectionsLeftLimitComposition`は未検証でコミットに含めない。
通常の合成記号、圏と端点の明示、Iso.homの明示引数、同型の合成、型つきletによる
固定を試したが、いずれも型の推論中のwhnfで200,000 heartbeatに達した。
最後のログは`/tmp/is-w1/s8-cech-and-comparison-laws-2/build.log`。
計算上限は変更していない。旧値の選択への同じ法則を証明し続ける前に、
上で見つけた指定余単位との両立の確認点を調整役へ報告した。

調整役の11-16の承認（main b54686dae、mainそのものは未取り込み）により、
上記3本文の選択を同じ指定余単位に沿う`valueTransport`の終端に置き換える。
公開の名前・型、全関手、元の余単位、sectionsOfの選択は保持。新しい仮定は置かない。
旧値とのrflは要求されない。差分は24,000行の外枠に数える。
Sheaves全体とその下流の枝のモジュールを全部、対象ビルドし直す。

新規の2ファイル`WeightedSectionsValueTransport`・`NativeWeightedSectionsValueTransport`
に指定輸送のdef・極限性・頂点等式を記述し、承認された3本文の選択箇所だけを変更した。
まず直接importerを含む対象ビルド・小監査・v3bの公開型/属性/公理の保存比較を実行中。
その後、全対象の再ビルドを分割して実施する。S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：承認された3本文の修正と、Sheaves全157本の再検証完了

3本文の修正は承認された錐の選択の置換と新規輸送ファイルのimportだけ。
新規`WeightedSectionsValueTransport`は44行・3宣言、
`NativeWeightedSectionsValueTransport`は48行・3宣言。
既存3ファイルの差分は追加14行・削除7行。外枠用には削除を控除せず106行を加算し、
検証済みの累計は**291本・18,549行**（物理的な差分の正味では18,542行）と数える。
前回の見込みの上端22,950行にこの例外106行を別枠で足しても23,056行であり、
現時点では24,000行の中。元の5群の主張を短縮せず進める。

1. 直接importerを含む7本の対象ビルドと48宣言の小監査が通過した。
   証拠は`/tmp/is-w1/s8-value-transport-1/target-audit-result.json`。
2. v3bの旧・新コンパイル環境の採取を行い、公開宣言および証明補題以外の生成宣言7本の
   kind・公開の型・属性・公理が一致した。本文のハッシュが変わった公開宣言は
   承認された3宣言だけ。証拠は同ディレクトリの`before.json`・`after.json`・
   `preservation-result.json`、公開比較コマンドは終了コード0。
   初回の比較は内部生成証明補題も名前集合の完全一致を要求したため終了コード1になった。
   具体的には承認した親の`nativeWeightedSections_leftLimitIso._proof_5`と
   `weightedSections_leftLimitIso._proof_8`が消えた。共通する内部証明補題14本の型も変わる。
   公開型の変更ではなく本文の証明分割の変更なので、この3親に属する内部proof行だけを
   区別して再比較した。共通する内部proof行についても属性・公理の一致は検査した。
   公開宣言と他の生成宣言は一切この例外に含めず、全て一致を要求した。
3. 全追跡モジュールのimportグラフを経由する推移的な下流を調べ、Sheaves配下157本、
   その外の枝の下流は0本だった。その全157本を対象ビルドし直し、同じ新鮮な環境の
   所有宣言963本の小監査も完了した。対象ソースのSHA一致、標準三公理のみを確認。
   監視プロセスの終了コード0も確認した。
   証拠は`/tmp/is-w1/s8-value-transport-all-1/scope.json`・`files.json`・
   `target-audit-result.json`。rootビルドとmainの取り込みは行っていない。

時間切れになった自作の未検証補助則は
`/tmp/is-w1/unverified-before-value-transport/NativeWeightedSectionsLeftLimitComposition.lean`
に保全し、productionのソース配下から外した。上の全157本に除外したソースはない。
停止中R2の4下書きは未変更。新しい輸送と3本文の変更は検証済みであり、
この後は同じ指定余単位のstart・diagram・fixedVertexを使って大域比較のhom_facへ照合する。
元の`weightedSections_discrete_map`と残る4宣言の完成はまだ主張しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：既存の制限APIへの統一と、枝の全追加モジュールの同時import監査

既存`SetSectionsRestriction`（9e7b918c2）は、制限の全関手と合成則を既に持っていた。
前回の`SectionsConeComposition`は、その`elementsMap_comp`と
`restrictSectionsCone_comp`の2名を重複して新設していた。見落としだった。
既存側の対象ビルドと9宣言の小監査を改めて通し（終了コード0、標準三公理のみ）、
新設してしまった46行のモジュールを撤回して、
`SectionsConeLimitComparison`のimportを既存`SetSectionsRestriction`へ変更した。
同ファイルの宣言の型・本文、既存`SetSectionsRestriction`の9宣言は一切変更していない。
撤回したソースは`/tmp/is-w1/retired-duplicate/SectionsConeComposition.lean`に保全。
削除46行を外枠から控除せず、外枠用の累計は18,549行のままにする。

個別の対象ビルドではこの種の別モジュール間の重複を検出できないため、
整理後の枝の全追加290モジュールを同時にimportする検証へ広げた。
対象ビルド・新鮮な環境の1,578宣言の公理監査・対象SHA一致が全て通り、
監視プロセスの終了コード0を確認した。証拠は
`/tmp/is-w1/s8-all-branch-import-audit-1/files.json`・`target-audit-result.json`。
全体の宣言数はこの同時importのモジュール所有権による1,578を正本とする。
個別採取の単純合算とは、上流のeq_1・congr_simp等の生成宣言の所有環境が異なる。
（照合資料：`/tmp/is-w1/s8-current-inventory-delta.json`。）

さらに全290ファイルの名前つき公開宣言952個を、元ソースを変更せず字句解析して
照合し、同名の重複0、未対応ファイル0を確認した。
この字句検査では文献属性をメモリ上だけで除去し、匿名instanceには検査用の仮名を
付けて名前の集計から除いている。これは型検査の代用ではなく、上記の同時importと
小監査を補う検査。結果は`/tmp/is-w1/s8-source-duplicate-review-after.json`。

指定余単位を保持する修正後も、旧補助則
`nativeWeightedSections_leftLimitIso_comp`の型をそのまま比較すると
isDefEqの200,000 heartbeatに達した。計算上限は上げず、候補は
`/tmp/is-w1/unverified-after-value-transport/NativeWeightedSectionsLeftLimitComposition.lean`
に保全し、productionソースから外した。これは元のS8の結論が偽という判定ではない。
次は既存の制限APIを使い、元の切断射と全錐の普遍辺の射影・合成の計算法則を先に検証する。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：元の切断射の射影・普遍辺の合成・一般重みのG8自然性

追加3本・141行・14所有宣言（内部証明補題を含む）の対象ビルドと小監査を完了した。
`/tmp/is-w1/s8-sections-map-projection-2/target-audit-result.json`、終了コード0、
標準三公理のみ、対象SHA一致。いずれも既存構成の計算法則・自然性で追加IDはなく、
200行を超える法則もない。外枠用累計は**18,690行**、検証済みの追加モジュールは293本。

* `SectionsMapConeProjection`（47行）：元の`sectionsMap`の類を、同じ
  `sectionsConeMap`の頂点射影と始点の等式による移送で表した。最初の`simpa`は
  射影した辺の標的の型の揃え方で不一致になったため、元の同じ辺の始点・標的を
  明示してから移送の法則を適用した。公開の射を変えていない。
* `SectionsConeMapComposition`（41行）：元のψの普遍辺を既存のφの制限関手で写し、
  同じφの普遍辺と合成したものが、元のφ≫ψの普遍辺の類に一致する。
  始点・標的の等式による移送も型に含め、錐の終対象への射の一意性だけで証明した。
* `SetWeightTensorSectionsNaturality`（53行）：既存G8の3つの一般の自然性を合成し、
  任意の集合重みの射φについて、元の`tensorSpaceFunctor_setWeightHomNatural`
  の下でテンソルの前合成と元の指定`sectionsMap`の後合成を結ぶ全族の`FunctorIso`を得た。
  篩包含に限定せず、同じ元の比較ηを保持している。

主張の型（略記η_Xは元の`tensorSpaceFunctor_setWeightHomNatural X hE M F cX hcX`）：

```lean
sectionsMap_hom_eq_projection φ O c hc q hq :
  homMk (sectionsMap φ O c hc q hq).toTruncated =
    eqToHom (congrArg HomotopyCategory.mk (restrictSectionsCone_vertex φ O q).symm) ≫
      (hoFunctor.map (sliceOverProjection (SetWeight.diagram P O))).toFunctor.map
        (homMk (sectionsConeMap φ O c hc q).toTruncated)
sectionsConeMap_comp_hom φ ψ O cP hcP cQ hcQ cR :
  let h0 := (restrictSectionsFunctor_vertex φ O (restrictSectionsCone ψ O cR)).trans
    (restrictSectionsCone_comp φ O ψ cR)
  let h1 := restrictSectionsFunctor_vertex φ O cQ
  eqToHom (congrArg HomotopyCategory.mk h0.symm) ≫
    (hoFunctor.map (restrictSectionsFunctor φ O)).toFunctor.map
      (homMk (sectionsConeMap ψ O cQ hcQ cR).toTruncated) ≫
    eqToHom (congrArg HomotopyCategory.mk h1) ≫
      homMk (sectionsConeMap φ O cP hcP cQ).toTruncated =
    homMk (sectionsConeMap (φ ≫ ψ) O cP hcP cR).toTruncated
setWeightTensorSections_shapeIso φ hE M F cP hcP cQ hcQ :
  FunctorIso
    (precompose (functorVertex F) (homMk (tensorWeightEdge hE M φ).toTruncated) ≫ η_P.hom)
    (η_Q.hom ≫ postcompose M (homMk (sectionsMap φ F cP hcP cQ hcQ).toTruncated))
```

完全な型は各新規ファイル。hEとcP・cQの指定極限性以外に比較や自然性の仮定を
足していない。最後の一般重みの合成は、既存の
`tensorSpaceFunctor_diagramHom_weight_naturality`・
`setWeightSectionsEquivalenceNatural_shapeIso`・`setWeightSectionsLimitTail_shapeIso`
を再利用した。新しいunstraightening比較や指定極限の比較を作り直していない。
これは元の`weightedSections_discrete_map`そのものの完成ではない。同じ指定余単位の
輸送からの固定値比較と、この既存G8の自然性との照合は引き続き残る。
S1の一般Coverage判定、一般の局所同値、同じ層化の比較も未完のまま保持する。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：left全空間の固定値比較の合成則を検証、未検証候補の型の訂正

`NativeLeftSectionsComparisonLaws`（65行・8所有宣言）の対象ビルド・小監査が通過した。
`/tmp/is-w1/s8-native-left-boxed-4/target-audit-result.json`、終了コード0、
標準三公理のみ、対象SHA一致。元の同じ図式・頂点・値の同型に型を固定した名前を
付け、次の既存構成の合成則を証明した。比較や余単位の新しい選択は行っていない。

```lean
nativeLeftSectionsDiagram P O :=
  ulift.map (smallLeftUnstraighteningProjection P) ≫ (uliftOppositeIso A).hom ≫ O
nativeLeftSectionsValue P O hE :=
  (nativeWeightedSections O hE).app _ (opObjEquiv.symm (functorVertex P))
nativeLeftSectionsValueIso P O hE d hd := nativeWeightedSections_leftLimitIso P O hE d hd
nativeLeftSectionsValueIso_comp P O hE d e hd he :
  nativeLeftSectionsValueIso P O hE d hd ≪≫ limitVertexIso d e hd he =
    nativeLeftSectionsValueIso P O hE e he
```

Pの底は一般の小さい準圏A、Eは元のpresentable係数、d・eは元の同じleft全空間の
係数図式の指定極限錐。完全な型は新規ファイル。定義の展開は図式と頂点の型だけに
局所化し、元の値比較を頂点移送の式へ書き直して、結合則と
`limitVertexIsoOfDiagramEq_hom_comp`を適用した。計算上限は変更していない。
既存の構成の法則・証明の分割で追加IDはない。外枠用累計は**18,755行**、294本。

前の未検証候補の時間切れの記録を補足・訂正する。候補ではMorphismSpacesの開放を
落とし、図式の型に現れる`uliftOppositeIso`が未解決だった。自動暗黙引数が有効な
宣言の型にこれが入ったまま、元の図式との型の比較を進めていた。
このため、以前のログを意図した正しい型そのもののkernel上限の証拠とはしない。
補助定義の本文へ分けた段階でUnknown identifierを確認し、名前空間を明示し、
`autoImplicit false`にして意図した型へ訂正した。その型では時間切れは起こらず、
順射の式の明示と図式・頂点の型の局所的な展開で上の合成則が通った。
この訂正は、別に確認し承認された指定余単位の3本文の修正を取り消すものではない。

同じ見落としが他の今回の追加にないか確認するため、0cde9bbd3以降に追加した11ファイル
（撤回した重複モジュールは除く）の一時コピーに`set_option autoImplicit false`を
加え、元ソースを変更せず全てコンパイルした。全11本が終了コード0で通り、
uses-sorry警告なし、元ソースのSHA不変を確認した。
証拠は`/tmp/is-w1/s8-autoimplicit-false-1/files.json`・`result.json`。

次の係数図式の等式による同じ比較の移送は、新規ファイルの下書きにあり未検証。
この段階では固定された`weightedSections_discrete_map`の全体やS8の完成は主張しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：係数移送と元のweightedSections_leftLimitIsoの合成則

追加2本・129行・7所有宣言の対象ビルド・小監査が完了、各プロセス終了コード0。
標準三公理のみ、対象SHA一致。外枠用累計は**18,884行**、296本。

* `NativeLeftSectionsCoefficientTransport`（60行・6宣言）：元の同じ値比較を係数図式の
  等式で移すdefと、指定極限比較との合成則（同型・順射の両方）。
  証拠：`/tmp/is-w1/s8-native-left-coefficient-1/target-audit-result.json`。
* `WeightedSectionsLeftLimitComposition`（69行・1宣言）：元の同じ
  `weightedSections_leftLimitIso`の順射の後合成則。
  証拠：`/tmp/is-w1/s8-weighted-left-composition-2/target-audit-result.json`。

```lean
nativeLeftSectionsValueIsoOfDiagramEq P O hE
  (hD : D = nativeLeftSectionsDiagram P O) (d : JoinCone D) (hd : IsLimitCone d) :
  VertexIso (nativeLeftSectionsValue P O hE) d.vertex
nativeLeftSectionsValueIsoOfDiagramEq_comp P O hE hD d e hd he :
  nativeLeftSectionsValueIsoOfDiagramEq P O hE hD d hd ≪≫ limitVertexIso d e hd he =
    nativeLeftSectionsValueIsoOfDiagramEq P O hE hD e he
nativeLeftSectionsValueIsoOfDiagramEq_hom_comp P O hE hD d e hd he :
  (nativeLeftSectionsValueIsoOfDiagramEq P O hE hD d hd).hom ≫
    (limitVertexIso d e hd he).hom =
      (nativeLeftSectionsValueIsoOfDiagramEq P O hE hD e he).hom
weightedSections_leftLimitIso_hom_comp O hE F d e hd he :
  (weightedSections_leftLimitIso O hE F d hd).hom ≫ (limitVertexIso d e hd he).hom =
    (weightedSections_leftLimitIso O hE F e he).hom
```

最後のd・eは元の`WeightedSectionsLeftLimit`と同じ形状・係数の錐。
元の本文と同じP、O'、同じ指定輸送の錐c、同じ値比較ewを局所的に固定した。
係数の等式hDも元の式と同じ式で示し、元の値比較の順射をその固定部分と上の
係数移送の比較の合成へ分解した。この現本文の分解の等式はrflで確認できた。
これは修正前の旧値とのrflではない。途中の頂点の別名に対して▸の型が見えなかった
初回の候補は、元の頂点の式をchangeで明示してから同じhvで移送する形に直した。
新しい比較や新しい仮定は導入していない。既存構成の法則・証明分割で追加IDはなく、
いずれも200行未満。既存の宣言をさらに変更していない。
次は制限した標準極限比較の頂点射と、元の圏への同じ比較を結ぶ法則。
固定されたweightedSections_discrete_mapの全体とS8の完成は未完のまま。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：制限した標準比較と、元の底上の同値による比較の前後の合成則

追加3本・169行・11所有宣言の対象ビルド・小監査が完了、監視プロセス終了コード0。
標準三公理のみ、対象SHA一致。
証拠：`/tmp/is-w1/s8-over-equivalence-composition-1/target-audit-result.json`。
外枠用累計は**19,053行**、299本。全て既存構成の法則で追加IDはなく、各法則200行未満。

* `LimitVertexIsoRestriction`（47行・2宣言）：標準極限比較を制限した射と元の頂点射を、
  同じ頂点の等式の射で結ぶ。錐の標準比較の制限の既存の法則と、頂点射影の等式からの
  自然変換の自然性を使った。
* `EquivalentRestrictionLimitTargetComposition`（40行・1宣言）：既存の同値な添字による
  比較の後に標的の標準極限比較を合成する法則。
* `OverEquivalenceLimitComposition`（82行・8宣言）：元の`limitVertexIsoOfOverEquivalence`
  の前後の標準極限比較との合成則。元の定義内の、標的を固定した同じ図式等式の移送を
  privateな補助に表示し、現定義をchangeでそのまま読み直して証明した。

```lean
limitVertexIso_restrict_hom f d e hd he hdf hef :
  eqToHom (congrArg HomotopyCategory.mk (restrictJoinCone_vertex d f)) ≫
    (limitVertexIso d e hd he).hom =
  (limitVertexIso (restrictJoinCone d f) (restrictJoinCone e f) hdf hef).hom ≫
    eqToHom (congrArg HomotopyCategory.mk (restrictJoinCone_vertex e f))
limitVertexIsoOfEquivalentRestriction_hom_comp a ha O c d e hc hd he :
  (limitVertexIsoOfEquivalentRestriction a ha O c d hc hd).hom ≫
    (limitVertexIso d e hd he).hom =
      (limitVertexIsoOfEquivalentRestriction a ha O c e hc he).hom
limitVertexIso_hom_comp_overEquivalence a ha hw O c c' d hc hc' hd :
  (limitVertexIso c c' hc hc').hom ≫
    (limitVertexIsoOfOverEquivalence a ha hw O c' d hc' hd).hom =
      (limitVertexIsoOfOverEquivalence a ha hw O c d hc hd).hom
limitVertexIsoOfOverEquivalence_hom_comp a ha hw O c d e hc hd he :
  (limitVertexIsoOfOverEquivalence a ha hw O c d hc hd).hom ≫
    (limitVertexIso d e hd he).hom =
      (limitVertexIsoOfOverEquivalence a ha hw O c e hc he).hom
```

`hdf`・`hef`は同じ二つの制限錐の極限性。後の適用では同値な添字への制限から出す。
最後の2本は元の底上の可換式`hw : a ≫ q = p`と、同じ底係数Oを保つ。
比較の自然性を入力に置かず、仮定は元の構成が取る同値・可換式・指定極限性だけ。
元の比較を新しい比較へ置き換えていない。次は元の圏に戻す値比較への接続。
S8の固定された全族比較およびS1の一般Coverage判定は依然未完。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：元の圏へ戻す同じ値比較の合成則

追加2本・130行・7所有宣言の対象ビルドと小監査が完了（終了コード0、標準三公理のみ、SHA一致）。
証拠：`/tmp/is-w1/s8-original-left-composition-2/target-audit-result.json`。
外枠用累計は **19,183行・301本**。

* `WeightedLeftSectionsCoefficientTransport`（61行）：元の同じ図式に名前を付け、
  図式の等式に沿って元の値比較と合成則を移す。
* `WeightedSectionsOriginalLeftLimitComposition`（69行）：同じ底同型への制限で標準極限比較を照合し、
  元の値比較の合成則を示す。

```lean
weightedLeftSectionsValueIsoOfDiagramEq O hE F hD d hd :
  VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm (functorVertex F))) d.vertex
weightedLeftSectionsValueIsoOfDiagramEq_hom_comp O hE F hD d e hd he :
  (weightedLeftSectionsValueIsoOfDiagramEq O hE F hD d hd).hom ≫
    (limitVertexIso d e hd he).hom =
      (weightedLeftSectionsValueIsoOfDiagramEq O hE F hD e he).hom
weightedSections_originalLeftLimitIso_hom_comp O hE F d e hd he :
  (weightedSections_originalLeftLimitIso O hE F d hd).hom ≫
    (limitVertexIso d e hd he).hom =
      (weightedSections_originalLeftLimitIso O hE F e he).hom
```

係数等式の補題のD・hDは元の同じleft図式を移す型、最後のd・eは元の圏上の同じ図式の錐。
初回候補は元の本文のletを残したままrwしたため不一致だった。
元の同じ頂点移送をchangeで明示して、既存の移送の法則を適用すると通った。
計算上限は変更していない。いずれも既存構成の法則で200行未満、追加IDなし。
次の3本の下書き（パラメータの頂点移送、元の切断比較の合成則、固定離散値比較の可換三角形）は
未検証なので今回のコミットには含めない。固定した射の自然性とS1は依然未完。
mainは取り込まず、S7・R2・R3も再開していない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：固定離散値比較の可換三角形と、同じ指定輸送錐の表示

追加4本・248行・16所有宣言の対象ビルドと小監査が完了（終了コード0、標準三公理のみ、SHA一致）。
証拠：`/tmp/is-w1/s8-discrete-factorization-3/target-audit-result.json`。
外枠用累計は **19,431行・305本**。

* `VertexIsoParameterTransport`（35行）：頂点のパラメータの等式による同じ同型の移送を、
  ホモトピー圏の等式の射との合成で表す（始点・標的の2法則）。
* `DiscreteSectionsLeftComparison`（61行）：元の離散比較の本文と同じ要素の圏の比較と
  射影等式を固定し、同じ切断錐からの比較とその合成則を表示する。
* `WeightedSectionsDiscreteFactorization`（63行）：固定された元の離散値の同型を、
  任意の指定left極限との可換三角形で特徴付ける。
* `NativeLeftSectionsTransportCone`（89行）：元の指定余単位の輸送錐を、同じleft全空間へ
  制限した錐に名前を付ける。その頂点等式と極限性を証明し、元の値比較の順射を
  その同じ錐との標準極限比較として表示する。新しい錐の選択はない。

```lean
vertexIso_parameter_source_cast_hom f h e :
  (cast (congrArg (fun z => VertexIso (f z) c) h) e).hom =
    eqToHom (congrArg HomotopyCategory.mk (congrArg f h.symm)) ≫ e.hom
vertexIso_parameter_target_cast_hom f h e :
  (cast (congrArg (fun z => VertexIso c (f z)) h) e).hom =
    e.hom ≫ eqToHom (congrArg HomotopyCategory.mk (congrArg f h))
discreteSectionsLeftComparison_hom_comp O P hP d e hd he :
  (discreteSectionsLeftComparison O P hP d hd).hom ≫ (limitVertexIso d e hd he).hom =
    (discreteSectionsLeftComparison O P hP e he).hom
weightedSections_discrete_hom_fac O hE P hP d hd :
  let f := fun v => (weightedSections O hE).app _ (SSet.opObjEquiv.symm v)
  (weightedSections_discrete O hE P hP).hom ≫
    (discreteSectionsLeftComparison O P hP d hd).hom =
      eqToHom (congrArg HomotopyCategory.mk
        (congrArg f ((discretePresheafInclusion C).property.1 P))) ≫
          (weightedSections_originalLeftLimitIso O hE (discretePresheaf P) d hd).hom
nativeLeftSectionsTransportCone_vertex P O hE :
  (nativeLeftSectionsTransportCone P O hE).vertex = nativeLeftSectionsValue P O hE
nativeLeftSectionsTransportCone_isLimit P O hE :
  IsLimitCone (nativeLeftSectionsTransportCone P O hE)
nativeLeftSectionsValueIso_hom_transportCone P O hE d hd hc :
  (nativeLeftSectionsValueIso P O hE d hd).hom =
    eqToHom (congrArg HomotopyCategory.mk
      (nativeLeftSectionsTransportCone_vertex P O hE).symm) ≫
        (limitVertexIso (nativeLeftSectionsTransportCone P O hE) d hc hd).hom
```

可換三角形は、元のweightedSections_discreteを展開し、同じ埋め込みの頂点等式の移送を計算する。
中間のClassical.chooseの極限を2つの既存比較の合成則で消す。別の同型への差し替えではない。
移送則の引数を省略した候補は未確定な等式が残ったため、f・hp.symm・同型を明示した。
合成側はe0・wという同じ定義の別名だけを展開して逆射を消すと通った。
指定輸送錐の法則では既存の制限の判定が入る名前空間のopenを補った。
計算上限は上げず、既存構成の法則・証明分割だけ（各200行未満、追加IDなし）。
可換三角形は重みの射についての自然性自体ではない。次はその射影の法則と指定余単位との照合。
S8全体、一般の局所同値と同じ層化の比較、S1の一般Coverage判定は未完。
mainは取り込んでいない。S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：任意の錐の射の制限と、外枠の再見積もり

`SectionsRestrictionProjection`（48行・1所有宣言）の対象ビルド・小監査が完了
（終了コード0、標準三公理のみ、対象SHA一致）。証拠：
`/tmp/is-w1/s8-sections-restriction-projection-2/target-audit-result.json`。

型は、P・Qを同じ小さい通常の圏C上の集合値関手、OをULift(nerve C)からXへの射、
c・dをdiagram Q O上の錐、ℓをそのsliceOverのホモトピー圏の任意の射とする。
R := restrictSectionsFunctor φ O、πP・πQを頂点射影、
hc・hdを既存のR ≫ πP = πQをそれぞれc・dで評価した頂点等式とすると、

```lean
restrictSectionsFunctor_projection_naturality φ O c d ℓ :
  (hoFunctor.map πP).toFunctor.map ((hoFunctor.map R).toFunctor.map ℓ) ≫
    eqToHom (congrArg HomotopyCategory.mk hd) =
  eqToHom (congrArg HomotopyCategory.mk hc) ≫
    (hoFunctor.map πQ).toFunctor.map ℓ
```

実ソースではR・πP・πQ・hc・hdを全て明示している。制限した錐の極限性を仮定しない。
一般の重みの射で、同値な添字による制限の場合だけの極限比較の法則を誤用しないための法則。
初回はSheaves内のPresheafという略記をその名前空間の外で使ったためエラーになった。
未知名はautoImplicit falseで検出された。一般の元の係数の型を明示し、頂点の等式も
既存の全射影の等式から直接評価する形で通った。初回の後続whnfはこの型エラーに続くもの。
計算上限は上げていない。既存構成の法則（200行未満、追加IDなし）。

#### 外枠の現物による保守的な確認

全306本の同時import検証用の一覧から、現物の物理行を再採取した。
現物19,517行、撤回した重複46行と承認済み3本文で削った7行を控除せず加え、
**外枠用には19,570行**を採用する。
証拠：`/tmp/is-w1/s8-all-branch-import-audit-2/cap-inventory.json`。
以前の累計に今回48行を加えた19,479行とは91行差がある。過少計上を避け、今回から
上記の現物による大きい方を正とする。引用属性・docstringだけの変更の除外を
この現物の上限には再適用していない。91行の差の個々の由来の照合は未完であり、
引用属性だけが原因と確定したものではない。

#### 残りの見込み（元の型を保持）

| 残り | 行数の見込み |
| --- | ---: |
| 固定されたweightedSections_discrete_map：下の(A)〜(C) | 1,000〜1,650 |
| 実際のČech対角の全族と定値錐・余極限の反転の接続 | 380〜650 |
| 元の任意係数Eでのsections_localEquiv_isoと必要な宇宙移送 | 350〜600 |
| 元のordinary層化単位との比較、同じ反射の全関手と指定単位の比較 | 550〜950 |
| 元の一般Coverage判定（普遍降下性を追加入力にしない） | 450〜800 |
| **残り計** | **2,730〜4,650** |
| **現物による外枠用19,570行との計** | **22,300〜24,220** |

固定された比較の残りを次のように分けて見積もった（重複なし）。

(A) 同じ指定余単位を保つ既存の大域Kan比較の成分を、指定輸送錐の標準極限比較に照合する
法則（350〜550行）。一般の同じδ、同じ係数O、α : δ ≫ F ⇒ O、β : δ ≫ G ⇒ O、
η : FunctorIso F G、ηの元のhom_fac、両指定輸送tF・tGの極限性を入力として、型は

```lean
eqToHom (congrArg HomotopyCategory.mk tF.cone_vertex.symm) ≫
  (limitVertexIso tF.cone tG.cone htF htG).hom ≫
    eqToHom (congrArg HomotopyCategory.mk tG.cone_vertex) =
      functorHomEvaluate η.hom v
```

を示すもの。新しいηを点ごとに組み立てず、既存のrightKanHomUniversalIso・hom_facを使う。
htF・htGは元のKan延長から供給する。現在のconeFamily_isoは同型の存在を返すが、
この式の頂点射とηの成分との一致は結論に含んでいない。可換三角形だけでこの法則を
供給済みと数えることはできない。

(B) 元の指定形状同型・係数移送からleft全空間・要素の圏までの同じ比較を、重みの射φに
沿う族で照合する（400〜650行）。ここで必要なのは、既存のG8の全族比較と、今回の同じ
指定輸送錐との比較であり、形状同型の自然性を追加入力に置かない。

(C) 埋め込みの頂点等式の移送と同じ切断射の射影を合わせ、最後の固定された四角形を閉じる
（250〜450行）。型は元のdraftsどおり

```lean
homMk (weighted_sections_edge φ) ≫ (weightedSections_discrete O hE P hP).hom =
  (weightedSections_discrete O hE Q hQ).hom ≫ homMk (sectionsOf_map φ O hP hQ)
```

という向き（weighted_sections_edgeは元の同じ全関手によるφの像の辺の略記）。
今回の可換三角形は、選んだ中間極限を消す部分までで、(A)〜(C)の全族比較自体を完成していない。
元の固定比較の見込みの上端1,710行を単に使い切った残りと扱うと、未着手の指定余単位の
成分照合を小さく見積もるため、残った主張ごとに上の内訳へ出し直した。

**上端24,220行が外枠24,000行を220行超える見込みになったため、検証済みを保存してLeanの追加を止める。**
下端の見込みに寄せて未証明部分を省略することはしない。これは完成の停止点ではない。
S7・R2・R3は再開しない。mainも取り込んでいない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


#### 保存前の全追加モジュールの統合検証

全306本を同時にimportする対象ビルドと、採取し直した1,640所有宣言の小監査が完了した。
監視プロセス終了コード0、成功JSON、全対象SHA一致、標準三公理のみを確認。
証拠：`/tmp/is-w1/s8-all-branch-import-audit-2/target-audit-result.json`、
`catalog-after.json`、`audit-after.log`。rootビルドやroot監査ではなく当レーンの対象検証であり、
mainの取り込みも行っていない。承認された3本文以外の既存の数学的宣言は変更していない。
停止中R2の4下書きは未変更・未検証・コミット対象外。
以上の検証済みを保存し、前記の外枠の停止条件に従ってLeanの追加を止める。
5∞-1の完成ではなく、未完はS1とS8。再開時は(A)の指定余単位と成分の照合から。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：外枠26,000行の承認を受けた再開

調整役・ユーザー承認6d2c4d4abを会話で受領。mainは取り込まず、S1・S8の元の型と
上の残りの一覧で再開する。外枠26,000行、約24,000行で止まらずに中間報告。
出発点の保守的な累計19,570行、残り2,730〜4,650行、全体22,300〜24,220行。
最初は(A)の同じ指定輸送の頂点成分を固定する。既存構成の法則として型を記録し、
計算上限は変えない。S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-16：指定右Kan輸送の脚・頂点・標準形状の法則の検証

追加11本・598行・29所有宣言の対象ビルドと小監査が完了（終了コード0、標準三公理のみ、
全対象SHA一致）。証拠：`/tmp/is-w1/s8-right-kan-factorization-8/target-audit-result.json`。
外枠用累計は **20,168行・317本**。既存の構成の法則・証明分割で追加IDなし、各法則200行未満。
既存の数学的宣言は変更せず、新規ファイルだけに置いた。

| 新規ファイル | 行数 | 内容 |
| --- | ---: | --- |
| ConeApexEvaluationVertex | 36 | 同じ全錐の頂点評価とjoin錐の頂点の等式 |
| RightKanTransportApex | 51 | 元の指定輸送の辺は頂点で同じ定値辺 |
| RightKanTransportApexHom | 67 | 元の輸送の頂点射は同じ頂点等式の射 |
| CoreCoconeLegHom | 35 | 任意の余錐の射についての脚と頂点射影の合成則 |
| TransportBaseTargetLeg | 98 | 既存の輸送終点の比較が元の脚を保つ法則（基底の辺の類での比較も含む） |
| TransportEndIsoFactorization | 82 | 元の二つの辺との因子分解式を持つ同じ終点比較 |
| LimitConeFamilyProjection | 54 | 錐の関手圏の比較射と、元の標準極限比較の頂点射との照合 |
| CocartesianTypedComposition | 49 | 既存の型つき辺の合成でのcocartesian性の法則 |
| ConeFamilyApexEvaluation | 35 | 錐のfiberの頂点射影と同じ全錐の評価の厳密な一致 |
| RightKanCanonicalShapeLaws | 44 | 元の標準錐の内部の同じ形状写像と、その両因子への制限 |
| RightKanCanonicalRestriction | 47 | 同じ標準形状による前合成と、図式側・頂点側の照合 |

以下でHoは元のhoFunctor、mkはその対象の構成子、qはconeApexEvaluation、
πは元のsliceの頂点射影。全て実ソースで模型・宇宙を明示している。

```lean
coneApexEvaluation_vertex d :
  (coneApexEvaluation K X).app _ (functorVertex d.val) = d.vertex
RightKanConeTransport.apex_edge_eq_constant t :
  (t.edge.map ((truncation 2).map (coneApexEvaluation (rightKanShape δ c) D))).edge =
    PinchedHom.constant (rightKanCanonicalCone δ F c).vertex 1
RightKanConeTransport.apex_hom t :
  (Ho.map q).toFunctor.map (homMk t.edge) ≫
    eqToHom (congrArg mk ((coneApexEvaluation_vertex t.cone).trans t.cone_vertex)) =
  eqToHom (congrArg mk ((coneApexEvaluation_vertex (rightKanCanonicalCone δ F c)).trans
    (rightKanCanonicalCone_vertex δ F c)))
JoinCocone.leg_comp_projection_hom c d m i :
  homMk (c.leg i) ≫ (Ho.map π).toFunctor.map m = homMk (d.leg i)
```

TransportBaseTargetLegの型は次の通り。
V := transportBaseFiber a p b、J := Vから元のsliceUnder aへの既存の包含、
T := transportBaseFiberTarget a p b、ι := vertexFiberι p bとすると、

```lean
transportBaseFiberTarget_leg_comp_projection a p b v w m :
  homMk (JoinCocone.leg (J.app _ v) (𝟙 Δ[0])) ≫
    (Ho.map ι).toFunctor.map ((Ho.map T).toFunctor.map m) =
      homMk (JoinCocone.leg (J.app _ w) (𝟙 Δ[0]))
transportBaseFiberTargetIso_leg_comp_projection a p b v w e :
  homMk (JoinCocone.leg (J.app _ v) (𝟙 Δ[0])) ≫
    (Ho.map ι).toFunctor.map (transportBaseFiberTargetIso a p b v w e).hom =
      homMk (JoinCocone.leg (J.app _ w) (𝟙 Δ[0]))
```

3つ目の法則は、元の基底のcoslice fiberの辺の類が等しいという入力から、
上の合成式を持つ同じ終点比較同型eの存在を得る。新たな同型の構成にはしていない。
これを元の辺e・fへ戻した型は、元のexists_kanTransportEndVertexIso_of_homMk_eqと
同じ入力に全空間Eのquasicategory性を明示した上で、結論を

```lean
∃ (v w : (vertexFiber p b) _⦋0⦌) (hv : v.val = y) (hw : w.val = z)
  (i : VertexIso v w),
  homMk e ≫ eqToHom (congrArg mk hv.symm) ≫
    (Ho.map (vertexFiberι p b)).toFunctor.map i.hom ≫
      eqToHom (congrArg mk hw) = homMk f
```

とする。元の持ち上げ空間の比較同型そのものを選び、cosliceの脚の法則を適用した。
標準極限比較へ戻す法則は、Φ := sliceConeFamilyMap p、A := coneFamilyApex pとして、

```lean
sliceConeFamilyMap_apex_vertex c : A.app _ (Φ.app _ c) = c.vertex
limitVertexIso_coneFamily_projection c d hc hd m :
  (Ho.map A).toFunctor.map m ≫ eqToHom (congrArg mk (sliceConeFamilyMap_apex_vertex d)) =
    eqToHom (congrArg mk (sliceConeFamilyMap_apex_vertex c)) ≫ (limitVertexIso c d hc hd).hom
hasCocartesianHornLifting_comp p e f he hf : HasCocartesianHornLifting p (e.comp f)
coneFamilyApex_eq_evaluation p :
  coneFamilyApex p = vertexFiberι (coneRestriction K X) (functorVertex p) ≫
    coneApexEvaluation K X
```

最後の標準形状q₀ := rightKanCanonicalShape δ cは元のrightKanCanonicalConeの本文の
同じsliceUnderUncurryを名前にしただけで、選択は追加していない。

```lean
rightKanCanonicalShape_inr δ c : joinInr Δ[0] _ ≫ q₀ = rightKanProjection δ c ≫ δ
rightKanCanonicalShape_inl δ c : joinInl Δ[0] _ ≫ q₀ = SSet.yonedaEquiv.symm c
rightKanCanonicalCone_val δ F c : (rightKanCanonicalCone δ F c).val = q₀ ≫ F
rightKanCanonicalShape_precomposition δ c :
  (pre q₀).app D ≫ (pre (joinInr Δ[0] _)).app D =
    (pre δ).app D ≫ (pre (rightKanProjection δ c)).app D
rightKanCanonicalShape_apex δ c : q₀.app _ ((joinInl Δ[0] _).app _ (stdSimplex.obj₀Equiv.symm 0)) = c
```

検証の初期候補は、頂点の定義上の一致、余錐のSubtypeでの脚の記法、ホモトピー圏のmkの
略記などで不一致になった。既存の評価補題・Yonedaの後合成・Fin 1の一意性を使い、
模型・端点・既存関数を明示して修正した。依存した型を壊す関手の書き換えは、
既存の関手等式の自然性で置き換えた。等式の射の相殺はeqToHom_trans_assocを使用。
計算上限は一切上げていない。未検証の厳密な基底の特殊版TransportTargetLegは不要となり、
`/tmp/is-w1/unverified-strict-transport-leg/`に保全して本体配下から外した（未検証・未コミット）。

**残る(A)は、元の大域比較を同じ標準形状で前合成し、そのhom_facを上の因子分解式へ渡す部分。**
全二胞体の標準頂点での評価の46行の下書きは現在検証中で、今回の保存には含めない。
S8の固定された射の自然性やS1を完成したという報告ではない。
(A)の基礎法則が見込み350〜550行に対して598行になったため、残る(A)を350〜650行、
(B)400〜650行、(C)250〜450行、他の4行は前表のまま（計1,730〜3,000行）として、
現時点の全体を **22,898〜24,918行**と見積もり直す。検証中46行は残る(A)に含め、二重計上しない。
外枠26,000行の中。約24,000行での中間報告を保持する。
mainは取り込まず、S7・R2・R3も再開していない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 再開後の(A)の残りの型（検証待ちの下書き）

以下7本・約500行（現在の作業木。未検証・未コミット）の型を記録する。
いずれも既存の構成の前合成・係数移送・自然性・合成の法則または証明分割であり、追加IDなし。
各宣言200行未満。検証済みの20,168行・317本にはまだ加えていない。
以下ではq := rightKanCanonicalShape δ c、j := joinInr Δ[0] (rightKanShape δ c)、
π := rightKanProjection δ c、P := coneRestriction (rightKanShape δ c) Dと略す。

1. `RightKanCanonicalHomEvaluation` の `rightKanCanonicalShape_hom_apex`：全二胞体ηの
   同じ標準錐による前合成を、元の指定頂点で評価する。

```lean
functorHomEvaluate ((Ho.map ((pre q).app D)).toFunctor.map η) apex ≫
  eqToHom (congrArg (fun x => mk (G.app _ x)) (rightKanCanonicalShape_apex δ c)) =
  eqToHom (congrArg (fun x => mk (F.app _ x)) (rightKanCanonicalShape_apex δ c)) ≫
    functorHomEvaluate η c
```

実ソースではfunctorHomEvaluateのU・Vをq ≫ F・q ≫ Gとして明示し、mkの模型もDに固定する。
2. `RightKanCanonicalHomRestriction` の `rightKanCanonicalShape_hom_restriction`：
   hF : j ≫ (q ≫ F) = π ≫ (δ ≫ F)、hGも同様とし、型は

```lean
kanFunctorHomCongr hF hG
  ((Ho.map ((pre j).app D)).toFunctor.map
    ((Ho.map ((pre q).app D)).toFunctor.map η)) =
  (Ho.map ((pre π).app D)).toFunctor.map
    ((Ho.map ((pre δ).app D)).toFunctor.map η)
```

3. `RightKanTransportDiagramHom` の `RightKanConeTransport.diagram_hom`：
   t : RightKanConeTransport δ O F α cに対し、元のdiagram条件を二胞体の類として評価する。

```lean
kanFunctorHomCongr (rightKanCanonicalCone δ F c).property t.cone.property
  ((Ho.map P).toFunctor.map (homMk t.edge)) =
    (Ho.map ((pre π).app D)).toFunctor.map (homMk (functorEdgeOfSimplicialHomotopy α))
```

4. `RightKanTransportCounitRestriction` の `rightKanTransport_counit_restriction`：
   η : FunctorHom F G、hη : rightKanHomMap δ [β] F η = [α]、s : RightKanConeTransport δ O G β c、
   ηq := (Ho.map ((pre q).app D)).toFunctor.map ηとして、型は

```lean
kanFunctorHomCongr (rightKanCanonicalCone δ F c).property s.cone.property
  ((Ho.map P).toFunctor.map (ηq ≫ homMk s.edge)) =
    (Ho.map ((pre π).app D)).toFunctor.map [α]
```

[α]・[β]は元の指定ホモトピーをfunctorEdgeOfSimplicialHomotopyで辺にして取るhomMk。
hηは既存の大域Kan比較のhom_facから入れる入力であり、自然性を新たに仮定する最終定理ではない。
5. `RightKanTransportComparisonFactorization` の `rightKanTransport_comparison_factorization`：
   ηをFunctorIso F Gとし、同じhη、t・sの両指定輸送に対して、型は

```lean
∃ i : VertexIso (coneFamilyVertexEquiv _ t.cone) (coneFamilyVertexEquiv _ s.cone),
  homMk t.edge ≫ (Ho.map (vertexFiberι P (functorVertex (rightKanDiagram δ O c)))).toFunctor.map i.hom =
    (Ho.map ((pre q).app D)).toFunctor.map η.hom ≫ homMk s.edge
```

既存のηの前合成の辺代表、同じs.edgeとの合成、既存の終点比較の因子分解式を使う。
新しい大域関手や、その同型を点ごとに組み立てる構成にはしていない。
6. `LimitConeFamilyProjectionArrow` の `limitVertexIso_coneFamily_arrow`：
   c₁・c₂は同じ図式pの指定極限錐、mはconeFamilyVertexEquiv p c₁からc₂への任意の射として、

```lean
Arrow.mk ((Ho.map (coneFamilyApex p)).toFunctor.map m) =
  Arrow.mk (limitVertexIso c₁ c₂ hc₁ hc₂).hom
```

7. `RightKanTransportComparisonVertex` の `rightKanTransport_comparison_vertex`：
   上のη・hη・t・sに元の両錐の極限性ht・hsを追加し、(A)の元の型そのものを結論にする。

```lean
eqToHom (congrArg mk t.cone_vertex.symm) ≫
  (limitVertexIso t.cone s.cone ht hs).hom ≫ eqToHom (congrArg mk s.cone_vertex) =
    functorHomEvaluate η.hom c
```

7のprivateな正方形の正規化の法則は、通常の圏でf≫b.hom=a.hom、g≫d.hom=c.hom、
f≫μ=ν≫gのとき、b.inv≫μ≫d.hom=a.inv≫ν≫c.homを結論にする。前後の4つは指定同型。
既存の同型の消去と結合則だけを使う。

この段階の(A)は同じ添字写像δに関する法則。(B)で元の指定添字同型・分類・底変換へ戻す際は、
既存のrightKanHomUniversalIso・hom_facと同じ指定余単位を使う。
RightKanHomUniversal.indexIsoのπ₀の結論を、未証明の点ごとの右Kan条件として流用しない。
そのため、(B)には指定した点ごとの比較と余単位の両立の照合が依然残る。
元のweightedSections_discrete_map・一般の局所同値・同じ層化比較・S1の完成は未完。
S7・R2・R3を再開せず、mainも取り込んでいない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### (A)の基礎4本を検証・保存（11-17 未明）

前節の1・2・3・6（RightKanCanonicalHomEvaluation、RightKanCanonicalHomRestriction、
RightKanTransportDiagramHom、LimitConeFamilyProjectionArrow）の4本・203行・10所有宣言の
対象ビルドと小監査が完了した。基礎段の監視子プロセス終了コード0、成功JSON、全対象SHA一致、
標準三公理のみ。証拠：`/tmp/is-w1/s8-right-kan-comparison-2/primitive/target-audit-result.json`・
`process-result.json`。一回の鍵で基礎段を監査してから後段へ進む方式で、鍵は編集時には保持しない。
後段はRightKanTransportCounitRestrictionの書き換えに失敗し、組全体の終了コードは1。
組全体の成功とは扱わず、通った基礎4本だけを保存する。

主な修正は、頂点評価のletと前合成する全関手を明示したこと、
最後の二つの等式の射をeqToHom_transで相殺したこと、
元のHoFunctorでの辺の像をSSet.mapHomotopyCategoryと既存の辺の写像の法則で表示したこと、
実在するeqToHom_mapを使ってArrow上の端点移送を消したこと。
主張の型・範囲、既存の宣言、計算上限は変えていない。
全て既存構成の法則・証明分割、各200行未満、追加IDなし。
外枠用累計は **20,371行・321本**。
後段の同じ制限写像の別名coneRestrictionを明示して再検証を続ける。
(A)の最終成分照合、S8全体、S1は依然未完。S7・R2・R3は再開せず、mainも取り込まない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


#### (A)の末尾に接続する既存構成の法則の型（未検証）

8. `RightKanGlobalComparisonVertex` の `kanRightKanExtensionIso_transport_vertex`：
   同じδに沿う元の二つのKan延長hα・hβ、任意の指定輸送t・sから、上の7と同じ式を
   η := kanRightKanExtensionIso δ α β hα hβについて結論にする。
   t・sの極限性はisRightKanExtension_iff_forall_transportから証明し、
   hηはkanRightKanExtensionIso_hom_facから供給する。点ごとの同型で大域比較を作らない。

```lean
-- ht・hsは元のKan条件から証明した同じ輸送錐の極限性。
eqToHom (congrArg mk t.cone_vertex.symm) ≫
  (limitVertexIso t.cone s.cone ht hs).hom ≫ eqToHom (congrArg mk s.cone_vertex) =
    functorHomEvaluate (kanRightKanExtensionIso δ α β hα hβ).hom c
```

9. `RightKanFunctorIsoTransfer` の `isRightKanExtension_of_compatible_functorIso`：
   同じ指定余単位の類との両立を持つ元の全関手同型に沿い、実際のKan条件を移す。

```lean
(α : SSet.Homotopy (δ ≫ F) O) → (β : SSet.Homotopy (δ ≫ G) O) →
(η : FunctorIso F G) →
(rightKanHomMap δ [β] F η.hom = [α]) →
IsRightKanExtension δ O F α → IsRightKanExtension δ O G β
```

証明案は、元のKan延長からtとその極限性を取り、G側の任意の輸送sと上の5の比較iを使い、
実際のconeFamily内で終対象性を移すもの。RightKanHomUniversalを点ごとのKan条件と
見なす証明にはしていない。この2本も既存構成の法則・証明分割で、追加IDなし、200行未満。
現在は未検証・未コミットであり、検証済みの累計は20,371行・321本のまま。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 11-17 未明：(B)で使う指定unstraightening比較の仕様の照合（紙）

(A)の対象検証を一枚の整理券で待つ間に、(B)の元の比較を展開した。
`smallLeftUnstraighteningComparisonOfFunctorIso η` は
`(exists_smallLeftUnstraighteningComparison_of_functorIso η).choose` である。
存在の命題の結論にはηの射との両立がなく、F・G・底上の射影と前合成同値性だけがある。
したがって同じF・Gに対するη・η′の選択の違いは、その命題の証明の違いにしか現れない。
proof irrelevanceによる次の二つのrfl検査を一時ファイルに用意した（この追記時点では未実行）。

```lean
-- Bは準圏、F G : ulift B ⟶ SpaceInfinity、e e' : FunctorIso F G。
smallLeftUnstraighteningComparisonOfFunctorIso e =
  smallLeftUnstraighteningComparisonOfFunctorIso e'

-- K・C・Dは準圏、e e' : FunctorIso δ δ'、c・dは同じ指定局所極限錐。
rightKanLimitVertexIsoOfFunctorIso e O v c d hc hd =
  rightKanLimitVertexIsoOfFunctorIso e' O v c d hc hd
```

この点は「(A)の同じδに沿う比較」と「(B)の元の指定添字同型に沿う比較」を接続する際の問題。
任意のeについて、元の局所比較がeの指定余単位と両立することは、底上の同値の存在だけからは
導かない。固定したYoneda同型の場合に元の最終定理が偽だと判定したわけではない。
(A)の新しい法則はこの選択を使わず、そのまま対象検証を続けられる。

既存の射作用を使う差分案（まだ適用しない）：
`SmallLeftUnstraighteningFunctorIso.lean` に `SmallUnstraighteningIsoHom` をimportし、
次の三本文だけを置き換える。

```lean
smallLeftUnstraighteningComparisonOfFunctorIso η :=
  smallUnstraighteningFunctorHom η.hom

-- 同じ公開の射影の型の証明：
smallUnstraighteningFunctorHom_projection η.hom

-- 同じ公開の前合成同値性の型の証明：
smallUnstraighteningFunctorHom_isPrecompositionEquivalence η.hom
```

元の存在定理の証明だけの置換ではproof irrelevanceによる消去を避けられないので、
データの定義の本文を変える必要がある。公開の名前・型・仮定は変えない。
既存構成の射作用とその射影・同値性を再利用し、分類や局所同型を新しく作らない。
静的なimport閉包884本の照合で、この追加importから元ファイルへの循環はなかった。
差分案は `/tmp/is-w1/s8-index-comparison-choice-check/proposed-body-change.diff`、
一時検査は同ディレクトリの `check.lean`。差分は+4/-3行、docstringの説明の修正は別途必要。
既存本文の変更なので、適用には指示書§2の例外の承認が必要。
承認された場合、同じ余単位を保つ比較の法則を引き続き証明し、変更した全Sheavesと
枝の下流の対象ビルド・小監査・公開型の保存比較を行う。旧選択とのrfl一致は要求しない案。

検証済み累計は20,371行・321本のまま。未検証の(A)5本393行を混ぜて数えていない。
S1・S8は未完、S7・R2・R3は再開せず、mainも取り込まない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


#### 上の三本文の変更の承認（11-17 未明）

調整役の回答「3本文の変更を承認する」を受領した。
現在待っている(A)の対象と依存先を途中で変えず、その検証の終了後に適用する。
同じ一枚の整理券の検証用ランナーに、変更前の公開型・属性・公理の保存採取と上の診断を追加した。
Leanの対象・依存ソースは変更していない。変更後は公開の型・属性・公理の一致を照合する。
前に承認されたSheaves三本文とは別の変更であることを明示する。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### (A)の指定余単位の制限を検証・保存（11-17 未明）

`RightKanTransportCounitRestriction` 1本・67行・1所有宣言の対象ビルドと小監査が通った。
検証子の終了コード0、成功JSON、ソースSHA一致、標準三公理のみ。
証拠は `/tmp/is-w1/s8-right-kan-comparison-3/counit/`。
同じ組の後段は辺の端点の型推論に失敗したため、組全体の成功とはしない。
既存構成の辺と端点の等式を明示して、4本の後段の再検証を一枚の整理券で待っている。
外枠用の検証済み累計は **20,438行・322本**。

変更前のv3b採取は `/tmp/is-w1/s8-index-comparison-choice-check/before.json` に成功。
最初の診断は同じ環境に `SmallUnstraighteningIsoHom.olean` がなかったため、import段で終了1。
rflが通った・失敗したとは扱わない。旧選択だけの検査を `old-choice-only.lean` に分離し、
次の対象ビルドの前に実行する。承認された三本文は、今待つ検証の依存先でもあるためまだ適用していない。
S1・S8は未完。S7・R2・R3は再開せず、mainも取り込まない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


#### 三本文の承認差分の適用と、同じ余単位の類の代表の移送（11-17 未明）

次の整理券も待機中だったため、その開始前に承認差分を適用した。
SmallLeftUnstraighteningFunctorIsoの三本文と説明だけ、+8/-7行。
同じ指定同型ηの実際の射作用 `smallUnstraighteningFunctorHom η.hom` と、
その射影・同値性の既存補題を使う。新しい仮定や公開の型の変更はない。
旧oleanでの等式検査→新本文の対象ビルド→v3b採取・保存比較→(A)の検証、の順にした。
待機中の数学対象・その依存を実行途中で変更したわけではなく、検証は新しい本文の環境で行う。
まだビルド待ちなので、この差分を検証済みの累計・コミットには入れない。
差分の8挿入行を通過後に外枠へ加え、7削除行を返金しない方針。

10. `RightKanHomRepresentativeTransfer`（新規36行・未検証）は次の型の既存構成の法則。

```lean
(α : SSet.Homotopy (δ ≫ F) F₀) → (b : FunctorHom (δ ≫ G) F₀) →
(η : FunctorIso F G) →
(rightKanHomMap δ b F η.hom = homMk (functorEdgeOfSimplicialHomotopy α)) →
IsRightKanExtension δ F₀ F α →
IsRightKanExtension δ F₀ G (functorHomHomotopy b)
```

既存の代表 `functorHomHomotopy b` の類がbであることを
`functorHomHomotopy_hom`で書き換え、上の9を使うだけ。
(B)では b := ((fixedOppositeSetYoneda_nativeIso C).postcomp G).hom ≫ [β] として、
元の `weightedSections_nativeShape_comparison_hom_fac` から入力する。
実際のKan条件は元のweightedSectionsのKan条件とこの移送で証明し、
`RightKanHomUniversal.indexIso` のπ₀の条件を点ごとのKan条件に読み替えない。
分類・底変換の同じ比較との一致は、この補題だけでは完了しない。
200行未満の既存構成の法則、追加IDなし。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


#### 待ち時間の宇宙移送の法則（11-17 未明、未検証）

11. `NativeSheafUniverseLift`（新規47行）に、元の篩の全錐の二つの法則を書いた。
C : Type u、E : SSet u、F : nerve Cᵒᵖ ⟶ Eとして、型は

```lean
(JoinCone.ulift (nativeRestrictionCone F S)).val =
  (restrictionCone ((SSet.uliftFunctor.{u + 1, u}).map F) S).val

NativeIsSheaf J F ↔ IsSheaf J ((SSet.uliftFunctor.{u + 1, u}).map F)
```

前者は元の全射の等式、後者は既存の `isLimitCone_iff_ulift` と前者による錐の比較。
presentable性や極限の存在を仮定しない。200行未満の既存構成の法則、追加IDなし。
任意の係数のHomの宇宙を上げる際には、C′ := AsSmall.{u + 1} Cを使える。
元の形状とnerve C′ᵒᵖの同型は既存の `asSmallSiteShapeIso C`。
元のIsSheafを既存のAsSmallのNativeIsSheafへ送り、その同じ全被覆錐をこの法則で持ち上げる案。
この法則だけをもって、任意の係数の `sections_localEquiv_iso` が完成したとは扱わない。
現在の同じ一枚の整理券の後段に対象検証を入れた。検証済み累計は20,438行・322本のまま。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


12. `WeightedSectionsNativeRepresentative`（新規43行・未検証）は10の元の値への特殊化。

```lean
-- βは元のnativeShape射δ′に沿う指定右Kan延長の余単位、hβはそのKan条件。
let b := ((fixedOppositeSetYoneda_nativeIso C).postcomp G).hom ≫
  homMk (functorEdgeOfSimplicialHomotopy β)
IsRightKanExtension (oppositeSpaceYoneda C) O G (functorHomHomotopy b)
```

元の `weightedSections_nativeShape_comparison` とその `hom_fac`、
元の `weightedSections_isRightKanExtension` をそのまま10へ入れる。
点ごとの同型の組み立てやHom普遍性を仮定に置く証明ではない。
同じ指定局所比較との一致は別途残る。既存構成の法則、200行未満、追加IDなし。
同じ一枚の整理券の最後に対象検証を入れた。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


13. `WeightedSectionsGlobalComparisonVertex`（新規60行・未検証）は(A)を元の全比較へ特殊化する。
bは上の12の同じ合成、t := weightedSections_valueTransport O hE P、
sはbの既存代表に沿う任意のRightKanConeTransportとして、型は

```lean
eqToHom (congrArg mk t.cone_vertex.symm) ≫
  (limitVertexIso t.cone s.cone ht hs).hom ≫ eqToHom (congrArg mk s.cone_vertex) =
  functorHomEvaluate (weightedSections_nativeShape_comparison O hE β hβ).hom P
```

htは元のweightedSections_valueTransportの極限性、hsは12と
isRightKanExtension_iff_forall_transportで証明する。
同じ大域比較の成分・元のtの選択・同じ指定余単位の類を保つ。
既存構成の自然性の法則、200行未満、追加IDなし。元の添字同型に沿う局所比較との照合は依然残る。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


14. `WitnessPointedDiagramIso`（新規53行・未検証）の型は、同じ表現空間の頂点同型hについて

```lean
kanFunctorHomCongr R.pointedMap_projection S.pointedMap_projection
  ((Ho.map ((ihom E).map pointedSpaceProjection)).toFunctor.map (R.pointedIso S h).hom) =
  (Ho.map ((pre p).app SpaceInfinity)).toFunctor.map (R.diagramIso S h).hom
```

既存の `transportWitnessDiagram_condition` を同じhの射へ適用する法則。
二つの同型を独立に選ばず、同じ族の二射影を同時に保持する。
端点の移送はArrow上で消去し、既存の同じ射影の等式からHomの等式を回収する案。
新しい分類の存在・一意性の定理ではなく、既存構成の射影・係数移送の法則、追加IDなし。
この法則から元の分類・復元の選択へ戻す比較は、なお(B)に残る。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 承認された三本文の置換の対象検証・保存比較（11-17 未明）

`SmallLeftUnstraighteningFunctorIso` の置換後の対象ビルドが終了0。
同じモジュールの旧・新のv3b採取を行い、8宣言すべてについて kind・公開型・属性・公理が一致した。
証明の内部行の除外は0、標準三公理のみ。データの本文の変更は承認された
smallLeftUnstraighteningComparisonOfFunctorIsoだけ。承認された二つの証明の本文は公理・型とも一致。
ソースSHAも一致。証拠：`/tmp/is-w1/s8-index-comparison-choice-check/` の
`replacement-build-result.json`・`before.json`・`after.json`・`preservation-result.json`。
このモジュール単体の検証済み差分として保存する。直接importer13本と既存Sheaves165本の
対象再ビルド・小監査は別の一枚の整理券で待っており、まだ統合検証済みとはしない。

最初の旧選択だけの診断は、後半の単体記法のscope不足で終了1。
診断全体が成功したとは扱わない。旧本文の式そのものを独立の一時補題に写したrfl検査と、
新本文が指定η.homの既存射作用であるrfl検査を用意し、次の対象再ビルドの先頭で行う。
新たな本体の検査補題は追加しない。

(A)の因子分解は端点の明示で進み、右単位の相殺だけが残ったためCategory.comp_idを明示した。
この因子分解とその後段、宇宙移送、元の全比較への特殊化はまだ未検証。
今回の本文差分8挿入行を加え、7削除行は返金せず、外枠用の検証済み累計は
**20,446行・新規322本＋承認された既存1本の本文差分**。
S1・S8は未完。S7・R2・R3は再開せず、mainも取り込まない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 直接importerの再ビルドでの既存証明の簡約深さ（11-17 未明）

`/tmp/is-w1/s8-right-kan-comparison-5/` の検証で、旧本文の式の独立性と新本文の指定射のrfl検査は
両方終了0・標準三公理のみ。新しい実装の検査を、旧compiled環境の二つ目の検査と混同しない。
今回通った旧側は、保存した旧本文の `Classical.choose (exists_… η)` という式そのもの。

直接importer13本の組は7100ジョブのうち一つ、既存の
`DensityFiberYonedaValue.lean:47` の `presheafElementsYonedaSliceValue_interval` の末尾の
`rfl` で `maximum recursion depth has been reached`、終了1。
記録：同ディレクトリの `direct-importers.log`・`direct-importers-result.json`。
計算上限は上げていない。既存Sheavesの統合再検証や新規補題の段は、この組ではまだ実行されていない。

元の証明は二つのrwの後、全体の定義上の比較をrflへ任せていた。
`presheafElementsYonedaSliceInterval` の定義は同じMappingと同じ区間比較の合成なので、
次の既存の定義二つと既証の等式・結合則だけに展開を局所化する差分案を用意した。

```lean
-- 主張の型・名前は同じ。以下だけへ証明を置換する案。
rw [presheafElementsYonedaSliceValue, yonedaPresheafEvaluation_interval,
  presheafElementsYonedaSliceInterval, Category.assoc]
```

前のrwとrflの2行をこのrwの2行にするだけ。新しい定理、構成、仮定、計算上限は置かない。
一時ファイル `/tmp/is-w1/s8-density-value-local-proof/check.lean` に同じ型の検査を用意した。
本体の既存証明はまだ変更していない。§2.1の例外として、この一証明の局所化の承認が必要。
承認時は公開型・属性・公理の保存比較と、同じ直接importer・Sheaves・枝の下流を再検証する。
S1・S8は未完。検証済み累計20,446行のまま。mainを取り込まず、S7・R2・R3も再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


#### 一証明の局所化の承認と適用（11-17 未明）

調整役から承認（指示書追記430b0c87f）を受領した。
presheafElementsYonedaSliceValue_intervalの証明2行だけを、上記の指定rwの2行に置き換えた。
主張の型・名前、他の既存の本文、maxRecDepth・heartbeatsは変更していない。
同じ一枚の待機中の整理券の先頭へ、DensityFiberYonedaValueと直接のimporter
DensityCanonicalValueCriterionの対象ビルド・小監査を追加した。
その通過後に(A)と依存する宇宙移送・元の大域比較への特殊化を検証する。
旧証明の全文は `/tmp/is-w1/s8-density-value-local-proof/before-source.lean` に保存した。
旧モジュールのoleanは失敗後に存在しないため、この一証明について旧compiled環境との
完全なv3b前後比較が得られたとは扱わない。公開の型・名前・属性は、承認差分が証明2行だけで
あるソース比較で保持を確認し、新しい環境の公理は小監査で確認する。
承認されたSmallLeftUnstraighteningFunctorIsoの8宣言のv3b前後比較とは分けて記録する。
この差分もまだ検証前で、累計20,446行には未算入。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


15. `NativeSheafRepresentableCoefficients`（新規44行・未検証）の型は、
C : Type u、E : SSet uが準圏、F : nerve Cᵒᵖ ⟶ Eとして

```lean
NativeIsSheaf J F → ∀ x : E _⦋0⦌,
  IsSheaf J ((SSet.uliftFunctor.{u + 1, u}).map F ≫ covariantRepresentableInfinity x)
```

11の元の全被覆錐の値の等式と、既存のcovariantRepresentableInfinity_isLimitを使う。
ULift Eの任意の大きな図式に対する極限保存を仮定せず、元の被覆錐自体を持ち上げて写す。
この違いで元の係数にpresentable性や宇宙を超える完全性を追加しない。
任意の係数への最終のsection射の比較・反映は未完。既存構成の係数移送の法則、追加IDなし。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 承認された一証明と、指定比較の因子分解・係数移送の検証（11-17 未明）

次の各段の対象ビルド・小監査が終了0、成功JSON、ソースSHA一致、標準三公理のみ。
証拠は `/tmp/is-w1/s8-right-kan-comparison-6/` の各段のtarget-audit-result.json・process-result.json。

- density：DensityFiberYonedaValueと直接のimporter DensityCanonicalValueCriterion、2本・6所有宣言。
  主張・名前・属性を含む元のソースは、承認された証明2行以外に変更がないことを保存ソースと照合した。
  計算上限は変更しない。
- factor：RightKanTransportComparisonFactorization、1本・135行・1所有宣言。
- transfer：RightKanFunctorIsoTransfer・RightKanHomRepresentativeTransfer、2本・79行・3所有宣言。

新規3本214行と承認された既存証明の2挿入行を外枠に加え、削除2行は返金しない。
外枠用の検証済み累計は **20,662行・新規325本＋承認された既存2本の差分**。

一時ファイルの局所化の検査は、implicit transparencyの下での型の表示の不一致により終了1。
これを成功とは扱わない。実際の元のモジュールでは承認どおりの証明が対象ビルドを通り、
その直接のimporterも同じ新しい環境で通り、全6宣言を小監査したことを正本の検証結果とする。
旧compiled環境とのv3b前後比較が得られたとは主張しない。

vertex段は新規RightKanTransportComparisonVertexの最後の評価の表示をそろえるsimpaで失敗。
同じ関数functorHomEvaluateを目標側にも展開する法則を明示して再検証する。
universe段は依存の再コンパイル中に外側の280秒のguardで終了124。
kernelの時間切れではなく、計算上限を上げたわけでもない。
witness・nativeRep・nativeVertexはこの組では未検証。組全体を成功とはしない。

次は短い独立の検査を先にし、その後に直接importer13本と既存Sheaves165本の統合再検証を
一枚の整理券で行う（外側guardは15分、一回30分以内の規則内。数学の計算上限は同じ）。
S1・S8は未完。mainは取り込まず、S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### (A)の成分照合と、元の全比較・表現可能係数への接続を検証（11-17 未明）

`/tmp/is-w1/s8-right-kan-comparison-7/` で次の4段が対象ビルド・小監査の終了0。
各段の成功JSON・全対象SHA一致・標準三公理のみを確認した。

- vertex：RightKanTransportComparisonVertex・RightKanGlobalComparisonVertex、2本・153行・3所有宣言。
  元の同じδに沿う(A)の型を、既存の大域Kan比較・hom_facから閉じた。
  大域同型を点ごとの同型で組み立てず、同じ余単位の輸送を使う。
- universe：NativeSheafUniverseLift・NativeSheafRepresentableCoefficients、2本・91行・3所有宣言。
  元の被覆錐全体の宇宙移送と、共変表現可能係数への保存。presentable性は追加しない。
- nativeRep：WeightedSectionsNativeRepresentative、1本・43行・1所有宣言。
  元の大域Hom比較のhom_facから、元の射に沿う指定余単位の類の実際のKan条件を証明。
- nativeVertex：WeightedSectionsGlobalComparisonVertex、1本・60行・1所有宣言。
  元のweightedSections_nativeShape_comparisonの成分を、元のvalueTransportの標準比較へ特殊化。

新規6本・347行の検証済み差分を保存する。外枠用累計は **21,009行・新規331本＋承認された既存2本の差分**。
(A)は同じδの範囲で完成したが、(B)の元の指定添字同型・分類・復元の比較との一致は未完。
S8の元の固定離散値比較の自然性を、この段で完成したとは扱わない。

witness段の未検証53行は、主張の型のrawなHo射作用の推論で既定200,000heartbeatsのwhnfに到達した。
計算上限は上げず、既存のpostcomposeFunctorHom・precomposeFunctorHomで型を先に固定し、
前後合成の既存のeq_mapの法則で元の射作用へ戻す表示に直した（新規61行・未検証）。
これは元の二射影の射そのものを保持する表示の変更で、仮定・結論を弱めるものではない。
同じ元の射への等式は既存のLeftKanHomMapPostcomposition等の法則を使う。

組全体は、直接importer13本の再ビルド中に外側900秒のguardで終了124。
数学のkernel上限ではなく、scope段は未実行。直接importer・既存Sheavesの統合再検証は未完。
通った4段だけを保存し、組全体の成功とはしない。
次はpointedな法則の短い検証を先にし、直接importerと既存・追加Sheavesの再検証を続ける。
mainは取り込まず、S7・R2・R3は再開しない。S1・S8は依然未完。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 承認変更後の全Sheaves・直接importerとpointedな法則の統合検証（11-17 未明）

`/tmp/is-w1/s8-integration-after-designated-comparison-1/` の監視プロセスが終了0。
phase-results.jsonの全3段が0。各小監査の成功JSON・対象ソースのSHA一致、標準三公理のみを確認した。

- witness：WitnessPointedDiagramIso、1本・61行・1所有宣言。
  型付きの前後合成と明示的な端点・宇宙を使うことで、既定の計算上限で通った。
  元のrawな射作用へ戻す法則は既存のeq_mapを使い、射そのもの・仮定・結論は保持。
- scope：Sheaves全169本とSmallLeftUnstraighteningFunctorIsoの合計170本・1,012所有宣言。
  前に承認された値の選択の3本文、今回の指定ηの射作用の3本文、その下での全Sheavesを再検証した。
- direct-importers：SmallLeftUnstraighteningFunctorIsoの直接importer13本の対象ビルドが終了0。
  DensityFiberYonedaValueの承認された一証明の局所化後も含む。F1の入口も含めた対象であり、
  root全体のビルド・監査を行ったものではない。

承認された既存の本文以外は変更していない。maxRecDepth・heartbeatsも同じ。
mainは取り込んでいない。新規の入口・全体監査の登録は調整役に残す。
今回の61行を外枠に加え、検証済み累計は **21,070行・新規332本＋承認された既存2本の差分**。

残りは報告の(B)・(C)、Čechの局所同値、任意の係数への反映、同じ通常の層化との比較、S1の一般Coverage。
(B)では既存のRepresentationComparisonCoherence、StraighteningCounitRestriction・Naturality、
RepresentationEdgeComparisonの同じ表現空間内の比較を再利用する。
新しい独立の分類・単位を作るのでなく、元の指定比較に沿う法則として接続する。
S1・S8は未完。S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### (B)の元の分類比較の合成則（11-17 未明、未検証）

既存のRepresentationComparisonCoherenceのdiagramIso_trans・比較の一意性と、
RepresentationComparisonRestrictionの同じcartesian制限の法則を使う。
同じ主張を再実装せず、残る接続として次の二つの既存構成の法則を新規ファイルに書いた。

16. `NerveRepresentationComparisonLaw`（43行）の型：
p : E ⟶ nerve C、R・Sはulift pの実際の表現、aは同じ表現空間の指定頂点同型として、

```lean
nerveCoherentTransportRepresentationIso p R ≪≫ R.diagramIso S a =
  nerveCoherentTransportRepresentationIso p S
```

17. `StraighteningRepresentationComparisonLaw`（65行）の型：
p : E ⟶ B、R・S・aは同様、底Bは一般の小さい単体集合として、

```lean
leftStraighteningInfinityDiagram_representationIso p R ≪≫ R.diagramIso S a =
  leftStraighteningInfinityDiagram_representationIso p S
```

17の内部では、同じ初頂点の制限で元のpreimageVertexIsoをmap_preimageにより回収し、
同じcartesianRestrict_diagramIsoと16を使う。最後は既存のfunctorIso_precomp_injectiveで反映する。
KST/のファイルはimportせず、既存の一般の充満忠実性・制限のAPIを直接使う。
新しい分類・単位の存在定理を作らず、元の同じ指定比較の合成則を保つ。
いずれも200行未満、既存構成の法則・証明分割で追加IDなし。
一枚の整理券で順に対象ビルド・小監査を待っている。検証済み累計は21,070行のまま。
S1・S8は未完、mainは取り込まず、S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### nerve上の元の分類比較の合成則を検証（11-17 未明）

16のNerveRepresentationComparisonLaw 1本・43行・1所有宣言の対象ビルドと小監査が終了0。
成功JSON・対象SHA一致、標準三公理のみ。
証拠：`/tmp/is-w1/s8-representation-comparison-laws-1/nerve/`。
既存のdiagramIso_transと小さいfiberの表現比較の一意性を使った合成則であり、追加IDなし。
外枠用の検証済み累計は **21,113行・新規333本＋承認された既存2本の差分**。

同じ組の17は、初頂点での回収と制限を照合した後、nativeRestrictの別名のrwだけで失敗。
同じ既存の法則を明示的な引数で適用して再検証を待っている（65行、まだ未検証）。
組全体の成功とはせず16だけを保存する。S1・S8は未完。
mainを取り込まず、S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 一般の底での指定分類比較の合成則を検証（11-17 未明）

17のStraighteningRepresentationComparisonLaw（65行・1本・2所有宣言）の対象ビルドと小監査が終了0。
証拠：`/tmp/is-w1/s8-representation-comparison-laws-2/target-audit-result.json`。
対象SHA一致、標準三公理のみ。別名の展開を強めず、既存のnerve上の合成則を
明示的な引数で適用した。計算上限・既存の本文は変更しない。
外枠用の検証済み累計は **21,178行・新規334本＋承認された既存2本の差分**。
残る(B)は、同じ底変換の分類比較と復元比較を同じ余単位に沿って照合する法則。
点ごとの同型を集める構成は作らない。S1・S8は未完。
mainは取り込まず、S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 任意の係数への移送に使う要素圏の係数移送（11-17 未明、未検証）

`PresheafElementsSiteLift`に、AsSmall.down.opとULiftによる既存の係数移送を記述する。
型は `P.Elements ≌ (AsSmall.down.op ⋙ P ⋙ uliftFunctor).Elements`。
同じup/downであり、射影との厳密な一致と、任意のφに関する
`(siteLiftPresheafMap φ).mapElements ⋙ siteLiftElementsDown Q =
siteLiftElementsDown P ⋙ φ.mapElements`を保持する。
任意の模型の選択ではなく、既存の宇宙移送の法則として記録する（200行未満、追加IDなし）。
検証済み累計21,178行。S1・S8は未完。mainは取り込まず、S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 要素圏の同じ宇宙移送を検証（11-17 未明）

PresheafElementsSiteLiftは80行・1本・16所有宣言。
`/tmp/is-w1/s8-site-elements-lift-3/`の対象ビルド・小監査が終了0、成功JSON・SHA一致、標準三公理のみ。
初回と二回目はwhiskeringのimport・名前空間の不足で失敗し、既存Functor APIの明示で解消した。
元の要素・前層の射・射影を保つ同じ係数移送の法則で、追加IDなし。
検証済み累計 **21,258行・新規335本＋承認された既存2本の差分**。
次に、同じULiftが像篩・等化篩を保ち、局所全射・局所単射の条件を保存・反映する法則を記述する。
型は `IsLocallySurjective J (Functor.whiskerRight φ uliftFunctor) ↔ IsLocallySurjective J φ`
と同じIsLocallyInjective版。200行未満の係数移送として扱う。
S1・S8は未完。mainは取り込まず、S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 同じ局所同値の宇宙移送まで検証（11-17 未明）

- LocalBijectivityUniverseLift：79行・1本・4所有宣言。
  `/tmp/is-w1/s8-local-bijectivity-lift-3/`の対象ビルド・小監査が終了0。
  不在のimportを既存のElementsUniverseLiftに直し、逆向きでは指定した篩等式でgoalを直接rwした。
- SiteLiftLocalEquivalence：42行・1本・1所有宣言。
  `/tmp/is-w1/s8-site-local-equivalence-1/`の対象ビルド・小監査が終了0。
  型：`IsLocalEquivSet J φ → IsLocalEquivSet (AsSmall.down.inducedTopology J)
  (siteLiftPresheafMap φ)`。既存の同値siteの局所全単射性の保存と、
  同じULiftの像篩・等化篩の保存・反映を合成した。

両方とも成功JSON・対象SHA一致、標準三公理のみ。既存の本文・計算上限は変更しない。
既存構成の係数移送の法則で、200行未満、追加IDなし。
LocalBijectivityUniverseLiftの保存時には行数assertを80として79行で失敗したため、
直前のコミット6c35d20feにはLeanだけが入った。本節で検証証拠と実測79行を補記する。
外枠用の検証済み累計は **21,379行・新規337本＋承認された既存2本の差分**。
S8の同じ指定大域比較と局所比較の照合、Čechの局所同値、任意係数への反映、
同じ通常の層化との比較、S1の一般Coverageは未完。
mainは取り込まず、S7・R2・R3は再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 指定spanの制限同型の回収（11-17 未明、未検証）

(B)の調査で、既存LeftFibrationSpanStrictificationの証明中の相対同型hが、
結論の `∃ f, f ≫ q = p ∧ IsPrecompositionEquivalence f` では捨てられていることを確認した。
新規LeftFibrationSpanRestrictionWitnessは、その同じ証明の分割として
`∃ f hf, IsPrecompositionEquivalence f ∧ Nonempty (VertexIso
  ((relativeFunctorOverPre q (Over.homMk a ha)).app _ (relativeFunctorVertex q p f hf))
  (relativeFunctorVertex q r b hb))` を記述した（200行未満、追加IDなし）。
既存の本文は変更しない。この型の証明と、旧chooseがspanに関する引数を
選択条件に保持しないことの一時rfl検査を、一枚の整理券で検証する。
後者は元の最終定理の反例ではなく、選択条件の内容を確かめる検査である。
検証済み累計21,379行。S1・S8は未完。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


## 指定復元比較の選択条件についての判断依頼（11-17 未明）

一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 検証済みの証明分割と代案

- LeftFibrationSpanRestrictionWitness：49行・1本・1所有宣言。
  `/tmp/is-w1/s8-span-restriction-witness-2/`で対象ビルド・小監査が終了0。
  元の証明中の同じ相対同型hを保持する型が通った。旧chooseのspan引数に関する
  一時rfl検査も終了0。これは最終定理の反例の検査ではない。
- ScaffoldCoherentComparison：78行・1本・9所有宣言。
  `/tmp/is-w1/s8-scaffold-coherent-comparison-1/`で対象ビルド・小監査が終了0。
  既存のscaffoldTransportComparisonSpanをそのまま再利用し、新しい置換やspanは作らない。
  この同じspanのsource脚に沿う制限とtarget脚との相対同型を選択条件に含め、
  比較射・射影の等式・前合成同値性・指定制限同型を同時に得る。

両方とも成功JSON・対象SHA一致、標準三公理のみ。計算上限は同じ。
既存の本文は変更していない。検証済み累計は
**21,506行・新規339本＋承認された既存2本の差分**（今回127行）。

### 残る照合の型と、現在の選択条件で保持されないもの

(B)で使う同じ比較の法則は、適切なQuasicategory・LeftFibrationの仮定の下で

```lean
leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
  leftStraighteningInfinityDiagram_representationIso (pullback.snd p k)
    (R.nativeRestrict k) =
  (leftStraighteningInfinityDiagram_representationIso p R).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map k)
```

という元の指定同型の等式。任意の別の同型の存在では足りない。
元のrepresentationIsoは初頂点上のnerveLeftTransportRepresentationを経由し、
そのcomparisonはleftCoherentTransportDirectComparisonを使う。
この比較射は、底上の等式と前合成同値性だけを結論にした存在命題からchooseしている。
元のstrictificationの証明には同じspanに沿う相対同型hがあるが、公開の選択条件にはない。
今回の一時rfl検査は、同じp・qに対してspanの引数を変えても、
弱い存在命題のchooseは定義上同じになることを確認した。
この事実だけから元の最終定理が偽だとは結論しない。
ただし、この選択条件だけから指定scaffoldとの制限同型を取り出す経路は現時点でない。

### 具体的な既存本文の差分案（未適用）

対象はLeftCoherentTransportDirectComparison.leanの次の3本文だけ。

```lean
leftCoherentTransportDirectComparison p := scaffoldCoherentComparison p
leftCoherentTransportDirectComparison_projection p := scaffoldCoherentComparison_projection p
leftCoherentTransportDirectComparison_isPrecompositionEquivalence p :=
  scaffoldCoherentComparison_isPrecompositionEquivalence p
```

新規ScaffoldCoherentComparisonのimportを1行追加する。公開の名前・型・仮定を保ち、
存在定理exists_leftCoherentTransport_directComparisonとQCatEquivalenceの証明は変えない。
完全な差分は `/tmp/is-w1/s8-scaffold-coherent-comparison-1/proposed-existing-bodies.patch`。
新規ファイルの現ソースのimport閉包に旧DirectComparisonはなく、置換で循環しないことを確認した。
これは先に承認されたSmallLeftUnstraighteningFunctorIsoの3本文とは別の変更なので、
指示書§2.1「既存の宣言の本文・型・名前は変えない（どうしても要るときは止めて報告）」に従い、
適用前に判断を依頼する。旧値とのrfl一致を主張しない。
承認された場合は、適用前後の保存比較v3bで公開の型・属性・公理を照合し、
直接importerのNerveTransportRepresentation・SmallLeftCoherentTransportReconstruction・F1、
および変更した選択に依存する全Sheavesを対象検証する。
この修正だけで(B)の全式が済むとは主張せず、指定制限の同型を起点として残る法則を証明する。

S1・S8は未完。S7・R2・R3は再開せず、mainも取り込んでいない。
外枠26,000行は据え置き。上の既存本文の適用は止め、検証済みと差分案を保存して報告する。


## 承認された三本文の適用前の採取（11-17 朝）

調整役の承認（指示書末尾0ca1ae558、チャット）を受けた。
LeftCoherentTransportDirectComparison・_projection・_isPrecompositionEquivalenceの三本文と
新規ScaffoldCoherentComparisonのimport1行だけを適用対象とする。
公開の名前・型・仮定、exists_leftCoherentTransport_directComparison、
QCatEquivalenceの証明は保つ。旧値とのrflの一致は求めない、という承認も確認した。
mainは引き続き取り込まない。

`/tmp/is-w1/s8-scaffold-choice-approved/`に適用前ソースとSHA、検証プログラムを保存した。
v3bの適用前採取は `--class impl --wait 3600` の整理券一枚で待っている。
採取の完了後に本文を置換し、鍵を取り直して、直接importer3本
（NerveTransportRepresentation・SmallLeftCoherentTransportReconstruction・F1）、
Sheaves全172本と変更モジュールの対象ビルド・小監査、適用後v3bと比較を順に行う。
下流全体のビルド・監査は調整役の取り込み時に残す。

待ちの間、同じ指定比較を元のscaffoldへ制限する法則
ScaffoldCoherentComparisonRestriction（57行、未検証）を新規ファイルに準備した。
型：`FunctorIso (ulift.map (universalScaffold p) ≫ scaffoldCoherentComparison p)
(ulift.map (tautScaffold (leftStrictTransportDiagram p)) ≫ leftCoherentTransportComparison p)`。
元のrestrictionIsoを忘却して同じembeddingで前合成し、既存のsource_restriction・
weighted_restrictionで端点を正規化する法則である。200行未満、追加IDなし。
未検証のためコミットしない。検証済み累計21,506行、外枠26,000行。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 同じ型の置換の事前承認と依存本数（11-17 朝）

追加承認c709577a2（チャット）を確認した。弱い存在命題からのchooseを、
指定構成との両立を保持する選択へ替える場合に限り、同じ条件で事前承認。
公開の型・名前・仮定の保持、v3b、直接importerと全Sheavesの対象検証、
新しい仮定なし・計算上限不変を守る。主張・型の変更、5,000本超、他レーンの枝の対象なら止まる。
今回の三本文は既に個別承認0ca1ae558の対象である。

置換箇所：LeftCoherentTransportDirectComparison.leanのcomparison・projection・isPrecompositionEquivalenceの三本文（未適用、採取待ち）。
推移的importer：現枝8f06e1bcd、ソース35,015本のimportグラフで **4,874本**（直接3本、対象自身を除く）。

現ソースから数え、古い索引は使っていない。採取結果は
`/tmp/is-w1/s8-scaffold-choice-approved/importers-current-branch.json`。
5,000本の基準内なので、この承認変更の適用・検証は続ける。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


## 指定scaffoldを保持する三本文の検証（11-17）

承認0ca1ae558の三本文とimport一行を適用し、直接importer3本
（NerveTransportRepresentation・SmallLeftCoherentTransportReconstruction・F1）の対象ビルド、
Sheaves全172本と変更モジュールの対象ビルド、小監査を通した。
適用前v3bはbefore-attempt2（exit 0）、適用後v3bを含む三段階は全てexit 0。
途中の10:31の待ち時間切れはexit 75で終了を確認し、調整役の指示で一枚だけ並び直した。
一回の検証のguardは1,600秒、計算上限は変更していない。

v3bは元の所有宣言5本でkind・型のhash・属性・公理が一致（証明行の除外0）。
データ本文のhashの変更はleftCoherentTransportDirectComparisonだけ。
exists_leftCoherentTransport_directComparisonとQCatEquivalenceの証明のソースは変更なし。
小監査は173モジュール・1030宣言、標準三公理のみ。
現ソースのSHAも照合した。[検証記録](inf-supply-scaffold-choice-1117-verification.json)。
ログ・適用前後v3bは`/tmp/is-w1/s8-scaffold-choice-approved/`。
下流全体のroot・全監査は調整役の取り込み時に残す。

置換箇所：LeftCoherentTransportDirectComparison.leanのcomparison・projection・isPrecompositionEquivalenceの三本文、+4/-3行。
推移的importer：現枝の現ソースで4,874本（対象自身を除く、直接3本）。他レーンの該当変更なし。
旧値とのrflは要求しない承認に従った。mainは取り込んでいない。
検証済み累計は保守的に21,510行・新規339モジュール＋承認された既存3ファイルの差分。
未検証57行のScaffoldCoherentComparisonRestrictionは作業木に残し、今回の対象ビルドとコミットから外す。
ここでLeanを止め、以下の紙をまとめた。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


## 5∞-1 の残りの計画（11-17）

一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

S2〜S6は検証済み、S1・S8は未完。以下は残る(B)・(C)と元のS1・S8の証明の計画。
公開の最終型はdrafts/Sheavesを正本とし、指定した余単位・形状同型・層化単位を保持する。
S7・R2・R3は再開しない。mainは取り込んでいない。

### 1. choose の全列挙と置き換え案

対象は現枝の残る17のrootからのimport閉包6,855本。
コメントを除いて`Classical.choose`・`Classical.choice`・`.choose`を含むデータ宣言を洗い、
255候補を[全列挙表](inf-supply-choose-1117.md)と
[選択元の原文を含むJSON](inf-supply-choose-1117.json)に保存した。
各行に宣言のソース名・ファイル・存在命題または選択元・処置の理由・推移的importer数・他レーンの照合結果を付した。
Sheaves全体を起点とする広い予備調査では87ファイルが汎用parser未対応だった。
残る範囲の255候補・221ファイルのうち53ファイルは宣言境界で再抽出し、原文を保持した。
これはソースの保守的な候補の全列挙であり、kernelによる完全修飾名の採取ではない。
表のソース名とファイルで特定する。型の検証済みの一覧と混同しない。

残る証明で実際に指定構成との両立が必要な弱い選択の修正は次のN1〜N5。
N1は今回、N2〜N5は前の承認で適用済み。追加の弱いchooseの本文変更は計画に置かない。
この五つの旧選択は公開の型としては正しく、別の指定構成との両立を結論に含まないことが問題である。

|ID|宣言・ファイル|元の存在命題|保持する指定構成・置換案|行数・状態|推移的importer|他レーンの枝|
|---|---|---|---|---|---:|---|
|N1|`leftCoherentTransportDirectComparison`、`ClassificationOfCocartesianFibrations/LeftCoherentTransportDirectComparison.lean`|`exists_leftCoherentTransport_directComparison p : ∃ f, f ≫ projection = ulift.map p ∧ IsPrecompositionEquivalence f`|元の`scaffoldTransportComparisonSpan p`への相対制限同型を含む`ScaffoldCoherentComparison`で三本文を置換。元の存在定理とQCatEquivalence証明は保持|+4/-3行。結果は直前の検証節|4,874（直接3）|なし|
|N2|`smallLeftUnstraighteningComparisonOfFunctorIso`、同節`SmallLeftUnstraighteningFunctorIso.lean`|`exists_smallLeftUnstraighteningComparison_of_functorIso η : ∃ f, f ≫ projection G = projection F ∧ IsPrecompositionEquivalence f`|ηの端点だけでなく、同じ`η.hom`の`smallUnstraighteningFunctorHom`を使い射影・同値性もその法則にする|承認a568132bfで適用検証済み。三本文の差分+4/-3行、docstringを含む当時のファイル差分+8/-7行（既計上）|3,802（直接15）|なし|
|N3|`weightedSections_nativeShapeLimitIso`、`Sheaves/WeightedSectionsLocalComparison.lean`|`weightedSections_limitValue … : ∃ c, IsLimitCone c ∧ c.vertex = W(P)`|元の同じ指定余単位の`weightedSections_valueTransport`の錐を使用|e14e7b479で適用検証済み（+4/-2行）。今後の追加0行|9（直接1）|なし|
|N4|`nativeWeightedSections_leftLimitIso`、`Sheaves/NativeWeightedSectionsLeftLimit.lean`|`nativeWeightedSections_limitValue … : ∃ c, IsLimitCone c ∧ c.vertex = W_native(P)`|元の同じnative余単位の`nativeWeightedSections_valueTransport`の錐を使用|同上（+6/-3行）。今後の追加0行|11（直接2）|なし|
|N5|`weightedSections_leftLimitIso`、`Sheaves/WeightedSectionsLeftLimit.lean`|元のnativeの`limitValue`から選ぶ中間錐|指定した形状同型で運んだ同じ余単位の`nativeWeightedSections_valueTransport`を使用|同上（+4/-2行）。今後の追加0行|7（直接2）|なし|

N1・N2のファイルは`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/`下、
N3〜N5は`SerrePositivity/InfinityCategories/`下。
数は現枝の35,015本のソースのimportグラフで対象自身を除いて数えた。
mainの先の3,959本とは枝・採取時点が異なる。他レーンは現在残る4枝
`fix/audit-reimport`・`refactor/organize-einfinity`・`research/cited-coverage`・`math/scheme`について、
mainとのmerge-base以後のコミット差分と作業木を照合した（候補245ファイル、該当なし）。
N2〜N5の追加確認も本文適用済みファイルの差分がないことを確認する。

依存していても追加の両立を要求しない／既に指定構成を保持している主なもの：

|宣言・ファイル|選択元・指定構成との関係|処置|
|---|---|---|
|`directKanUnstraighteningComparison`、`ClassificationOfCocartesianFibrations/DirectKanUnstraightening.lean`|`exists_directKanUnstraighteningComparison F`は底の等式と前合成同値性だけ。指定分類との追加の一致は含まない。推移的8,054本|変更0行。今回の(B)では明示的な`oppositeKanUnstraighteningComparison`と同じscaffoldを使用。この弱い比較との照合が要れば5,000本超の停止条件|
|`IsRightKanExtension.valueIso`・`IsLeftKanExtension.valueIso`、`KanExtensions/Definition.lean`|二つの`limitValue`／`colimitValue`。点ごとの任意の極限であり元の余単位との両立は含まない。推移的2,626本|変更0行。大域比較は既存`rightKanHomUniversalIso`・`hom_fac`から出し、この点同型を集めない|
|`colimitCoconeOfFunctorIso`、`HomotopyLimitsAndColimits/KanDiagramColimitTransport.lean`|`exists_colimitCocone_functorIso_sameVertex e c hc`。頂点と余極限性は保持するが指定増大余錐との比較を保持しない。推移的2,190本|変更0行。元の`presheafRelativeCechCocone_isColimit`と指定余錐の射を使い、選択余錐を元の余錐と同一視しない|
|`sectionsEquivalence`・`tensorSpaceFunctor_setWeightHom`、`Project/SetWeightedTensors/SetSections.lean`|旧経路のelements比較に弱いdirectKan比較が入る。推移的144本|変更0行。指定射の照合には既存`sectionsEquivalenceNatural`・`tensorSpaceFunctor_setWeightHomNatural`を使用|
|同上の`…Natural`、`SetSectionsNaturality.lean`|指定した係数の反転同型とweighted比較の合成`elementsComparisonNatural`。全前合成の比較を既に持つ。推移的140本|同じ全族のAPIを再利用。置換0行|
|`weightedSectionsData`・`nativeWeightedSectionsData`、`Sheaves/*Data.lean`|全関手Gと同じε、`IsRightKanExtension … G ε`の一組|その同じεのvalueTransport・hom_facを使う。置換0行|
|`weightedSections_valueTransport`・`nativeWeightedSections_valueTransport`、`Sheaves/*ValueTransport.lean`|同じεの`RightKanConeTransport`と極限性|辺・射影・頂点を保持済み。置換0行|
|`rightKanHomUniversalIso`・`leftKanHomUniversalIso`、`KanExtensions/UniversalProperty.lean`|指定α・βのHom像を満たす逆像。全単射のため一意|同じ指定余単位を保持する`hom_fac`を使用。置換0行|
|`sectionsOfCone`・`globalSectionsCone`、`Sheaves/SectionsOf.lean`・`GlobalSections.lean`|固定図式の全極限錐|元の選択を保持し、同じ射影の一意性で比較。置換0行|
|`weightedSections_discrete`、`Sheaves/WeightedSectionsDiscrete.lean`|同じ図式の中間極限d|元の固定比較を保持し、検証済み合成則でdを相殺。置換0行|
|`weightedSections_nativeLimitIso`、`Sheaves/WeightedSectionsNativeLimitComparison.lean`|最初の極限選択はHasLimitの証明。中間sも同じ極限射影の比較に使用|sを比較の合成則で相殺。別の余単位と同一視しない。置換0行|
|`specifiedLimitConeTransport`・`specifiedApexLimitConeTransport`|同じ指定prismの錐・頂点・全比較円柱と両端条件を同時に選ぶ|構造の同じ円柱を使用。置換0行|
|`limitVertexIsoOfLeftStraighteningIso`|内部のs,tは全極限錐。元の復元射・指定同型eに沿う三つの比較を合成|N1・N2の射を固定し、s,tは極限比較の合成則で相殺。追加置換0行|
|`smallLeftStraighteningRepresentation`・`smallFiberLeftStraighteningRepresentation`・`essentiallySmallLeftStraighteningRepresentation`|分類図式、全空間の比較、底条件、fiber同値性を保持する`LeftTransportRepresentation`の非空性|R全体と既存witnessIsoを使い、図式だけの弱い存在へ落とさない。置換0行|
|`scaffoldTransportComparisonSpan`・`strictTransportComparisonSpan`|元の二脚・射影・制限の等式を含む全spanの非空性|同じspanを再利用。置換0行|
|`leftUnstraighteningTransformationChoice`・`…FamilyLift`|固定した全H・初期値・射影を保つ持ち上げ空間の非空性|既存の可縮性・witnessIsoの全パラメータの法則を使う。置換0行|
|`functorHomotopyComposite`・`relativeFunctorHomotopyComposite`・`unstraighteningPrecompositionIso`・`…PostcompositionIso`|同じ指定辺を含む三角形の三面／相対三面|三面を保持した既存全族比較を使う。置換0行|
|`FunctorIso.edge`・`functorHomHomotopy`・`spaceValueEquivalence`|指定homMkの逆像|homMkとの一致を保持済み。端点だけの辺に替えない。置換0行|
|`coherentResolutionFaceExtensionIsoAll`・`cosliceUniversalPrismLift`|前者は元の面包含との可換性、後者は同じ普遍prismの射影と初期値を保持|指定条件の法則を使用。置換0行|
|`sheafificationFunctor`・`sheafifyUnitHom`、`Sheaves/Sheafify.lean`・`SheafifyUnit.lean`|同じhJから選ぶ反射データとそのunit|外から任意のunitを足さず、その同じ反射の全Hom普遍性でmateを作る。置換0行|
|Mathlibの`presheafToSheaf`・`sheafificationAdjunction`・`toSheafify`、`Mathlib/CategoryTheory/Sites/Sheafification.lean`|選んだ同じ左随伴と随伴のunit。元のordinary単位を固定|`toSheafify`そのものの全自然変換を使用。Mathlibは変更しない（本枝の推移的本数の集計対象外）|

`discretePresheafInclusion`の実体も確認した。元の`kanDiscretePresheafMap`は
全通常関手・nerveToCoherent・同じ実現の明示的な合成であり、頂点と辺の仕様を持つ。
Dの射作用を正規化するときに新たなchooseを足す必要はない。

上の要点表以外も含む255候補の各行の理由は別表に一行ずつある。import閉包に入ることと、
残る証明で選択値を展開して別の指定構成に同一視することは区別した。
候補全てをcanonicalとする主張ではない。列挙外の弱い選択の修正が必要と判明した場合は止める。

### 2. 残る補題の単位（型案）

以下は既存のS1・S8の証明分割と、指定構成の法則であり、独立の数学的目標を追加しない。
同じ指定射・余単位・ordinary層化単位を使う。`S7`・`R2`・`R3`は対象外。
型案はLeanでの検証前であり、存在だけへの弱化や新しい仮定の追加を許すものではない。
namespaceは各既存ファイルのものを使う。`FunctorHom`・`FunctorIso`・`JoinCone`等は既存の略記。
(B)は各ブロックで文脈を束縛する。(C)以降の共通文脈は次で、型中で使わない変数は含めない。

```lean
universe u
open CategoryTheory SSet
open scoped Simplicial
variable {C : Type u} [SmallCategory C]
variable {E : SSet.{u + 1}} [Quasicategory E]
variable {P Q : Cᵒᵖ ⥤ Type u}
```

`IsPresentable`は既存HTT.PresentableInfinityCategoriesのもの。
Kan・極限・同型・SetWeightの略記も対応する既存namespaceをopenした形で記す。

依存表のN1〜N5は前節の置換ID。各番号は元のS1・S8の証明分割／既存構成の法則で、
共通規則の数学的目標数には加えない。以下の各項目の型は端点・指定射を明示した案であり、
自由変数は共通文脈または同じ項目の前行で束縛する。段階的にLeanで型検証する。

|番号|位置づけ|choose置換への依存|先行する項目|
|---|---|---|---|
|1|B：同じscaffoldへの制限|N1|なし|
|2|B：元の復元射の全空間比較|N1・N2|1、検証済みwitness・合成則|
|3|B：同じ表現の底変換|N1・N2|1・2|
|4|B：同じ添字同型の局所頂点作用|N1・N2|2・3|
|5|B：元の大域比較の成分|N3|4、検証済みA|
|6|C：固定離散値比較の自然性|N1〜N5|1〜5|
|7|S8：同じ全Čech対角射|なし（射の構成だけ）|既存の全自然変換の実現|
|8|S8：その全射の可逆性|N1〜N5を6経由|6・7|
|9|S8：空間値で元の局所同値|N1〜N5を6・8経由|6〜8、既存の指定Čech極限|
|10|S8：同じ元の圏の宇宙移送|なし|検証済みsite/value lift|
|11|S8：同じ錐・制限の宇宙移送|なし|10|
|12|S8：任意Eへの反映と元の切断写像|N1〜N5を9経由|9〜11、既存の全Homによる反映|
|13|S8：同じDのHom作用の局所性|N1〜N5を9経由|9、既存のNaturalなG8比較|
|14|S8：元の反射による可逆性|同上|13、同じhJの反射|
|15|S8：同じordinary単位の全関手比較|同上|14、既存の離散層判定|
|16|S1：一般Coverageの全引き戻し|なし|既存の篩の極限合成・refinement|
|17|S1：元のCoverage判定|なし|16、既存の普遍降下性つき判定|

置き場所：1〜3は既存のKerodonのClassificationOfCocartesianFibrations節、
4は同KanExtensions節、5〜17はInfinityCategories/Sheaves/の新規ファイル。
旧F2/・HomotopyLimits/の下には作らない。既存の公開の主張・仮定は変えない。

#### (B)：同じ指定分類・復元から同じ添字同型の比較へ

Bの依存：今回修正した`leftCoherentTransportDirectComparison`、修正済みの
`smallLeftUnstraighteningComparisonOfFunctorIso`。`directKanUnstraighteningComparison`の
弱い比較射は指定比較の照合に使わない。元の`oppositeKanUnstraighteningComparison`と
同じscaffoldの制限の証拠を使う。

1. `scaffoldCoherentComparison_scaffoldIso`（57行の未検証下書きあり）。

```lean
{C : Type u} [Category.{u} C] {E : SSet.{u}}
(p : E ⟶ nerve C) [LeftFibration p] :
FunctorIso
  ((SSet.uliftFunctor.{u + 1, u}).map (universalScaffold p) ≫
    scaffoldCoherentComparison p)
  ((SSet.uliftFunctor.{u + 1, u}).map
      (tautScaffold (leftStrictTransportDiagram p)) ≫
    leftCoherentTransportComparison p)
```

同じ相対制限同型を`vertexFiberι`で忘却し、同じembeddingで前合成する。
元の`source_restriction`・`weighted_restriction`を使う。新しいspanは作らない。

2. `leftStraighteningInfinityReconstruction_representationComparison`。

```lean
{E B : SSet.{u}} [Quasicategory B]
(p : E ⟶ B) [LeftFibration p]
(R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p)
let a := leftStraighteningInfinityDiagram_representationIso p R
let f := smallLeftUnstraighteningLift R.diagram R.comparison ≫
  smallUnstraighteningFunctorHom a.inv
∃ hf : f ≫ q = p,
  Nonempty (VertexIso
    (relativeFunctorVertex q p (leftStraighteningInfinityReconstruction p)
      (leftStraighteningInfinityReconstruction_projection p))
    (relativeFunctorVertex q p f hf))
```

これは全空間の底上の射を比較する型で、頂点の値だけの同型ではない。
既存の表現空間の比較・`WitnessPointedDiagramIso`・検証済みのrepresentationIso合成則を使う。
`R`を選び直さず、native表現との中間比較を相殺する。

3. `leftStraighteningInfinityDiagram_representationIso_baseChange`。

```lean
{E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
(p : E ⟶ B) [LeftFibration p] (k : D ⟶ B)
(R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
letI : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩
leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
  leftStraighteningInfinityDiagram_representationIso (pullback.snd p k)
    (R.nativeRestrict k) =
  (leftStraighteningInfinityDiagram_representationIso p R).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map k)
```

同じ初頂点の制限で、元のjoint sectionの係数比較とscaffoldの制限を照合する。
`RepresentationComparisonRestriction`・`StraighteningCounitRestriction`・
`StraighteningCounitNaturality`・既検証の元の底変換の貼り合わせを再利用する。
最後は`functorIso_precomp_injective`。任意の別の底変換同型を作らない。

4. `rightKanIndexTransport_valueHom`。

```lean
{K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
{δ δ' : K ⟶ C} (e : FunctorIso δ δ') (O : K ⟶ D) (G : C ⟶ D)
(β : SSet.Homotopy (δ' ≫ G) O) (v : C _⦋0⦌) :
let b := (e.postcomp G).hom ≫
  Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
∀ s : RightKanConeTransport δ O G (functorHomHomotopy b) v,
∀ t : RightKanConeTransport δ' O G β v,
∀ hs : IsLimitCone s.cone, ∀ ht : IsLimitCone t.cone,
  eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
    s.cone_vertex.symm) ≫
  (rightKanLimitVertexIsoOfFunctorIso e O v s.cone t.cone hs ht).hom ≫
  eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
    t.cone_vertex) = 𝟙 (HomotopyCategory.mk (G.app _ v))
```

指定`e`に沿う同じ余単位の類であることを型に残す。
上の全分類の法則を元のcoslice射影に適用し、実際の`smallUnstraighteningFunctorHom`
の作用と同じ再添字・同じ錐の脚を照合する。中間極限は指定射影の一意性で消去する。
`IsRightKanExtension.valueIso`の点ごとの選択から大域同型を組み立てない。

5. `weightedSections_nativeShapeLimitIso_hom_eq_globalComparison`。

```lean
{C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
(O : Presheaf C E) (hE : IsPresentable E)
{G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E}
(β : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O)
(hβ : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O G β)
(P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
(t : RightKanConeTransport (nativeSetShapeOppositeYoneda C) O G β P)
(ht : IsLimitCone t.cone)
(d : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) O P))
(hd : IsLimitCone d) :
(weightedSections_nativeShapeLimitIso O hE P d hd).hom =
  functorHomEvaluate (weightedSections_nativeShape_comparison O hE β hβ).hom P ≫
  eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj E))
    t.cone_vertex.symm) ≫
  (limitVertexIso t.cone d ht hd).hom
```

既検証の`weightedSections_nativeShape_comparison_transport_vertex`（A）と4を合成する。
右辺の大域比較は元の`rightKanHomUniversalIso`・hom_facのもの。
両方のHom普遍性は実際のKan条件から証明済みのものを入れる。

#### (C)：元の固定された離散値比較の自然性

6. `weightedSections_discrete_map`。draftsの元の固定された型をそのまま回収する。

```lean
(O : Presheaf C E) (hE : IsPresentable E) {P Q : Cᵒᵖ ⥤ Type u}
(φ : P ⟶ Q) (hP : HasLimit (sectionsOfDiagram P O))
(hQ : HasLimit (sectionsOfDiagram Q O)) :
let e := (nerve.edgeMk φ).map (discretePresheafInclusion C).val
let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
Truncated.HomotopyCategory.homMk r ≫
  (weightedSections_discrete O hE P hP).hom =
(weightedSections_discrete O hE Q hQ).hom ≫
  Truncated.HomotopyCategory.homMk (sectionsOf_map φ O hP hQ).toTruncated
```

5、元の形状・係数の指定同型、`WeightedSectionsOriginalLeftLimitComposition`、
`DiscreteSectionsLeftComparison`、G8の全族の指定辺の比較を使う。
`weightedSections_discrete`の中間極限dと`sectionsOf`の選択は変えない。

#### S8：Čechの全族と局所同値

7. `weightedSections_relativeCechDiagonalHom`。

```lean
{P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) (O : Presheaf C E)
(hE : IsPresentable E) :
FunctorHom
  (SSet.opFunctor.map
      (strictCoherentDiagram (relativeCechDiagram f ⋙ kanDiscretePresheafFunctor C) ≫
        kanDiagramRealization Cᵒᵖ) ≫ weightedSections O hE)
  (SSet.const ((weightedSections O hE).app _
    (SSet.opObjEquiv.symm (functorVertex (discretePresheaf P)))))
```

`relativeCechDiagonal f`を`strictCoherentNatTransMap`で全族のまま実現し、反対とWを適用する。
同じ普通の対角と増大余錐の射の三角形も保持する。各jでの評価は6の同じ指定射である。

8. `weightedSections_relativeCechDiagonalHom_isIso`。

```lean
(J : GrothendieckTopology C) (f : P ⟶ Q)
[CategoryTheory.Presheaf.IsLocallyInjective J f]
(O : Presheaf C E) (hO : IsSheaf J O) (hE : IsPresentable E) :
IsIso (weightedSections_relativeCechDiagonalHom f O hE)
```

既存の`relativeCechDiagonal_sections_isInvertible`は零次を含む全jで使える。
6で同じ辺へ移し、先に構成した一つの全自然変換7の可逆性を成分で検出する。
独立に選んだ点ごとの同型を集める構成ではない。

9. `sections_localEquiv_iso_space`。

```lean
(J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
(φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
(O : Presheaf C SpaceInfinity.{u}) (hO : IsSheaf J O)
(hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)) :
IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated
```

同じtoRangeのČech増大の余極限、`weightedSections_rangeCech_isLimit`、7・8、
`cechConstantCone_isLimit`を使う。全増大余錐の射の頂点作用が元のφであることを照合する。
`ColimitHomotopyPointwise`・`ColimitHomotopyInvertible`の双対で、
両側の極限性と底図式上の可逆性から同じ頂点の辺の可逆性を回収する。
像の包含では既存の`sections_localMono_iso`を使い、最後は`Subfunctor.toRange_ι`と
指定切断写像の合成則で元のφに戻す。局所全射を点ごとの全射と仮定しない。

#### S8：任意の係数、同じ宇宙移送、元の切断錐

10. `siteLiftElementsShapeIso`・`siteLiftElementsShapeIso_naturality`。

```lean
(P : Cᵒᵖ ⥤ Type u) :
(SSet.uliftFunctor.{u + 1, u}).obj (nerve P.Elements) ≅
  nerve (siteLiftPresheaf P).Elements

{P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
(siteLiftElementsShapeIso P).hom ≫ nerveMap ((siteLiftPresheafMap φ).mapElements) =
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) ≫
    (siteLiftElementsShapeIso Q).hom
```

検証済み`PresheafElementsSiteLift`の同じup/downを各単体へ適用する。
既存の`AsSmall`の形状同型と同じ方式で、任意の小さい模型を選ばない。

11. `siteLiftSectionsCone`とその指定頂点・制限・極限性の法則。
ここで`nativeSetSectionsDiagram P' O' := nerveMap (Functor.Elements.π P') ≫ O'`。

```lean
(P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
(c : JoinCone (sectionsOfDiagram P O)) :
JoinCone (nativeSetSectionsDiagram (siteLiftPresheaf P)
  ((asSmallSiteShapeIso C).inv ≫ O))

(P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
(c : JoinCone (sectionsOfDiagram P O)) :
(siteLiftSectionsCone P O c).vertex = c.vertex

(φ : P ⟶ Q) (O : Presheaf C E)
(c : JoinCone (sectionsOfDiagram Q O)) :
joinMap (𝟙 _) (nerveMap ((siteLiftPresheafMap φ).mapElements)) ≫
  (siteLiftSectionsCone Q O c).val =
(siteLiftSectionsCone P O (SetWeight.restrictSectionsCone φ O c)).val

(P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
(c : JoinCone (sectionsOfDiagram P O)) :
IsLimitCone (siteLiftSectionsCone P O c) ↔ IsLimitCone c
```

同じ形状同型で全錐を再添字し、図式の同じ等式でcastするだけ。
`NativeSheafRepresentableCoefficients`・`SiteLiftLocalEquivalence`は検証済み。

12. `restrictSectionsCone_isLimit_of_localEquiv`と元の`sections_localEquiv_iso`。

```lean
(J : GrothendieckTopology C) (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
(O : Presheaf C E) (hO : IsSheaf J O)
(c : JoinCone (sectionsOfDiagram Q O)) (hc : IsLimitCone c) :
IsLimitCone (SetWeight.restrictSectionsCone φ O c)

(J : GrothendieckTopology C) (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
(O : Presheaf C E) (hO : IsSheaf J O)
(hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)) :
IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated
```

Eのpresentabilityは仮定しない。同じcを11で運び、全Hom(x,−)へ写し、
9を一段上のsiteで用いる。反映は既存の`isLimitCone_of_covariantRepresentableInfinity`。
最後の行は`sectionsMap_isInvertible_iff`と同じ選択済みの錐で回収する。
像への分解は空間値の9でのみ行うので、一般Eにおける中間のrangeの極限を追加仮定にしない。

#### S8：同じordinary層化と反射単位

13. `discretePresheafHom`と`discreteHom_isLocalForHom_of_localEquiv`。

```lean
{P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
FunctorHom (discretePresheaf P) (discretePresheaf Q)

(J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
(φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
(O : Presheaf C SpaceInfinity.{u}) (hO : IsSheaf J O) :
IsLocalForHom (discretePresheafHom φ) (functorVertex O)
```

最初の射は元のDのHom作用をD.property.1のeqToHomだけで正規化する。新しい辺を選ばない。
二つ目は9とG8の`sectionsEquivalenceNatural`・全族の指定前合成の比較から出す。

14. 元の`localEquiv_of_sheafifyIso`（draftsの型）。

```lean
(J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
{P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ) :
IsInvertibleEdge ((nerve.edgeMk φ).map
  ((discretePresheafInclusion C).val ≫ sheafificationFunctor J hJ)).toTruncated
```

既存の`reflective_isIso_map_iff_localHom`へ13を入れる。
指定の同じhJを使い、τ₀や別の反射に取り替えない。

15. 同じordinary単位に沿う全関手比較`sheafifyDiscreteFunctorIso`、
元の`sheafify_discrete_eq`とその`_hom_fac`。

```lean
(J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}) :
FunctorIso
  ((discretePresheafInclusion C).val ≫ sheafificationFunctor J hJ)
  (nerveMap (presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)) ≫
    (discretePresheafInclusion C).val)

(J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
(P : Cᵒᵖ ⥤ Type u) :
FunctorIso (sheafify J hJ (discretePresheaf P))
  (discretePresheaf (((presheafToSheaf J (Type u)).obj P).obj))

(J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
(P : Cᵒᵖ ⥤ Type u) :
sheafifyUnitHom J hJ (discretePresheaf P) ≫
  (sheafify_discrete_eq J hJ P).hom =
  discretePresheafHom (CategoryTheory.toSheafify J P)
```

ordinary単位をまず全自然変換としてDで写す。その標的が層であることは
`isSheaf_discretePresheaf_iff`で証明する。同じhJの随伴の全関手Hom普遍性でmateを作り、
14をordinary単位に適用して、その同じmateが同型であることを示す。
成分ごとの任意の同型を組み立てず、全mateの可逆性を検出する。

#### S1：元の一般Coverage判定

16. `coverage_basis_pullback_isLimit`。

```lean
(K : Coverage C) (F : Presheaf C E)
(hF : ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
  IsLimitCone (restrictionCone F (Sieve.generate R)))
{U V : C} (R : Presieve U) (hR : R ∈ K.coverings U) (f : V ⟶ U) :
IsLimitCone (restrictionCone F ((Sieve.generate R).pullback f))
```

ここが残る数学。単なるrefinementの選択だけでは極限性は出ない。
Coverageのrefinementの条件から、元の係数の全図式・全制限錐を比較する必要がある。
既存の`SieveFactorizationLimitComparison`・`SieveIntersectionDescent`による極限合成を再利用し、
refinementを一つずつ選んで自然性を仮定するのでなく、分解の全添字で比較する。
この∞版のrefinementの比較は未供給であり、規模の再見積もりに独立に含める。

17. 元の`isSheaf_toGrothendieck_iff`。

```lean
(K : Coverage C) (F : Presheaf C E) :
IsSheaf K.toGrothendieck F ↔
  ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
    IsLimitCone (restrictionCone F (Sieve.generate R))
```

16で既存の`isSheaf_toGrothendieck_iff_universallyDescending`への入力を証明して結ぶ。
全引き戻しでの降下を仮定には足さず、KをGrothendieckTopologyのcovering全体に制限しない。
空の被覆・空のsiteも除外しない。

### 3. 外枠の再見積もり（原型を保持）

承認された三本文とimportの差分は+4/-3行。削除の戻しを数えず4行を加える。
適用検証後の基準は21,510行・新規339本＋承認された既存3本の差分となる。
下の(B)には未検証の57行を含め、二重に加算しない。

| 群 | 型つき一覧 | 残りの下端 | 残りの上端 |
|---|---|---:|---:|
| (B) 指定scaffold・表現・底変換・添字同型・大域比較の同じ成分 | 1〜5 | 800 | 1,500 |
| (C) 元の固定離散値比較の全射の自然性 | 6 | 200 | 400 |
| Čechの全対角・増大の全族・元の局所同値への回収 | 7〜9 | 400 | 700 |
| 任意Eへの同じ形状・錐・制限の移送と全Homでの反映 | 10〜12 | 220 | 420 |
| 同じordinary単位、全反射のmate、元の層化比較 | 13〜15 | 500 | 900 |
| 一般Coverageのrefinementの∞降下比較と元の判定 | 16〜17 | 700 | 1,300 |
| **残り計** | | **2,820** | **5,220** |
| **累計見込み** | | **24,330** | **26,730** |

(B)の以前の400〜650行には、指定scaffoldの制限条件を回収して元の分類底変換へ
照合する部分が十分に入っていなかった。既検証の合成則・pointed比較を再利用しても、
復元の全空間比較・初頂点の係数比較・同じ添字同型の全作用の三つの接続が残る。
S1ではMathlibの集合値のrefinementの証明をそのまま∞係数に適用できず、
全図式と指定制限錐の比較が未供給である。この不足を独立に見積もった。
任意Eについては、検証済みの201行の宇宙移送と既存の
isLimitCone_of_covariantRepresentableInfinityを再利用し、追加を220〜420行へ抑える。

上端26,730行は外枠26,000行を730行超える。上端を都合よく切り詰めず、
この紙を保存したらLeanを再開せず止まって報告する。
S7・R2・R3は再開しない。S1を普遍降下性つきへ弱めず、S8をpresentable係数だけへ縮めない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


## 27,000 行で再開、残り第1項の検証（11-17）

mainの指示書末尾「5∞-1 の外枠を 27,000 行に」を読み、承認を確認した。
mainは取り込まず、残り17項目の一覧で再開。S7・R2・R3は再開しない。
chooseの表は指定どおり枝に保持し、取り込み時の移動は調整役に残す。

第1項 scaffoldCoherentComparison_scaffoldIso を新規ファイル
ScaffoldCoherentComparisonRestriction.lean（57行）で検証した。
元の相対制限同型をvertexFiberιで忘却し、同じembeddingへ制限して、
source_restriction・weighted_restrictionで端点だけを移す。
既存の型・仮定・本文を変更せず、新しいchooseの置換なし。
対象ビルドexit 0、小監査1宣言は標準三公理のみ、exit 0。
証拠：/tmp/is-w1/s8-scaffold-restriction-1.log と
/tmp/is-w1/s8-scaffold-restriction-1/{audit.log,source-sha.json}。

検証済み累計21,567行、新規340モジュール＋承認された既存3ファイルの差分。
17項目の証明分割は1まで検証済み、元の数学的な一覧の数は変わらない。
次は第2項：同じ表現空間のpointed比較と指定したunstraighteningの射作用を、
元の復元射の相対同型へ接続する。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 残り第2項の証明分割：同じ表現の比較の実現（11-17）

新規TransportRepresentationUnstraighteningComparison.lean（159行）。
第2項の証明分割として、既存のpointed比較の射影、指定辺への代表変更、
既存の全族unstraightening比較の頂点評価を接続した（新しい数学的目標の追加なし）。
公開の最終第2項はまだ未完。既存の本文・型・仮定、choose表は変更していない。

検証した公開の証明分割の型（既存namespaceをopenした表記）：
```lean
{E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
(R S : LeftTransportRepresentation p)
(h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
let e := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy
  (functorHomHomotopy (R.diagramIso S h).hom))
let g := leftUnstraighteningMappingVertexMap R.diagram S.diagram (intervalMappingVertexOfEdge e)
∃ hf : (R.comparison ≫ g.val) ≫ leftUnstraighteningProjection S.diagram = p,
  Nonempty (VertexIso
    (relativeFunctorVertex (leftUnstraighteningProjection S.diagram) p (R.comparison ≫ g.val) hf)
    (relativeFunctorVertex (leftUnstraighteningProjection S.diagram) p S.comparison S.over_base))
```
二つのprivateな計算は、pointedIsoの射影を同じdiagramIsoへ移す法則と、
その同じ辺を底に持つpointed prismの回収。小さい底専用のsmallUnstraighteningHomEdgeを
一般のBに適用しようとした検証ではisDefEqが200,000 heartbeatsに達したため、
その箇所だけを一般のfunctorHomHomotopyの辺の代表にした。上限は上げていない。

対象ビルドexit 0、現環境からの小監査4宣言（privateを含む）は標準三公理のみ、exit 0。
記録：/tmp/is-w1/s8-reconstruction-2/production/{verify.log,target-audit-result.json}。
検証済み累計21,726行、新規341モジュール＋承認された既存3ファイルの差分。
次は同じ射作用の合成則と宇宙の縮小を使い、元の第2項へ渡す。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 残り第2項の証明分割：指定Homの作用の合成（11-17）

新規UnstraighteningFunctorHomComposition.lean（91行）。
既存のcompStruct_nonempty_of_homMk_facで三つの指定辺を保つ三角形を取り、
leftUnstraighteningEdgeMap_compositionIsoへ渡し、元の全写像空間の指定頂点へ戻す。
前後合成の既存の頂点計算で端点を明示し、本文やchooseの選択を変更しない。
第2項に必要な既存構成の合成法則の証明分割で、新しい数学的目標の追加なし。

型（既存namespaceをopenした表記）：
```lean
{B : SSet.{u}}
{F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
(a : FunctorHom F G) (b : FunctorHom G J) :
Nonempty (VertexIso
  (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
    (unstraighteningFunctorHom (a ≫ b)) (unstraighteningFunctorHom_projection _))
  (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
    (unstraighteningFunctorHom a ≫ unstraighteningFunctorHom b)
    (by rw [Category.assoc, unstraighteningFunctorHom_projection,
      unstraighteningFunctorHom_projection])))
```
対象ビルドexit 0、現環境からの小監査2宣言は標準三公理のみ、exit 0。
記録：/tmp/is-w1/s8-reconstruction-2/composition-production/{verify.log,target-audit-result.json}。
同じ鍵の塊で続けた宇宙移送の仮検証は、Overの表示の下の準圏インスタンスで失敗。
既存の相対写像空間のKan性を局所に明示して再検証しており、入力の仮定は足さない。
検証済み累計21,817行、新規342モジュール＋承認された既存3ファイルの差分。
元の第2項は未完、一覧の外の補題・chooseの置換なし、計算上限は不変。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 残り第2項の証明分割：元の小さい宇宙への降下（11-17）

新規SmallTransportRepresentationComparison.lean（120行）。
同じ相対内部Homの宇宙移送と、元の指定縮小同型を組み合わせ、
二つの同じ実射の比較を元の相対写像空間へ反映した。
前節のOver表示の問題は同じ同型の始域・標的の型を明示して解消。
既存のKan性を局所に使うだけで、型に新しい仮定は足さない。

型（既存namespaceをopenした表記）：
```lean
{E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
(R S : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
(h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
let a := (R.diagramIso S h).hom
let f := smallLeftUnstraighteningLift R.diagram R.comparison ≫ smallUnstraighteningFunctorHom a
∃ hf : f ≫ smallLeftUnstraighteningProjection S.diagram = p,
  Nonempty (VertexIso
    (relativeFunctorVertex (smallLeftUnstraighteningProjection S.diagram) p f hf)
    (relativeFunctorVertex (smallLeftUnstraighteningProjection S.diagram) p
      (smallLeftUnstraighteningLift S.diagram S.comparison)
      (smallLeftUnstraighteningLift_projection S.diagram p S.comparison S.over_base)))
```
対象ビルドexit 0、小監査1宣言は標準三公理のみ、exit 0。
証拠：/tmp/is-w1/s8-reconstruction-2/small-production/{verify.log,target-audit-result.json}。
検証済み累計21,937行、新規343モジュール＋承認された既存3ファイルの差分。
第2項の証明分割で、数学的な一覧の追加・chooseの置換はない。
元の復元射の第2項全体はまだ未完。main・S7・R2・R3は触れていない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


## 残り第2項の完成：元の復元射と任意の表現の比較（11-17）

新規SmallUnstraighteningFunctorHomComposition.lean（100行）と
StraighteningReconstructionRepresentationComparison.lean（120行）。
前者は前節の指定Homの合成則を同じ縮小同型で元の相対写像空間へ反映する法則。
型は前節のunstraighteningFunctorHom_comp_isoの全てのunstraighteningFunctorHom・
leftUnstraighteningProjectionを、それぞれsmallUnstraighteningFunctorHom・
smallLeftUnstraighteningProjectionへ置き換えたNonempty (VertexIso …)。
新しいchooseの置換や入力の仮定の追加なし。

後者の公開宣言は承認された第2項の型そのもの：
```lean
{E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
(R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p)
let a := leftStraighteningInfinityDiagram_representationIso p R
let f := smallLeftUnstraighteningLift R.diagram R.comparison ≫ smallUnstraighteningFunctorHom a.inv
∃ hf : f ≫ q = p,
  Nonempty (VertexIso
    (relativeFunctorVertex q p (leftStraighteningInfinityReconstruction p)
      (leftStraighteningInfinityReconstruction_projection p))
    (relativeFunctorVertex q p f hf))
```
同じ表現空間でnative表現との比較を取り、既検証のrepresentationIsoの合成則で
元の指定逆同型を分解し、同じ射作用の合成と元の復元射の定義へ戻す。
strictな図式に狭めず、任意のcoherentなRと、元の底上の二射を保つ。
元の小さい全空間から従うULiftの小ささを局所に明示しただけで、型の仮定は不変。

それぞれ対象ビルドexit 0、小監査2宣言・1宣言は標準三公理のみ、exit 0。
記録：/tmp/is-w1/s8-reconstruction-2/{small-composition-production,final-production}/
のverify.log・target-audit-result.json。ソースSHAも照合済み。
第2項の証明分割の実測は159+91+120+100+120=590行。第1項と合わせて647行。
検証済み累計22,157行、新規345モジュール＋承認された既存3ファイルの差分。
残り17項目は第1・2項まで検証済み。数学的な一覧の追加はない。
次は第3項の底変換の同じ全分類比較との両立。mainは取り込まず、S7・R2・R3も再開しない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


## 残り第10・11項：同じ要素圏・切断錐の宇宙移送（11-17）

第3項の共同比較とcartesian制限の照合を続ける間、その接続に依存しない
第10・11項を先に検証した。SiteLiftElementsShape.lean（39行）と
SiteLiftSectionsCone.lean（81行）の新規2ファイル。
指定したsiteLiftElementsUp・Downを全nerveへ送り、別の小さい模型は選ばない。
同じ係数を保つ図式の等式で錐をcastするだけなので、chooseの置換も追加仮定もない。

主な型（既存namespaceをopenした表記）：
```lean
siteLiftElementsShapeIso (P : Cᵒᵖ ⥤ Type u) :
  (SSet.uliftFunctor.{u + 1, u}).obj (nerve P.Elements) ≅ nerve (siteLiftPresheaf P).Elements

siteLiftElementsShapeIso_naturality (φ : P ⟶ Q) :
  (siteLiftElementsShapeIso P).hom ≫ nerveMap (siteLiftPresheafMap φ).mapElements =
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) ≫ (siteLiftElementsShapeIso Q).hom

siteLiftSectionsCone (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
  (c : JoinCone (sectionsOfDiagram P O)) :
  JoinCone (nativeSetSectionsDiagram (siteLiftPresheaf P) ((asSmallSiteShapeIso C).inv ≫ O))

siteLiftSectionsCone_vertex (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
  (c : JoinCone (sectionsOfDiagram P O)) : (siteLiftSectionsCone P O c).vertex = c.vertex

siteLiftSectionsCone_restrict (φ : P ⟶ Q) (O : Presheaf C E)
  (c : JoinCone (sectionsOfDiagram Q O)) :
  joinMap (𝟙 _) (nerveMap (siteLiftPresheafMap φ).mapElements) ≫ (siteLiftSectionsCone Q O c).val =
    (siteLiftSectionsCone P O (SetWeight.restrictSectionsCone φ O c)).val

siteLiftSectionsCone_isLimit_iff [Quasicategory E] (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
  (c : JoinCone (sectionsOfDiagram P O)) :
  IsLimitCone (siteLiftSectionsCone P O c) ↔ IsLimitCone c
```
第11項のnativeSetSectionsDiagramは紙の略記どおりnerveMap (Functor.Elements.π P) ≫ O。
係数移送の等式siteLiftSectionsDiagram_eqも同じファイルに保持した。
二本とも対象ビルドexit 0、小監査は13宣言、標準三公理のみ、exit 0。
記録：/tmp/is-w1/s8-site-lift-cone-1/{verify-2.log,target-audit-result.json}。
検証済み累計22,277行、新規347モジュール＋承認された既存3ファイルの差分。
残る17項目では1・2・10・11まで検証済み。S1・S8は未完。
mainは取り込まず、S7・R2・R3も再開していない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 残り第7項：同じ相対 Čech 対角の全族（11-17）

WeightedSectionsRelativeCechDiagonal.lean、123行を追加した。第7項は元の型のまま検証済み。
元の relativeCechDiagonal f を kanDiscretePresheafFunctor で写した同じ自然変換を、
strictCoherentNatTransMap で一度だけ実現する。定値始域を等式で正規化し、同じ円柱を
homotopyOpposite で反対化、元の weightedSections O hE を後合成する。
点ごとの射を集めず、既存の choose や既存宣言の本文は変えていない。

第7項の証明の分割・既存構成の計算法則（一覧の追加項目ではない）：

```lean
relativeCechDiagonal_cocone (f : P ⟶ Q) :
  relativeCechDiagonal f ≫ (relativeCechCocone f).ι =
    (Functor.const (AsSmall.{u} SimplexCategoryᵒᵖ)).map f

discreteStrictConstantDiagram_eq {I : Type u} [SmallCategory I]
  (A : KanDiagramObject Cᵒᵖ) :
  strictCoherentDiagram ((Functor.const I).obj A) = SSet.const (coherentNerveVertex A)

discreteRelativeCechDiagonalHomotopy (f : P ⟶ Q) :
  SSet.Homotopy (SSet.const (functorVertex (discretePresheaf P)))
    (strictCoherentDiagram (relativeCechDiagram f ⋙ kanDiscretePresheafFunctor C) ≫
      kanDiagramRealization Cᵒᵖ)

discreteRelativeCechDiagonalHomotopy_component (f : P ⟶ Q)
  (j : AsSmall.{u} SimplexCategoryᵒᵖ) :
  (simplicialHomotopyVertexEdge (discreteRelativeCechDiagonalHomotopy f)
    (ULift.up (ComposableArrows.mk₀ j))).edge =
    (((nerve.edgeMk ((relativeCechDiagonal f).app j)).map (kanDiscretePresheafMap C)).edge)
```

指定成分と元の増大射の三角形を保持した。主構成に HTT 6.2.2.6 の属性を
partial := special と理由つきで付与。Kerodon §2.4.3 / Tag 00KM はこの特殊な実現の
docstring のみに記載。第8項の可逆性は、第6項の指定離散値比較の自然性との接続後に証明する。
対象ビルド exit 0、小監査は生成宣言を含む12宣言、標準三公理のみ、exit 0。
証拠：/tmp/is-w1/s8-cech-diagonal/production/{verify-3.log,target-audit-result.json}。
検証済み累計22,400行、新規348モジュール＋承認された既存3ファイルの差分。
残り17項目のうち1・2・7・10・11が検証済み。mainは取り込んでいない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 第3項の証明の分割：同じ表現空間内の移送（11-17）

StraighteningRepresentationBaseChangeTransfer.lean、52行。第3項の追加の数学ではなく、
既存の representationIso_comp_diagramIso と cartesianRestrict_diagramIso の合成則。

```lean
leftStraighteningInfinityDiagram_representationIso_baseChange_transfer
  {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B)
  (R S : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p))
  (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))
  (h : leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
      leftStraighteningInfinityDiagram_representationIso (pullback.snd p k) (R.nativeRestrict k) =
    (leftStraighteningInfinityDiagram_representationIso p R).precomp
      ((SSet.uliftFunctor.{u+1,u}).map k)) :
  leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
      leftStraighteningInfinityDiagram_representationIso (pullback.snd p k) (S.nativeRestrict k) =
    (leftStraighteningInfinityDiagram_representationIso p S).precomp
      ((SSet.uliftFunctor.{u+1,u}).map k)
```

条件hは第3項全体への追加仮定ではなく、同じ可換式を表現RからSへ移す中間補題の入力。
無条件の第3項は未完。指定 joint-section 比較と初頂点・scaffold 比較との照合を続ける。
対象ビルドexit 0、小監査2宣言・標準三公理のみexit 0。
証拠：/tmp/is-w1/s8-representation-basechange/transfer-production/{verify.log,target-audit-result.json}。
検証済み累計22,452行、新規349モジュール＋承認された既存3ファイルの差分。
残り17項目の済みは1・2・7・10・11のまま。mainは取り込んでいない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 第13項の前半：元の離散埋め込みによる実射（11-17）

DiscretePresheafHom.lean、40行。第13項の最初の構成は検証済み。
元の discretePresheafInclusion の実射を頂点の仕様の等式だけで移す。

```lean
discretePresheafHom {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
  FunctorHom (discretePresheaf P) (discretePresheaf Q)

discretePresheafHom_eq_normalized (φ : P ⟶ Q) :
  discretePresheafHom φ =
    eqToHom (congrArg HomotopyCategory.mk ((discretePresheafInclusion C).property.1 P).symm) ≫
    Truncated.HomotopyCategory.homMk
      (((nerve.edgeMk φ).map (discretePresheafInclusion C).val).toTruncated) ≫
    eqToHom (congrArg HomotopyCategory.mk ((discretePresheafInclusion C).property.1 Q))
```

後半の discreteHom_isLocalForHom_of_localEquiv は第9項に依存するため未完。
この構成・正規化則はその代わりの局所性仮定を置くものではない。
対象ビルドexit 0、小監査3宣言・標準三公理のみexit 0。
証拠：/tmp/is-w1/s8-discrete-hom/production/{verify.log,target-audit-result.json}。
検証済み累計22,492行、新規350モジュール＋承認された既存3ファイルの差分。
残り17項目の済みは1・2・7・10・11（第13項は前半のみ）。
mainは取り込まず、S7・R2・R3も再開していない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 27,000行の外枠に対する再見積もり・停止（11-17）

検証済みは951e66201までコミット済み（22,492行）。今回進めた元の17項目では
1・2・7・10・11が済み。第3項は表現の移送則のみ、第13項は実射の構成のみで、
いずれも元の項目全体を済みとは数えていない。choose表二本はそのまま残した。

#### 指定された全族の照合に残る法則

第3項の移送則は、ある表現で分かった可換式を別の表現へ渡せる。しかし、指定された
joint-section底変換と初頂点・scaffoldの比較の可換式そのものはまだ要る。
この部分を成分ごとの等式だけで閉じることはしない。

今回照合した既存APIにはKanEnrichedComparison.trans、
kanEnrichedComparisonEdge_hom_trans、kanEnrichedComparisonTriangleFamily_first/second/longがある。
一方、KanEnrichedDiagramComparison.realizationIsoは、添字と全係数の共同族を実現して
curryする構成である。kanEnrichedRealizationValueIso_homは一つの係数での値を回収するが、
それだけでは全族のHomの等式にならない。前の上端1,500行では、この境目の合成・移送の
費用を十分に数えていなかった。

ここで必要となる既存構成の合成則の型案（紙、未実装。新しい数学のIDは付けない）：

```lean
{C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
{J : Type u} [Category.{u} J]
{D E F : KanEnrichedDiagram C J}
(η : KanEnrichedDiagramComparison D E)
(θ : KanEnrichedDiagramComparison E F)
(χ : KanEnrichedDiagramComparison D F)
(hχ : ∀ j, χ.component j =
  KanEnrichedComparison.trans (η.component j) (θ.component j))
(hη : ∀ j (X : C), IsQCatEquivalence ((η.component j).val X))
(hθ : ∀ j (X : C), IsQCatEquivalence ((θ.component j).val X))
(hχe : ∀ j (X : C), IsQCatEquivalence ((χ.component j).val X)) :
η.realizationIso hη ≪≫ θ.realizationIso hθ = χ.realizationIso hχe
```

この法則は200行を超える見込み（200〜350行）。既存の二点・三点図式を全添字で束ね、
三面を同じ共同実現の三辺に照合する必要がある。対象ごとの同型の組立は使わない。
続いて同じ係数の底変換・underへの制限の合成を照合し、強いscaffold制限の第1項と
復元の第2項を用いて、第3項の指定可換式を初頂点の充満忠実性で反映する。
これらも既存構成の法則として扱うが、証明の行数は外枠に含める。
第3項の残りは現在の経路で900〜1,450行と見積もる。
第4項では、これを同じcoslice射影に用い、指定した余単位の類と錐の脚まで照合する。
極限の存在だけや、独立に選んだ値の同型で代用しない。

#### 残りの規模（既に検証した分を二重に数えない）

| 残り | 下端 | 上端 |
|---|---:|---:|
| 第3項：全族の合成・係数・scaffoldの照合と降下 | 900 | 1,450 |
| 第4項：同じ右Kan添字輸送の値の射 | 250 | 450 |
| 第5項：元の大域比較の成分との一致 | 80 | 150 |
| 第6項：固定された離散値比較の自然性 | 200 | 400 |
| 第8・9項：Čech全族の可逆性と空間値の局所同値 | 350 | 600 |
| 第12項：任意係数への全Homでの反映 | 120 | 300 |
| 第13項後半・第14・15項：局所Homと同じ層化単位 | 450 | 860 |
| 第16・17項：一般Coverageのrefinementと判定 | 700 | 1,300 |
| **残り計** | **3,050** | **5,510** |
| **検証済み22,492行との累計** | **25,542** | **28,002** |

上端28,002行は27,000行の外枠を1,002行超える。これは現在の証明経路の見込みであり、
数学的な不可能性の主張ではない。指定された全族・同じ値比較を保ったままの計画として報告する。
指示書末尾「5∞-1の外枠を27,000行に」の停止条件に従い、ここでLeanを止めた。
承認済み17項目の型・仮定は変更せず、一覧外のchoose置換も行っていない。
mainは取り込まず、S7・R2・R3は再開していない。

直近の検証：第7項12宣言、第3項の移送則2宣言、第13項前半3宣言、いずれも
対象ビルド・小監査exit 0、標準三公理のみ。共有鍵の待ちは残っておらず、鍵も放している。
未追跡の旧R2下書き4本は従前のまま、今回の検証・コミットに含めていない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

### 第3項の残りを補題の単位へ分解する紙（11-17午後）

調整役の11-17午後の指示による紙。以下は型案・証明計画で、Leanの実装・検証済みという
意味ではない。第3項のLeanはまだ再開していない。元の17項目の第3項を六つに分割する。
構成の法則・証明の分割であり、最終の型・仮定・同型の選択は変更しない。

#### P3-A：全添字・全係数を保持する実現の合成則（200〜350行）

```lean
{C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
{J : Type u} [Category.{u} J]
{D E F : KanEnrichedDiagram C J}
(η : KanEnrichedDiagramComparison D E)
(θ : KanEnrichedDiagramComparison E F)
(χ : KanEnrichedDiagramComparison D F)
(hχ : ∀ j, χ.component j =
  KanEnrichedComparison.trans (η.component j) (θ.component j))
(hη : ∀ j (X : C), IsQCatEquivalence ((η.component j).val X))
(hθ : ∀ j (X : C), IsQCatEquivalence ((θ.component j).val X))
(hχe : ∀ j (X : C), IsQCatEquivalence ((χ.component j).val X)) :
η.realizationIso hη ≪≫ θ.realizationIso hθ = χ.realizationIso hχe
```

名前案：kanEnrichedDiagramRealizationIso_trans。
KanEnrichedComparisonTriangle・Faces・EdgeCompositionの三辺の構成を、同じ添字全体の
jointArrowで使う。既存のKanEnrichedComparisonだけの合成則を、点ごとの等式として
並べて結論することはしない。χの成分には既存transを使い、naturalityの証明は合成則。
置き場所はKerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/の新規ファイル。

#### P3-B1：係数の底変換と定義域の制限の可換式（100〜150行）

```lean
{B D : SSet.{u}} {J : Type u} [Category.{u} J]
(k : D ⟶ B) {A T : Jᵒᵖ ⥤ Over D} (η : A ⟶ T)
(hη : ∀ j (p : LeftFibrationObject D),
  IsQCatEquivalence (relativeFunctorOverPre p.val.hom (η.app (Opposite.op j))))
(hηk : ∀ j (p : LeftFibrationObject B),
  IsQCatEquivalence (relativeFunctorOverPre p.val.hom
    ((Functor.whiskerRight η (Over.map k)).app (Opposite.op j)))) :
relativeSectionBaseChangeRealizationIso k T ≪≫
  relativeSectionRealizationComparisonIso (Functor.whiskerRight η (Over.map k)) hηk =
(relativeSectionRealizationComparisonIso η hη).precomp
    (leftFibrationInfinityBaseChange k) ≪≫
  relativeSectionBaseChangeRealizationIso k A
```

名前案：relativeSectionBaseChangeRealizationIso_overPre。
向きは制限に関して反変（TからA）。同じrelativeFunctorBaseChangeForwardとoverPreの
可換式を全joint族へ送り、P3-Aで合成を照合する。hη/hηkはこの法則の入力であり、
最終の第3項への仮定ではない。適用ではtransportSimplexUnderPre_isQCatEquivalenceと
既存の底変換同型から証明する。置き場所はKerodon/LimitsAndColimits/LimitsAndColimits/。

#### P3-B2：underへの指定制限と底の写像との合成（80〜120行）

まず元の全単体での式を固定する。

```lean
{B D : SSet.{u}} (k : D ⟶ B) (s : TransportSimplexCategory D) :
nerveMap (Under.post (X := s) (transportSimplexFunctor k)) ≫
  transportSimplexUnderDomainMap ((transportSimplexFunctor k).obj s) =
transportSimplexUnderDomainMap s
```

名前案：transportSimplexUnderDomainMap_baseChange。
両辺の終域stdSimplexは、transportSimplexFunctorが単体の次数を変えないため同じ型。
射列のunder構造射の下の単体作用素が不変であることを全次数で計算する。
これをP3-B1へ入れ、transportSimplexUnderRealizationIsoと
transportSimplexUnderBaseChangeRealizationIsoの同じ合成を照合する。
この二つの既存同型を別の存在同型で置換しない。置き場所はCartesianFibrations/の新規ファイル。

#### P3-C：指定底変換が同じscaffoldの表現比較を保つこと（350〜500行）

以下の略記をすべて元の指定構成で固定する。

```lean
U   := SSet.uliftFunctor.{u+1,u}
lB  := transportSimplexFirstVertexMap B
lD  := transportSimplexFirstVertexMap D
H   := transportSimplexFunctor k
q   := pullback.snd p k
p₀  := pullback.snd p lB
r   := pullback.snd q lD
θp  := leftStraighteningInfinityDiagram_firstVertexTransportIso p
θq  := leftStraighteningInfinityDiagram_firstVertexTransportIso q
β   := leftStraighteningInfinityDiagram_baseChangeIso p k
ν   := (θp.precomp (U.map (nerveMap H))).symm ≪≫
  diagramIsoCongr
    (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
      Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
```

νの型はFunctorIso (U.map (nerveMap H) ≫ leftCoherentTransport p₀)
(leftCoherentTransport r)。νを新しく選ばず、この式のまま使う。
標準の引き戻しの比較tを固定する（pullback.liftで作り、IsPullbackの証拠も証明する）。

```lean
t : pullback q lD ⟶ pullback p lB
ht : IsPullback t r p₀ (nerveMap H)
R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
  (U.map t) (U.map (nerveMap H))
  -- htをuliftしたIsPullbackの証拠
Rr := nerveLeftTransportRepresentation r
```

残る校正の型は次。

```lean
{E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
(p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
∃ a : VertexIso (transportWitnessVertex R₀) (transportWitnessVertex Rr),
  R₀.diagramIso Rr a = ν
```

名前案：leftStraighteningBaseChange_transportWitness。
略記のt/ht/R₀はこの補題の入力仮定に足さず、標準pullbackから作る局所構成。
これは「何らかの図式同型の存在」ではなく、指定されたνそのものが同じ全空間の
表現比較に由来する、という等式を含む。

証明では、P3-B1/B2でνのjoint-section側を同じ制限の合成へ戻す。
第1項scaffoldCoherentComparison_scaffoldIsoでuniversalScaffoldへの制限を固定し、
第2項leftStraighteningInfinityReconstruction_representationComparisonで、同じηの逆を
unstraighteningした射と復元射を相対VertexIsoで照合する。
この二つを経由する全空間の比較をrelativeFunctorOverPreで読み、相対表現の点aを得る。
指定の同じscaffoldの前合成同値で比較を反映する。aの存在を無根拠に可縮性だけから出さない。
可縮性は、aが実際にνを表すことを示した後、既存の標準aとの一意性にだけ使う。
置き場所はClassificationOfCocartesianFibrations/の新規ファイル。

#### P3-D：任意の表現での初頂点上の可換式（120〜220行）

```lean
{E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
(p : E ⟶ B) [LeftFibration p] (k : D ⟶ B)
(R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
(leftStraighteningInfinityDiagram_baseChangeIso p k).precomp (U.map lD) ≪≫
  leftStraighteningInfinityDiagram_firstVertexTransportIso q ≪≫
  nerveCoherentTransportRepresentationIso r ((R.nativeRestrict k).nativeRestrict lD) =
((leftStraighteningInfinityDiagram_representationIso p R).precomp (U.map k)).precomp
  (U.map lD)
```

名前案：leftStraighteningRepresentation_baseChange_firstVertex。
P3-Cでνの同じ表現の点を得た後、smallFiberTransportRepresentationVertexIso_unique、
nerveCoherentTransportRepresentationIso_comp_diagramIso、cartesianRestrict_diagramIsoで
標準比較と合成する。二段pullbackの同型・端点の等式の移送もこの行数に含む。
済みのbaseChange_transferは、必要なら一つの表現から任意のRへの移送に再利用する。
同じηの初頂点制限がfirstVertexTransportIsoとnerveCoherentTransportRepresentationIsoの
合成に等しいことは、既存のFF.preimageVertexIso_mapからの法則として使う。

#### P3-E：初頂点の充満忠実性での反映・第3項そのもの（50〜110行）

```lean
{E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
(p : E ⟶ B) [LeftFibration p] (k : D ⟶ B)
(R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
  leftStraighteningInfinityDiagram_representationIso q (R.nativeRestrict k) =
(leftStraighteningInfinityDiagram_representationIso p R).precomp (U.map k)
```

元の型。左辺をU.map lDで前合成すると、既存FFの逆像の像の式でP3-Dの左辺となる。
functorIso_precomp_injectiveとtransportSimplexFirstVertexMap_ulift_isLocalizationで反映する。
P3-Dの可換式を新しい仮定にせず証明して入れる。以上の合計は900〜1,450行。
この紙の型はLean未検証であり、特にP3-Cが数学的な芯。P3-Aだけで閉じるという見込みにはしない。

#### 続行対象の依存を再確認（第3〜5項の代用はしない）

| 項目 | 確認できた依存 | 今回の扱い |
|---|---|---|
| 6 | 5（同じ固定値比較と指定大域比較の成分の一致）→4→3 | 依存があるためLeanは保留 |
| 8 | 6で同じ指定辺へ移し、済み7の全族の可逆性を検出 | 同上 |
| 9 | 6・8と元のrange Čech増大 | 同上 |
| 12 | 9と済み10・11、既存全Homの反映 | 同上 |
| 14 | 13後半が9に依存 | 同上 |
| 15 | 14と元のordinary単位 | 同上 |
| 16 | 篩・Coverageのrefinementと既存の極限合成。3〜5への依存なし | 続行する |
| 17 | 16と既存CoverageUniversalDescent | 16の後に続行する |

第6項の依存は11-17の元の計画にも明記されていた。点ごとに新しい同型を選ぶことで
この依存を外すことはしない。今回、他の経路でこれを除けたという証明はまだない。
第16・17項の型は元のまま。現在22,492行で、これらの上端1,300行を加えても23,792行。
今回の続行については26,500行で停止して報告する。mainは取り込まない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。

#### P3-B2の共同実現側の型を補足（同じ午後の紙）

P3-B2のrawなunderの等式だけでは、共同実現の合成式の型を列挙したことにはならないため、
次も明示する。追加の最終定理ではなくP3-B2の分割。この分を含めB2は120〜220行、
第3項の残り計は**940〜1,550行**へ訂正する（前の900〜1,450行との差は40〜100行）。

全てJ = TransportSimplexCategory D、底Bの図式として、次を固定する。

```lean
H  := transportSimplexFunctor k
AD := transportSimplexDomainFunctor D ⋙ Over.map k
UD := transportSimplexUnderDomains D ⋙ Over.map k
UB := H.op ⋙ transportSimplexUnderDomains B
hA := transportSimplexDomainFunctor_baseChange k
ηD := Functor.whiskerRight (transportSimplexUnderDomainTransformation D) (Over.map k)
ηB := Functor.whiskerLeft H.op (transportSimplexUnderDomainTransformation B) ≫ eqToHom hA
```

ρ : UD ⟶ UBは、sでの成分がOver.homMk (nerveMap (Under.post (X := s) H)) …
となる実際の自然変換。底との可換性とnaturalityは初頂点の自然性とUnder.postの作用を使う。
ここでのρは新しい任意の比較の選択ではない。

```lean
-- transportSimplexUnderTransformation_baseChange（rawな合成の式）
{B D : SSet.{u}} (k : D ⟶ B) : ηD = ρ ≫ ηB

-- transportSimplexUnderBaseChangeComparison_isQCatEquivalence
{B D : SSet.{u}} (k : D ⟶ B)
(s : TransportSimplexCategory D) (p : LeftFibrationObject B) :
IsQCatEquivalence (relativeFunctorOverPre p.val.hom (ρ.app (Opposite.op s)))

-- transportSimplexUnderRealization_baseChange_composition
{B D : SSet.{u}} (k : D ⟶ B) :
relativeSectionRealizationComparisonIso ηB hηB ≪≫
  relativeSectionRealizationComparisonIso ρ hρ =
relativeSectionRealizationComparisonIso ηD hηD
```

hρは直前の補題、hηB/hηDは既存のunder初頂点への制限の同値性と底変換から証明して渡す。
型の略記であり、最終定理の未証明の仮定にはしない。hρの証明では二つのunderの初対象からの
点包含の同じ三角形へ戻し、relativeFunctorOverPre_isQCatEquivalence_of_initialComparisonを使う。
最後の合成はP3-Aと同じ全joint族の合成則を用いる。これにP3-B1を続け、初頂点の
二段pullbackの指定同型を消去してP3-Cのνを得る。点ごとに独立した同型を組み立てない。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### 第16項の独立な前提計算を続行・検証（11-17午後）

CoveragePullbackRefinement.lean、42行。第3〜5項をimportせず、第16項の
Coverage.pullbackの因子分解を生成篩の包含に移す法則を新規ファイルに置いた。

```lean
coverageRefinement_generate_le {U V : C} (R : Presieve U) (T : Presieve V)
  (f : V ⟶ U) (h : T.FactorsThruAlong R f) :
  Sieve.generate T ≤ (Sieve.generate R).pullback f

coveragePullbackRefinement_isLimit (K : Coverage C) (F : Presheaf C E)
  (hF : ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
    IsLimitCone (restrictionCone F (Sieve.generate R)))
  {U V : C} (R : Presieve U) (hR : R ∈ K.coverings U) (f : V ⟶ U) :
  ∃ T : Presieve V, T ∈ K.coverings V ∧
    Sieve.generate T ≤ (Sieve.generate R).pullback f ∧
    IsLimitCone (restrictionCone F (Sieve.generate T))
```

どちらもCoverageの既存構成の前提計算で、一覧の新しい数学IDではない。
存在を使う側で細分を選んでも、その選択を自然な図式と仮定しない。
残りは、これらの細分から元の全引き戻し篩の制限錐へ極限性を移す∞の比較。
既存restrictionCone_inf_isLimit_iff_of_pullbacksは各局所引き戻しでの極限性を入力に取るため、
この入力を今回の細分の存在だけで満たしたとは扱わない。
第16項・第17項は未完。元の型・仮定を変更していない。

対象ビルドexit 0、小監査2宣言・標準三公理のみexit 0。計算上限は変更なし。
証拠：/tmp/is-w1/s1-coverage-refinement/production/{verify-2.log,target-audit-result.json}。
検証済み累計22,534行、新規351モジュール＋承認された既存3ファイルの差分。
今回の第3項の紙は87b2e1aba・c4a239f81。第3項のLeanは再開していない。
第6・8・9・12・14・15項は紙に記した第3〜5項への依存のため保留。
mainは取り込まず、S7・R2・R3も再開していない。共有鍵は返却済み、待ちもなし。
一覧：済み 5／全体 8（うち追加 0、S7 は後続）。


### ⑥方式の標準署名台帳へ揃えた紙（11-17午後）

c4a239f81の紙を、inf-supply-signatures-1117.mdと同名JSONへ展開した。
対象は今回の実装再開範囲（元の残り1〜17項）。P3-A〜Eと第4〜17項の全署名に、
名前・完全な型・依存署名・既存宣言名@パス:行・原典番号・素の見込み・2倍補正を記録。
P3-B2のrawな式／自然変換／三角形／同値性／共同実現を分け、P3-Cの標準pullbackの
データもC0へ露出した。200行超のA・C1・D・R04・R06・R09・R12a・R13b・R15aは
独立署名。元の最終型や仮定は変えていない。未実装の型のLean elaborationは未実施と明記。

再現用道具：formalization-plans/stage-ii/check-inf-supply-signatures-1117.py。
Kahn法で35頂点・50辺を全て処理し、循環なし。未知の依存・重複ID・重複名は0。
2倍補正と既存宣言の参照行の名前を検査し、結果をinf-supply-signatures-1117-check.jsonへ保存。
依存DAGの検査であって数学の証明ではない。既存参照ソースのSHAも結果に記録。

指定構成・chooseの現ソースの点検はinf-supply-signatures-1117-choice-check.json。
承認済みN1〜N5は指定構成を保つ実装のまま。追加の既存本文の置き換え予定は0件。
同じ反射hJ、同じ余単位、同じ中間極限の選択は保つ。元の255候補表二本は変更していない。
既存本文・他レーンのファイルを変更する計画はなく、第3項のLeanにはまだ入っていない。

新しい数え方：今回の再開範囲の署名35本＝検証済み10本・未完23本・別停止点2本。
旧S2〜S6の検収済み出力はこの台帳へ再採番しない。旧5/8と混ぜず、以後この署名台帳で報告する。
素の残り：第3〜15項2,390〜4,310行、係数2では4,780〜8,620行。
検証済み22,534行との累計は27,314〜31,154行。
第16・17項も含めると補正後28,714〜33,754行となるため、11-17の規則に従って
第16・17項を次の停止点へ切り離した（型は保持、新しい外枠はここで定めない）。
切り離した後も補正上端が29,000行を2,154行超える点は隠さない。最後の外枠は上げず、
実装の実測を追い、28,500行で途中報告する。S7・R2・R3は再開しない。
今回の紙はビルドの鍵を使っていない。mainも取り込んでいない。
一覧：済み 10／全体 35（うち追加 0、別停止点 2）。

### 29,000行の区切り規則とP3-Aの再利用の訂正（11-17午後）

調整役のe4d1f4ee2への判断に従い、外枠29,000行と係数2を保つ。
着手前に「検証済み実測＋次の署名のまとまりの補正後上端」を計算し、
上端が29,000行を超えるまとまりには入らない。その直前を今回の停止点とする。
P3-Aは22,534＋700＝23,234行なので着手可。P3-B1はP3-Aの45行が検証された場合、
22,579＋300＝22,879行で着手可。既存本文・型・仮定は変えない。

紙の既存APIの照合に漏れがあった。
JointRealizationComposition.lean:94のjointRealizationIso_transは、全添字・全係数の
joint比較の合成則を既に証明している。P3-Aはそれを再利用し、台帳の任意のχを
既存jointComparisonTransへ同定するだけにした。新しい三角形の構成は作らない。
下書きは45行で試行検証済み。本体の対象ビルド・小監査は共有鍵の待ち列にある。
旧見込み200〜350行との差は既存APIの見落としによるもので、係数2の較正の証拠とはしない。
台帳の元の型・見込みは検証結果の更新時にも履歴として残す。
一覧：済み 10／全体 35（うち追加 0、別停止点 2）。

P3-A本体の対象ビルド・小監査が完了（exit 0、1宣言、標準三公理のみ）。
文献属性はHTT §1.1.5の特殊な構成の合成則としてpartial := specialを付けた。
証拠：/tmp/is-w1/p3-a/production/target-audit-result.json（ソースSHA照合済み）。
検証済み累計22,579行。新規352モジュール＋承認済み既存3ファイル差分。
mainの取り込み・既存本文の変更・計算上限の変更はなし。
一覧：済み 11／全体 35（うち追加 0、別停止点 2）。

### P3-B1の対象検証（11-17午後）

対象ビルド・小監査exit 0。1モジュール・6宣言、標準三公理のみ。
今回107行、検証済み累計22,686行。
文献属性はHTTの構成の照合法則としてpartial := special。Kerodonの特殊化はdocstringに記す。
証拠：/tmp/is-w1/p3-b1/production/target-audit-result.json（ソースSHA照合済み）。
新しいchoose、既存本文の変更、型・仮定の変更、計算上限の変更はなし。mainは取り込まない。
一覧：済み 12／全体 35（うち追加 0、別停止点 2）。

P3-B1内の小さい証明分割（独立署名を増やさない既存構成の束ね直しと法則）：

```lean
private def overPreJoint {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T : Jᵒᵖ ⥤ Over B} (η : A ⟶ T) :
    KanEnrichedDiagramComparison (relativeSectionEnrichedDiagram T)
      (relativeSectionEnrichedDiagram A)

private lemma overPreJoint_iso {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T : Jᵒᵖ ⥤ Over B} (η : A ⟶ T)
    (hη : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (η.app (Opposite.op j)))) :
    relativeSectionRealizationComparisonIso η hη = (overPreJoint η).realizationIso hη

private lemma overPreJoint_baseChange {B D : SSet.{u}} {J : Type u} [Category.{u} J]
    (k : D ⟶ B) {A T : Jᵒᵖ ⥤ Over D} (η : A ⟶ T) :
    jointComparisonTrans (relativeSectionBaseChangeComparison k T)
        (overPreJoint (Functor.whiskerRight η (Over.map k))) =
      jointComparisonTrans
        (jointComparisonPrecompose (overPreJoint η) (leftFibrationBaseChangeEnriched k))
        (relativeSectionBaseChangeComparison k A)
```

比較の成分は既存relativeFunctorOverPreComparison、添字の自然性も既存のもの。
新しい数学的な比較を選ばず、元のrelativeSectionRealizationComparisonIsoとの一致はrflで検証した。
最後の法則は既存relativeFunctorBaseChangeForward_overPreの全成分の等式。
三つとも200行以下、親署名P3-B1の証明分割として記録する。

次の着手判定：P3-B2a〜dの補正上端320行を22,686行へ足して23,006行で枠内。
この組が130行で検証された場合のP3-C0は22,816＋160＝22,976行で枠内。
P3-B2eの補正上端は120行で、C0を含めた検証見込み22,885行へ足して23,005行。
いずれも29,000行を超えない。B2eの具体的なcongrArgはwhnfの既定上限に達したため、
一般の自然変換の合成則を先に証明し、同じ指定自然変換へ適用する分割を検証する。
計算上限は上げず、元の型・仮定も保つ。
一覧：済み 12／全体 35（うち追加 0、別停止点 2）。

### P3-B2a,P3-B2b,P3-B2c,P3-B2d,P3-C0の対象検証（11-17午後）

対象ビルド・小監査exit 0。2モジュール・18宣言、標準三公理のみ。
今回199行、検証済み累計22,885行。
文献属性はHTTの構成の照合法則としてpartial := special。Kerodonの特殊化はdocstringに記す。
証拠：/tmp/is-w1/p3-b2/production/target-audit-result.json（ソースSHA照合済み）。
新しいchoose、既存本文の変更、型・仮定の変更、計算上限の変更はなし。mainは取り込まない。
一覧：済み 17／全体 35（うち追加 0、別停止点 2）。

### P3-C1の指定pointed比較：台帳外の独立署名が要る判断点（11-17午後）

P3-B2eの本体検証を完了したところで、Leanを止める。
29,000行への到達ではなく、標準署名台帳にない200行超の照合が要るため。
以下は承認待ちの紙であり、既存35署名の台帳には追加していない。
S7・R2・R3は再開しない。C1の元の型・仮定を弱めず、指定同型νを変えない。

不足の中身：R₀とRrの表現間の頂点同型の存在は既存APIから出るが、
そのdiagramIsoが指定したνであることには、元の全空間の点も保つ比較が必要。
smallFiberTransportRepresentationVertexIso_unique（RepresentationComparisonCoherence.lean:26）は
既に表現空間にある二つの同型を比べる補題で、任意のνをその空間へ持ち上げる補題ではない。
WitnessPrism.lean:67のtransportWitnessSpaceEdgePrism_conditionも、表現空間の辺を入力に取る。
TransportRepresentationUnstraighteningComparison.lean:57のprivate pointPrismは
与えた表現間同型をpointed prismへ送る向きであり、νの持ち上げに使うと循環する。
同じファイル:89の公開比較も表現間同型を入力に取る。
FunctorIsoEdgeRepresentative.lean:26のfunctorIso_exists_edge_representative_overは
pointedな同型と、その像が指定同型と一致することを既に入力に要求するので、
この不足を省略できない。単に各点で同値な比較へ差し替えない。

提案ID **P3-C1P**：leftStraighteningBaseChange_pointedPrism。
置き場所：Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/
LeftStraighteningBaseChangePointedPrism.lean（新規）。
依存：R01・R02・P3-B1・P3-B2e・P3-C0。
既存C1と同じ共通環境・同じ局所pullbackのLeftFibration instanceで読む。
以下は紙の完全な型で、Lean elaborationの成功はまだ主張しない。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let e := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
  ∃ W : (Δ[1] : SSet.{u+1}) ⊗ U.obj (pullback q lD) ⟶ PointedSpaceInfinity.{u},
    prismEndpoint 0 (U.obj (pullback q lD)) ≫ W = R₀.pointedMap ∧
    prismEndpoint 1 (U.obj (pullback q lD)) ≫ W = Rr.pointedMap ∧
    W ≫ pointedSpaceProjection = (Δ[1] ◁ U.map r) ≫ functorEdgePrism e
```

指定構成の点検：Wの底の辺はν.homを代表する同じfunctorHomHomotopyを使い、
既存functorHomHomotopy_homが元の射の類を保持する。新しいchooseの置き換えは予定しない。
νは元のθp・β・θq、R₀の比較は元のC0の二座標pullback、Rrの比較は既存の
scaffoldCoherentComparisonに由来する同じもの。任意の別の比較や底の辺は仮定しない。

| 署名／作業 | 素の見込み | 係数2の見込み | 再利用 |
|---|---:|---:|---|
| P3-C1P：元のscaffoldへの制限・比較 | 100〜140 | 200〜280 | scaffoldCoherentComparison_scaffoldIso @ ClassificationOfCocartesianFibrations/ScaffoldCoherentComparisonRestriction.lean:30、C0 |
| 同じ署名内：underの三角形とopposite比較の照合 | 90〜160 | 180〜320 | P3-B1・B2eの同じ共同実現、R02 @ ClassificationOfCocartesianFibrations/StraighteningReconstructionRepresentationComparison.lean:34 |
| 同じ署名内：νの指定辺への端点・射影の正規化 | 60〜100 | 120〜200 | functorHomHomotopy_hom、functorIso_exists_edge_representative_over |
| **P3-C1P合計** | **250〜400** | **500〜800** | 原典：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の照合で、独立の原典番号なし |
| P3-C1残部：同じpointed比較から表現空間の辺・diagramIsoの一致を回収 | 80〜140 | 160〜280 | 表現空間の既存の境界・辺の図式射影の法則 |

C1残部の見込みも紙の見込みであり、pointed prismの存在だけから最後まで
形式化済みと扱わない。C1Pは単なる証明ファイルの分割ではなく、指定νのpointedな
持ち上げの存在を一つの独立した型として先に閉じるための署名である。
200行超の照合は独立署名へ出すという標準に従い、未承認のままLeanで証明しない。

提案だけを仮に足した依存DAGをKahn法で検査：36頂点・56辺、循環なし。
証拠：/tmp/is-w1/p3-c1-proposed-dag.json。承認済み台帳の35頂点・50辺は変更していない。
新しい依存はC1P←既存のC1の5入力、C1←C1Pで、後段を入力に使わない。
B2eが90行で本体検証された場合の実測累計は22,975行。
現台帳の次のC1だけなら22,975＋840＝23,815行で枠内。
提案のC1PとC1残部を合わせても補正上端は1,080行で、22,975＋1,080＝24,055行。
外枠・係数は上げない。この時点の停止理由は台帳外署名であり、行数超過ではない。
後段の残りも、承認後には一まとまりずつ補正上端を足して29,000行で区切る。
一覧：済み 17／全体 35（うち追加 0、別停止点 2。C1Pは未承認の提案で分母外）。

### P3-B2eの対象検証（11-17午後）

対象ビルド・小監査exit 0。1モジュール・6宣言、標準三公理のみ。
今回90行、検証済み累計22,975行。
文献属性はHTTの構成の照合法則としてpartial := special。Kerodonの特殊化はdocstringに記す。
証拠：/tmp/is-w1/p3-b2e/production/target-audit-result.json（ソースSHA照合済み）。
新しいchoose、既存本文の変更、型・仮定の変更、計算上限の変更はなし。mainは取り込まない。
一覧：済み 18／全体 35（うち追加 0、別停止点 2）。

### 今回の停止点（11-17午後、P3-A・B1・B2a〜e・C0）

| 検証組 | 素の見込み | 係数2の見込み | 実測 |
|---|---:|---:|---:|
| P3-A | 200〜350 | 400〜700 | 45 |
| P3-B1 | 100〜150 | 200〜300 | 107 |
| P3-B2a〜d | 90〜160 | 180〜320 | 130 |
| P3-C0 | 40〜80 | 80〜160 | 69 |
| P3-B2e | 30〜60 | 60〜120 | 90 |
| 合計 | 460〜800 | 920〜1,600 | 441 |

検証済み22,534＋441＝22,975行、新規累計356モジュール＋承認済み既存3ファイル差分。
P3-Aの差は既存APIの照合漏れなので、今後の係数を下げる根拠に使わない。
B2eは素の上端60行を30行超えたが、補正上端120行には収まった。
B2eのcongrArgの具体式でのwhnf時間切れは、以下の一般の既存構成の合成則へ
分割して解消した。どちらも200行以下で、親署名B2eの証明分割として記録する。

```lean
private lemma overPreJoint_comp {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T Z : Jᵒᵖ ⥤ Over B} (η : A ⟶ T) (θ : T ⟶ Z) :
    overPreJoint (η ≫ θ) = jointComparisonTrans (overPreJoint θ) (overPreJoint η)

private lemma overPreJoint_comp_iso {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T Z : Jᵒᵖ ⥤ Over B} (η : A ⟶ T) (θ : T ⟶ Z) (γ : A ⟶ Z)
    (hγ : γ = η ≫ θ)
    (hη : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (η.app (Opposite.op j))))
    (hθ : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (θ.app (Opposite.op j))))
    (hγe : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (γ.app (Opposite.op j)))) :
    relativeSectionRealizationComparisonIso θ hθ ≪≫
      relativeSectionRealizationComparisonIso η hη =
      relativeSectionRealizationComparisonIso γ hγe
```

新規5モジュールの対象ビルド・小監査は全て成功（各組の所有宣言合計31、標準三公理のみ）。
文献属性は主な宣言へHTTの該当構成の法則としてpartial := specialを付け、
Kerodonの特殊化はdocstringへ記した。さらに今回の既存の枝の5モジュール
（ScaffoldCoherentComparisonRestriction、StraighteningReconstructionRepresentationComparison、
SiteLiftElementsShape、SiteLiftSectionsCone、DiscretePresheafHom）の主な6宣言の属性を補完。
この属性更新も対象ビルド・小監査成功（5モジュール・24宣言、標準三公理のみ）。
引用用importと属性を除いたソースは、変更前のソースと文字列で完全一致。
証拠：/tmp/is-w1/citation-refresh/{source-diff.json,target-audit-result.json}、
同じ証拠は署名JSONのcitation_refresh_1117にも保存。
文献メタデータのみの16行増は指示どおり外枠の数学の行数に含めない。
元の35署名の型・仮定は全て保持した。既存本文の変更・追加chooseの置換・計算上限の引上げは0。
台帳の参照行を更新し、35頂点・50辺のDAG・署名の完全な型・参照宣言名の検査を再実行した。

今回の停止理由は、直前の節に書いた未承認の独立署名P3-C1P（素250〜400、補正500〜800行）。
29,000行には達していない。C1のLeanや後段へは入らず、これを判断点として検証済みを渡す。
P3-C1・D・E、第4〜15項の残り、第16・17項は未完のまま。
5∞-1の完成を主張しない。mainは取り込まず、S7・R2・R3は再開していない。
鍵は検証終了時に返却済み。重複する整理券もなし。
一覧：済み 18／全体 35（うち追加 0、別停止点 2。未承認のC1P案は分母外）。

### P3-C1P承認後の再開（11-17夕）

調整役・ユーザー承認に従い、前節の完全な型をそのまま台帳へ登録した。
素250〜400行・補正500〜800行、依存5本は承認どおり。C1からC1Pへの依存も登録。
次の着手判定は22,975＋800＝23,775行で29,000行以内。係数2・外枠・既存の型は変えない。
まず型のelaborationと、指定pointed比較の構成を進める。mainは取り込まない。
一覧：済み 18／全体 36（うち追加 1、別停止点 2）。

### main取り込み前の検証の区切り（11-17夕）

P3-C1Pの証明分割2本の対象ビルド・小監査が成功（87行・2宣言、標準三公理のみ）。
前合成で指定pointed同型を戻し、その射影の指定辺に沿うprismへ揃える既存構成の法則。
親署名leftStraighteningBaseChange_pointedPrismはまだ証明していない。
検証済み累計23,062行、P3-C1Pの内訳87行を台帳に部分実測として記録。
完了時には同じファイルの既計上87行を二重に加えない。

```lean
private lemma pointedComparisonIsoOfRestriction {A Z X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (i : Z ⟶ A) (hi : IsPrecompositionEquivalence i) (q : X ⟶ Y)
    {f g : A ⟶ X} (d : FunctorIso (f ≫ q) (g ≫ q))
    (e : FunctorIso (i ≫ f) (i ≫ g))
    (h : e.postcomp q = d.precomp i) :
    ∃ a : FunctorIso f g, a.precomp i = e ∧ a.postcomp q = d
```

```lean
private lemma pointedPrismOfRestriction {A B Z : SSet.{u+1}} (p : A ⟶ B)
    (i : Z ⟶ A) (hi : IsPrecompositionEquivalence i)
    {F G : B ⟶ SpaceInfinity.{u}} (ν : FunctorIso F G)
    {f g : A ⟶ PointedSpaceInfinity.{u}}
    (hf : f ≫ pointedSpaceProjection = p ≫ F)
    (hg : g ≫ pointedSpaceProjection = p ≫ G)
    (e : FunctorIso (i ≫ f) (i ≫ g))
    (h : e.postcomp pointedSpaceProjection =
      (functorIsoOfEq (ν.precomp p) hf.symm hg.symm).precomp i) :
    let r := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
    ∃ W : (Δ[1] : SSet.{u+1}) ⊗ A ⟶ PointedSpaceInfinity.{u},
      prismEndpoint 0 A ≫ W = f ∧ prismEndpoint 1 A ≫ W = g ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ functorEdgePrism r
```

証拠：/tmp/is-w1/c1p/production/target-audit-result.json（ソースSHA一致）。
未検証の後続下書きは/tmp/is-w1/c1p/AllNext.lean。直近の試行はUniverseAscent.oleanが
ないため入口で終了し、後続の数学の検証には入っていない。計算上限は変更していない。
調整役からroot・全監査の完了とmain取り込みの指示を受けたので、この検証済みを
コミットしてmain（確認時35988dd08）を取り込み、改名表を確認してから再検証する。
一覧：済み 18／全体 36（うち追加 1、別停止点 2）。

### main取り込み後の再検証とP3-C1Pの証明分割（11-17夕）

調整役のOE-W1・A1完了の通知を受け、検証済み87行を50eec1d0fでコミットした後、
main 35988dd08を取り込んだ（merge e2fec6929、競合なし）。
OEの改名表588件と枝の変更済みLean360本を照合し、旧importは0。
数学6モジュール・33宣言、属性のみ5モジュール・24宣言の対象ビルドと小監査を再実行し成功。
最初の2組は依存キャッシュの再構築中に280秒のwall guardで終了したので、
一回30分の鍵の範囲内の900秒guardで完了した。Leanのheartbeats・maxRecDepthは不変。

P3-C1Pの次の既存構成の法則・証明分割12本を同じ新規ファイル内に置いた。
各本は200行以下。指定比較の型・仮定・chooseの本文は変えていない。
これらはscaffold・relative sections・既存G14の移送の法則であり、新しい独立署名は加えていない。
全ファイル324行の対象ビルド・小監査が成功（所有宣言23、標準三公理のみ）。
既計上87行から237行増で、検証済み累計23,299行。
本来の署名leftStraighteningBaseChange_pointedPrismはまだ未完で、
指定νへの射影の照合は未証明。部分補題を完成と数えない。

```lean
private lemma oppositePointWeightedBase {C D : Type u} [SmallCategory C] [SmallCategory D]
    (H : D ⥤ C) (F : C ⥤ KanObject.{u}) :
    weightedNerveBaseMap H (F ⋙ kanObjectForget) ≫ (oppositePointHomWeightedIso F).inv =
      (oppositePointHomWeightedIso (H ⋙ F)).inv ≫
        weightedNerveBaseMap H
          (simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor)
```

```lean
private lemma oppositeComparisonPointedBase {C D : Type u} [SmallCategory C] [SmallCategory D]
    (H : D ⥤ C) (F : C ⥤ KanObject.{u}) :
    oppositeKanUnstraighteningComparison (H ⋙ F) ≫
      pullback.fst pointedSpaceProjection
        (kanDiagramCoherentNerve ((H ⋙ F) ⋙ kanObjectOpFunctor)) =
      (SSet.uliftFunctor.{u+1,u}).map (weightedNerveBaseMap H (F ⋙ kanObjectForget)) ≫
        oppositeKanUnstraighteningComparison F ≫
          pullback.fst pointedSpaceProjection
            (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))
```

```lean
private def pullbackSectionsShift {E P B D : SSet.{u}} {J : Type u} [Category.{u} J]
    (p : E ⟶ B) [LeftFibration p] (r : P ⟶ D) [LeftFibration r]
    (t : P ⟶ E) (b : D ⟶ B) (hs : IsPullback t r p b) (A : Jᵒᵖ ⥤ Over D) :
    (relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf r) ⋙ kanObjectForget ≅
      (relativeSectionEnrichedDiagram (A ⋙ Over.map b)).evaluate
        (leftFibrationObjectOf p) ⋙ kanObjectForget
```

```lean
private def underBaseChange {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) :
    strictTransportDomains D ⋙ Over.map (nerveMap H) ⟶
      H.op ⋙ strictTransportDomains C where
  app s := Over.homMk (nerveMap (Under.post (X := s.unop) H)) (by
    have h₁ : nerveMap (Under.post (X := s.unop) H ⋙ Under.forget (H.obj s.unop)) =
        nerveMap (Under.post (X := s.unop) H) ≫ nerveMap (Under.forget (H.obj s.unop)) :=
      nerveFunctor.map_comp (Under.post (X := s.unop) H).toCatHom
        (Under.forget (H.obj s.unop)).toCatHom
    have h₂ : nerveMap (Under.forget s.unop ⋙ H) =
        nerveMap (Under.forget s.unop) ≫ nerveMap H :=
      nerveFunctor.map_comp (Under.forget s.unop).toCatHom H.toCatHom
    have hF : Under.post (X := s.unop) H ⋙ Under.forget (H.obj s.unop) =
        Under.forget s.unop ⋙ H
```

```lean
private def pullbackStrictComparison {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) :
    H ⋙ leftStrictTransportDiagram p ⟶ leftStrictTransportDiagram r
```

```lean
private lemma underRestrictionEq {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p] (H : D ⥤ C) (j : D) :
    IsQCatEquivalence (relativeFunctorOverPre p ((underBaseChange H).app (Opposite.op j)))
```

```lean
private lemma pullbackStrictComparison_app {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) (j : D) :
    (pullbackStrictComparison p r t H hs).app j =
      relativeFunctorOverPre p ((underBaseChange H).app (Opposite.op j)) ≫
        (relativeFunctorIsPullbackIso hs (nerveMap (Under.forget j))
          (nerveMap (Under.forget j) ≫ nerveMap H) rfl).inv
```

```lean
private lemma pullbackStrictComparison_eq {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) (j : D) :
    letI : KanComplex ((H ⋙ leftStrictTransportDiagram p).obj j) :=
      leftStrictTransport_kanComplex p (H.obj j)
    letI : KanComplex ((leftStrictTransportDiagram r).obj j) :=
      leftStrictTransport_kanComplex r j
    IsQCatEquivalence ((pullbackStrictComparison p r t H hs).app j)
```

```lean
private lemma precompAsEmptyLocalization {A B : SSet.{u}} (f : A ⟶ B)
    (h : IsPrecompositionEquivalence f) : IsLocalization f ∅
```

```lean
private lemma emptyInvertingEquivalence {A E : SSet.{u}} [Quasicategory E] :
    IsQCatEquivalence (invertingFunctors A E ∅).ι
```

```lean
private lemma uliftPrecomp {A B : SSet.{u}} (f : A ⟶ B)
    (h : IsPrecompositionEquivalence f) :
    IsPrecompositionEquivalence ((SSet.uliftFunctor.{u+1,u}).map f)
```

```lean
private def scaffoldPullbackData {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) :
    { l : simplicialReplacement (H ⋙ leftStrictTransportDiagram p) ⟶ P //
      l ≫ t = simplicialReplacementBaseMap H (leftStrictTransportDiagram p) ≫
        universalScaffold p ∧
      l ≫ r = simplicialReplacementProjection (H ⋙ leftStrictTransportDiagram p) ∧
      IsPrecompositionEquivalence l }
```

証拠は `evidence/inf-supply/c1p-prefix324-20261117/manifest.json`。
台帳のDAG・所在と署名の型の検査も再実行（これは未実装のLean証明の検査ではない）。

5∞-1完成時にこのレーンを閉じる最新の指示を受領した。
今回の停止点では、次の署名群の補正上端を足して29,000行を超える直前に区切る。
残る署名は取り込み後の別停止点へ送り、S7・旧R2・R3・P⁰は再開しない。
閉じる際は、署名の済み未完、見込みと実測、未追跡旧R2下書き、未コミットの有無を記す。
旧R2下書き4本は触らず、外部のlegacy-r2-drafts-20261117へ読み取りコピーとSHAを保存した。
今回のコミットの対象には含めない。
一覧：済み 18／全体 36（うち追加 1、別停止点 2）。

### P3-C1Pのscaffoldの相対比較まで（11-17夕）

scaffoldの引き戻しで作った射と、同じstrict係数比較から作るuniversal scaffoldの射が
厳密に一致することを示した。元のscaffoldCoherentComparison_restrictionIsoを同じembeddingで
制限した相対同型を使い、relativeFunctorBaseChangeForwardでpointed空間へ移した。
存在から新しく同型を選び直していない。mainの既存本文、公開型、仮定、計算上限の変更は0。
次の6本は既存の構成の法則・親署名P3-C1Pの証明分割で、全て200行以下。

```lean
private lemma pullbackStrictComparison_uncurry {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P T : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) (j : D)
    (τ : T ⟶ (H ⋙ leftStrictTransportDiagram p).obj j) :
    relativeFunctorUncurry (τ ≫ (pullbackStrictComparison p r t H hs).app j) ≫ t =
      (nerveMap (Under.post H) ▷ T) ≫ relativeFunctorUncurry τ
```

```lean
private lemma scaffoldUnderChain_post {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) {n : ℕ} (σ : ComposableArrows D n) :
    scaffoldUnderChain σ ⋙ Under.post H = scaffoldUnderChain (σ ⋙ H)
```

```lean
private lemma pullbackScaffold_naturality {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) :
    simplicialReplacementMap (pullbackStrictComparison p r t H hs) ≫ universalScaffold r ≫ t =
      simplicialReplacementBaseMap H (leftStrictTransportDiagram p) ≫ universalScaffold p
```

```lean
private lemma scaffoldPullbackData_eq {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) :
    (scaffoldPullbackData p r t H hs).val =
      simplicialReplacementMap (pullbackStrictComparison p r t H hs) ≫ universalScaffold r
```

```lean
private lemma scaffoldRelativeIso {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    let U := SSet.uliftFunctor.{u+1,u}
    let q := leftUnstraighteningProjection (leftCoherentTransport p)
    let f := U.map (universalScaffold p) ≫ scaffoldCoherentComparison p
    let g := U.map (tautScaffold (leftStrictTransportDiagram p)) ≫ leftCoherentTransportComparison p
    let b := U.map (simplicialReplacementProjection (leftStrictTransportDiagram p))
    ∃ (hf : f ≫ q = b) (hg : g ≫ q = b),
      Nonempty (VertexIso (relativeFunctorVertex q b f hf) (relativeFunctorVertex q b g hg))
```

```lean
private lemma scaffoldPointedRelativeIso {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    let U := SSet.uliftFunctor.{u+1,u}
    let F := leftCoherentTransport p
    let f := U.map (universalScaffold p) ≫ (nerveLeftTransportRepresentation p).pointedMap
    let g := U.map (tautScaffold (leftStrictTransportDiagram p)) ≫
      leftCoherentTransportComparison p ≫ pullback.fst pointedSpaceProjection F
    let b := U.map (simplicialReplacementProjection (leftStrictTransportDiagram p)) ≫ F
    ∃ (hf : f ≫ pointedSpaceProjection = b) (hg : g ≫ pointedSpaceProjection = b),
      Nonempty (VertexIso (relativeFunctorVertex pointedSpaceProjection b f hf)
        (relativeFunctorVertex pointedSpaceProjection b g hg))
```

対象ビルド・小監査は成功（1モジュール・30所有宣言、標準三公理のみ）。
C1Pの部分実測493行、前回から169行増、検証済み累計23468行。
親署名の元の見込みは素250〜400・補正500〜800行。途中で素の上端を超えたが、
未完の指定νとの照合を弱めない。800行は29,000行の外枠そのものではなく、
残りの見込みは既存の全Homのnative比較の再利用で確認する。
証拠：`evidence/inf-supply/c1p-scaffold-relative-20261117/manifest.json`。
一覧：済み 18／全体 36（うち追加 1、別停止点 2）。

### 指定native比較の頂点評価と、追加署名の判断点（11-17夕）

検証済みを区切って報告する。今回の停止理由は29,000行の境界ではなく、
下記の指定νとの照合に200行を超す見込みが出て、独立の署名が要ること。
coordination.md §2.1 (2)「法則・照合の補題でも、200行を超えそうなものは署名として書き出す」、
同 (4)「止まるのは、一覧にない署名が要るとき」に従う。
承認済みP3-C1Pの型を変えず、補助の自然性を仮定せず、未完の照合を結論として使わない。

#### 検証できたところ

既存のoppositeUnstraighteningHomComparisonIsoを、指定自然変換に対応する定値の
edgewise頂点で評価し、同じweighted射と同じunstraighteningの終点写像との相対同型を得た。
源のHom空間に準圏性を足さず、既存のfunctorIsoValueを使った。
さらに、指定prismの射影が指定した辺そのものであれば、その同型の射影も元の指定同型と
厳密に一致することを、内部Homのleft fibrationと可逆性の反映から示した。
以下の4本は200行以下の既存構成の法則・証明分割。親署名の完成とは数えていない。

```lean
private def naturalHomVertex {I : Type u} [SmallCategory I] (F G : KanDiagramObject I)
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    ((SSet.uliftFunctor.{u+1,u}).obj (edgewiseSubdivision (SimplicialCategory.sHom F G))) _⦋0⦌
```

```lean
private lemma oppositeHomLeft_at_natural {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    let U := SSet.uliftFunctor.{u+1,u}
    let q := leftUnstraighteningProjection (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor))
    let a := U.map (weightedNerveProjection (F.val ⋙ kanObjectForget))
    let f := U.map (weightedNerveMap η) ≫ oppositeKanUnstraighteningComparison G.val
    ∃ hf : f ≫ q = a,
      (oppositeUnstraighteningHomLeft F G).app _ (naturalHomVertex F G η) =
        relativeFunctorVertex q a f hf
```

```lean
private lemma oppositeHomComparison_at_natural {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    let U := SSet.uliftFunctor.{u+1,u}
    let F' := kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor)
    let G' := kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)
    let y := (kanDiagramOppositeHomInterval F G).app _ (naturalHomVertex F G η)
    let m := CartesianMonoidalCategory.lift (𝟙 (leftUnstraightening F')) (SSet.const y) ≫
      leftUnstraighteningMappingFamily F' G'
    let g := oppositeKanUnstraighteningComparison F.val ≫ m
    let f := U.map (weightedNerveMap η) ≫ oppositeKanUnstraighteningComparison G.val
    let a := U.map (weightedNerveProjection (F.val ⋙ kanObjectForget))
    let q := leftUnstraighteningProjection G'
    ∃ (hg : g ≫ q = a) (hf : f ≫ q = a),
      Nonempty (VertexIso (relativeFunctorVertex q a g hg) (relativeFunctorVertex q a f hf))
```

```lean
private lemma pointedIsoOfProjectedPrism {A : SSet.{u+1}}
    {f g : A ⟶ PointedSpaceInfinity.{u}}
    (d : FunctorIso (f ≫ pointedSpaceProjection) (g ≫ pointedSpaceProjection))
    (r : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom A).obj SpaceInfinity.{u}))
      (functorVertex (f ≫ pointedSpaceProjection)) (functorVertex (g ≫ pointedSpaceProjection)))
    (hr : SSet.Truncated.HomotopyCategory.homMk r = d.hom)
    (W : (Δ[1] : SSet.{u+1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (h₀ : prismEndpoint 0 A ≫ W = f) (h₁ : prismEndpoint 1 A ≫ W = g)
    (hp : W ≫ pointedSpaceProjection = functorEdgePrism r) :
    ∃ a : FunctorIso f g, a.postcomp pointedSpaceProjection = d
```

P3-C1Pの部分実測は数学620行（物理624行）、前回から127行増。
検証済み累計23595行。対象ビルド・小監査は1モジュール・34所有宣言、標準三公理のみ。
公開の主張・仮定や既存の本文は変えていない。計算上限は不変。
主な相対照合2本にHTT §3.3.2のspecial属性を付けた。Kerodon Tag 028Tへの特殊化は
docstringの規約に保持し、partialのkerodon属性は付けていない。文献のみの4行は外枠から除外。
今回のsource SHAは検証receiptと一致。新規ファイルの推移的importerは0（入口未登録）。
chooseの置き換えは0。他レーンのファイルの編集は0。R2の既存本体部品を再利用しただけで、
旧R2の証明や下書きは再開していない。

#### 提案P3-C1PN：元の指定νとnative区間の類の照合

名前：`leftStraighteningBaseChange_nativeInterval_hom`。
配置：P3-C1Pと同じ新規ファイル（privateの同じpullbackStrictComparison・naturalHomVertexを使う）。
依存署名：P3-B1・P3-B2e・P3-C0。P3-C1Pからこの署名へ依存を追加する案。
P3-C1Pの結論を前提にしない。元の指定νと、既存の元の全Hom上の区間の類の等号である。
別の同型を存在から選んだり、成分ごとの同型の存在へ弱めたりしない。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let Fh : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨leftStrictTransportFunctor r, trivial⟩
  let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
  let ε := intervalMappingEdgeOfVertex y
  let hsrc : U.map (nerveMap H) ≫ leftCoherentTransport p₀ =
      kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor) := by
    change U.map (nerveMap H) ≫
      kanDiagramCoherentNerve (leftStrictTransportFunctor p₀ ⋙ kanObjectOpFunctor) =
      kanDiagramCoherentNerve ((H ⋙ leftStrictTransportFunctor p₀) ⋙ kanObjectOpFunctor)
    rw [kanDiagramCoherentNerve_precomp]
    rfl
  ν.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hsrc) ≫
    SSet.Truncated.HomotopyCategory.homMk ε.toTruncated
```

上の主張の型は、同じソースの新しい出力先で#checkが成功（これは証明ではない）。
公開の仮定は増えない。元の存在命題からの新しいchooseも使わない。
原典の対応：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の指定構成の照合。独立の原典定理番号を主張しない。
Tagの特殊化なのでkerodon属性を付ける案ではない。

使う宣言と所在：

- `relativeSectionBaseChangeRealizationIso_overPre` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/RelativeSectionBaseChangePasting.lean:58`
- `transportSimplexUnderRealization_baseChange_composition` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/SimplexUnderJointComposition.lean:71`
- `kanEnrichedRealizationValueIso_heq_precomp` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedRealizationValue.lean:66`
- `straighteningBaseChangeIso_firstVertex` @ `SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/StraighteningBaseChangeRestriction.lean:77`
- `kanEnrichedJointEvaluation_restrict` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedRealizationValue.lean:35`
- `pullbackStrictComparison` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:214`
- `naturalHomVertex` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:501`

| 内訳 | 素の見込み | 係数2 |
|---|---:|---:|
| pullbackのstrict係数とunder比較・底変換の同じ成分の照合 | 40〜70 | 80〜140 |
| 同じ実現値とnative区間の類の照合 | 40〜70 | 80〜140 |
| P3-B1・B2eと指定初頂点・底変換同型の像の計算・相殺 | 100〜150 | 200〜300 |
| 始点と終点の指定表示の正規化 | 40〜70 | 80〜140 |
| **提案署名P3-C1PN** | **220〜360** | **440〜720** |

当初のC1Pは指定pointed比較全体を素250〜400行と見たが、scaffoldの相対性を保つ移送と
元の全Hom比較の評価だけで620行となった。指定νの類を保つ部分をこの中へ隠して
「小さな同定」として続けると、200行の署名規則から外れるためここで分ける。
既存のkanEnrichedRealizationValueIso_heq_precompは同じ共同比較への制限を与えるが、
原典の指定νとnative全Homの指定頂点の類との等号そのものを結論してはいない。
それが残りであり、新たな数学の仮定で埋めない。

仮に承認されれば、提案署名とP3-C1Pの残りの合成・降下（素90〜150、補正180〜300）を合わせ、
現在23,595＋補正上端720＋300＝24,615行で、29,000行の外枠内。
後続を全て29,000行に入るとは主張せず、次の署名群の補正上端を足す着手判定は継続する。
提案を仮に加えたDAGも道具で検査：37頂点・60辺、循環なし。
承認済みの台帳は36署名のまま。新規の提案は分母にも完了数にも入れていない。

#### 引き継ぎ用の現在値（レーンの閉鎖はまだ）

- 済み18：R01・R02・P3-A・B1・B2a〜e・C0・R07・R10a/b・R11a〜d・R13a。
- 未完16：P3-C1P・C1・D・E・R04・R05・R06・R08・R09・R12a/b・R13b・R14・R15a〜c。
- 別停止点2：R16・R17。提案P3-C1PNは未承認。
- 実測：P3-A〜B2eの前回の441行、C1Pの今回までの部分620行。見込みの元の数字は台帳に保持。
- 旧R2の未追跡下書き4本は編集・ビルド・コミットせず保持。SHAつきの読み取りコピーは
  外部legacy-r2-drafts-20261117に保存。削除や本体への混入をしていない。
- 今回の検証済みをコミット後、作業木の残りは上の旧R2未追跡4本だけと照合する。
  未検証の試行と採取物は外部evidenceに置いてあり、本体にsorryはない。

証拠は `evidence/inf-supply/c1p-stop-signature-20261117/manifest.json`。
鍵はビルド終了時に返却済み。整理券の重複なし。S7・R2・R3・P⁰は再開していない。
5∞-1の完成・今回の通常の29,000行停止点・レーン閉鎖は、いずれもまだ主張しない。
一覧：済み 18／全体 36（うち追加 1、別停止点 2。提案P3-C1PNは分母外）。

### 残る署名の一括洗い直し（11-17夕、P3-C1PN承認後）

P3-C1PNを報告どおりの型・依存で登録（36→37）。その後、P3-C1・D・Eと第4〜15項の
全ての未完署名を一度に洗い直した。200行超の照合として追加するのはR09-CechとR15-Unitの2本。
いずれも一本の補正上端800行以内で、今回の一括事前承認の条件内。元の署名の型・仮定は変更0。
係数2と外枠29,000は保持。P3-C1PNの記録も含めた全体は39署名（済18・未完19・別停止点2）。
以下は紙の段階の完全な型であり、新規2本のLeanの型検査と証明は紙のコミット後に行う。

#### 全行の点検結果

| ID | 素の残り | 補正 | 照合の分け方・再利用 |
|---|---:|---:|---|
| P3-C1PN | 220〜360 | 440〜720 | 承認済み。元の指定νと、同じstrict係数のnative区間の類を比較する。途中の実現・評価の法則もこの独立署名内に計上する。 |
| P3-C1P | 90〜150 | 180〜300 | 既計上620行の後、元のnative区間の同型、同じscaffoldの相対同型、指定辺の戻しと降下を合成する。P3-C1PN以外の残りの単独照合は200行以下。 |
| P3-C1 | 80〜140 | 160〜280 | 指定prismを既存のtransportWitnessの頂点同型へ移し、図式射影を計算する。指定νの照合はC1PN/C1Pへ分離済み。残り80〜140行。 |
| P3-D | 120〜220 | 240〜440 | nativeRestrict二回と同じC0正方形によるcartesianRestrictの図式・pointed射の等式（40〜70行）、既存のnerve比較とdiagramIsoの合成則（80〜150行）。D自身が独立署名で、追加の200行超の法則は見込まない。 |
| P3-E | 50〜110 | 100〜220 | 元の初頂点局所化の充満忠実性で同型の等号を反映する。P3-Dと指定前合成・合成則を使い、新しい降下の構成はしない。 |
| R04 | 250〜400 | 500〜800 | 独立署名R04自体に、復元・指定底変換の照合120〜180行、輸送錐の元の余単位とapexの照合90〜150行、eqToHom正規化40〜70行を計上（計250〜400）。P3-E・R02と既存のapex_homを使い、点ごとの同型を集めない。独立した200行超の法則を別に隠さない。 |
| R05 | 80〜150 | 160〜300 | weightedSections_nativeShape_comparison_transport_vertexとR04、元のhom_facと極限比較の合成則で同じ値比較へ戻す。新しい全関手比較を作らない。 |
| R06 | 200〜400 | 400〜800 | R05の元の固定値比較とsectionsEquivalenceNaturalの同じ全族を合わせる。既存の全自然性に加える各係数・表示の移送は一つ200行以下。R06自身は200〜400行の独立署名として保持する。 |
| R08 | 100〜180 | 200〜360 | R06で指定対角の各成分を同定し、relativeCechDiagonal_sections_isInvertibleから元の全族の可逆性を判定する。新たなČech形状や対角を作らない。 |
| R09-Cech | 220〜360 | 440〜720 | 200行超の追加照合。同じtoRangeのČech余錐をweightedSectionsで極限へ送り、同じ対角を用いて定値錐との同じ比較射を同定する。全有限次数と増大射の三角形を同時に保持する。 |
| R09 | 70〜120 | 140〜240 | ČechによるtoRangeの部分をR09-Cechに分離。残りは元の像の包含（既存localMonoの結果）との合成、Subfunctor.toRange_ιと元のsectionsOf_mapの正規化70〜120行。 |
| R12a | 100〜250 | 200〜500 | 既証R10・R11の係数・宇宙移送の法則とR09を使い、共変表現可能値で指定した同じ制限錐の極限性を反映する。100〜250行の既存独立署名で、新しい検出族を仮定しない。 |
| R12b | 20〜50 | 40〜100 | R12aと既存のsectionsMap_isInvertible_iffで同じ指定sectionsOf_mapへ戻す。 |
| R13b | 150〜250 | 300〜500 | 既存sectionsEquivalenceNaturalの同じ全自然性を、R09の局所同値とR13aの写像空間比較へ入れる。大きい頂点の入口は既証R11の移送を使い、新しい縮小を構成しない。 |
| R14 | 60〜110 | 120〜220 | 同じ反射のreflective_isIso_map_iff_localHomとR13bを使う。反射やunitを選び直さない。 |
| R15-Unit | 220〜340 | 440〜680 | 200行超の追加照合。元の通常の層化単位を、元のnerveのuncurryの全円柱として実現してηを一度構成する（resizedNatTransMapと同じ構成の混合宇宙の計算）。元の各成分の式を保持し、R14で反射後の全ηが可逆であることを示す。 |
| R15a | 80〜140 | 160〜280 | R15-Unitの全ηを反射し、通常の集合値層の離散像の層条件と反射の単位・余単位の法則で同じ全関手の同型にする。成分ごとに同型を選んで集めない。残り80〜140行。 |
| R15b | 20〜80 | 40〜160 | R15aを指定頂点で評価し、元のsheafifyと離散埋め込みの頂点等式で端点を揃える。 |
| R15c | 20〜90 | 40〜180 | R15-Unitの元の単位の各成分の式と、R15aの反射の三角法則を指定頂点へ制限する。元のtoSheafifyの射の類を保持する。 |

既存の署名で200行超のもの（D・R04・R06・R12a・R13b等）は既に独立の完全な署名なので、
同じ主張を別名の法則として二度登録しない。新たに漏れていた200行超の法則だけを以下の
R09-Cech・R15-Unitへ切り出した。元の見込みはJSONのoriginal欄に保持し、二重計上しない。
R07・R10a/b・R11a〜d・R13aは済みで、未実装の新しい照合として数え直さない。

#### 全ての未完署名の型・依存・既存宣言の所在


##### P3-C1PN — `leftStraighteningBaseChange_nativeInterval_hom`

依存：P3-B1, P3-B2e, P3-C0。素220〜360、補正440〜720行。
配置：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean`。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let Fh : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨leftStrictTransportFunctor r, trivial⟩
  let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
  let ε := intervalMappingEdgeOfVertex y
  let hsrc : U.map (nerveMap H) ≫ leftCoherentTransport p₀ =
      kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor) := by
    change U.map (nerveMap H) ≫
      kanDiagramCoherentNerve (leftStrictTransportFunctor p₀ ⋙ kanObjectOpFunctor) =
      kanDiagramCoherentNerve ((H ⋙ leftStrictTransportFunctor p₀) ⋙ kanObjectOpFunctor)
    rw [kanDiagramCoherentNerve_precomp]
    rfl
  ν.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hsrc) ≫
    SSet.Truncated.HomotopyCategory.homMk ε.toTruncated
```

- `relativeSectionBaseChangeRealizationIso_overPre` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/RelativeSectionBaseChangePasting.lean:58`
- `transportSimplexUnderRealization_baseChange_composition` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/SimplexUnderJointComposition.lean:71`
- `kanEnrichedRealizationValueIso_heq_precomp` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedRealizationValue.lean:66`
- `straighteningBaseChangeIso_firstVertex` @ `SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/StraighteningBaseChangeRestriction.lean:77`
- `kanEnrichedJointEvaluation_restrict` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedRealizationValue.lean:35`
- `pullbackStrictComparison` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:214`
- `naturalHomVertex` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:501`

原典：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の指定構成の照合。独立の原典定理番号を主張しない。

承認済み。元の指定νと、同じstrict係数のnative区間の類を比較する。途中の実現・評価の法則もこの独立署名内に計上する。

##### P3-C1P — `leftStraighteningBaseChange_pointedPrism`

依存：R01, R02, P3-B1, P3-B2e, P3-C0, P3-C1PN。素90〜150、補正180〜300行。
配置：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean`。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let e := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
  ∃ W : (Δ[1] : SSet.{u+1}) ⊗ U.obj (pullback q lD) ⟶ PointedSpaceInfinity.{u},
    prismEndpoint 0 (U.obj (pullback q lD)) ≫ W = R₀.pointedMap ∧
    prismEndpoint 1 (U.obj (pullback q lD)) ≫ W = Rr.pointedMap ∧
    W ≫ pointedSpaceProjection = (Δ[1] ◁ U.map r) ≫ functorEdgePrism e
```

- `scaffoldCoherentComparison_scaffoldIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/ScaffoldCoherentComparisonRestriction.lean:30`
- `leftStraighteningInfinityReconstruction_representationComparison` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/StraighteningReconstructionRepresentationComparison.lean:34`
- `smallFiberTransportRepresentationVertexIso_unique` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonCoherence.lean:26`

原典：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）。指定pointed比較の照合で、独立の原典番号はない。

既計上620行の後、元のnative区間の同型、同じscaffoldの相対同型、指定辺の戻しと降下を合成する。P3-C1PN以外の残りの単独照合は200行以下。

##### P3-C1 — `leftStraighteningBaseChange_transportWitness`

依存：R01, R02, P3-B1, P3-B2e, P3-C0, P3-C1P。素80〜140、補正160〜280行。
配置：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/leftStraighteningBaseChange_transportWitness.lean`。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  ∃ a : VertexIso (transportWitnessVertex R₀) (transportWitnessVertex Rr),
    R₀.diagramIso Rr a = ν
```

- `scaffoldCoherentComparison_scaffoldIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/ScaffoldCoherentComparisonRestriction.lean:30`
- `leftStraighteningInfinityReconstruction_representationComparison` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/StraighteningReconstructionRepresentationComparison.lean:34`
- `smallFiberTransportRepresentationVertexIso_unique` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonCoherence.lean:26`

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

指定prismを既存のtransportWitnessの頂点同型へ移し、図式射影を計算する。指定νの照合はC1PN/C1Pへ分離済み。残り80〜140行。

##### P3-D — `leftStraighteningRepresentation_baseChange_firstVertex`

依存：P3-C1。素120〜220、補正240〜440行。
配置：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/leftStraighteningRepresentation_baseChange_firstVertex.lean`。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  ∀ R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p),
  (leftStraighteningInfinityDiagram_baseChangeIso p k).precomp (U.map lD) ≪≫
    leftStraighteningInfinityDiagram_firstVertexTransportIso q ≪≫
    nerveCoherentTransportRepresentationIso r ((R.nativeRestrict k).nativeRestrict lD) =
  ((leftStraighteningInfinityDiagram_representationIso p R).precomp (U.map k)).precomp
    (U.map lD)
```

- `nerveCoherentTransportRepresentationIso_comp_diagramIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/NerveRepresentationComparisonLaw.lean:27`
- `cartesianRestrict_diagramIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonRestriction.lean:27`

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

nativeRestrict二回と同じC0正方形によるcartesianRestrictの図式・pointed射の等式（40〜70行）、既存のnerve比較とdiagramIsoの合成則（80〜150行）。D自身が独立署名で、追加の200行超の法則は見込まない。

##### P3-E — `leftStraighteningInfinityDiagram_representationIso_baseChange`

依存：P3-D。素50〜110、補正100〜220行。
配置：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/leftStraighteningInfinityDiagram_representationIso_baseChange.lean`。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  ∀ R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p),
  leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
    leftStraighteningInfinityDiagram_representationIso (pullback.snd p k) (R.nativeRestrict k) =
  (leftStraighteningInfinityDiagram_representationIso p R).precomp
    ((SSet.uliftFunctor.{u+1,u}).map k)
```

- `functorIso_precomp_injective` @ `SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/StraighteningBaseChangeRestriction.lean:101`
- `transportSimplexFirstVertexMap_ulift_isLocalization` @ `SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/Localization/LocalizationUlift.lean:22`

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

元の初頂点局所化の充満忠実性で同型の等号を反映する。P3-Dと指定前合成・合成則を使い、新しい降下の構成はしない。

##### R04 — `rightKanIndexTransport_valueHom`

依存：P3-E, R02。素250〜400、補正500〜800行。
配置：`SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/KanExtensions/RightKanIndexTransportValue.lean`。

```lean
∀ {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
  {δ δ' : K ⟶ C} (e : FunctorIso δ δ') (O : K ⟶ D) (G : C ⟶ D)
  (β : SSet.Homotopy (δ' ≫ G) O) (v : C _⦋0⦌),
  let b := (e.postcomp G).hom ≫
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
  ∀ (s : RightKanConeTransport δ O G (functorHomHomotopy b) v)
    (t : RightKanConeTransport δ' O G β v)
    (hs : IsLimitCone s.cone) (ht : IsLimitCone t.cone),
  eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
      s.cone_vertex.symm) ≫
    (rightKanLimitVertexIsoOfFunctorIso e O v s.cone t.cone hs ht).hom ≫
    eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
      t.cone_vertex) = 𝟙 (HomotopyCategory.mk (G.app _ v))
```

- `rightKanLimitVertexIsoOfFunctorIso` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/KanExtensions/RightKanLimitVertexTransport.lean:35`

原典：HTT 5.1.5.6の双対、Kerodon Definition 7.3.1.2（Tag 02Y9）。指定余単位に沿う値の比較の法則。

独立署名R04自体に、復元・指定底変換の照合120〜180行、輸送錐の元の余単位とapexの照合90〜150行、eqToHom正規化40〜70行を計上（計250〜400）。P3-E・R02と既存のapex_homを使い、点ごとの同型を集めない。独立した200行超の法則を別に隠さない。

##### R05 — `weightedSections_nativeShapeLimitIso_hom_eq_globalComparison`

依存：R04。素80〜150、補正160〜300行。
配置：`SerrePositivity/InfinityCategories/Sheaves/weightedSections_nativeShapeLimitIso_hom_eq_globalComparison.lean`。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (O : Presheaf C E) (hE : IsPresentable E)
  {G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E}
  (β : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O)
  (hβ : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O G β)
  (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
  (t : RightKanConeTransport (nativeSetShapeOppositeYoneda C) O G β P)
  (ht : IsLimitCone t.cone)
  (d : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) O P))
  (hd : IsLimitCone d),
  (weightedSections_nativeShapeLimitIso O hE P d hd).hom =
    functorHomEvaluate (weightedSections_nativeShape_comparison O hE β hβ).hom P ≫
    eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj E))
      t.cone_vertex.symm) ≫ (limitVertexIso t.cone d ht hd).hom
```

- `weightedSections_nativeShape_comparison_transport_vertex` @ `SerrePositivity/InfinityCategories/Sheaves/WeightedSectionsGlobalComparisonVertex.lean:32`
- `rightKanHomUniversalIso_hom_fac` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/KanExtensions/UniversalProperty.lean:83`

原典：HTT 5.1.5.6（双対）、Kerodon Definition 7.3.1.2（Tag 02Y9）。

weightedSections_nativeShape_comparison_transport_vertexとR04、元のhom_facと極限比較の合成則で同じ値比較へ戻す。新しい全関手比較を作らない。

##### R06 — `weightedSections_discrete_map`

依存：R05。素200〜400、補正400〜800行。
配置：`SerrePositivity/InfinityCategories/Sheaves/weightedSections_discrete_map.lean`。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (O : Presheaf C E) (hE : IsPresentable E) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hP : HasLimit (sectionsOfDiagram P O))
  (hQ : HasLimit (sectionsOfDiagram Q O)),
  let e := (nerve.edgeMk φ).map (discretePresheafInclusion C).val
  let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
  Truncated.HomotopyCategory.homMk r ≫ (weightedSections_discrete O hE P hP).hom =
    (weightedSections_discrete O hE Q hQ).hom ≫
      Truncated.HomotopyCategory.homMk (sectionsOf_map φ O hP hQ).toTruncated
```

- `weightedSections_discrete` @ `SerrePositivity/InfinityCategories/Sheaves/WeightedSectionsDiscrete.lean:34`
- `sectionsEquivalenceNatural` @ `SerrePositivity/InfinityCategories/Project/SetWeightedTensors/SetSectionsNaturality.lean:78`

原典：HTT 5.1.5.6（双対）。指定値比較の自然性の法則。

R05の元の固定値比較とsectionsEquivalenceNaturalの同じ全族を合わせる。既存の全自然性に加える各係数・表示の移送は一つ200行以下。R06自身は200〜400行の独立署名として保持する。

##### R08 — `weightedSections_relativeCechDiagonalHom_isIso`

依存：R06, R07。素100〜180、補正200〜360行。
配置：`SerrePositivity/InfinityCategories/Sheaves/weightedSections_relativeCechDiagonalHom_isIso.lean`。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallyInjective J f]
  (O : Presheaf C E) (hO : IsSheaf J O) (hE : IsPresentable E),
  IsIso (weightedSections_relativeCechDiagonalHom f O hE)
```

- `relativeCechDiagonal_sections_isInvertible` @ `SerrePositivity/InfinityCategories/Sheaves/RelativeCechLocalSections.lean:35`

原典：HTT 6.2.2.6、小さい通常のsiteのČech層条件への特殊化。

R06で指定対角の各成分を同定し、relativeCechDiagonal_sections_isInvertibleから元の全族の可逆性を判定する。新たなČech形状や対角を作らない。

##### R09-Cech — `weightedSections_toRangeHom_isInvertible`

依存：R06, R08。素220〜360、補正440〜720行。
配置：`SerrePositivity/InfinityCategories/Sheaves/WeightedSectionsRangeCechComparison.lean`。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]
  (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallyInjective J f]
  (O : Presheaf C E) (hO : IsSheaf J O) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E),
  let e := (nerve.edgeMk (Subfunctor.toRange f)).map (discretePresheafInclusion C).val
  let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
  IsInvertibleEdge r
```

- `weightedSections_rangeCech_isLimit` @ `SerrePositivity/InfinityCategories/Sheaves/WeightedSectionsRelativeCech.lean:39`
- `relativeCechDiagonal_sections_isInvertible` @ `SerrePositivity/InfinityCategories/Sheaves/RelativeCechLocalSections.lean:35`
- `cechConstantCone_isLimit` @ `SerrePositivity/InfinityCategories/Sheaves/CechIndexConstantLimit.lean:55`

原典：HTT 6.2.2.6 の小さい通常 site の集合値Čech解消への特殊化。全族の極限比較の照合。

200行超の追加照合。同じtoRangeのČech余錐をweightedSectionsで極限へ送り、同じ対角を用いて定値錐との同じ比較射を同定する。全有限次数と増大射の三角形を同時に保持する。

##### R09 — `sections_localEquiv_iso_space`

依存：R06, R08, R09-Cech。素70〜120、補正140〜240行。
配置：`SerrePositivity/InfinityCategories/Sheaves/sections_localEquiv_iso_space.lean`。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C SpaceInfinity.{u}) (hO : IsSheaf J O)
  (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)),
  IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated
```

- `rangeCechCocone_isColimit` @ `SerrePositivity/InfinityCategories/Sheaves/LocalEquivalenceImageReduction.lean:46`
- `cechConstantCone_isLimit` @ `SerrePositivity/InfinityCategories/Sheaves/CechIndexConstantLimit.lean:55`

原典：HTT 6.2.2.6・5.5.4.20の局所対象の筋。小さい通常のsiteと離散な局所同値への特殊化。

ČechによるtoRangeの部分をR09-Cechに分離。残りは元の像の包含（既存localMonoの結果）との合成、Subfunctor.toRange_ιと元のsectionsOf_mapの正規化70〜120行。

##### R12a — `restrictSectionsCone_isLimit_of_localEquiv`

依存：R09, R10a, R10b, R11a, R11b, R11c, R11d。素100〜250、補正200〜500行。
配置：`SerrePositivity/InfinityCategories/Sheaves/restrictSectionsCone_isLimit_of_localEquiv.lean`。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C E) (hO : IsSheaf J O)
  (c : JoinCone (sectionsOfDiagram Q O)) (hc : IsLimitCone c),
  IsLimitCone (SetWeight.restrictSectionsCone φ O c)
```

- `isLimitCone_of_covariantRepresentableInfinity` @ `SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/RepresentableLimitCharacterization.lean:52`
- `siteLiftSectionsCone_isLimit_iff` @ `SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean:76`

原典：HTT 6.2.2.6、表現可能関手による極限の検出（Kerodon §7.1）。任意の準圏係数への反映。

既証R10・R11の係数・宇宙移送の法則とR09を使い、共変表現可能値で指定した同じ制限錐の極限性を反映する。100〜250行の既存独立署名で、新しい検出族を仮定しない。

##### R12b — `sections_localEquiv_iso`

依存：R12a。素20〜50、補正40〜100行。
配置：`SerrePositivity/InfinityCategories/Sheaves/sections_localEquiv_iso.lean`。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C E) (hO : IsSheaf J O)
  (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)),
  IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated
```

- `sectionsMap_isInvertible_iff` @ `SerrePositivity/InfinityCategories/Sheaves/SieveSectionsCriterion.lean:62`

原典：HTT 6.2.2.6・5.5.4.20。draftsの元の局所同値の型。

R12aと既存のsectionsMap_isInvertible_iffで同じ指定sectionsOf_mapへ戻す。

##### R13b — `discreteHom_isLocalForHom_of_localEquiv`

依存：R09, R13a。素150〜250、補正300〜500行。
配置：`SerrePositivity/InfinityCategories/Sheaves/discreteHom_isLocalForHom_of_localEquiv.lean`。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C SpaceInfinity.{u}) (hO : IsSheaf J O),
  IsLocalForHom (discretePresheafHom φ) (functorVertex O)
```

- `sectionsEquivalenceNatural` @ `SerrePositivity/InfinityCategories/Project/SetWeightedTensors/SetSectionsNaturality.lean:78`

原典：HTT 5.5.4.20・6.2.2.6。小さい通常のsiteの離散重みでの局所Hom。

既存sectionsEquivalenceNaturalの同じ全自然性を、R09の局所同値とR13aの写像空間比較へ入れる。大きい頂点の入口は既証R11の移送を使い、新しい縮小を構成しない。

##### R14 — `localEquiv_of_sheafifyIso`

依存：R13b。素60〜110、補正120〜220行。
配置：`SerrePositivity/InfinityCategories/Sheaves/localEquiv_of_sheafifyIso.lean`。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
  {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ),
  IsInvertibleEdge ((nerve.edgeMk φ).map
    ((discretePresheafInclusion C).val ≫ sheafificationFunctor J hJ)).toTruncated
```

- `reflective_isIso_map_iff_localHom` @ `SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/ReflectiveInvertedHom.lean:80`

原典：HTT 5.5.4.15・6.2.2.7。指定された反射による局所同値の反転。

同じ反射のreflective_isIso_map_iff_localHomとR13bを使う。反射やunitを選び直さない。

##### R15-Unit — `exists_discreteSheafificationUnitHom`

依存：R14, R13a。素220〜340、補正440〜680行。
配置：`SerrePositivity/InfinityCategories/Sheaves/DiscreteSheafificationUnitComparison.lean`。

```lean
∀ {C : Type u} [SmallCategory C]
  (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
  let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
  let I := (discretePresheafInclusion C).val
  ∃ η : FunctorHom I (nerveMap S ≫ I),
    (∀ P : Cᵒᵖ ⥤ Type u,
      let h₁ := (discretePresheafInclusion C).property.1 P
      let h₂ : (nerveMap S ≫ I).app _ (nerveVertex P) =
          functorVertex (discretePresheaf (S.obj P)) := by
        exact (congrArg (fun v => I.app _ v) (nerveMap_app_mk₀ S P)).trans
          ((discretePresheafInclusion C).property.1 (S.obj P))
      functorHomEvaluate η (nerveVertex P) =
        eqToHom (congrArg (fun v => HomotopyCategory.mk v) h₁) ≫
          discretePresheafHom (CategoryTheory.toSheafify J P) ≫
          eqToHom (congrArg (fun v => HomotopyCategory.mk v) h₂.symm)) ∧
    IsIso (SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp I (nerveMap S ≫ I) (sheafificationFunctor J hJ) η)
```

- `isLocalEquivSet_toSheafify` @ `SerrePositivity/InfinityCategories/Sheaves/SetLocalEquivalence.lean:38`
- `resizedNatTransMap` @ `SerrePositivity/InfinityCategories/Project/HomotopyDiagramComparison/CatInfinity/StrictCoherentNatTrans.lean:30`
- `kanDiscretePresheafMap_vertex` @ `SerrePositivity/InfinityCategories/Sheaves/DiscretePresheafInclusion.lean:40`
- `sheafifyUnitHom` @ `SerrePositivity/InfinityCategories/Sheaves/SheafifyUnit.lean:35`

原典：HTT 6.2.2.7・5.5.4.15 の離散係数と小さい通常siteの場合。指定したMathlibの層化単位を全関手射として実現する法則。

200行超の追加照合。元の通常の層化単位を、元のnerveのuncurryの全円柱として実現してηを一度構成する（resizedNatTransMapと同じ構成の混合宇宙の計算）。元の各成分の式を保持し、R14で反射後の全ηが可逆であることを示す。

##### R15a — `sheafifyDiscreteFunctorIso`

依存：R14, R13a, R15-Unit。素80〜140、補正160〜280行。
配置：`SerrePositivity/InfinityCategories/Sheaves/sheafifyDiscreteFunctorIso.lean`。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
  FunctorIso
    ((discretePresheafInclusion C).val ≫ sheafificationFunctor J hJ)
    (nerveMap (presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)) ≫
      (discretePresheafInclusion C).val)
```

- `isSheaf_discretePresheaf_iff` @ `SerrePositivity/InfinityCategories/Sheaves/DiscreteSheafCondition.lean:48`
- `reflective_isIso_map_iff_localHom` @ `SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/ReflectiveInvertedHom.lean:80`

原典：HTT 5.5.6.28・6.2.2.7。集合値層化と0切り捨ての層化の比較の特殊な表示。

R15-Unitの全ηを反射し、通常の集合値層の離散像の層条件と反射の単位・余単位の法則で同じ全関手の同型にする。成分ごとに同型を選んで集めない。残り80〜140行。

##### R15b — `sheafify_discrete_eq`

依存：R15a。素20〜80、補正40〜160行。
配置：`SerrePositivity/InfinityCategories/Sheaves/sheafify_discrete_eq.lean`。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
  (P : Cᵒᵖ ⥤ Type u),
  FunctorIso (sheafify J hJ (discretePresheaf P))
    (discretePresheaf (((presheafToSheaf J (Type u)).obj P).obj))
```

- `isSheaf_discretePresheaf_iff` @ `SerrePositivity/InfinityCategories/Sheaves/DiscreteSheafCondition.lean:48`

原典：HTT 5.5.6.28、draftsの同名の型。

R15aを指定頂点で評価し、元のsheafifyと離散埋め込みの頂点等式で端点を揃える。

##### R15c — `sheafify_discrete_eq_hom_fac`

依存：R15a, R15b, R13a。素20〜90、補正40〜180行。
配置：`SerrePositivity/InfinityCategories/Sheaves/sheafify_discrete_eq_hom_fac.lean`。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
  (P : Cᵒᵖ ⥤ Type u),
  sheafifyUnitHom J hJ (discretePresheaf P) ≫ (sheafify_discrete_eq J hJ P).hom =
    discretePresheafHom (CategoryTheory.toSheafify J P)
```

- `sheafifyUnitHom` @ `SerrePositivity/InfinityCategories/Sheaves/SheafifyUnit.lean:35`
- `sheafificationReindexSpecifiedMateIso_mate` @ `SerrePositivity/InfinityCategories/Sheaves/SheafificationSiteSpecifiedComparison.lean:53`

原典：HTT 5.5.6.28・5.5.4.15。元の反射単位を保つ比較の法則。

R15-Unitの元の単位の各成分の式と、R15aの反射の三角法則を指定頂点へ制限する。元のtoSheafifyの射の類を保持する。

#### chooseと指定構成の点検

| 依存する選択 | 保持する仕様と今回の扱い |
|---|---|
| scaffoldCoherentComparison・scaffoldTransportComparisonSpan | 指定embeddingでの相対同型と元の二脚を保持。既計上620行で同じ相対同型を使うことまで検証済み。置き換えなし。 |
| nerveCoherentTransportRepresentationIso | 同じ可縮な表現空間内の比較。図式同型全体が一意とは使わない。C1は指定prismから証明する。 |
| limitVertexIsoOfLeftStraighteningIsoの中間極限hp・hq | 選択条件は指定図式の極限錐。全錐を引数として扱い、極限の一意性とapexで消去する。余単位を値だけへ忘れない。置き換えなし。 |
| weightedSections_valueTransport・nativeShape/leftLimitの比較 | 11-16/17の承認で同じ指定余単位αに沿うvalueTransportへ修正済み。R04〜06はその選択を再利用。置き換えなし。 |
| sectionsOf/sectionsOfCone | 元の各HasLimitから同じ極限錐を使う。自然性はsectionsEquivalenceNaturalと全関手比較へ還元する。新しく対象ごとに同型を選ばない。 |
| Classical.choice hJ・MathlibのsheafificationAdjunction | 元の二つの反射とそれぞれの指定単位をそのまま使う。R15-Unitで元の通常の単位の全族を一度実現する。置き換えなし。 |

新規choose置き換え0。既存のchoose表255件は変更しない。他レーン・main既存本文の変更予定0。
原典より狭い係数・siteの場合はspecialの文献属性を付け、partialのkerodon属性は付けない。

#### 29,000行の区切りの着手判定

検証済み23,595行を起点とし、各行を補正上端で積んだ保守的な仮置き：

| 群 | 追加する補正上端 | 累計仮置き |
|---|---:|---:|
| P3-C1PN | 720 | 24315 |
| P3-C1P | 300 | 24615 |
| P3-C1 | 280 | 24895 |
| P3-D | 440 | 25335 |
| P3-E | 220 | 25555 |
| R04 | 800 | 26355 |
| R05 | 300 | 26655 |
| R06 | 800 | 27455 |
| R08 | 360 | 27815 |
| R09-Cech | 720 | 28535 |
| R09 | 240 | 28775 |
| R12a | 500 | 29275（この仮置きでは着手せず区切る） |

上の累計は証明できた行数ではない。各群が通るたびに実測へ置き換え、次の群の補正上端を
足して再判定する。既計上のC1Pの620行や引用の4行を重ねて足さない。表で区切られる
後続とR16・R17は、全ての紙は今作るが、この外枠に押し込んで着手しない。
署名一本ごとの補正上端は全て800以内。全残りが29,000に入るとの主張ではなく、
ユーザー指定の「超える手前で完成した署名群を区切る」を実行する。
紙の範囲内の事前承認に従い、紙をコミットした後は止まらずP3-C1PNのLeanへ進む。
S7・R2・R3・P⁰は再開しない。旧R2の未追跡4本は編集・ビルド・コミットしない。
一覧：済み 18／全体 39（うち追加 4、別停止点 2）。

一括点検の道具の結果：39頂点・66辺のDAGで循環なし。旧36署名の完全な型と、承認されたC1PNの型は文字列で不変。未完署名の補正上端は全て800以下。証拠は `evidence/inf-supply/rescan-1117-evening/manifest.json`。


### P3-C1PN の証明分割（11-17夕、第一組）

紙のコミットは `46eb44e10`。39署名・66辺の非循環の一覧に従って続行中。
既存の本文・仮定・計算上限は変更していない。署名本体はまだ完了に数えない。

新規 `KanDiagramNaturalTransformationComposition.lean`（58物理行、引用も含め保守的に58数学行）に、
指定した通常の自然変換の実現の法則2本を分離した。型は次のとおり。

```lean
kanDiagramNaturalTransformationHom_eq_normalized :
  ∀ {I : Type u} [Category.{u} I] {F G : KanDiagramObject I}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget),
  Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated =
    normalizedVertexHomMap (kanDiagramRealization I) (kanDiagramRealization_vertex F).symm
      (kanDiagramRealization_vertex G).symm
      (Truncated.HomotopyCategory.homMk (coherentNerveEdge (kanDiagramHom η)).toTruncated)

kanDiagramNaturalTransformationHom_comp :
  ∀ {I : Type u} [Category.{u} I] {F G H : KanDiagramObject I}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (θ : G.val ⋙ kanObjectForget ⟶ H.val ⋙ kanObjectForget),
  Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge (η ≫ θ)).toTruncated =
    Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge θ).toTruncated
```

2本とも200行未満の既存構成の法則で、P3-C1PNの証明分割。点ごとの一致を仮定せず、元の図式全体の射を扱う。
対象ビルド成功、小監査はこのモジュールを所有する2宣言・標準三公理のみ。
数学行数は23,595 → **23,653**。C1PNの補正上端720を全て残りとして見ても24,373で、次の群への着手条件内。

一括点検で追加したR09-Cechの署名の型検査は成功。R15-Unitのlet内の端点証明は、
`nerveMap_app_mk₀`の命題等式を通すよう明示し、再検査中。これは存在する射・仮定・結論の変更ではなく、
同じ端点等式の証明の局所化と名前解決の明示化。型検査成功と証明完成は区別している。

区間評価の試験では、反転した自然変換の暗黙の端点推論が通常の200,000 heartbeatsに達した。
端点を明示し、既存のcoherent Homの頂点公式を独立に検証中。計算上限は上げていない。
証拠目録：`evidence/inf-supply/c1pn-native-composition-1117/manifest.json`。
旧R2の未追跡4本は変更・ビルド・コミットなし。S7・R2・R3は再開していない。

一覧：済み 18／全体 39（うち追加 4、別停止点 2）。


### P3-C1PN の指定頂点評価（11-17夕、第二組）

新規 `KanEnrichedHomIntervalVertices.lean` に既存区間構成の評価法則を分離した。
61物理行（引用も含め保守的に61数学行）、公開2宣言。いずれも200行未満でP3-C1PNの証明分割。
完全な型は次のとおり。

```lean
kanEnrichedDiagramHomInterval_vertex :
  ∀ {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌),
    intervalMappingEdgeOfVertex
      ((kanEnrichedDiagramHomInterval D X Y rfl rfl).app _ (ULift.up s)) =
    ((coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).map D.realization).ofEq
      (D.realization_vertex X) (D.realization_vertex Y)

kanEnrichedDiagramHomInterval_vertex_hom :
  ∀ {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌),
    Truncated.HomotopyCategory.homMk
      (intervalMappingEdgeOfVertex
        ((kanEnrichedDiagramHomInterval D X Y rfl rfl).app _ (ULift.up s))).toTruncated =
    normalizedVertexHomMap D.realization (D.realization_vertex X).symm (D.realization_vertex Y).symm
      (Truncated.HomotopyCategory.homMk
        (coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).toTruncated)
```

対象ビルド成功、所有2宣言の小監査は標準三公理のみ。数学行数は23,653 → **23,714**。
端点推論を明示した反転区間の試験も通常の計算上限で成功した。この反転の特殊化は別の新規モジュールとして対象検証中。
R09-Cech・R15-Unitの完全な署名の型検査はどちらも成功。これらの証明完成はまだ数えない。
証拠目録：`evidence/inf-supply/c1pn-interval-vertices-1117/manifest.json`。
P3-C1PN本体の残りは、元のνの指定Homとの照合。既存の全体の底変換・実現値の比較を使い、
任意の同型へのすり替えや点ごとの像の一致の仮定はしない。

一覧：済み 18／全体 39（うち追加 4、別停止点 2）。


### P3-C1PN の反転区間の類（11-17夕、第三組）

新規 `KanDiagramOppositeHomIntervalNatural.lean`（62物理行、引用も含め保守的に62数学行）。
反転区間の定値頂点は、元の自然変換を反転した同じ通常の自然変換の実現の射の類と一致する。
これはP3-C1PNの200行未満の評価法則の分割で、別の同型の存在を選んでいない。
完全な型：

```lean
lemma kanDiagramOppositeHomInterval_natural_hom {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    let τ : (F.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget ⟶
        (G.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget := Functor.whiskerRight η SSet.opFunctor
    Truncated.HomotopyCategory.homMk
      (intervalMappingEdgeOfVertex ((kanDiagramOppositeHomInterval F G).app _
        (ULift.up (SSet.const (strictDiagramMappingVertex η))))).toTruncated =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (G := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) τ).toTruncated
```

暗黙の二つの端点を明示するだけで、前の時間切れを通常の計算上限で解消した。
対象ビルド成功、所有1宣言の小監査は標準三公理のみ。
数学行数は23,714 → **23,776**。C1PNの新規の証明分割は累計181行。
証拠目録：`evidence/inf-supply/c1pn-opposite-verified-1117/manifest.json`。

接続の確認として、既存の `leftStraightening_baseChange_simplex_normalized`
（`LeftStraighteningSimplexPastingInputs.lean:36`）が、元のβの初頂点制限を
`leftClassificationSimplexIso` と `simplexSectionBaseChangeCoefficient` の共役へ既に同定している。
この宣言は作り直さず、P3-B1・P3-B2eと実現値の元のHomの評価を組み合わせる。
区間の右辺の計算は今回の法則で閉じたが、νそのもののHomの照合はまだ未完。
残りを証明済みとは報告しない。S7・R2・R3は停止のまま。

一覧：済み 18／全体 39（うち追加 4、別停止点 2）。


### P3-C1PN のνの正規化と、未列挙の成分分解（11-17夕）

#### 検証済み

新規 `LeftStraighteningTransportBaseChangeNormalization.lean`（57物理行、引用も含め保守的に57数学行）。
元の `leftStraightening_baseChange_simplex_normalized` を再利用し、指定νを単体切断の係数比較で正規化した。
P3-C1PN内の200行未満の構成の法則で、独立した完了署名には数えない。型：

```lean
lemma leftStraightening_baseChange_transport_normalized {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    let U := SSet.uliftFunctor.{u+1,u}
    let t := U.map (nerveMap (transportSimplexFunctor k))
    let q := pullback.snd p k
    let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
    let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
    let β := leftStraighteningInfinityDiagram_baseChangeIso p k
    let σp := (leftClassificationSimplexIso p).symm ≪≫ θp
    let σq := (leftClassificationSimplexIso q).symm ≪≫ θq
    (θp.precomp t).symm ≪≫
      diagramIsoCongr
        (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc]) rfl
        (β.precomp (U.map (transportSimplexFirstVertexMap D))) ≪≫ θq =
    (FunctorIso.precomp σp t).symm ≪≫ (simplexSectionBaseChangeCoefficient p k).symm ≪≫ σq
```

対象ビルド成功、所有3宣言（主補題と内部のinstance等）の小監査は標準三公理のみ。
文献属性はHTT §3.3.2の構成の特殊な法則として付けた。
数学行数は23,776 → **23,833**。今回のP3-C1PNの証明分割の実測は **238行**（58+61+62+57）。
既計上のC1Pの620行は重ねて数えない。
証拠：`evidence/inf-supply/c1pn-transport-normalization-3-1117/manifest.json`。

#### 未列挙の署名の提案：P3-C1PNV

一括点検では、θの成分の正規化をP3-C1PN内の小さい計算と見ていた。
元のβを既存の共役公式へ戻した結果、その次に必要なσの成分分解は、
coherentな対象での評価・二つの端点移送・同じ初頂点pullbackの射影をまとめて照合するため、
200行を超える見込みになった。独立した署名として以下を提案する。
**現在の39署名には未登録で、証明には入っていない。**

名前：`leftStraightening_firstVertexTransport_underValue`。
完全な型（`#check`成功。証明成功を意味しない）：

```lean
∀ {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p],
  let C := TransportSimplexCategory B
  let j := edgewiseEnrichedInfinityMap (LeftFibrationObject B)
  let b := leftFibrationEdgewiseFirstVertexBaseChange B
  let h : j ≫ (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
      leftStraighteningCoherentMap C) =
      b ≫ (edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve C)) ≫
        leftStraighteningCoherentMap C) := by
    rw [← Category.assoc, ← leftFibrationEdgewiseFirstVertexBaseChange_projection,
      Category.assoc]
  let γ := (transportSimplexUnderRealizationIso B).precomp j ≪≫
    ((transportSimplexUnderBaseChangeRealizationIso B).precomp j).symm ≪≫
    eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h) ≪≫
    (leftStraighteningCoherentMap_oppositeIso C).precomp b
  let X := edgewiseOrdinaryObject (leftFibrationObjectOf p)
  HEq ((leftClassificationSimplexIso p).symm ≪≫
      leftStraighteningInfinityDiagram_firstVertexTransportIso p)
    (functorIsoValue γ (coherentNerveVertex X))
```

依存先（台帳の他の署名）：なし。既存の指定構成の法則だけから作る。
P3-C1PNがこの署名に依存する向きで、提案を加えた依存グラフも道具で検査：40頂点・67辺、循環なし。
このHEqは元の全関手の同型そのものの成分比較で、各値の像の一致だけを仮定するものではない。
新しい仮定・chooseの置き換えは要らない。

| 使う既存の宣言 | 場所 |
|---|---|
| leftStraighteningInfinityDiagram_firstVertexTransportIso | `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningRepresentation.lean:79` |
| leftStraighteningInfinityMap_firstVertexOppositeIso | `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningOppositeRestriction.lean:53` |
| leftClassificationSimplexIso | `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftClassificationSimplexRestriction.lean:69` |
| functorIsoValue_trans | `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/FunctorIsoValueComposition.lean:24` |
| functorIsoValue_precomp | `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/FunctorIsoValueCurry.lean:75` |
| normalizedFunctorIsoComponent_heq_app | `SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/NormalizedFunctorIsoComponentRestriction.lean:31` |
| iso_endpoints_heq | `SerrePositivity/InfinityCategories/Project/LocalizationAndKanExtensionAuxiliaries/FunctorIsoPointEvaluation.lean:24` |

原典：HTT §3.3.2、Kerodon §5.6・Corollary 5.6.0.6（Tag 028T）の指定構成の照合法則。
独立した原典の定理番号に対応する一般定理とはしない。属性はHTTのspecial、Kerodon側はdocstringに特殊化を書く。

| 証明の分割 | 素の見込み | 係数2の見込み |
|---|---:|---:|
| 元の初頂点比較の全体の合成の分解 | 35〜55 | 70〜110 |
| 同じcoherent対象での成分と前合成の評価 | 60〜85 | 120〜170 |
| 単体切断値とpullbackの射影での端点正規化 | 60〜85 | 120〜170 |
| 指定した中間成分の相殺とHEqの接続 | 35〜45 | 70〜90 |
| **P3-C1PNV合計** | **190〜270** | **380〜540** |

一本の補正上端540は800以内だが、一覧にない署名なので、11-17夕の
「一覧にない署名が要るとき」に従い**ここでLeanを止める**。
この提案が通る場合、P3-C1PN本体の残り（既存P3-B1・B2eとの接続）は素80〜150・補正160〜300と見直す。
今回の実測238を含めるとC1PN本体は素318〜388・補正636〜776の見込み。
現在23,833に次の提案群540と本体残りの補正300を足して24,673で、29,000行の着手判定内。
これは承認や完了の主張ではない。29,000を超える手前で署名群を区切る規則は維持する。

補助試験として任意の源に対する自然性の端点正規化も試したが、公開モジュールには採用していない。
存在する元の全体の同型を使う道を保ち、計算上限は上げていない。
既存の本体の変更なし、他レーンのファイルの変更なし。
旧R2の未追跡4本はそのまま。S7・R2・R3・P⁰は再開していない。
現在の停止は5∞-1の完成ではなく、一覧外の署名が必要になったため。

一覧：済み 18／全体 39（うち追加 4、別停止点 2。P3-C1PNVは未登録）。


### P3-C1PNVの承認後の再開（11-17夕）

ユーザーの追加承認によりP3-C1PNVを登録。型・依存・既存参照・素190〜270、補正380〜540は前節のとおり。以後、既存構成の照合・合成則は、型・仮定・main本文を保ち一本の補正上端800以内なら記録して続行する。23,833＋540＝24,373なので着手。29,000を超える手前で署名群を区切る。

一覧：済み 18／全体 40（うち追加 5、別停止点 2）。


### P3-C1PNVの完成（11-17夕）

`LeftStraighteningFirstVertexTransportValue.lean` の `leftStraightening_firstVertexTransport_underValue`
を、承認された完全な型のまま証明した。mainの既存本文・仮定・計算上限の変更なし。
元の大域比較を先に分解し、同じ対象での評価を取った後、指定された端点移送を相殺する。
弱い存在命題からの選択や、別の自然同型への置き換えはない。

対象ビルド成功、所有9宣言の小監査は標準三公理のみ。文献属性はHTT §3.3.2のspecial、
Kerodon §5.6・Tag 028Tは構成の特殊化としてdocstringに記載。
素の見込み190〜270行（補正380〜540行）に対し、実測は171物理行を全て保守的に数学行へ計上。
検証済み累計は23,833 → **24,004行**。
証拠目録：`evidence/inf-supply/c1pnv-1117/manifest.json`。

内部の証明分割（いずれも200行未満、署名数には追加しない）の型：

```lean
firstVertexOpposite_factor : ∀ B : SSet.{u},
  leftStraighteningInfinityMap_firstVertexOppositeIso B =
    (leftStraighteningSimplexRestrictionIso B).precomp
      (edgewiseEnrichedInfinityMap (LeftFibrationObject B)) ≪≫ underOppositeComparison B

normalized_cancel : ∀ {L : Type*} [Category* L] {a b c a' b' c' : L}
    (e : a ≅ b) (f : b ≅ c) (ha : a = a') (hb : b = b') (hc : c = c'),
  HEq (((eqToIso ha).symm ≪≫ e ≪≫ eqToIso hb).symm ≪≫
    ((eqToIso ha).symm ≪≫ (e ≪≫ f) ≪≫ eqToIso hc)) f

normalize_of_heq : ∀ {L : Type*} [Category* L] {a b a' b' : L}
    (e : a ≅ b) (f : a' ≅ b') (ha : a = a') (hb : b = b') (h : HEq e f),
  (eqToIso ha).symm ≪≫ e ≪≫ eqToIso hb = f
```

`underOppositeComparison` は承認された型のlet γの右辺を同じ指定構成として固定したprivate略記。
次はP3-C1PN。今回の24373行の着手判定に対し実測24,004行なので、残りの補正上端300を足しても24,304行。
止まらず、既存の添字制限・実現値の法則を使って元のνと反転区間の類を照合する。
旧R2の未追跡4本はそのまま。S7・R2・R3は再開しない。

一覧：済み 19／全体 40（うち追加 5、別停止点 2）。


### P3-C1PNHの登録（11-17夕、指定実現の添字制限）

事前承認に従い、既存構成の法則 `kanDiagramNaturalTransformationHom_precomp` を独立に登録する。
元の自然変換の全図式の射を、同じ指定添字関手で制限した射と比較する。新しい数学・仮定・chooseの置き換えはなし。
P3-C1PNが依存する。再利用できる一般の計算法則なので独立した署名とし、小さい内部の合同則だけは証明分割として扱う。

```lean
∀ {I J : Type u} [SmallCategory I] [SmallCategory J] (H : I ⥤ J)
    {F G : KanDiagramObject J} (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget),
    kanFunctorHomCongr (kanDiagramCoherentNerve_precomp H F.val)
      (kanDiagramCoherentNerve_precomp H G.val)
      (precomposeFunctorHom ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H))
        (Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated)) =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨H ⋙ F.val, trivial⟩) (G := ⟨H ⋙ G.val, trivial⟩)
        (Functor.whiskerLeft H η)).toTruncated
```

既存宣言：`kanDiagramNaturalTransformationHom_eq_normalized` @
`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanDiagramNaturalTransformationComposition.lean:31`、
`KanEnrichedDiagram.realization_reindex` @同ディレクトリ`KanEnrichedDiagram.lean:195`、
`KanEnrichedDiagram.realization_homMk_of_homEquiv` @同ディレクトリ`KanEnrichedDiagramOrdinaryAction.lean:32`。
原典：HTT §1.1.5、Kerodon §2.4.3の構成の法則の特殊化（通常の小さい添字圏）。
素60〜100行、補正120〜200行。現在24,004＋200＝24,204行で着手条件内。mainの既存本文は変えない。

一覧：済み 19／全体 41（うち追加 6、別停止点 2）。


### P3-C1PNHの完成（11-17夕）

指定自然変換の全図式の射の添字制限則を証明した。対象ビルド・所有3宣言の小監査は成功し、標準三公理のみ。
素60〜100行・補正120〜200行に対し、実測78行（引用・見出しを含む物理行を全て保守的に計上）。
累計24,004 → **24,082行**。P3-C1PNの既計上238行とは別に一度だけ数える。
文献属性はHTT §1.1.5のspecial。主張・仮定・既存本文・計算上限の変更なし。
依存する端点証明のため関手の等式を直接rwできない箇所は、同じ関手と端点を保つ合同則へ局所化した。

内部の短い法則の型（署名数に含めない）：

```lean
normalized_map_congr : ∀ {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : f = g) {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌}
    (hf : x' = f.app _ x) (hf' : y' = f.app _ y)
    (hg : x' = g.app _ x) (hg' : y' = g.app _ y)
    (a : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y),
    normalizedVertexHomMap f hf hf' a = normalizedVertexHomMap g hg hg' a
```

証拠：`evidence/inf-supply/c1pn-native-precomp-1117/manifest.json`。
次のP3-C1PNの残り補正300を足して24,382行で、着手条件内。

一覧：済み 20／全体 41（うち追加 6、別停止点 2）。


### P3-C1PNOの登録（11-17夕、既存反転比較の同じ値の分解）

元の係数反転の指定比較の値を、同じ共通解像の左右の比較の値へ分解する既存構成の法則を登録。
新しい反転関手は作らず、main本文・一覧の他の型や仮定は変えない。P3-C1PNが依存する。
完全な型：

```lean
∀ {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J) (X : C),
  let Z := edgewiseOrdinaryObject X
  let z := coherentNerveVertex Z
  let j := edgewiseEnrichedInfinityMap C
  let hf : (j ≫ D.realization).app _ z =
      functorVertex (kanDiagramCoherentNerve (D.evaluate X)) := by
    change D.realization.app _ ((coherentNerveMap (edgewiseEnrichedRight C)).app _ z) = _
    rw [coherentNerveMap_vertex]
    exact D.realization_vertex X
  let hR := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj Y.val).obj)
  let hL := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj Y.val).obj)
  (eqToIso (congrArg (fun v => HomotopyCategory.mk v) hf)).symm ≪≫
    functorIsoValue D.oppositeRealizationIso z ≪≫
    eqToIso (congrArg (fun v => HomotopyCategory.mk v) (D.opposite.realization_vertex Z)) =
  (kanEnrichedRealizationValueIso D.edgewiseRightComparison hR Z).symm ≪≫
    kanEnrichedRealizationValueIso D.edgewiseLeftComparison hL Z
```

依存：なし。既存宣言と場所は `KanEnrichedDiagram.oppositeRealizationIso` @
`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedDiagramOppositeComparison.lean:42`、
`kanEnrichedRealizationValueIso` @同ディレクトリ `KanEnrichedRealizationValue.lean:58`、
`functorIsoValue_trans` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/FunctorIsoValueComposition.lean:24`、
`iso_endpoints_heq` @ `SerrePositivity/InfinityCategories/Project/LocalizationAndKanExtensionAuxiliaries/FunctorIsoPointEvaluation.lean:24`。
原典：HTT §1.1.5・Kerodon §3.1・§5.6（Tag 028T）の構成の特殊な照合。
素160〜250行、補正320〜500行。24,082＋500＝24,582で着手条件内。

一覧：済み 20／全体 42（うち追加 7、別停止点 2）。


### P3-C1PNO完成・P3-C1PNON登録（11-17夕）

P3-C1PNOは対象ビルド・所有5宣言の小監査成功、標準三公理のみ。
素160〜250行、補正320〜500行に対し実測115行。累計24,082 → **24,197行**。
証拠は `evidence/inf-supply/c1pn-opposite-factor-1117/manifest.json` にまとめる。
次に、同じ係数反転比較の指定自然変換に関する自然性をP3-C1PNONとして追加。既存構成の照合で新しい数学ではない。
完全な型：

```lean
∀ {J : Type u} [SmallCategory J] {F G : KanDiagramObject J}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget),
  let D := kanDiagramUniversalEnriched J
  let hR := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (KanDiagramObject J)) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj Y.val).obj)
  let hL := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (KanDiagramObject J)) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj Y.val).obj)
  let o := fun P : KanDiagramObject J =>
    (kanEnrichedRealizationValueIso D.edgewiseRightComparison hR (edgewiseOrdinaryObject P)).symm ≪≫
      kanEnrichedRealizationValueIso D.edgewiseLeftComparison hL (edgewiseOrdinaryObject P)
  Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated ≫
    (o G).hom = (o F).hom ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (G := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩)
        (Functor.whiskerRight η SSet.opFunctor)).toTruncated
```

依存：なし。使用する既存宣言：`kanEnrichedRealizationValueIso_hom` @
`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedRealizationValueHom.lean:31`、
`kanDiagramNaturalTransformationHom_comp` @同ディレクトリ `KanDiagramNaturalTransformationComposition.lean:43`、
`edgewiseRight_naturality`・`edgewiseLeft_naturality` @
`SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/EdgewiseEndpoints.lean:87`・`:99`。
原典：HTT §1.1.5、Kerodon §3.1・§5.6（Tag 028T）の既存の係数反転比較の自然性の特殊化。
素160〜250行、補正320〜500行。24,197＋500＝24,697で着手条件内。mainの既存本文と元の署名の型・仮定は変えない。

一覧：済み 21／全体 43（うち追加 8、別停止点 2）。


### P3-C1PNGの登録（11-17夕、三つの既存成分の合成の照合）

元のσを、同じunder制限・初頂点底変換・係数反転の三成分の値の合成へ照合する既存構成の法則を追加する。
型：

```lean
∀ {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p],
  (leftClassificationSimplexIso p).symm ≪≫
    leftStraighteningInfinityDiagram_firstVertexTransportIso p = firstVertexNativeCoefficientIso p
```

`firstVertexNativeCoefficientIso` は、新規 `LeftStraighteningNativeCoefficients.lean` で
既存の `kanEnrichedRealizationValueIso` を同じ対象に適用した三成分を合成するだけの略記。
その型は `∀ {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p], FunctorIso (simplexSectionValue p)
(leftCoherentTransport (pullback.snd p (transportSimplexFirstVertexMap B)))`。
右辺は `nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm ≪≫
nativeOppositeCoefficientIso (pullback.snd p (transportSimplexFirstVertexMap B))`。
各成分はそれぞれ既存のunder比較、`relativeSectionBaseChangeComparison`、左右のedgewise比較の同じ指定対象での値。
chooseの置き換え・新しい同型の選択・新しい数学はない。
依存P3-C1PNV・P3-C1PNO・P3-C1PNON。使用宣言・完全な場所はJSONのexisting欄。
原典：HTT §3.3.2・Kerodon §5.6（Tag 028T）の構成の特殊な照合。
素200〜350行、補正400〜700行（成分の略記も含む）。補正上端700は800以内。
先行PNONの補正500を全て残した保守的な判定でも24,197＋500＋700＝25,397で29,000以内。
新規ファイルで成分の型を先に確認し、その後に既存のσとの比較を閉じる。mainの既存本文・他レーンの枝は触らない。

一覧：済み 21／全体 44（うち追加 9、別停止点 2）。


### P3-C1PNONの完成（11-17夜）

元の自然変換に対する、指定された同じ係数反転比較の自然性を証明した。
左右の射影の自然性を同じcoherent実現に送り、右比較を相殺した全図式の射の等式。
型・仮定・main本文・計算上限の変更なし。追加のchooseはない。
素160〜250行、補正320〜500行に対し実測138行。対象ビルドと所有13宣言の小監査成功、標準三公理のみ。
P3-C1PNOの実測115行と合わせ、累計は24,082＋115＋138＝ **24,335行**。
引用の属性はどちらもHTT §1.1.5のspecial、Kerodon側はdocstringに構成の特殊化として記載。

再利用する短い法則も公開した（P3-C1PNON内の証明分割、署名数に追加しない）：

```lean
kanEnrichedRealizationValueIso_eq_native :
  ∀ {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E)
    (hη : ∀ j (X : C), IsQCatEquivalence ((η.component j).val X)) (X : C),
    kanEnrichedRealizationValueIso η hη X =
      kanDiagramFunctorIsoOfPointwise (F := ⟨D.evaluate X, trivial⟩)
        (G := ⟨E.evaluate X, trivial⟩) (η.app X) (fun j => hη j X)
```

P3-C1PNOの証拠：`evidence/inf-supply/c1pn-opposite-factor-1117/manifest.json`。
P3-C1PNONの証拠：`evidence/inf-supply/c1pn-opposite-naturality-1117/manifest.json`。
次のP3-C1PNGは補正上端700なので24,335＋700＝25,035行、着手条件内。止まらず続行。

一覧：済み 22／全体 44（うち追加 9、別停止点 2）。


### P3-C1PNBの登録（11-17夜、底変換の値の照合を一般形へ分離）

P3-C1PNGの初頂点底変換の値でkernelの決定的時間切れ。計算上限は上げず、任意の底変換の既存の指定成分の照合をP3-C1PNBへ分離する。新しい数学でなく、同じ `relativeSectionBaseChangeRealizationIso` の値の法則。
型：

```lean
∀ {B D : SSet.{u}} {J : Type u} [Category.{u} J]
      (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) (p : LeftFibrationObject B),
    HEq (kanEnrichedRealizationValueIso (relativeSectionBaseChangeComparison k A)
      (relativeSectionBaseChangeComparison_isQCatEquivalence k A) p)
      (functorIsoValue (relativeSectionBaseChangeRealizationIso k A) (coherentNerveVertex p))
```

依存なし。使用する既存宣言：`relativeSectionBaseChangeRealizationIso_normalized` @
`SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/SectionBaseChangeReindex.lean:35`、
`kanEnrichedRealizationValueIso` @
`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedRealizationValue.lean:58`、
`functorIsoValue_heq_of_heq` @
`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/FunctorIsoValueCurry.lean:26`。
原典：HTT §3.3.2、Kerodon §5.6（Tag 028T）の構成の特殊な照合。
素60〜120行、補正120〜240行。P3-C1PNGが依存する。
24,335＋240＋700＝25,275で、Gの残りを全て残しても29,000以内。型・仮定・main本文は変更しない。

一覧：済み 22／全体 45（うち追加 10、別停止点 2）。


### P3-C1PNBの完成（11-17夜）

底変換の指定成分の値を一般のパラメータのまま照合する法則が通った。
対象ビルドと所有1宣言の小監査成功、標準三公理のみ。計算上限・元の型と仮定・main本文の変更なし。
素60〜120行、補正120〜240行に対し実測53行。累計24,335 → **24,388行**。
P3-C1PNGの下書きはこの一般の法則を使うように分割し直して対象検証中。
証拠：`evidence/inf-supply/c1pn-basechange-value-1117/manifest.json`。

一覧：済み 23／全体 45（うち追加 10、別停止点 2）。


### P3-C1PNQの登録（11-17夜、同じ反転比較の添字制限）

指定した係数反転比較の値と、通常の添字関手による制限を照合する既存構成の法則を追加。
型：

```lean
∀ {I J : Type u} [SmallCategory I] [SmallCategory J] (H : I ⥤ J) (F : KanDiagramObject J),
    diagramIsoCongr (kanDiagramCoherentNerve_precomp H F.val)
      (kanDiagramCoherentNerve_precomp H (F.val ⋙ kanObjectOpFunctor))
      ((kanDiagramOppositeValueIso F).precomp ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H))) =
    kanDiagramOppositeValueIso ⟨H ⋙ F.val, trivial⟩
```

`kanDiagramOppositeValueIso F : FunctorIso (kanDiagramCoherentNerve F.val)
(kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))` は、P3-C1PNONの型のlet o Fの右辺を名付けた略記。
同じ普遍豊穣図式の左右の実現値の合成で、新しい反転関手や新しい同型の選択を作らない。
依存P3-C1PNH・P3-C1PNON。使用する既存宣言と完全な場所はJSONのexisting欄（添字制限、指定自然性、値の自然変換表示）。
原典：HTT §1.1.5、Kerodon §3.1・§5.6（Tag 028T）の構成の特殊な照合。
素120〜220行、補正240〜440行（同じ値の略記・自然性の回収も含む）。
Gの残りの上端700を全て残しても24,388＋700＋440＝25,528で着手条件内。
mainの既存本文・一覧の既存の型と仮定は変更しない。

一覧：済み 23／全体 46（うち追加 11、別停止点 2）。


### P3-C1PNGの完成（11-17夜）

`leftStraightening_firstVertexTransport_nativeCoefficients` を、登録した型のまま証明した。
元のσは、同じunder・初頂点底変換・係数反転の三成分の合成に一致する。
対象ビルド成功、二ファイルを所有する31宣言の小監査は標準三公理のみ。
素200〜350行・補正400〜700行に対し実測 **320行**（成分の略記160、比較160）。
引用を含む物理行を全て保守的に数学行として数え、累計24,388 → **24,708行**。
初頂点底変換のkernel時間切れは、二段の型移送を定義上一度に消さず、一段ずつHEqにして解消した。
heartbeats・maxRecDepth等は上げていない。mainの既存本文と元の署名の型・仮定は変更なし。
文献属性はHTT §3.3.2のspecial、Kerodon側はdocstringで構成の特殊化を記載。
証拠：`evidence/inf-supply/c1pn-native-coefficients-3-1117/manifest.json`。

短い内部の照合法則も同じ署名の証明分割として置いた（各200行未満）。型：

```lean
nativeUnderCoefficientIso_heq :
  ∀ {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p],
    HEq (nativeUnderCoefficientIso p)
      (functorIsoValue (transportSimplexUnderRealizationIso B) (leftFibrationInfinityVertex p))

nativeBaseChangeCoefficientIso_heq :
  ∀ {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p],
    HEq (nativeBaseChangeCoefficientIso p)
      (functorIsoValue (transportSimplexUnderBaseChangeRealizationIso B)
        (leftFibrationInfinityVertex p))

nativeOppositeCoefficientIso_heq :
  ∀ {C : Type u} [Category.{u} C] {E : SSet.{u}}
      (p : E ⟶ nerve C) [LeftFibration p],
    HEq (nativeOppositeCoefficientIso p)
      (functorIsoValue (leftStraighteningCoherentMap_oppositeIso C)
        (coherentNerveVertex (edgewiseOrdinaryObject (leftFibrationObjectOf p))))
```

`nativeUnderJointComparison` は、既存の `relativeFunctorOverPreComparison` の全成分を
元の共同実現に入る同じ比較として公開した略記。新しい数学・choose・新しい仮定はない。
P3-C1PNQは補正上端440なので24,708＋440＝25,148、着手条件内で検証を続行する。
旧R2の未追跡4本は変更も登録もしていない。

一覧：済み 24／全体 46（うち追加 11、別停止点 2）。


### P3-C1PNQ完成・P3-C1PNC登録（11-17夜）

P3-C1PNQは対象ビルド・所有10宣言の小監査成功、標準三公理のみ。
素120〜220行、補正240〜440行に対し実測118行。累計24,708 → **24,826行**。
証拠：`evidence/inf-supply/c1pn-opposite-precomp-1117/manifest.json` にまとめる。
元の単体切断の指定底変換係数を、同じ指定比較の通常の自然変換として読む照合P3-C1PNCを追加。
型：

```lean
∀ {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let F : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨(relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
        (leftFibrationObjectOf (pullback.snd p k)), trivial⟩
    let G : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨transportSimplexFunctor k ⋙
        (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p), trivial⟩
    HEq (simplexSectionBaseChangeCoefficient p k).hom
      (Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := F) (G := G) (simplexSectionNativeBaseChange p k)).toTruncated)
```

`simplexSectionNativeBaseChange p k` は、元の `relativeSectionBaseChangeComparison` の同じ成分を
`transportSimplexDomainFunctor_baseChange k` の元の定義域等式で移した自然変換の略記。
型は `(relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
(leftFibrationObjectOf (pullback.snd p k)) ⋙ kanObjectForget ⟶
(transportSimplexFunctor k ⋙ (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
(leftFibrationObjectOf p)) ⋙ kanObjectForget`。
単位・余単位を選び直さず、元の比較の成分をEq.mpで移すだけ。新しい数学・仮定・chooseはない。
依存P3-C1PNB。既存の `simplexSectionBaseChangeCoefficient_heq`、
`functorIso_transpose_postcomp_heq_value`、`relativeSectionBaseChangeValue_heq`、
`kanEnrichedRealizationValueIso_hom` を使う（場所と行はJSONのexisting欄）。
原典：HTT §3.3.2・Kerodon §5.6（Tag 028T）の指定構成の特殊な照合。
素200〜350行、補正400〜700行。24,826＋700＝25,526で着手条件内。
このHEqは元の全図式の射の指定された端点移送を保つ計算用の法則であり、P3-C1PNの結論の型は変えない。

一覧：済み 25／全体 47（うち追加 12、別停止点 2）。


P3-C1PNQの検証済みファイルをコミットする。元の同じ値の略記・自然性の回収・指定添字制限を含め118行。
主な宣言にHTT §1.1.5のspecial属性、Kerodon側はdocstringに構成の特殊化を記載。
次のCの下書きは未検証なのでこのコミットには含めない。
一覧：済み 25／全体 47（うち追加 12、別停止点 2）。


### P3-C1PNUの追加（11-17夜、既存構成の照合）


## P3-C1PNU（元のunder制限と単体切断の底変換の長方形）

```lean
∀ {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    simplexSectionNativeBaseChange p k ≫
      Functor.whiskerLeft (transportSimplexFunctor k)
        ((nativeUnderJointComparison B).app (leftFibrationObjectOf p)) ≫
      relativeSectionDiagramComparison (transportSimplexUnderBaseChangeTransformation k)
        (leftFibrationObjectOf p) =
    (nativeUnderJointComparison D).app (leftFibrationObjectOf (pullback.snd p k)) ≫
      (relativeSectionBaseChangeComparison k (transportSimplexUnderDomains D)).app
        (leftFibrationObjectOf p)
```

依存：P3-C1PNC・P3-C1PNG・P3-B2c。素200〜350行、補正400〜700行。
既存参照：
- `transportSimplexUnderTransformation_baseChange` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean:88
- `relativeFunctorBaseChangeForward_overPre` @ SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/FunctorCategories/RelativeFunctorBaseChangeNaturality.lean:89
- `relativeFunctorOverPre_comp` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorOverPrecomposition.lean:56
- `simplexSectionNativeTarget_eq` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/SimplexSectionNativeBaseChange.lean:41

HTT §3.3.2・Kerodon §5.6（Tag 028T）の指定構成の法則。元の制限と底変換の合成の特殊な照合。
新しい数学・仮定・chooseなし。元の定義域等式による移送、既存のunder三角形、底変換と制限の可換式だけを使用する。

24,826＋次の補正上端700＝25,526。現在検証中のCの実測を加えてから着手判定を再計算する。
一覧：済み 25／全体 48（うち追加 13、別停止点 2）。


### P3-C1PNLの追加（11-17夜、既存構成の合成則）


## P3-C1PNL（指定pullbackの二つの底変換との長方形）

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    Functor.whiskerLeft H
      ((relativeSectionBaseChangeComparison lB (strictTransportDomains (TransportSimplexCategory B))).app
        (leftFibrationObjectOf p)) ≫
      relativeSectionDiagramComparison (transportSimplexUnderBaseChangeTransformation k)
        (leftFibrationObjectOf p) =
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1 ≫
      (relativeSectionBaseChangeComparison lD (strictTransportDomains (TransportSimplexCategory D))).app
        (leftFibrationObjectOf q) ≫
      (relativeSectionBaseChangeComparison k (transportSimplexUnderDomains D)).app
        (leftFibrationObjectOf p)
```

依存：P3-C0・P3-B2b。素120〜220行、補正240〜440行。
既存参照：
- `pullbackStrictComparison_uncurry` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:334
- `leftStraighteningBaseChangePullbackData` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePullbackData.lean:27
- `relativeFunctorBaseChangeForward_uncurry` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorBaseChange.lean:58
- `relativeFunctorOverPre_uncurry` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorSquarePost.lean:68

HTT §3.3.2・Kerodon §5.6（Tag 028T）の指定構成の法則。指定pullbackの二座標と相対uncurryの既存の合成則の特殊化。
既存のαのuncurryの公式を同じ二つの射影へ合成する照合。親ファイルはこの枝の新規ファイルでmainには存在しない。既存本文を変えずprivate補題を追記する。

一覧：済み 25／全体 49（うち追加 14、別停止点 2）。


### P3-C1PNRの追加（11-17夜、既存構成の照合）


## P3-C1PNR（反転前の指定長方形の実現と相殺）

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let t := U.map (nerveMap H)
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    let Fh : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
    let Fr : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨leftStrictTransportFunctor r, trivial⟩
    let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
      pullbackStrictComparison p₀ r d.val H d.property.2.2.1
    let ν₀ := (FunctorIso.precomp
        (nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm) t).symm ≪≫
      (simplexSectionBaseChangeCoefficient p k).symm ≪≫
      nativeUnderCoefficientIso q ≪≫ (nativeBaseChangeCoefficientIso q).symm
    let hsrc : t ≫ leftStraighteningCandidate p₀ = kanDiagramCoherentNerve Fh.val := by
      change t ≫ kanDiagramCoherentNerve (leftStrictTransportFunctor p₀) =
        kanDiagramCoherentNerve (H ⋙ leftStrictTransportFunctor p₀)
      exact kanDiagramCoherentNerve_precomp H _
    ν₀.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hsrc) ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := Fh) (G := Fr) α).toTruncated
```

依存：P3-C1PNU・P3-C1PNL・P3-C1PNH・P3-C1PNC・P3-C1PNG。素180〜300行、補正360〜600行。
既存参照：
- `simplexUnderNativeBaseChange_square` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/SimplexUnderNativeBaseChange.lean:78
- `leftStraighteningBaseChange_native_pullback_square` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:632
- `kanDiagramNaturalTransformationHom_comp` @ SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanDiagramNaturalTransformationComposition.lean:43
- `kanDiagramNaturalTransformationHom_precomp` @ SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanDiagramNaturalTransformationPrecomposition.lean:47
- `simplexSectionBaseChangeCoefficient_native_hom` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/SimplexSectionNativeBaseChange.lean:125

HTT §3.3.2・Kerodon §5.6（Tag 028T）の指定構成の法則。上下の元の自然変換の長方形を実現し可逆な底変換を相殺する照合。
新しい数学・choose・仮定なし。前合成と自然変換の実現の既存法則、指定長方形U/L、同型の相殺だけを使用する。private αの同じ型を保持するため親の枝だけの新規ファイルにprivate補題として追記。

着手判定はU/Lの検証済み実測を加えた後で再計算する。補正上端600は800以内。
一覧：済み 25／全体 50（うち追加 15、別停止点 2）。


### P3-C1PNC・P3-C1PNU・P3-C1PNLの完成（11-17夜）

元の単体切断の指定底変換係数の自然変換による表示Cと、元のunderへの制限・二射影の上下の長方形U/Lを、登録した型のまま証明した。
対象3モジュール・所有53宣言の小監査成功、標準三公理のみ。Cだけの対象・12宣言の小監査も成功。
Cのwhnf時間切れは、元のEq.mprと同じ向きの一般の移送法則で二段を分けて解消した。
heartbeats・maxRecDepthなどの計算上限、mainの既存本文、元の型・仮定は変更していない。
文献属性はHTT §3.3.2のspecial、Kerodon Tag 028T側はdocstringに特殊な照合として記載。

| 署名 | 素の見込み | 補正の見込み | 実測 |
|---|---:|---:|---:|
| P3-C1PNC | 200〜350 | 400〜700 | 160 |
| P3-C1PNU | 200〜350 | 400〜700 | 119 |
| P3-C1PNL | 120〜220 | 240〜440 | 68（既存の枝だけの新規ファイルへの追記分） |

累計24,826 → **25,173行**。次のP3-C1PNRは補正上端600、25,173＋600＝25,773で着手条件内。
証拠：`evidence/inf-supply/c1pn-simplex-native-1117/manifest.json` と
`evidence/inf-supply/c1pn-native-upper-1117/manifest.json`。
台帳の参照行の更新で、名前が修飾された既存参照に更新スクリプトが停止したため修正した。
ソースの検証結果は影響を受けず、台帳の更新と検査を完了してコミットを確定する。
旧R2の未追跡4本は触っていない。署名50頂点の依存グラフは循環なし（Leanの型検査は済み署名のみ）。

一覧：済み 28／全体 50（うち追加 15、別停止点 2）。


### P3-C1PNR内の短い法則の証明分割（11-17夜）

以下はいずれも200行未満で、元の実現の合成・前合成・同型相殺の法則。独立署名として数えずP3-C1PNRに含める。

```lean
private lemma nativeRectangleHom_comp {J : Type u} [SmallCategory J]
    (F G K : KanDiagramObject J)
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (θ : G.val ⋙ kanObjectForget ⟶ K.val ⋙ kanObjectForget) :
    nativeRectangleHom F K (η ≫ θ) = nativeRectangleHom F G η ≫ nativeRectangleHom G K θ
```

```lean
private lemma nativeRectangleHom_precomp {I J : Type u} [SmallCategory I] [SmallCategory J]
    (H : I ⥤ J) (F G : KanDiagramObject J)
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (e : FunctorIso (kanDiagramCoherentNerve F.val) (kanDiagramCoherentNerve G.val))
    (he : e.hom = nativeRectangleHom F G η) :
    (diagramIsoCongr (kanDiagramCoherentNerve_precomp H F.val)
      (kanDiagramCoherentNerve_precomp H G.val)
      (e.precomp ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H)))).hom =
      nativeRectangleHom ⟨H ⋙ F.val, trivial⟩ ⟨H ⋙ G.val, trivial⟩ (Functor.whiskerLeft H η)
```

```lean
private lemma nativeRectangle_cancel.{v, w} {C : Type v} [Category.{w} C]
    {a b c d e f g : C} (x : a ≅ b) (u : b ≅ c) (v : d ≅ c)
    (s : a ≅ e) (t : f ≅ e) (z : e ≅ g) (w : c ⟶ g) (r : d ⟶ f)
    (h₁ : x.hom ≫ u.hom ≫ w = s.hom ≫ z.hom)
    (h₂ : v.hom ≫ w = r ≫ t.hom ≫ z.hom) :
    (v ≪≫ u.symm ≪≫ x.symm ≪≫ s ≪≫ t.symm).hom = r
```

`nativeRectangleHom F G η` は既存の `kanDiagramNaturalTransformationEdge η` の `homMk` の略記で、新しい選択はない。
一覧：済み 28／全体 50（うち追加 15、別停止点 2）。


### P3-C1PNRの完成（11-17夜）

上下の元の自然変換の長方形を全図式の射へ写し、同じ底変換の可逆な成分を相殺して、登録した反転前の共役の型を証明した。
対象1モジュール・所有40宣言の小監査成功、標準三公理のみ。
素180〜300行・補正360〜600行に対し実測**180行**（元の枝だけの新規ファイルへのimportと追記を含む）。
累計25,173 → **25,353行**。既存の本体・型・仮定・choose・計算上限は変更していない。
主な宣言はHTT §3.3.2 special属性つき、Kerodon Tag 028Tはdocstringで特殊化を記載。
証拠：`evidence/inf-supply/c1pn-native-rectangle-1117/manifest.json`。
次のP3-C1PNは補正上端720、25,353＋720＝26,073で着手条件内。

一覧：済み 29／全体 50（うち追加 15、別停止点 2）。


### P3-C1PNの短い端点移送法則（11-17夜）

以下の二つは200行未満の既存構成の照合で、P3-C1PNの証明分割として含める。

```lean
private lemma normalizedIsoHom_iff {A X : SSet.{u}} {f f' g : A ⟶ X}
    (hf : f = f') (e : FunctorIso f g) (a : FunctorHom f' g) :
    (diagramIsoCongr hf rfl e).hom = a ↔
      e.hom = eqToHom (congrArg (fun h => HomotopyCategory.mk (functorVertex h)) hf) ≫ a
```

`normalizedIso_rfl` の型：

```lean
∀ {A X : SSet.{u}} {f g : A ⟶ X} (e : FunctorIso f g),
  diagramIsoCongr rfl rfl e = e
```

元の同型・辺・余単位の選択を保つ。新しい数学・仮定・chooseなし。
一覧：済み 29／全体 50（うち追加 15、別停止点 2）。


### P3-C1PSの追加（11-17夜、既存構成の照合）


## P3-C1PS（同じscaffoldでの指定pointed比較）

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
    let i := U.map s.val
    let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
      (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
    let Rr := nerveLeftTransportRepresentation r
    let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
    let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
    let β := leftStraighteningInfinityDiagram_baseChangeIso p k
    let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
      diagramIsoCongr
        (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
    ∃ e : FunctorIso (i ≫ R₀.pointedMap) (i ≫ Rr.pointedMap),
      e.postcomp pointedSpaceProjection =
        (functorIsoOfEq (ν.precomp (U.map r)) R₀.pointedMap_projection.symm
          Rr.pointedMap_projection.symm).precomp i
```

依存：P3-C1PN・R01・R02・P3-C0。素200〜350行、補正400〜700行。
既存参照：
- `scaffoldPointedRelativeIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:456
- `oppositeHomComparison_at_natural` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:536
- `oppositeComparisonPointedBase` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:141
- `pointedIsoOfProjectedPrism` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:581
- `leftUnstraighteningEdgeLiftFamily_projection` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftUnstraighteningEdgeLiftFamily.lean:58

HTT §3.3.2・特に3.3.2.8、Kerodon §5.6（Tag 028T）の指定構成の法則。このscaffold上での指定pointed比較への特殊化。
既存のscaffold制限比較・反転Homの指定比較・全写像空間の持ち上げを同じ辺で合成する照合。新しい数学・仮定・choose・main既存本文の変更なし。

P3-C1PNの検証後に着手判定を再計算する。現在25,353行＋PNの補正上端720＋この補正上端700＝26,773で区切りの範囲内。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。


### P3-C1PNのkernel検査の分割（11-17夜）

P3-C1PNは戦術上は閉じたがkernel検査が既存の上限で時間切れ。計算上限は上げない。
主張の型を保持し、証明で使わない二つの表現のletを内部の芯の補題から省いた証明分割で検査箇所を切り分ける。元の署名には元どおり二つのletを残す。
内部の芯の完全型：

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let Fh : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨leftStrictTransportFunctor r, trivial⟩
  let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
  let ε := intervalMappingEdgeOfVertex y
  let hsrc : U.map (nerveMap H) ≫ leftCoherentTransport p₀ =
      kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor) := by
    change U.map (nerveMap H) ≫
      kanDiagramCoherentNerve (leftStrictTransportFunctor p₀ ⋙ kanObjectOpFunctor) =
      kanDiagramCoherentNerve ((H ⋙ leftStrictTransportFunctor p₀) ⋙ kanObjectOpFunctor)
    rw [kanDiagramCoherentNerve_precomp]
    rfl
  ν.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hsrc) ≫
    SSet.Truncated.HomotopyCategory.homMk ε.toTruncated
```

新しい構成・定理・仮定・chooseなし。PN内の証明分割として数える。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。

証明分割の生成が型内の `:= by` を区切りと誤認したので、完全な型と証明本体を分けて再生成した。主張の型は台帳の文字列をそのまま使用し、元のPNにも引用属性を保持した。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。


### P3-C1PNの分割箇所の局所化（11-17夜）

未使用のletを省いた内部の芯でもkernel時間切れとなったため、指定νの因子分解を独立に検査し、逆同型と前合成の計算を一般の同型の法則で処理する。いずれも200行未満の証明分割で、元のPNの型・仮定は保持。

```lean
private lemma nativeTwistInverseChain {K J X : SSet.{u}} (t : K ⟶ J)
    {f g h i : J ⟶ X} {fq gq hq iq : K ⟶ X}
    (a : FunctorIso f g) (b : FunctorIso h g) (o : FunctorIso h i)
    (c : FunctorIso fq (t ≫ f)) (aq : FunctorIso fq gq) (bq : FunctorIso hq gq)
    (oq : FunctorIso hq iq) :
    (FunctorIso.precomp (a ≪≫ b.symm ≪≫ o) t).symm ≪≫ c.symm ≪≫ aq ≪≫ bq.symm ≪≫ oq =
    (o.precomp t).symm ≪≫ (FunctorIso.precomp (a ≪≫ b.symm) t).symm ≪≫
      c.symm ≪≫ aq ≪≫ bq.symm ≪≫ oq
```

`nativeTransportIntervalFactorization`：

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let t := U.map (nerveMap H)
  let ν₀ := (FunctorIso.precomp
      (nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm) t).symm ≪≫
    (simplexSectionBaseChangeCoefficient p k).symm ≪≫ nativeUnderCoefficientIso q ≪≫
      (nativeBaseChangeCoefficientIso q).symm
  ν = ((nativeOppositeCoefficientIso p₀).precomp t).symm ≪≫ ν₀ ≪≫
    nativeOppositeCoefficientIso r
```

一覧：済み 29／全体 51（うち追加 16、別停止点 2）。


P3-C1PSの再利用先を補記（型・依存・見込みは変更なし）：
- `relativeFunctorVertexIsoImage_postcomp` @ SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/IndCompletionsOfInfinityCategories/RelativeFunctorVertexIsoProjection.lean:34
- `tautScaffold_map` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementFunctor.lean:97
- `tautScaffold_baseMap` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementBaseChange.lean:73
- `leftUnstraighteningEdgeLiftFamily_zero` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftUnstraighteningEdgeLiftFamily.lean:49
- `leftUnstraighteningEdgeLiftFamily_one` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftUnstraighteningEdgeLiftFamily.lean:67

全写像空間の持ち上げは元の同じ族で始点・射影を保ち、終点はその族から定義される。追加のchoose置き換えは不要。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。


P3-C1PNの短い係数反転の照合を一度だけ検査し、具体的な二成分の比較ではその補題を使う（200行未満、PNの証明分割）。

```lean
private lemma nativeOppositeCoefficientIso_eq_universal {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p] :
    nativeOppositeCoefficientIso p =
      kanDiagramOppositeValueIso ⟨leftStrictTransportFunctor p, trivial⟩
```

引用は元の具体的なtransportの因子分解とPNに付け、一般の逆同型の内部計算法則からは外す。型・仮定・選択・計算上限は変更しない。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。

因子分解でのletの全体的な簡約もwhnf上限に達した。既存の正規化定理の同じ結論を、必要なσ二成分を露出した型で直接受け、全体へのdsimpを避ける。計算上限は変更しない。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。


### mainの取り込み（11-17夜）

対象検証の区切りでmain 645f1dfa9（⑥の1fb2c6dccを含む）を取り込んだ。merge commit 2ce1cf7ee。未検証PNと紙の作業は保持し、旧R2の未追跡4本は触っていない。
型を露出しても因子分解のwhnf上限に達するため、その一宣言だけ診断ログを有効にして箇所を調べる。計算上限は上げない。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。

診断では、因子分解の書換え時に `leftFibrationBaseChangeEnriched` が8,055回、`KanEnrichedDiagram.evaluate` が2,471回展開されていた。ν全体の書換えをやめ、型を付けた二引数の合成式へσ二成分の等式を `congrArg₂` で写す。診断用optionは外し、上限は既存のまま。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。

診断の短い区切りでは、正規化・合同写像・逆同型の一般則・正規化と合同写像の合成まで通り、最後の略記の定義上の照合に上限がかかることを確認。以下の定義の法則を一度だけ証明し、合成式への合同写像で接続する（200行未満のPN内の証明分割）。

```lean
private lemma firstVertexNativeCoefficientIso_factorization {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    firstVertexNativeCoefficientIso p = nativeUnderCoefficientIso p ≪≫
      (nativeBaseChangeCoefficientIso p).symm ≪≫
        nativeOppositeCoefficientIso (pullback.snd p (transportSimplexFirstVertexMap B))
```

計算上限・元のPNの型・仮定・選択は変更なし。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。

最後の接続の括弧を点検し、PN内部の一般則の右辺を元のν₀の四因子のまとまりに合わせた。平坦な合成との結合則は一般則の内部で証明し、実際の大きな同型の定義上の結合性は要求しない。元の署名PNの型は変更しない。修正後の内部法則：

```lean
private lemma nativeTwistInverseChain {K J X : SSet.{u}} (t : K ⟶ J)
    {f g h i : J ⟶ X} {fq gq hq iq : K ⟶ X}
    (a : FunctorIso f g) (b : FunctorIso h g) (o : FunctorIso h i)
    (c : FunctorIso fq (t ≫ f)) (aq : FunctorIso fq gq) (bq : FunctorIso hq gq)
    (oq : FunctorIso hq iq) :
    (FunctorIso.precomp (a ≪≫ b.symm ≪≫ o) t).symm ≪≫ c.symm ≪≫ aq ≪≫ bq.symm ≪≫ oq =
    (o.precomp t).symm ≪≫ ((FunctorIso.precomp (a ≪≫ b.symm) t).symm ≪≫
      c.symm ≪≫ aq ≪≫ bq.symm) ≪≫ oq
```

一覧：済み 29／全体 51（うち追加 16、別停止点 2）。


### P3-C1PNの完成（11-17夜）

元の指定νの射を、同じpullbackの自然変換αの反転区間模型の指定辺の類へ同定した。
原署名の型（未使用のR₀・Rrのletも含む）・仮定・選択は変更していない。
元のνの正規化、三つの指定係数の同定、反転前の長方形の相殺、指定した係数反転の自然性と添字制限を順に使用した。
型の内部では同じ指定余単位と全図式の射を保ち、点ごとの像の一致だけに置き換えていない。

対象1モジュール・所有48宣言の小監査成功、標準三公理のみ。
診断traceを除いた最終ソースを `build-final.log` で再ビルド・再監査し、SHAを照合した。
素220〜360行・補正440〜720行に対し、実測**260行**（import・内部の小さい計算法則・型を保持する最終署名を含む）。
累計25,353 → **25,613行**。heartbeats・maxRecDepth等は上げていない。
大きな項の定義上の一致は要求せず、三成分の定義の等式と一般の結合則を使い、四因子のν₀のまとまりを保って接続したことで時間切れを解消した。
主な宣言はHTT §3.3.2のspecial属性、Kerodon Tag 028T側はdocstringで構成の特殊化を記載。
証拠：`evidence/inf-supply/c1pn-interval-native-1117/manifest.json`。

mainは645f1dfa9（⑥の1fb2c6dccを含む）を2ce1cf7eeで取り込み済み。
旧R2の未追跡4本は変更も登録もしていない。S7・R2・R3は再開しない。
次は記録済みP3-C1PS（補正上端700）。25,613＋700＝26,313で着手条件内。

一覧：済み 30／全体 51（うち追加 16、別停止点 2）。


### P3-C1PSの短い射影の計算法則（11-17夜）

新規補助ファイル `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RelativeFunctorIsoImageTransport.lean`。既存の `relativeFunctorVertexIsoImage_postcomp` を再利用し、同じ指定同型を前合成・端点移送したときの射影を計算する。200行未満で、Sの証明分割として数え、署名の型・見込みは変えない。新しい選択・仮定はない。

```lean
lemma functorIsoEq_precomp {A D X : SSet.{u}} {f g : A ⟶ X}
    (h : f = g) (i : D ⟶ A) :
    FunctorIso.precomp (eqToIso (congrArg (fun k => HomotopyCategory.mk (functorVertex k)) h)) i =
      eqToIso (congrArg (fun k => HomotopyCategory.mk (functorVertex k))
        (congrArg (fun k => i ≫ k) h))
```

```lean
lemma relativeFunctorVertexIsoImage_transport_projection
    {A D E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f g : A ⟶ E) (hf : f ≫ p = a) (hg : g ≫ p = a)
    (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg))
    (i : D ⟶ A) {f' g' : D ⟶ E} (hf' : i ≫ f = f') (hg' : i ≫ g = g')
    (hp : f' ≫ p = g' ≫ p) :
    (functorIsoOfEq ((relativeFunctorVertexIsoImage p a f g hf hg e).precomp i) hf' hg').postcomp p =
      eqToIso (congrArg (fun k => HomotopyCategory.mk (functorVertex k)) hp)
```

一覧：済み 30／全体 51（うち追加 16、別停止点 2）。

同じ指定辺のprismの前合成も、既存の `functorFamilyPrism_pre` で計算する短い法則としてSの補助ファイルに置く。200行未満の証明分割で署名は増やさない。

```lean
lemma functorEdgePrism_precomp {A D X : SSet.{u}} {f g : A ⟶ X}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (functorVertex f) (functorVertex g)) (i : D ⟶ A) :
    functorEdgePrism (F := i ≫ f) (G := i ≫ g)
      (e.map ((truncation 2).map ((pre i).app X))) =
      (Δ[1] ◁ i) ≫ functorEdgePrism e
```

一覧：済み 30／全体 51（うち追加 16、別停止点 2）。

短い底変換と端点移送の同一視もS内の計算法則として置く。補助ファイル全体は200行未満。前者は `relativeFunctorBaseChangeForward_vertex` を二端点で評価して同じ指定同型を写すだけで、後者は既存の移送のHEqを合成する。

```lean
lemma relativeFunctorBaseChangeForward_vertexIso {A E B D : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (a : A ⟶ D) (f g : A ⟶ pullback p k)
    (hf : f ≫ pullback.snd p k = a) (hg : g ≫ pullback.snd p k = a)
    (e : VertexIso (relativeFunctorVertex (pullback.snd p k) a f hf)
      (relativeFunctorVertex (pullback.snd p k) a g hg)) :
    ∃ (hf' : (f ≫ pullback.fst p k) ≫ p = a ≫ k)
      (hg' : (g ≫ pullback.fst p k) ≫ p = a ≫ k),
      Nonempty (VertexIso (relativeFunctorVertex p (a ≫ k) (f ≫ pullback.fst p k) hf')
        (relativeFunctorVertex p (a ≫ k) (g ≫ pullback.fst p k) hg'))
```

```lean
lemma functorIsoOfEq_eq_diagramIsoCongr {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') :
    functorIsoOfEq e hf hg = diagramIsoCongr hf hg e
```

一覧：済み 30／全体 51（うち追加 16、別停止点 2）。


### P3-C1PSの補助部分の検証（11-17夜）

新規補助ファイル `CartesianFibrations/RelativeFunctorIsoImageTransport.lean` の5宣言の対象ビルド・小監査成功、標準三公理のみ。
相対同型の射影の本体の宣言と、前合成・底変換・端点移送・prismの既存の構成の法則を再利用した。
新しい選択・仮定はなく、mainの既存の本文は変更していない。
実測**100行**。Sは未完のまま、検証済みの証明分割として累計に一度だけ加算する。
累計25,613 → **25,713行**。
Sの残りは素150〜300行・補正300〜600行とする。元の補正上端700に対し、検証済み100＋残り補正600＝700で着手枠を保っている。
次の判定25,713＋600＝26,313で今回の区切りの範囲内。補助ファイル全体は200行未満なので署名の数は増やさない。
主な射影公式にはHTT §3.3.2 special属性、Kerodon Tag 028Tはdocstringに特殊化として記載。
証拠：`evidence/inf-supply/c1ps-projection-1117/manifest.json`。

一覧：済み 30／全体 51（うち追加 16、別停止点 2）。


### P3-C1PSGの追加（11-17夜、既存構成の照合）


## P3-C1PSG（νに独立な三つの指定pointed比較）

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
    let i := U.map s.val
    let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
      (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
    let Rr := nerveLeftTransportRepresentation r
    let Fh : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
    let Fr : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨leftStrictTransportFunctor r, trivial⟩
    let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
      pullbackStrictComparison p₀ r d.val H d.property.2.2.1
    let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
    let ε := intervalMappingEdgeOfVertex y
    let FH := kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor)
    let FR := kanDiagramCoherentNerve (Fr.val ⋙ kanObjectOpFunctor)
    let v := U.map (tautScaffold (Fh.val ⋙ kanObjectForget))
    let f₀ := v ≫ oppositeKanUnstraighteningComparison Fh.val ≫ pullback.fst pointedSpaceProjection FH
    let f₁ := v ≫ oppositeKanUnstraighteningComparison Fh.val ≫
      leftUnstraighteningEdgeLiftMap FH FR ε ≫ pullback.fst pointedSpaceProjection FR
    let fT := v ≫ U.map (weightedNerveMap α) ≫ oppositeKanUnstraighteningComparison Fr.val ≫
      pullback.fst pointedSpaceProjection FR
    ∃ (h₀ : (i ≫ R₀.pointedMap) ≫ pointedSpaceProjection = f₀ ≫ pointedSpaceProjection)
      (h₁ : f₁ ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection)
      (hT : (i ≫ Rr.pointedMap) ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection),
      ∃ a₀ : FunctorIso (i ≫ R₀.pointedMap) f₀,
      ∃ a₁ : FunctorIso f₁ fT,
      ∃ aT : FunctorIso (i ≫ Rr.pointedMap) fT,
        a₀.postcomp pointedSpaceProjection = eqToIso
          (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h₀) ∧
        a₁.postcomp pointedSpaceProjection = eqToIso
          (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h₁) ∧
        aT.postcomp pointedSpaceProjection = eqToIso
          (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hT)
```

依存：R01・R02・P3-C0。素180〜300行、補正360〜600行。
既存参照：
- `scaffoldPointedRelativeIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:456
- `scaffoldPullbackData_eq` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:392
- `oppositeHomComparison_at_natural` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:536
- `oppositeComparisonPointedBase` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:141
- `relativeFunctorVertexIsoImage_transport_projection` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RelativeFunctorIsoImageTransport.lean:45
- `relativeFunctorBaseChangeForward_vertexIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RelativeFunctorIsoImageTransport.lean:71
- `tautScaffold_map` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementFunctor.lean:97
- `tautScaffold_baseMap` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementBaseChange.lean:73

HTT §3.3.2（特に3.3.2.8）・Kerodon §5.6（Tag 028T）の既存構成の法則。scaffold制限同型と元の全写像空間の区間族の三成分の照合。
νに依存しない三つの指定pointed比較を記録する。既に検証済みのC1P内の証明分割を使い、未完のC1P本体には依存しない。新しい数学・仮定・choose・mainの既存本文の変更なし。

Sの未完部分を、νに独立な三つのpointed比較と、元のνを使う接続に分ける。前者は独立して200行超の見込みなので署名を追加。後者は元のP3-C1PSの型を保ち、残り見込みを素100〜220・補正200〜440とする。補助100行は既に累計へ加算済みで二度数えない。
次の判定25,713＋600＝26,313。さらにSの補正440を一度に加えても26,753で29,000以内。
一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

P3-C1PSG内の短い射影の法則（200行未満、署名は増やさない）：

```lean
private lemma pointedProjection_of_under {A B : SSet.{u+1}}
    (F : B ⟶ SpaceInfinity.{u}) (g : A ⟶ leftUnstraightening F) (b : A ⟶ B)
    (hg : g ≫ leftUnstraighteningProjection F = b) :
    (g ≫ pullback.fst pointedSpaceProjection F) ≫ pointedSpaceProjection = b ≫ F
```

既存のpullbackの可換条件と指定した第二射影の式だけで証明する。
一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

### P3-C1PSの短い証明分割（11-17 夜）

P3-C1PSGと合わせても次のまとまりの補正上端は1,040行で、25,713＋1,040＝26,753。29,000以内なので続行する。次の三つは既存の辺の持ち上げ・端点移送・前合成の法則（各200行未満）で、署名は増やさない。

```lean
private lemma edgeLift_pointedIso {A B : SSet.{u+1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u})
      (functorVertex F) (functorVertex G))
    (d : FunctorIso F G)
    (hd : d.hom = SSet.Truncated.HomotopyCategory.homMk e.toTruncated)
    (c : A ⟶ leftUnstraightening F) (b : A ⟶ B)
    (hc : c ≫ leftUnstraighteningProjection F = b)
    (f g : A ⟶ PointedSpaceInfinity.{u})
    (hf : f = c ≫ pullback.fst pointedSpaceProjection F)
    (hg : g = c ≫ leftUnstraighteningEdgeLiftMap F G e ≫
      pullback.fst pointedSpaceProjection G)
    (hfp : f ≫ pointedSpaceProjection = b ≫ F)
    (hgp : g ≫ pointedSpaceProjection = b ≫ G) :
    ∃ a : FunctorIso f g, a.postcomp pointedSpaceProjection =
      functorIsoOfEq (d.precomp b) hfp.symm hgp.symm
```

```lean
private lemma pointedProjection_chain {A X : SSet.{u}}
    {fA f₀ f₁ fT fB l r : A ⟶ X}
    (hA : fA = f₀) (hN : f₁ = fT) (hT : fB = fT)
    (h₀ : l = f₀) (h₁ : r = f₁) (hF : l = fA) (hG : r = fB)
    (e : FunctorIso l r) :
    eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hA) ≪≫
      diagramIsoCongr h₀ h₁ e ≪≫
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hN) ≪≫
      (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hT)).symm =
        diagramIsoCongr hF hG e
```

```lean
private lemma functorIsoPrecomp_heq {A D X : SSet.{u}}
    {f g : A ⟶ X} (e : FunctorIso f g) {i j : D ⟶ A} (h : i = j) :
    HEq (e.precomp i) (e.precomp j)
```

対象ビルドの整理券が待機中であることを確認して追記した。検証器は鍵の取得後に対象ソースのSHAを採取し、終了時にも一致を確認する。
一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

P3-C1Pは元の登録済みの型のまま、P3-C1PSと検証済みpointedPrismOfRestriction・uliftPrecompへ接続した。次のまとまりの補正上端をP3-C1PSG 600＋S 440＋P 300としても25,713＋1,340＝27,053。29,000以内。整理券の待機中に追記し、鍵取得後の同じ対象検証へ含める。
一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

P3-C1PSの型のν.precompは、νが一般のIsoとして推論されドット記法が解決しないため、同じ既存関数FunctorIso.precompを明記した。数学的な型・仮定は変えず、名前解決だけの修正。P3-C1PSGとSの辺の持ち上げ・端点計算にはエラーなし。
一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

P3-C1PSのwhnf上限を避ける証明分割（200行未満の既存構成の法則）：指定νの具体的な三因子を接続の各段で展開せず、任意のνと既に証明した区間の辺の式を引数に取り、最後に元の同じνとP3-C1PNを代入する。新しい数学・仮定は元の主張に足さない。

```lean
private lemma scaffoldPointedComparison_of_intervalHom :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
    let i := U.map s.val
    let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
      (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
    let Rr := nerveLeftTransportRepresentation r
    let F₀ : KanDiagramObject (TransportSimplexCategory B) := ⟨leftStrictTransportFunctor p₀, trivial⟩
    let Fh : KanDiagramObject (TransportSimplexCategory D) := ⟨H ⋙ F₀.val, trivial⟩
    let Fr : KanDiagramObject (TransportSimplexCategory D) := ⟨leftStrictTransportFunctor r, trivial⟩
    let α := pullbackStrictComparison p₀ r d.val H d.property.2.2.1
    let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
    let ε := intervalMappingEdgeOfVertex y
    let hs : U.map (nerveMap H) ≫ leftCoherentTransport p₀ =
        kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor) :=
      kanDiagramCoherentNerve_precomp H (F₀.val ⋙ kanObjectOpFunctor)
    ∀ (ν : FunctorIso (U.map (nerveMap H) ≫ leftCoherentTransport p₀) (leftCoherentTransport r)),
      ν.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hs) ≫
        SSet.Truncated.HomotopyCategory.homMk ε.toTruncated →
    ∃ e : FunctorIso (i ≫ R₀.pointedMap) (i ≫ Rr.pointedMap),
      e.postcomp pointedSpaceProjection =
        (functorIsoOfEq (FunctorIso.precomp ν (U.map r)) R₀.pointedMap_projection.symm
          Rr.pointedMap_projection.symm).precomp i
```

一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

P3-C1PSの再見込み：一般のνに対する証明分割の型の記載を数え、残り素140〜300・補正280〜600（旧100〜220・200〜440）。P3-C1PSG・S・Pの三署名の着手判定は25,713＋600＋600＋300＝27,213。各署名の補正上端は800以下で、29,000以内。補助100行の二重計上なし。
一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

Sの計算の局所化：traceで正規化入力・中間の持ち上げ・中間の正規化までは通り、具体的なscaffoldの四因子の後合成のrwでwhnfに達すると確認した。次の二つを一般の射に対して一度だけ証明し、具体的な比較には適用だけを行う（既存の構成の法則、各200行未満）。

```lean
private lemma pointedProjection_fourChain {A : SSet.{u+1}}
    {fA f₀ f₁ fT fB : A ⟶ PointedSpaceInfinity.{u}}
    {l r : A ⟶ SpaceInfinity.{u}}
    (aA : FunctorIso fA f₀) (aM : FunctorIso f₀ f₁)
    (aN : FunctorIso f₁ fT) (aT : FunctorIso fB fT)
    (hA : fA ≫ pointedSpaceProjection = f₀ ≫ pointedSpaceProjection)
    (hN : f₁ ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection)
    (hT : fB ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection)
    (h₀ : l = f₀ ≫ pointedSpaceProjection) (h₁ : r = f₁ ≫ pointedSpaceProjection)
    (hF : l = fA ≫ pointedSpaceProjection) (hG : r = fB ≫ pointedSpaceProjection)
    (e : FunctorIso l r)
    (haA : aA.postcomp pointedSpaceProjection =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hA))
    (haM : aM.postcomp pointedSpaceProjection = diagramIsoCongr h₀ h₁ e)
    (haN : aN.postcomp pointedSpaceProjection =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hN))
    (haT : aT.postcomp pointedSpaceProjection =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hT)) :
    FunctorIso.postcomp (aA ≪≫ aM ≪≫ aN ≪≫ aT.symm) pointedSpaceProjection =
      diagramIsoCongr hF hG e
```

```lean
private lemma normalizedIso_precomp_pair {A B Z X : SSet.{u}}
    {F G : B ⟶ X} (e : FunctorIso F G)
    (p : A ⟶ B) (i : Z ⟶ A) (b : Z ⟶ B) (hb : i ≫ p = b)
    (f g : A ⟶ X) (hf : f = p ≫ F) (hg : g = p ≫ G)
    (hF : b ≫ F = i ≫ f) (hG : b ≫ G = i ≫ g) :
    diagramIsoCongr hF hG (e.precomp b) =
      (functorIsoOfEq (e.precomp p) hf.symm hg.symm).precomp i
```

一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

後合成のrwは一般の四因子の法則へ局所化した。続いて接続のkernel検査が時間切れなので、scaffold固有の定義を含まない一般の両端接続の法則へ分割し、scaffold版はその適用にする。計算上限は変えない。既存の構成の法則（200行未満）：

```lean
private lemma pointedComparisonOfEnds {A B Z : SSet.{u+1}}
    (p : A ⟶ B) (i : Z ⟶ A) (b : Z ⟶ B) (hb : i ≫ p = b)
    (F F' G : B ⟶ SpaceInfinity.{u}) (hs : F = F') (ν : FunctorIso F G)
    (ε : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F') (functorVertex G))
    (hε : (diagramIsoCongr hs rfl ν).hom = Truncated.HomotopyCategory.homMk ε.toTruncated)
    (f g : A ⟶ PointedSpaceInfinity.{u})
    (hf : f ≫ pointedSpaceProjection = p ≫ F) (hg : g ≫ pointedSpaceProjection = p ≫ G)
    (c : Z ⟶ leftUnstraightening F') (hc : c ≫ leftUnstraighteningProjection F' = b)
    (f₀ f₁ fT : Z ⟶ PointedSpaceInfinity.{u})
    (h₀ : f₀ = c ≫ pullback.fst pointedSpaceProjection F')
    (h₁ : f₁ = c ≫ leftUnstraighteningEdgeLiftMap F' G ε ≫ pullback.fst pointedSpaceProjection G)
    (geometry : ∃ (hA : (i ≫ f) ≫ pointedSpaceProjection = f₀ ≫ pointedSpaceProjection)
      (hN : f₁ ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection)
      (hT : (i ≫ g) ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection),
      ∃ aA : FunctorIso (i ≫ f) f₀, ∃ aN : FunctorIso f₁ fT, ∃ aT : FunctorIso (i ≫ g) fT,
        aA.postcomp pointedSpaceProjection =
            eqToIso (congrArg (fun z => HomotopyCategory.mk (functorVertex z)) hA) ∧
        aN.postcomp pointedSpaceProjection =
            eqToIso (congrArg (fun z => HomotopyCategory.mk (functorVertex z)) hN) ∧
        aT.postcomp pointedSpaceProjection =
            eqToIso (congrArg (fun z => HomotopyCategory.mk (functorVertex z)) hT)) :
    ∃ e : FunctorIso (i ≫ f) (i ≫ g), e.postcomp pointedSpaceProjection =
      (functorIsoOfEq (ν.precomp p) hf.symm hg.symm).precomp i
```

一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

Sの再見込みは型の記載を含め素200〜380・補正400〜760（各補正上端800以下）。三署名の着手判定は25,713＋600＋760＋300＝27,373で29,000以内。

### P3-C1の証明分割と再利用（11-17 夜）

親の対象ビルドの待ち時間に、依存先P3-C1Pを使う次のC1の本文を下書きした。未検証のためコミット・済みへの加算はしない。次は親が通ってから対象検証する。

短い既存構成の法則（本文68行、200行未満）：

```lean
private lemma transportWitnessIso_of_pointedPrism {E B : SSet.{u+1}}
    (p : E ⟶ B) [LeftFibration p] (R S : LeftTransportRepresentation p)
    (ν : FunctorIso R.diagram S.diagram)
    (W : (Δ[1] : SSet.{u+1}) ⊗ E ⟶ PointedSpaceInfinity.{u})
    (h₀ : prismEndpoint 0 E ≫ W = R.pointedMap)
    (h₁ : prismEndpoint 1 E ≫ W = S.pointedMap)
    (hp : W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫
      functorEdgePrism (functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom))) :
    ∃ a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S),
      R.diagramIso S a = ν
```

- `pullbackEdgeOfComponents` @ SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/PullbackEdgeRepresentatives.lean:29
- `pullbackEdgeOfComponents_snd` @ SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/PullbackEdgeRepresentatives.lean:81
- `exists_fullSubcomplexEdgeLift` @ SerrePositivity/InfinityCategories/Project/QuasicategoryAuxiliaries/VertexTransport/FullSubcomplexEdgeLift.lean:23
- `transportWitnessSpaceEdgeIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationEdgeIso.lean:28
- `transportWitnessSpaceDiagramEdge_hom` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationEdgeIso.lean:45

同じ節内の配置名を`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangeTransportWitness.lean`へ揃えた。型・仮定は登録済みのまま。素90〜180・補正180〜360（旧80〜140・160〜280）。現在の作業木の親を全て検証できたと仮定した実測は25,713＋574＝26,287で、次の補正上端360を足しても26,647。実際の着手判定は親の検証完了後に改めて行う。
一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

一般の接続則は検証を通るが、そのscaffoldへの代入のkernel検査が既定上限に達した。端点f₀・f₁・fTをP3-C1PSGの署名と同じ右結合の表示に揃え、持ち上げ元との比較はrflでなく既存のCategory.assocを明記して局所化する。元の主張・仮定・構成値は変えない。
一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

### 11-17 夜：目標解除による区切り

main の取り込みは `2ce1cf7ee` で完了。取り込み点は `645f1dfa9`（AlgebraicGeometry `1fb2c6dcc` を含む）。競合なし。main の作業木では作業していない。

目標解除の通知を受けて Lean を止めた。待機中だった `c1psg-1117/build-10.log` の自分の整理券だけをSIGINTで終了（exit 130）。待ちの重複・残存なし。他レーンのプロセスや鍵は操作していない。

検証済みの末尾は `ba3b207d8`、累計25,713行のまま。今回のP3-C1PSG・P3-C1PS・P3-C1Pは対象モジュール全体のビルド・小監査が未完なので、済みへの加算・Leanのコミットはしていない。一般の辺の持ち上げ・四因子の射影則・一般の両端接続則にはエラーなしだが、直近の完了した対象検証（build-8）はscaffoldへの代入の補助宣言のkernel上限で失敗した。続く結合則の明示版はまだ未検証。計算上限を上げていない。

build-9は共有鍵の待機中にシステム全体の `Too many open files in system` で終了。旧整理券が残っていないことをstatusで確かめて一枚で並び直したが、その後の目標解除により上記build-10を終了した。Leanの新しい検証結果としては数えない。

作業木の未検証Leanは次の2本：
- `LeftStraighteningBaseChangePointedPrism.lean`：P3-C1PSG・S・Pと短い既存構成の法則。型は台帳のまま、Sの前合成名の解決だけ明記。最後の変更は三端点の結合順序を先の署名と揃え、`Category.assoc`を使うもの。
- `LeftStraighteningBaseChangeTransportWitness.lean`：C1の下書き152行。親が通ってから検証する。

上の2本は同じ `InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/` にある。旧R2の未追跡4本は触らずに残した。S7・R2・R3は再開していない。台帳の依存DAG・完全な署名の記載・参照の所在は静的検査で再確認した（未実装の型のLean検証を意味しない）。この区切りは29,000行の停止点・5∞-1の完成ではなく、目標解除に伴う中断。

一覧：済み 30／全体 52（うち追加 17、別停止点 2）。

### 11-17 夜：目標再設定後、P3-C1PSG・S・Pの完成

前の目標ターンは、検証で次の修正箇所を特定し、実装・台帳・中断状態を記録したprogress。今回は作業木を再確認し、古い整理券なしをstatusで確認して一枚で再開した。mainは取り込んでいない。

最後の修正版（結合則Category.assocを明示した版）のbuild-11が成功：対象ビルド5,599 jobs、小監査1モジュール61宣言、標準三公理のみ。heartbeats・maxRecDepthを上げていない。主張・仮定と元の指定νを保ち、chooseの追加・mainの既存本文の変更なし。ソースSHAは検証開始時・終了時・記録時に一致。

|署名|最後の素の見込み|補正の見込み|今回の実測|
|---|---:|---:|---:|
|P3-C1PSG|180〜300|360〜600|224|
|P3-C1PSの残り|200〜380|400〜760|300|
|P3-C1Pの残り|90〜150|180〜300|55|

新規計上は579行、累計25,713＋579＝26,292。既計上のPの補助620行・Sの補助100行は二重に数えない。輸入・docstring込みの保守的な物理差分。主な三宣言にHTT §3.3.2のspecial属性を付け、Kerodon Tag 028Tの特殊化はdocstringに記した。

次のC1の補正上端360を足すと26,652で29,000以内。続けて、作業木のC1の下書き（152行）を対象ビルド・小監査する。旧R2の4本は触らない。

一覧：済み 33／全体 52（うち追加 17、別停止点 2）。

### 11-17 夜：P3-C1の完成

build-4で対象ビルド5,604 jobs・小監査1モジュール3宣言が成功（標準三公理のみ、ソースSHA照合済み）。元のνを保つwitnessまでつながった。名前空間と切断一次単体の添字の明記だけで閉じ、計算上限・主張・仮定の変更なし。
素90〜180・補正180〜360に対し実測157行。累計26,292＋157＝26,449行。P3-Dの現時点の補正上端440を足して26,889で区切り内。次はDに進む。mainと旧R2の4本は触っていない。

一覧：済み 34／全体 52（うち追加 17、別停止点 2）。

### P3-Dの短い既存構成の法則（11-17 夜）

次の四法則は登録済みDの証明分割（各200行未満）。新しい数学・choose・仮定は足さず、元の比較と指定cartesian制限を保つ。

```lean
lemma nativeRestrict_firstVertex_diamond
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B)
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let d := leftStraighteningBaseChangePullbackData p k
    (R.nativeRestrict lB).cartesianRestrict (U.map d.val) (U.map (nerveMap H))
      d.property.2.2.2 = (R.nativeRestrict k).nativeRestrict lD
```

```lean
lemma exists_nerveComparison_witness {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    ∃ a : VertexIso (transportWitnessVertex (nerveLeftTransportRepresentation p))
      (transportWitnessVertex R),
      (nerveLeftTransportRepresentation p).diagramIso R a = nerveCoherentTransportRepresentationIso p R
```

```lean
lemma nerveComparison_of_witness {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p))
    (a : VertexIso (transportWitnessVertex (nerveLeftTransportRepresentation p))
      (transportWitnessVertex R)) :
    (nerveLeftTransportRepresentation p).diagramIso R a = nerveCoherentTransportRepresentationIso p R
```

```lean
lemma nerveComparison_cartesian_witness
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E P : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (r : P ⟶ nerve D) [LeftFibration r]
    (e : P ⟶ E) (t : nerve D ⟶ nerve C)
    (h : IsPullback ((SSet.uliftFunctor.{u+1,u}).map e) ((SSet.uliftFunctor.{u+1,u}).map r)
      ((SSet.uliftFunctor.{u+1,u}).map p) ((SSet.uliftFunctor.{u+1,u}).map t))
    (a : VertexIso
      (transportWitnessVertex ((nerveLeftTransportRepresentation p).cartesianRestrict
        ((SSet.uliftFunctor.{u+1,u}).map e) ((SSet.uliftFunctor.{u+1,u}).map t) h))
      (transportWitnessVertex (nerveLeftTransportRepresentation r)))
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    (nerveCoherentTransportRepresentationIso p R).precomp ((SSet.uliftFunctor.{u+1,u}).map t) =
      ((nerveLeftTransportRepresentation p).cartesianRestrict
        ((SSet.uliftFunctor.{u+1,u}).map e) ((SSet.uliftFunctor.{u+1,u}).map t) h).diagramIso
        (nerveLeftTransportRepresentation r) a ≪≫
      nerveCoherentTransportRepresentationIso r
        (R.cartesianRestrict ((SSet.uliftFunctor.{u+1,u}).map e)
          ((SSet.uliftFunctor.{u+1,u}).map t) h)
```

- `LeftTransportRepresentation.ext` @ SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/LeftTransportRepresentation.lean:139
- `leftStraighteningBaseChangePullbackData` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePullbackData.lean:27
- `nerveCoherentTransportRepresentationIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/NerveStraighteningRepresentation.lean:25
- `smallFiberTransportRepresentationVertexIso_unique` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonCoherence.lean:26
- `LeftTransportRepresentation.cartesianRestrict_diagramIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonRestriction.lean:27
- `LeftTransportRepresentation.diagramIso_trans` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonCoherence.lean:77

依存：上の既存宣言、Dの本体はC1にも依存。HTT §3.3.2・Kerodon Tag 028Tの構成の法則で、独立した原典の定理は足さない。端点の移送を短い法則へ分割するため、Dの全体の再見込みは素200〜380・補正400〜760（旧120〜220・240〜440）。26,449＋760＝27,209で29,000以内。四法則の計175行程度と、後段の端点の移送・反映を含めた見込み。
一覧：済み 34／全体 52（うち追加 17、別停止点 2）。

P3-Dの後半の短い一般の合成・移送の法則（各200行未満）：

```lean
lemma congr_refl {A X : SSet.{u}} {f g : A ⟶ X} (e : FunctorIso f g) :
    diagramIsoCongr rfl rfl e = e
```

```lean
lemma precomp_base_congr {A B X : SSet.{u}} {F G : B ⟶ X}
    (e : FunctorIso F G) {p q : A ⟶ B} (h : p = q) :
    diagramIsoCongr rfl (congrArg (fun z => z ≫ G) h) (e.precomp p) =
      diagramIsoCongr (congrArg (fun z => z ≫ F) h.symm) rfl (e.precomp q)
```

```lean
lemma firstVertexBaseChange_isoAlgebra {B D K L X : SSet.{u}}
    (i : K ⟶ B) (j : L ⟶ D) (t : L ⟶ K) (k : D ⟶ B) (h : t ≫ i = j ≫ k)
    (F : B ⟶ X) (G : D ⟶ X) (T : B ⟶ X) (P : K ⟶ X) (Q : L ⟶ X)
    (θp : FunctorIso (i ≫ F) P) (θq : FunctorIso (j ≫ G) Q)
    (β : FunctorIso (k ≫ F) G) (γ : FunctorIso F T)
    (α : FunctorIso P (i ≫ T)) (a : FunctorIso Q (j ≫ k ≫ T))
    (hγ : γ.precomp i = θp ≪≫ α)
    (hA : let hs : j ≫ k ≫ F = t ≫ i ≫ F := congrArg (fun z => z ≫ F) h.symm
      diagramIsoCongr rfl (congrArg (fun z => z ≫ T) h) (α.precomp t) =
        ((θp.precomp t).symm ≪≫ diagramIsoCongr hs rfl (β.precomp j) ≪≫ θq) ≪≫ a) :
    β.precomp j ≪≫ θq ≪≫ a = (γ.precomp k).precomp j
```

依存：JointRealizationCompositionのdiagramIsoCongr_trans・CurryPrecompositionのdiagramIsoCongr_precomp、DiagramIsoNormalizationAlgebraのdiagramIsoCongr_trans_three、FunctorIsoWhiskerCancellationのfunctorIso_precomp_precomp、FunctorIsoWhiskerAlgebraのfunctorIso_precomp_trans。すべて既存の構成の法則。本文は約35行で、先のDの素200〜380・補正400〜760の見込みに含める。
一覧：済み 34／全体 52（うち追加 17、別停止点 2）。

Dの前半四法則は対象ビルド3,125 jobs・小監査2モジュール9宣言が成功（標準三公理のみ）。まだD全体は未完なので署名数・累計には加算しない。終端の等式での移送の短い法則（200行未満）：

```lean
private lemma nerveComparison_target_congr {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p]
    {R S : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)} (h : R = S)
    {F : (SSet.uliftFunctor.{u+1,u}).obj (nerve C) ⟶ SpaceInfinity.{u}}
    (e : FunctorIso F (leftCoherentTransport p)) :
    diagramIsoCongr rfl (congrArg (fun T => T.diagram) h)
      (e ≪≫ nerveCoherentTransportRepresentationIso p R) =
        e ≪≫ nerveCoherentTransportRepresentationIso p S
```

Dの本体は型を変えず、同じ節のCamelCaseのLeftStraighteningRepresentationBaseChangeFirstVertex.leanへ置いた。前半二本と一般の合成則と本体の四本を一緒に対象検証する。
一覧：済み 34／全体 52（うち追加 17、別停止点 2）。

Dの短い終端移送の法則の添字を訂正：Fの始域は任意のAでなく、既存のleftCoherentTransport pと同じ`(SSet.uliftFunctor.{u+1,u}).obj (nerve C)`。元の誤記は型が通らないもので、登録済みDの型・仮定は変えない。Dの証明では既存のlet束縛をintroで保ち、全体をdsimpして大きい比較を展開しない。
一覧：済み 34／全体 52（うち追加 17、別停止点 2）。

Dの終端移送の法則は、具体的なnerve比較でのsimpがwhnf上限に達したため、任意の同じ同型の族での法則へ分割する。先のprivateな終端移送の補助はこの一般の法則の適用に置き換える（元のDの型・仮定は不変）。既存構成の法則、200行未満：

```lean
lemma diagramIsoCongr_family_comp {A X : SSet.{u}} {Z : Type v}
    {F H : A ⟶ X} (G : Z → (A ⟶ X)) (a : ∀ z, FunctorIso H (G z))
    {r s : Z} (h : r = s) (e : FunctorIso F H) :
    diagramIsoCongr rfl (congrArg G h) (e ≪≫ a r) = e ≪≫ a s
```

依存：diagramIsoCongr @ JointRealizationComposition.lean:26、eqToIsoとIsoの恒等合成の法則。素約10行、補正20行、既に記録したDの全体の素200〜380・補正400〜760に含む。
一覧：済み 34／全体 52（うち追加 17、別停止点 2）。

Dの診断：型とintro・ν・底の等式・C1 witness・nerve比較・書き換え・native制限のダイヤモンドまでは通る。時間切れはhAの係数正規化で、toSquareやcartesianRestrictの展開が多数発生した。図式射影πのラムダ引数を`LeftTransportRepresentation (U.map r)`と明示し、congrArgと一般の族の法則に同じπを渡して局所化する。型・仮定・計算上限は不変。
一覧：済み 34／全体 52（うち追加 17、別停止点 2）。

Dの一般の合成・移送の法則で使う既存宣言の所在（完全パス、再確認）：
- `diagramIsoCongr` @ SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/JointRealizationComposition.lean:26
- `diagramIsoCongr_trans` @ SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/JointRealizationComposition.lean:44
- `diagramIsoCongr_precomp` @ SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/CurryPrecomposition.lean:116
- `diagramIsoCongr_trans_three` @ SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/DiagramIsoNormalizationAlgebra.lean:35
- `functorIso_precomp_precomp` @ SerrePositivity/InfinityCategories/Project/QuasicategoryAuxiliaries/MappingSpaces/FunctorIsoWhiskerCancellation.lean:22
- `functorIso_precomp_trans` @ SerrePositivity/InfinityCategories/Project/QuasicategoryAuxiliaries/MappingSpaces/FunctorIsoWhiskerAlgebra.lean:43

一覧：済み 34／全体 52（うち追加 17、別停止点 2）。

### 11-17 夜：P3-Dの完成

build-7で最終版の対象ビルド5,610 jobs、小監査4モジュール16宣言が成功（標準三公理のみ、現行SHA一致）。主な四宣言にHTT §3.3.2のspecial属性、Kerodon Tag 028Tの特殊化はdocstring。元のDの型・仮定・指定νを保持し、main既存本文・choose・計算上限の変更なし。診断用trace・オプションは除去した。

Dの初期見込みは素120〜220・補正240〜440、分割後の再見込みは素200〜380・補正400〜760、実測は332行（59＋93＋86＋94、輸入・docstring込み）。型を明示した図式射影πを共有した版で、hAのwhnf上限は解消した。短い法則の型と既存参照は上記に記録済み。
累計26,449＋332＝26,781。次のEの補正上端220を足すと27,001で29,000以内。Eは初頂点制限の充満忠実性で反映する。旧R2の4本・mainは触っていない。

一覧：済み 35／全体 52（うち追加 17、別停止点 2）。

P3-Eは登録済みの型のまま、同じ節のCamelCaseのLeftStraighteningRepresentationBaseChangeLaw.leanに置く。Dの初頂点での比較を既存の局所化による制限の充満忠実性で反映する。新しい数学・補助の署名・choose・main既存本文の変更なし。
一覧：済み 35／全体 52（うち追加 17、別停止点 2）。

### 11-17 夜〜11-18 未明：P3-Eの完成、第3項の全族比較の接続完了

build-3で対象ビルド5,611 jobs・小監査1モジュール1宣言が成功（標準三公理のみ、現行SHA一致）。初頂点の定義先の名前空間を正して、Dを既存の充満忠実性で反映できた。元のEの型・仮定・全同型の類は変えない。HTT special属性とKerodon特殊化のdocstringを付けた。
素50〜110・補正100〜220に対し実測52行。累計26,781＋52＝26,833。次のR04の補正上端800を足して27,633で29,000以内なので着手する。S7・R2・R3、旧R2の4本、mainは触っていない。

一覧：済み 36／全体 52（うち追加 17、別停止点 2）。

### R04の中間極限の消去（11-18 未明）

R04の既存構成の合成則の証明分割（各200行未満、署名数は増やさない）。chooseの選び方を変えず、元の三因子と全極限錐を使う。二つ目のE・Fのquasicategory性は、元のconstructorと同じquasicategory_of_innerFibrationで入力から出るもので、R04へ仮定を足さない。

```lean
lemma iso_span_middle {C : Type u} [Category.{v} C] {x y s₁ s₂ t₁ t₂ : C}
    (a₁ : x ≅ s₁) (a₂ : x ≅ s₂) (m₁ : s₁ ≅ t₁) (m₂ : s₂ ≅ t₂)
    (c₁ : y ≅ t₁) (c₂ : y ≅ t₂) (s : s₁ ≅ s₂) (t : t₁ ≅ t₂)
    (ha : a₁ ≪≫ s = a₂) (hm : s ≪≫ m₂ = m₁ ≪≫ t) (hc : c₁ ≪≫ t = c₂) :
    a₁ ≪≫ m₁ ≪≫ c₁.symm = a₂ ≪≫ m₂ ≪≫ c₂.symm
```

```lean
lemma limitVertexIsoOfOverEquivalence_span_middle
    {A B C D K X : SSet.{u}} [Quasicategory A] [Quasicategory B]
    [Quasicategory C] [Quasicategory D] [Quasicategory X]
    (a : A ⟶ B) (b : B ⟶ C) (c : D ⟶ C)
    (ha : IsQCatEquivalence a) (hb : IsQCatEquivalence b) (hc : IsQCatEquivalence c)
    {p : A ⟶ K} {q : B ⟶ K} {r : C ⟶ K} {s : D ⟶ K}
    (hwa : a ≫ q = p) (hwb : b ≫ r = q) (hwc : c ≫ r = s) (O : K ⟶ X)
    (c₀ : JoinCone (p ≫ O)) (d₀ : JoinCone (s ≫ O))
    (s₁ s₂ : JoinCone (q ≫ O)) (t₁ t₂ : JoinCone (r ≫ O))
    (hc₀ : IsLimitCone c₀) (hd₀ : IsLimitCone d₀)
    (hs₁ : IsLimitCone s₁) (hs₂ : IsLimitCone s₂)
    (ht₁ : IsLimitCone t₁) (ht₂ : IsLimitCone t₂) :
    limitVertexIsoOfOverEquivalence a ha hwa O c₀ s₁ hc₀ hs₁ ≪≫
      limitVertexIsoOfOverEquivalence b hb hwb O s₁ t₁ hs₁ ht₁ ≪≫
      (limitVertexIsoOfOverEquivalence c hc hwc O d₀ t₁ hd₀ ht₁).symm =
    limitVertexIsoOfOverEquivalence a ha hwa O c₀ s₂ hc₀ hs₂ ≪≫
      limitVertexIsoOfOverEquivalence b hb hwb O s₂ t₂ hs₂ ht₂ ≪≫
      (limitVertexIsoOfOverEquivalence c hc hwc O d₀ t₂ hd₀ ht₂).symm
```

```lean
lemma limitVertexIsoOfLeftStraighteningIso_eq_middle
    {E F B X : SSet.{u}} [Quasicategory E] [Quasicategory F]
    [Quasicategory B] [Quasicategory X]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))
    (O : B ⟶ X) (c : JoinCone (p ≫ O)) (d : JoinCone (q ≫ O))
    (hc : IsLimitCone c) (hd : IsLimitCone d)
    (s : JoinCone (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O))
    (t : JoinCone (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O))
    (hs : IsLimitCone s) (ht : IsLimitCone t) :
    limitVertexIsoOfLeftStraighteningIso p q e O c d hc hd =
      limitVertexIsoOfOverEquivalence (leftStraighteningInfinityReconstruction p)
        (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence
        (leftStraighteningInfinityReconstruction_projection p) O c s hc hs ≪≫
      limitVertexIsoOfOverEquivalence (smallLeftUnstraighteningComparisonOfFunctorIso e)
        (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence e).isQCatEquivalence
        (smallLeftUnstraighteningComparisonOfFunctorIso_projection e) O s t hs ht ≪≫
      (limitVertexIsoOfOverEquivalence (leftStraighteningInfinityReconstruction q)
        (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q).isQCatEquivalence
        (leftStraighteningInfinityReconstruction_projection q) O d t hd ht).symm
```

- `limitVertexIsoOfLeftStraighteningIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningLimitVertex.lean:27
- `limitVertexIso_hom_comp_overEquivalence` @ SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/OverEquivalenceLimitComposition.lean:53
- `limitVertexIsoOfOverEquivalence_hom_comp` @ SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/OverEquivalenceLimitComposition.lean:68

依存は上の既存の合成則のみ。原典：HTT §1.2.13・5.1.5.6の既存構成の法則、Kerodon §7.1 Tag 02K2・§5.6 Tag 028Tの特殊化。二本の素の見込み180〜230行、補正360〜460行はR04全体の素250〜400・補正500〜800に含む。今回の着手判定は26,833＋800＝27,633で29,000以内。
一覧：済み 36／全体 52（うち追加 17、別停止点 2）。

R04の復元・指定底変換の照合の短い証明分割（各200行未満）。P3-Eと、既存の前後合成の交換則を同じ指定eへ適用する：

```lean
lemma iso_conjugation_square {𝒞 : Type u} [Category.{v} 𝒞]
    {a b c d r s : 𝒞} (bf : a ≅ b) (bg : c ≅ d) (z : a ≅ c)
    (ef : b ≅ r) (eg : d ≅ s) (f : a ≅ r) (g : c ≅ s) (k : r ≅ s)
    (hf : bf ≪≫ ef = f) (hg : bg ≪≫ eg = g) (hn : z ≪≫ g = f ≪≫ k) :
    (bf.symm ≪≫ z ≪≫ bg) ≪≫ eg = ef ≪≫ k
```

```lean
lemma leftPullbackClassificationIso_representation_naturality
    {E B K : SSet.{u}} [Quasicategory B] [Quasicategory K]
    (p : E ⟶ B) [LeftFibration p] {f g : K ⟶ B} (e : FunctorIso f g)
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    leftPullbackClassificationIso p e ≪≫
      leftStraighteningInfinityDiagram_representationIso (pullback.snd p g) (R.nativeRestrict g) =
    leftStraighteningInfinityDiagram_representationIso (pullback.snd p f) (R.nativeRestrict f) ≪≫
      (functorIso_ulift.{u,u+1} e).postcomp R.diagram
```

- `leftPullbackClassificationIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftPullbackLimitTransport.lean:32
- `leftStraighteningInfinityDiagram_representationIso_baseChange` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningRepresentationBaseChangeLaw.lean:33
- `functorIso_whisker_exchange` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/TheInfinityCategoryQC/FunctorIsoWhiskerExchange.lean:31

原典はHTT §3.3.2・Kerodon Tag 028Tの既存構成の法則。この一本は素50〜80・補正100〜160行をR04全体の見込みに含める。分類同型・表現比較は元のものを使い、chooseや仮定を追加しない。
一覧：済み 36／全体 52（うち追加 17、別停止点 2）。

### 11-18 未明：R04の三本の証明分割を検証（本体は継続）

中間の二極限の選択を消去する二本と、指定引き戻し分類同型を同じ表現上の作用へ戻す一本が、同時の対象ビルド5,634 jobs・小監査3モジュール6宣言を通過（標準三公理のみ、開始・終了・記録時にソースSHA一致）。

|補助ファイル|最後の素の見込み|実測|
|---|---:|---:|
|OverEquivalenceLimitSpan＋LeftStraighteningLimitVertexComputations|180〜230|148|
|LeftPullbackRepresentationComparison|50〜80|70|

148＋70＝218行を新規計上。累計26,833＋218＝27,051。R04の本体を済みにはしていない。残る元の余単位に沿う輸送錐・apexの比較とeqToHomの正規化は、登録済みR04の型のまま進める。現段階では安全側に元の補正上端800を残りにも保持し、27,051＋800＝27,851で29,000以内。218行の二重計上はしない。

CH067の選択条件を変えていない。新しい計算補助の証明内のs₀・t₀は、元のHasLimitの同じ命題の証明から選ぶ元の中間極限で、proof irrelevanceを通して元のconstructorの値へ展開し、既存の合成則で消去する。別の弱い存在命題から指定比較を選び直していない。mainの既存本文・元のconstructor・公開の型・仮定・計算上限の変更はない。

この時点は正式な停止点ではない。次はR04本体の指定余単位とapexの照合を続ける。R05以降・R16/R17は未完。S7・R2・R3は再開せず、旧R2の未追跡4本は触っていない。検証済みの三本をコミットし、作業木の未追跡はその4本だけになる。mainは取り込んでいない。

一覧：済み 36／全体 52（うち追加 17、別停止点 2）。

### 11-18：台帳本文の古い状態・見込みの表示を訂正

現状を確認すると、JSONのR04は承認済み洗い直し表どおり素250〜400・補正500〜800なのに、MDの当初の章には250〜450・500〜900が残っていた。P3のいくつかの章もpendingの表示が残っていた。最新のJSON・検証記録へ表示を揃え、MD先頭に全52署名の現在状態・残り見込みを生成した。型・仮定・見積もり自体は変更していない。型の章・検証履歴は保持する。
自分の枝だけにある台帳検査器へ状態表の一致検査と--syncを加え、今後は古い状態・停止判定の見込みの表示では検査が失敗する。これはLeanの未実装の型の検証や成功を意味しない。R04本体は未完、累計27,051と残り補正上端800による27,851の着手判定は変わらない。

一覧：済み 36／全体 52（うち追加 17、別停止点 2）。

### 11-18：R04の相対逆射による普遍錐の移送（短い証明分割）

元の復元射を変えず、既存の相対逆射に沿って任意の錐を制限する。新しい数学の入力・chooseの置き換えはない。型は次のとおり。

```lean
lemma leftStraighteningInfinityReconstruction_coneInverse
    {E B D : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (O : B ⟶ D) (c : JoinCone (p ≫ O)) :
    let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p)
    let r := leftStraighteningInfinityReconstruction p
    ∃ (g : smallLeftUnstraightening (leftStraighteningInfinityDiagram p) ⟶ E)
      (hg : g ≫ p = q),
      Nonempty (VertexIso
        (relativeFunctorVertex p p (r ≫ g)
          (by rw [Category.assoc, hg, leftStraighteningInfinityReconstruction_projection]))
        (relativeFunctorVertex p p (𝟙 E) (Category.id_comp p))) ∧
      ∃ d : JoinCone (q ≫ O), d.vertex = c.vertex
```

依存はR02と既存の `exists_relativeFunctorInverse_of_precompositionEquivalence` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RelativeFunctorInverse.lean:31、`restrictJoinCone` @ SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/LimitConeExtension.lean:28、`JoinCone.vertex_cast` @ SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/TerminalMap.lean:115。原典HTT §3.3.2、Kerodon Tag 028Tの既存構成の法則。素40〜70行・補正80〜140行で、R04全体の補正上端800内に含む。200行未満の証明分割なのでIDは増やさない。まだ未検証であり、R04の完了ではない。

一覧：済み 36／全体 52（うち追加 17、別停止点 2）。

### 11-18：R04の相対逆射による錐の移送を検証

`LeftStraighteningReconstructionConeInverse.lean` の対象ビルド（3,123 jobs）と2宣言の小監査が成功。標準三公理のみ、開始・終了・記録時のソースSHA一致。素40〜70行に対し実測56行。累計27,107行、R04の検証済み部分は274行。署名R04本体は未完で、指定余単位を保つ二つの局所錐と元の分類spanとの照合を続ける。残り補正上端800を保持し、27,107＋800＝27,907で着手条件内。main本文とchooseの変更、計算上限の増加はない。旧R2の未追跡4本はそのまま。

一覧：済み 36／全体 52（うち追加 17、別停止点 2）。
