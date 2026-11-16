# ⑤∞ A-1 段0：∞層 S1〜S8（11-12夜、紙）

IS-W1 段3の上限再見積もりに伴う、承認済みの代替作業。実装の承認や完了を主張しない。
正本は `bhatt-scholze/infinity-sheaves-design.md` と `drafts/Sheaves/` 全7本。
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
