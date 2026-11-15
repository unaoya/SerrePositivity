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
