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
| S3 | `IsLimitCone c ↔ IsLimitCone (restrictJoinCone c (cechShape d))`；逆向き `∃ c, IsLimitCone c ∧ restrictJoinCone c (cechShape d) = c₀`（元の頂点の指定Čech錐を保つ）。大きいsite版も同じ頂点 | G9のleft cofinality、CategoryTheory/CechNerveData。600〜1,000行 |
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
