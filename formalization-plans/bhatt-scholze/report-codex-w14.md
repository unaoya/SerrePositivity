# BS-W14 停止点 0

`math/bs-impl` に `main`（`07d8bd691`、指示書と設計は `d26906658`）を取り込んで調べた。以下はソースを照合した型案。ビルド、Lean の型検査、公理監査は段 0 の対象外。判定の「証明済み」は本体に同じ強さの宣言がある場合、「一部」は模型側に構成・比較・特殊例がある場合、「なし」は該当する本体の構成を確認できなかった場合を指す。

## 1. 依存と本体の範囲

- `SerrePositivity/BhattScholze/` 内の Lean 宣言には `CAlg_R` や実忘却を使う箇所は見つからなかった。`Perfectoidization/Derived/Interface.lean` の「CAlg 版」は説明で、同ファイルの E3 は D(R) 版。一般の `CommAlgCat` や環の under 圏はそのまま使える。
- 本体の **`SerrePositivity/EInfinity/Perfectoidization/`** には実際の BS の利用がある。`Comparison` の `algebraEmbeddingForgetIso`・`underlyingUnit`・`underlyingUnit_hom`・`targetCAlgDiagramForgetIso`・`forget_pullback`、`Interface` の `BSLimitConeDataCAlg`・`PerfectoidizationInterfaceCAlg`、`DerivedCorollary` の `BSLimitConeDataCAlg.underlying_isLimit`・`PerfectoidizationInterfaceCAlg.toE3`・`nonempty_e3_of_cAlg`。指定錐の境界で同じ `discrete_forget` を使い、単位の実代表と `comparison_boundary` を保持する。新しい一般版を別名で追加し、既存の公開宣言は模型への特殊化・互換用として保つ案。G1′ の `h0 : H0RingData …` は既存の乗法・指定射の情報を持つため、`pi0` の追加だけを理由に消さない。
- D71 の import をソースから再帰的に追った。候補の D(R)・離散埋め込み・ホモロジー・テンソル・presentable の入口に `BarrattEccles` と `Hammock` への経路は見つからなかった。一方、既存の `derivedInfinityCategory` にも `Derived/InfinityCategory → DGNerve → DGNerve/PinchedKan → Mathlib.AlgebraicTopology.SimplicialSet.KanComplex → Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant` という推移経路がある。`Derived/Tensor/Fixed` から Mathlib の `ModelCategory.LeftHomotopy` への別経路もある。直接の import と模型の API への依存を禁じる規則なら下の案で進められる。Mathlib を含む推移依存まで禁止する解釈なら、現行の D(R) を固定する設計 §3 と両立せず、段 1 の前に切り分けが要る。
- `EInfinity/Interface/` 全体に直接の禁止を適用するため、実例は `EInfinity/BarrattEccles/Theory.lean` を候補とする。設計 §3 の `Interface/BarrattEccles.lean` に実例を置く案との差分は場所だけ。D73 の比較は実例側に置き、BS 側の型の追加条件にしない。
- 今回の報告パスに ⑤b・⑥ の差分との重複はなかった。段 2 の候補のうち `drafts/A1/CrystallineInput.lean` と `drafts/A1/HodgeTateMap.lean` には ⑤b の枝差分がある。編集前に範囲を照合し、重なる場合はそこで止める。

## 2. 欄ごとの利用と現模型の状況

模型のファイル名は、特記がなければ `SerrePositivity/EInfinity/BarrattEccles/` からの相対名。drafts の宣言は、型と利用の根拠として列挙する。

| 設計 §2 の欄 | 実際の利用 | 現模型での判定と根拠 |
| --- | --- | --- |
| `CAlg` と準圏性 | A2 `CompleteCAlg`、A4 `prismaticPerfectionFunctor`・`perfectoidizationFunctor`、A7 `perfectoidizationAnimated`、本体 `PerfectoidizationInterfaceCAlg.perfd`。係数環を変えるため同じ宇宙の環の族。 | **証明済み**。`CAlg.lean` の `CAlg_R` と準圏インスタンス `cAlg_R_quasicategory`。 |
| `forget` | A2 `prismComplete`、A4 `cAlgH0OnHomotopy`、A8 `perfdModule`・`perfdMapFiber`、Sheaves `forgetPresheaf`。本体の `toE3` は同じ忘却を使う。 | **証明済み**。`CAlgForgetDerived.lean` の `cAlgForgetDerived`・`cAlgForgetDerived_sourceIso`。 |
| `forget_conservative` | Sheaves `forget_reflects_isLimitCone` と `isSheaf_iff_forget`、Shared `totEInfinity_map_isInvertible`。A5 の極限や A6 の pullback を U から戻す場合も辺の可逆性の反映が要る。本体 `forget_pullback` は保存の向き。 | **一部**。`cofibrantAlgebraRelativeCategory_weakEquivalences_iff` が厳密射の弱同値を擬同型で判定し、`algebraCAlgSource_map_weak` が厳密射を可逆辺に送る。`cAlgLocalizationSource_isLocalization` は局所化比較。任意の CAlg の辺に対する U の反映を、この三つのどれもそのまま述べていない。 |
| `forget_preservesLimits` | Sheaves `forget_isLimitCone`、A5 の指定極限、A6 の四角形。本体 `BSLimitConeDataCAlg.underlying_isLimit` は同じ指定錐を U で送り `comparison` に沿って移す。 | **証明済み（保存）**。`FreeProbeDerivedFreeForget.lean` の無条件の `cAlgForgetDerived_mapJoinCone_isLimit`・`cAlgForgetDerived_hasLimit_postcomp`。前者は `…_of_transport` に `freeProbeUnitTransportCondition` を代入済み。任意の極限の存在・錐の創出は別。 |
| `forget_preservesSifted` | A2 `animatedCAlgRealization` に小さい sifted 余極限の存在、`discreteRealizationIso` に多項式分解の実現と増大の U での計算。A4 `restrictFrobeniusTowerColimit` では ℕ 塔の指定余錐、A7 `preservesRelativeTensor_of_siftedAndTensor` では幾何学的実現を使う。 | **一部**。`EInfinity/Operad/AlgebraSiftedColimits.lean` の `Operad.Algebra.forget_createsSiftedColimitsOfShape` は通常圏の `[IsSifted J]`。 `freeAlgebraForget_preservesSiftedColimits` も通常圏。`PreservesSmallSiftedColimits (cAlgForgetDerived S)` の native ∞ 比較は確認できなかった。 |
| `presentable` | Sheaves `sheafification_exists_cAlg`・`derivedGlobalSectionsCAlg`、A2 `coefficientPresentable`、A5 `perfectCoefficientPresentable`。反射には極限の存在、sifted 延長には余極限の存在を取り出す。 | **なし（G12）**。draft の `coefficientPresentable`・`perfectCoefficientPresentable` は仮置き。自由忘却の随伴は本体の `cAlgFreeForgetDerivedAdjunction` にあるが、CAlg の accessible 生成と native 余極限を供給する G12 とは別。 |
| `coproduct_tensor` | A2 `prismaticCohomologyPoly_tensor`・`derivedPrismaticCohomology_tensor` は**指定した二項余積錐**、`derivedPrismaticCohomology_initial` は空の余積。A7 `twoSidedBar`・`preservesRelativeTensor_of_siftedAndTensor` は有限余積とその射を使う。 | **一部**。D(R) の固定因子テンソル `tensorWith`・`tensorLeft`・`tensorWithSymmetry` は本体。既存 CAlg の指定余積の U 像をそれと比較する宣言は確認できなかった。U が D(R) の**余積**に送るという型は不要で、そこでは ⊕ でなく ⊗ᴸ。 |
| `restrict`・`baseChange`・随伴 | A2 `prismModIdeal`・`prismaticFrobeniusPoly`・`BaseChangeAndTensor` は底変換と随伴の単位を使う。A4 `frobeniusTower` は係数制限の反復、`modPrismFunctor` は A→A/d、A5 `discreteRestrictionIso`・`prismScalarExtension` と A6 `arcElementSections` の係数比較は離散入力を使い、A7 `restrictFrobenius_preservesTensorSpans` は**環同型**に沿う場合の押し出し保存。 | **一部（D 側）、CAlg 欄はなし**。D 側に `derivedInfinityBaseChange`・`dgNerveRestrictScalarsIso`。後者は dg nerve のスカラー制限比較で、指定の D(T)→D(S) を与える `derivedInfinityRestrictScalars` は draft。CAlg の `cAlgRestrictScalars`・`cAlgBaseChange`・`cAlgBaseChange_restrictScalars_adjunction` と両忘却比較は同じく `DerivedGeneral/ScalarRestriction` の仮置き。 |
| `discrete` | Sheaves `ringPresheafToCAlg`、A2 `animatedCAlgRealization`、A4 `discreteToH0`、A5 の perfectoid 試験対象、A6 `structurePresheaf`。本体 `underlyingUnit` は全関手同型を前置する。A7 の離散性には U の Hⁱ=0（i≠0）の判定も使う。 | **証明済み（指定関手・U 比較・離散対象の認識）**。`discreteCAlgUnderEmbedding`・`discreteCAlgUnderEmbedding_forgetIso`・`cAlgUnderlyingDisc_iff_discreteUnder`、本体 `algebraEmbeddingForgetIso`・`disc_forget_iff`。全忠実性そのものを新しい必須欄にする利用は見つからなかった。 |
| `pi0` | A2 `derivedPrismaticCohomology_h0_ring`、A4 `cAlgH0Algebra`・`cAlgH0OnHomotopy`・`restrictH0Equiv_base`、A7 `perfdRing` と A8 `IsDiscretePerfectPerfection`。E3 の単位と射影のため、環構造・係数・射の自然性が要る。 | **一部**。`homologyCommRing`・`homologyAlgebra`・`homologyCommAlgebra` は厳密な模型の H⁰、`cAlgUnderlyingHomologyIso` は元の模型頂点で同じ U の各次数を比較する。`cAlgZeroDegreeDiscreteIso`・`cAlgUnderlyingDiscDiscreteUnderIso` は離散対象。任意の CAlg のホモトピー圏上の A 代数値関手と、U の H⁰ との自然同型・係数制限整合は draft 側。 |
| `ofCosimplicial` | Shared `totEInfinityFunctor`・`totEInfinity_isLimitCone`・`totEInfinity_map_isInvertible`、A1 `totEInfinity_isLimit_truncations` と `baseChangeTotHomotopy`、A2 `prismaticCohomologyCAlg_eq_totEInfinity`。元の射、指定錐、交代余面複体との自然比較を使う。 | **なし（G-A1-11 のこの強さ）**。`totEInfinityFunctor`・`totEInfinityCone` は Shared の仮置き。既存の `discreteCAlgUnderEmbedding`、`complexOrdinaryDerivedSource`、`cAlgForgetDerived_mapJoinCone_isLimit` は部品。G10 の指定 Δ 極限と交代余面複体の比較、CAlg の錐との同定は別。 |
| `ofCdga` | Shared `cdgaCAlg`・`totCDGAFunctor`・`totCDGA_evalZero`、A1 `formsCDGAFunctor`・`formsCAlg_eq` と `rootFormsAugmentation`。後者は厳密 cdga 射を写し、次数零 cdga の像を指定の離散埋め込みと比較する。 | **一部**。draft `cdgaCAlg` の式には sorry がなく、`commutativeAlgebraFunctor`、`Operad.restrictAlgebra (augmentation S)`、`algebraCAlgSource` は本体。`algebraCAlgSource_forgetIso` は置換後の全関手比較。厳密 cdga の元の底の複体への自然比較と指定離散埋め込みとの照合は別。余単体的 cdga の Tot は draft。 |
| `powerOp0` | Shared `powerOperationZero_natTrans`・`powerOperationZero_component`・`powerOperationZero_eq_frobenius_discrete`・`…_tot`、A4 `prismaticPerfectionFrobenius` 周辺の Lemma 8.4。π₀ の p 乗、正の**ホモトピー**次数で零、離散・Tot と実現の Frobenius 比較を使う。 | **なし（M14）**。Shared の `powerOperationZero` と coherent 変換は仮置き。`homologyBinary`・`homologyCommRing_mul` は通常積の部品で、次数を保つ P⁰ を供給しない。 |

## 3. Lean の型案

以下は欄の宣言型を読むための断片。`D S` は `derivedInfinityCategory S`、`RAlg S` は `Under (CommRingCat.of S)` の略。`V X` は `X _⦋0⦌`、`atVertex F x` は `F.app (Opposite.op ⦋0⦌) x`、`Ho X` は `SSet.hoFunctor.obj X`、`hoMap F` は `(SSet.hoFunctor.map F).toFunctor`。環は `Type u`、準圏は `SSet.{u+1}`、小さい図式は `SSet.{u}` の ulift を基本とする。既存の極限保存の入口と G1′ の錐は `SSet.{u+1}` の形を取るので、極限保存の欄にはその型を採る。

### 中核と極限・余極限

```lean
CAlg : (S : Type u) → [CommRing S] → SSet.{u+1}
quasicategory : (S : Type u) → [CommRing S] → Quasicategory (CAlg S)
forget : (S : Type u) → [CommRing S] → CAlg S ⟶ D S
forget_conservative : ∀ (S : Type u) [CommRing S]
  {x y : V (CAlg S)} (e : SSet.Edge x y),
  IsInvertibleEdge (e.map (forget S)).toTruncated →
    IsInvertibleEdge e.toTruncated
forget_preservesLimits : ∀ (S : Type u) [CommRing S]
  {K : SSet.{u+1}} {F : K ⟶ CAlg S} (c : JoinCone F),
  IsLimitCone c → IsLimitCone (mapJoinCone (forget S) c)
forget_preservesSifted : ∀ (S : Type u) [CommRing S],
  HomotopyLimits.PreservesSmallSiftedColimits (forget S)
presentable : ∀ (S : Type u) [CommRing S],
  @F2.Presentable.IsPresentable (CAlg S) (quasicategory S)
discrete : (S : Type u) → [CommRing S] → nerve (RAlg S) ⟶ CAlg S
discrete_forget : ∀ (S : Type u) [CommRing S],
  FunctorIso (discrete S ≫ forget S) (discreteEmbedding S)
discrete_recognition : ∀ (S : Type u) [CommRing S] (x : V (CAlg S)),
  (∀ i : ℤ, i ≠ 0 → Limits.IsZero
    (derivedInfinityHomology S i (atVertex (forget S) x))) →
  ∃ B : RAlg S, Nonempty (VertexIso x (atVertex (discrete S) (nerveVertex B)))
```

`derivedInfinityHomology` の `HasDerivedCategory.standard` は既存 D(R) API と同じ局所インスタンスを置く。小さい sifted 余極限の存在はまず `presentable` から引き出す。宇宙の境界で既存 API が合わない場合は、暫定の別欄を置くより `HasSmallSiftedColimits (CAlg S)` への接続補題にする。極限反映は極限の存在・保存・辺の反映から `isLimitCone_of_conservative_image`。極限・余極限の「創出」全体は欄に要求しない。

### 二項余積と係数変更

二項余積の比較に、一般の対称モノイダル ∞ 圏全体は要らない。下の型は第一段の頂点比較。A2・A7 の各変数での議論に自然性が要る場合は、右因子 `y` ごとに同じ二項余積関手の選択と `FunctorIso (coprodWith S y ≫ forget S) (forget S ≫ tensorWith (atVertex (forget S) y))` に強める。単に同型な頂点を毎回選ぶだけでは、この強さを供給しない。押し出し（相対テンソル）の U による保存は一般に要求しない。

```lean
coproduct_tensor : ∀ (S : Type u) [CommRing S]
  (x y : V (CAlg S)) (c : JoinCocone (binaryPointDiagram x y)),
  IsColimitCone c → VertexIso (atVertex (forget S) c.vertex)
    (atVertex (tensorWith (atVertex (forget S) y)) (atVertex (forget S) x))
discrete_initial : ∀ (S : Type u) [CommRing S],
  IsInitialVertex (atVertex (discrete S)
    (nerveVertex (Under.mk (𝟙 (CommRingCat.of S)))))
restrict : ∀ {S T : Type u} [CommRing S] [CommRing T],
  (S →+* T) → CAlg T ⟶ CAlg S
baseChange : ∀ {S T : Type u} [CommRing S] [CommRing T],
  (S →+* T) → CAlg S ⟶ CAlg T
baseChange_adjunction : ∀ {S T : Type u} [CommRing S] [CommRing T]
  (f : S →+* T), QCatAdjunction (baseChange f) (restrict f)
restrict_forget : ∀ {S T : Type u} [CommRing S] [CommRing T]
  (f : S →+* T), FunctorIso (restrict f ≫ forget S) (forget T ≫ restrictD f)
baseChange_forget : ∀ {S T : Type u} [CommRing S] [CommRing T]
  (f : S →+* T), FunctorIso (baseChange f ≫ forget T)
    (forget S ≫ derivedInfinityBaseChange f)
restrict_id : ∀ (S : Type u) [CommRing S],
  FunctorIso (restrict (RingHom.id S)) (𝟙 (CAlg S))
restrict_comp : ∀ {S T W : Type u} [CommRing S] [CommRing T] [CommRing W]
  (f : S →+* T) (g : T →+* W),
  FunctorIso (restrict (g.comp f)) (restrict g ≫ restrict f)
discrete_restrict : ∀ {S T : Type u} [CommRing S] [CommRing T]
  (f : S →+* T),
  FunctorIso (nerveMap (Under.map (CommRingCat.ofHom f)) ≫ discrete S)
    (discrete T ≫ restrict f)
```

ここで `restrictD : ∀ {S T : Type u} [CommRing S] [CommRing T], (S →+* T) → D T ⟶ D S` は D 側 M13 の入力。数学的には同じ D(T) の係数制限を指定し、CAlg の実例ごとに別の D 側の演算を選ばない。D 側の `restrictD_id` と、加法群上で係数制限と Hⁱ が可換という自然同型も D 側で共用する。A4 の `cAlgRestrictScalars_isColimitCone` は U の sifted 余極限保存・反映と `restrictD` の余極限保存を使う。A7 の環同型の場合は `restrict_id`・`restrict_comp` で逆の制限を構成して得る。任意の環準同型に沿う制限に押し出し保存を要求しない。

### 零次環と厳密な入力の実現

`H S i` は `(homotopyCategoryBridge (D S)).inverse ⋙ derivedInfinityHomologyFunctor S i` とする。 `forgetModule S` は既存の `discreteAlgebraModule S`。ここで `nerveHomotopyFunctor` は通常圏からその nerve のホモトピー圏への既存関手（`F2.Idempotent.nerveHomotopyFunctor`）。`strictToD` は `complexOrdinaryDerivedSource` と同じ型の D 側の共用入口とし、模型の import を避けるため必要なら独立の補助モジュールに切り出す。`Cos S := CosimplicialObject (RAlg S)`、`CosCdga S := CosimplicialObject (CommMon (Complex S))`、`totComplex S : Cos S ⥤ Complex S` は台の加群への後合成・`alternatingCofaceMapComplex`・`ComplexShape.embeddingUpNat.extendFunctor` の合成。`totDiagram S X` は `nerveMap X` の Δ だけを ulift し、`discrete S` を後合成した既存 draft と同じ図式。

```lean
pi0 : ∀ (S : Type u) [CommRing S], Ho (CAlg S) ⥤ RAlg S
pi0_forget : ∀ (S : Type u) [CommRing S],
  pi0 S ⋙ forgetModule S ≅ hoMap (forget S) ⋙ H S 0
pi0_discrete : ∀ (S : Type u) [CommRing S],
  nerveHomotopyFunctor (RAlg S) ⋙ hoMap (discrete S) ⋙ pi0 S ≅ 𝟭 (RAlg S)
pi0_restrict : ∀ {S T : Type u} [CommRing S] [CommRing T]
  (f : S →+* T),
  hoMap (restrict f) ⋙ pi0 S ≅ pi0 T ⋙ Under.map (CommRingCat.ofHom f)
ofCosimplicial : ∀ (S : Type u) [CommRing S], nerve (Cos S) ⟶ CAlg S
ofCosimplicial_forget : ∀ (S : Type u) [CommRing S],
  FunctorIso (ofCosimplicial S ≫ forget S) (nerveMap (totComplex S) ≫ strictToD S)
ofCosimplicial_cone : ∀ (S : Type u) [CommRing S] (X : Cos S),
  { c : JoinCone (totDiagram S X) //
    c.vertex = atVertex (ofCosimplicial S) (nerveVertex X) ∧ IsLimitCone c }
ofCosimplicial_restrict : ∀ {S T : Type u} [CommRing S] [CommRing T]
  (f : S →+* T), FunctorIso (nerveMap (restrictCosimplicial f) ≫ ofCosimplicial S)
    (ofCosimplicial T ≫ restrict f)
ofCdga : ∀ (S : Type u) [CommRing S], nerve (CommMon (Complex S)) ⟶ CAlg S
ofCdga_forget : ∀ (S : Type u) [CommRing S],
  FunctorIso (ofCdga S ≫ forget S)
    (nerveMap (CommMon.forget (Complex S)) ≫ strictToD S)
ofCdga_discrete : ∀ (S : Type u) [CommRing S],
  FunctorIso (nerveMap (discreteCDGA S) ≫ ofCdga S) (discrete S)
ofCosimplicialCdga : ∀ (S : Type u) [CommRing S], nerve (CosCdga S) ⟶ CAlg S
ofCosimplicialCdga_discrete : ∀ (S : Type u) [CommRing S],
  FunctorIso
    (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj (discreteCDGA S)) ≫
      ofCosimplicialCdga S) (ofCosimplicial S)
ofCosimplicialCdga_evalZero : ∀ (S : Type u) [CommRing S],
  SSet.Homotopy (ofCosimplicialCdga S)
    (nerveMap ((evaluation SimplexCategory (CommMon (Complex S))).obj ⦋0⦌)
      ≫ ofCdga S)
```

`discreteCDGA` は既存 draft の次数零 single の関手を共用する。`ofCosimplicial_cone` の比較に用いる射は `ofCosimplicial` の**同じ関手像**でなければならない。段 1 では、評価した錐を射について自然に選ぶ全図式（`SSet` の評価写像で作る二変数図式）を補助データとしてまとめ、指定錐をそこから得る案。型は `join (Δ[0] : SSet.{u+1}) Δsmall ⊗ nerve (Cos S) ⟶ CAlg S` で、二つの境界を `ofCosimplicial S` と離散評価図式に固定する。ここで `Δsmall` は Δ の nerve の ulift。点ごとの錐の存在だけでは `totEInfinity_restrict` の関手同型は直ちに出ない。`ofCosimplicialCdga` にも同じ形式の極限錐、次数零 cdga の列との `FunctorIso` を持たせるか、同じ自然な選択から導く。これが `totCDGA_discrete` と `pdDeRhamFunctorIso` に対応する。

`pi0` は全頂点で使う。非連結な E∞ 代数にも H⁰ の環はあるが、任意の E∞ 代数について離散化への単位や `pi0 ⊣ discrete` を要求する案にはしない。必要な離散対象の復元は `discrete_recognition` の型。

### P⁰

`k` は `[CommRing k] [CharP k p] [Fact p.Prime]`。 `fr := frobenius k p`。次の `POnH` は新しい任意の演算欄ではなく、`functorHomEvaluate` に `H k (-n)` を適用し、D 側の係数制限で Hⁱ の台を読む加法同型を合成したもの。`piZeroAddEquiv` は `pi0_forget` の成分。

```lean
powerOp0 : ∀ (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p],
  FunctorHom (forget k) (forget k ≫ restrictD (frobenius k p))

-- powerOp0 から読む写像の型
POnH (x : V (CAlg k)) (n : ℤ) :
  derivedInfinityHomology k (-n) (atVertex (forget k) x) →+
    derivedInfinityHomology k (-n) (atVertex (forget k) x)

powerOp0_zero : ∀ (x : V (CAlg k))
  (a : ((pi0 k).obj (SSet.HomotopyCategory.mk x)).right),
  (piZeroAddEquiv x).symm (POnH x 0 (piZeroAddEquiv x a)) = a ^ p
powerOp0_pos : ∀ (x : V (CAlg k)) (n : ℤ), 0 < n → POnH x n = 0

-- ℤ/p では fr = id。restrictD_id を通して得る型
powerOp0_primeField (p : ℕ) [Fact p.Prime] :
  FunctorHom (forget (ZMod p)) (forget (ZMod p))
```

離散 Frobenius との比較は、`B : RAlg k` と p 乗写像 `frB : B ⟶ (Under.map (CommRingCat.ofHom fr)).obj B` について、次の同じホモトピー圏の射の等式にする。`x := atVertex (discrete k) (nerveVertex B)`。

```lean
functorHomEvaluate (powerOp0 k p) x =
  SSet.HomotopyCategory.homMk ((nerve.edgeMk frB).map (discrete k ≫ forget k)) ≫
    (((discrete_restrict fr).app (nerveVertex B)).map (forget k)).hom ≫
    ((restrict_forget fr).app x).hom
```

Tot 版はこの式の `frB` を `X ⟶ X ⋙ Under.map (CommRingCat.ofHom fr)` に取り替え、`ofCosimplicial` の像と `ofCosimplicial_restrict` の成分を使う。成分等式だけから coherent な錐の比較が作れない場合は、Tot と幾何学的実現の**指定錐との比較**を M14 のデータに残す。自然性は `FunctorHom` とホモロジーへの作用から導き、別々に選んだ次数ごとの演算を独立に入力しない。正次数は πₙ（H^{-n}）であり、Hⁱ の正次数と取り違えない。

## 4. 足す欄・まとめる欄

1. **追加候補**は `pi0_discrete`・`pi0_restrict`、`discrete_restrict` と `ofCdga_discrete`、離散対象の認識、指定錐としての `ofCosimplicial` と余単体的 cdga の版。特に `rootFormsAugmentation` では `ofCdga` の射の像を `ofCdga_discrete` の指定比較で終域へ移す。両者を頂点の等号と仮定しない。
2. A1 の `totEInfinity_cohomologyRing : True` は全次数の積の照合をまだ表していない。現在の `CrystallineInput` と `HodgeTateMap` の積の式は古典的 `cohomologyCup` 上。まずその式を保ち、全次数の CAlg 側比較が必要になった段で Tot の専用条件として足す。π₀ の環や P⁰ の欄だけから全次数の cup 積を供給した扱いにはしない。
3. `forget_createsLimits`、`forget_createsSifted`、一般の相対テンソルの U による保存、全忠実性、自由代数は中核の必須欄にしない。自由忘却随伴は現模型が極限保存を証明する入口で、確認した BS の呼び出しはその帰結を使う。完備化・descendability・A7 の有限余積から相対テンソルへの補題は、D(R) または一般の準圏の補題として分ける。完備反射は `cAlgCompletionReflection`・`prismCompleteReflection` の別の供給課題として記録する。
4. **実例の未証明欄**を処理するため、証明済みの中核と、全欄を持つ `EInfinityTheory` を分ける。段 1 の本体では `barrattEcclesCore` と証明済みの比較を作る。全欄を要求する `barrattEcclesTheory` は未供給欄を明示引数に取る組立関数か、完全な値を drafts に置く。証明済みの中核を全欄実装済みとして公開しない。BS の新しい定理は必要な全欄を `E : EInfinityTheory` から受け、D73 の模型同値を仮定しない。

## 5. 規模と停止点

- 段 1 の型と共用補助は約 **350–650 行**。モデル側の証明済み部分の実例と互換比較は **120–250 行**、未供給欄を型付きで束ねる draft は **80–180 行**。全ての G12・M14・M13-CAlg・Tot の証明はこの見積もりの外。とくに G12 と P⁰ の coherent な錐比較は、それぞれ独立した供給課題。
- 段 2 の drafts は API 参照が多数あるので、まず `DerivedGeneral` と `Shared`、次に A2・A4 と Sheaves、最後に A1・A5〜A9 の利用順で進める。約 **30–40 ファイル・650–1,300 行の変更**を見込む。README §1 の模型参照箇所では `formsNerve` と `rootFormsAugmentation` の端点、H⁰ の自然性、Tot の係数制限が主な照合点。本体の CAlg 版 G1′ の一般化を含める場合は別に **180–350 行**を見込む。
- 段 1 の前に、D71 の推移依存の解釈、実例の配置、G1′ の一般版を W14 で追加する範囲、および `coproduct_tensor` に求める自然性の強さを調整役と確定する。段 0 はこの報告で止める。

## 停止点 1（D71–D72）

`main` の a24fae02a を `math/bs-impl` に取り込んだ（df92616d8）。本体は新設 4 ファイル。既存の公開宣言と入口・監査スクリプトに差分なし。

- `SerrePositivity.EInfinity.Interface.Core` は `EInfinityCore`。指定極限保存、離散埋め込み、忘却比較、離散対象の認識をまとめた。離散性は G1′ の universal と integral が逆向きに使うため、既存の `cAlgUnderlyingDisc_iff_discreteUnder` の両方向を欄にした。
- `SerrePositivity.EInfinity.Interface.StrictInputs` は次数零の可換 dg 代数への関手。既存の `moduleAlgebraMonObj` と single 複体のモノイダル関手を使用。
- `SerrePositivity.EInfinity.Interface.Theory` は `EInfinityTheory`。強い `coproduct_tensor`、π₀ と自然比較、係数変更、指定 Tot 錐、半線形 P⁰ を含む。Tot の極限性は指定錐ごとに、係数制限・離散 cdga との比較は全関手の同型として受け取る。cdga の [0] への自然な辺は、指定した同じ極限錐の [0] の脚と一致する欄を設けた。D 側の `restrictD` と `strictToD` は界面に供給する。
- `SerrePositivity.EInfinity.BarrattEccles.Theory` は `barrattEcclesCore`。既存の `cAlgForgetDerived_mapJoinCone_isLimit`、`discreteCAlgUnderEmbedding_forgetIso`、`cAlgUnderlyingDisc_iff_discreteUnder` ほかを代入した。
- 全欄の実例は `drafts/Shared/BarrattEcclesTheory.lean`。既存の中核と厳密入力の関手を使う実例案とし、未供給の欄はここに記した。drafts の運用に従い、このファイルはビルド対象外。

`--wait 1800` で共有鍵を取得し、`Interface.Theory` と `BarrattEccles.Theory` を対象ビルド。上記 4 モジュールの限定監査は **125 宣言、標準三公理のみ**。本体の `sorry`・新規公理と、D71 が禁止する Interface 内の直接 import・模型 API・模型圏の仮定は各 0。入口と監査への登録候補は上記の本体 4 モジュール。

## 段 2 中断（D73）

drafts の既存の主張を維持したまま、名前と引数だけを替えるために必要な比較が、段 1 の界面に二つ足りない。指示書 §1 の条件に従い、既存 drafts への移行はここで止めた。

1. `Shared/EInfinityPowerOperation.lean` の `powerOperationZero_natural` は、任意の辺と全整数次数で P⁰ が可換であることを要求する。界面の `powerOp0` 自体は半線形な自然変換だが、それを加法的な自己写像に読む `restrictD_homology f i x` は、頂点ごとの加法同型。異なる頂点で選んだ同型が Hⁱ の射と可換である条件がない。例えば i ≠ 0 の各成分を加法自己同型で変えても、現界面の `powerOp0_zero` と `powerOp0_pos` の型はその変更を検出しない。
2. `Shared/CosimplicialEInfinity.lean` の `totEInfinity_forget` は、交代余面複体そのもののホモロジーとの比較を要求する。`totEInfinity_map_isInvertible` は、その複体の擬同型が Tot の可逆な辺になることを使う。`ofCosimplicial_forget` の比較先にある `strictToD` は現界面では関手のみ。厳密複体の Hⁱ との比較、または擬同型の反転の仕様が必要。既存の実例側には `ComplexLimits.complexOrdinaryDerivedSource_map_weak` があり、反転の方はその定理を使える。

欄の型の候補。第 1 の比較は成分を既存 `restrictD_homology` に合わせるか、現在の同型をこの比較の成分として定義する。第 2 の比較からは Tot のコホモロジーの同定を読み、擬同型の反転には D(S) の全次数 Hⁱ による検出を使う。

```lean
-- HAdd S i := cohomologyOnHo S i ⋙ forget₂ (ModuleCat S) AddCommGrpCat
restrictD_homologyIso (f : S →+* T) (i : ℤ) :
  hoMap (restrictD f) ⋙ HAdd S i ≅ HAdd T i

strictToD_homologyIso (S : Type u) [CommRing S] (i : ℤ) :
  ordinaryToHoNerve (Complex S) ⋙ hoMap (strictToD S) ⋙ cohomologyOnHo S i ≅
    HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.up ℤ) i
```

A1 の二本は後回し（`CrystallineInput.lean`・`HodgeTateMap.lean`、⑤b）。`DeRhamComparisonPoly` の `rootFormsAugmentation` では、`ofCdga` で送った厳密な増大の後に `ofCdga_discrete` の成分を合成する経路まで確認した。始点の `formsVertex` と `bigZigzagIso` の最後の `pdDeRhamFunctorIso` は後回しの `CrystallineInput` で定義している。`totEInfinity_cohomologyRing : True` は元のまま。既存 drafts に差分がないので、模型参照 0 の検査は未達。

A0・A3 は ⑤c（main d39908253 の BS-W14 §4。A0/CechAlexander.lean は例外）。これらのファイルにも差分なし。

### 段 2 の完了分（G1′）

`SerrePositivity.EInfinity.Perfectoidization.TheoryInterface` を新設した。`TheoryBSLimitConeData`・`TheoryPerfectoidizationInterface`・`TheoryPerfectoidizationInterface.toE3`・`nonempty_e3_of_theory` を `E : EInfinityTheory` で述べた。元の単位、H⁰ の環、指定錐の境界・頂点、excision の通常の商を保持している。必要な E の欄は段 1 の中核に収まり、上記の二つの比較には依存しない。従来の Barratt–Eccles 版の宣言は無変更。

`--wait 1800` の共有鍵でこの 1 モジュールを対象ビルド。限定監査は **63 宣言、標準三公理のみ**。本体の新規 `sorry`・公理は各 0。この 1 モジュールを段 2 の完了分として入口・監査の登録候補にする。今回のビルドでは既存の `Perfectoid/Defs` と `Derived/Interface` の linter 警告が再表示された。

## 停止点 2（D73、§5 の自然比較と drafts）

main 903ec3a0e（§5 の 217f931f9 を含む）を `math/bs-impl` に fast-forward して作業した。G1′ は取り込み済みの `TheoryPerfectoidizationInterface`、`TheoryBSLimitConeData`、`nonempty_e3_of_theory` を使う。

- `EInfinity.Interface.Theory` に `restrictD_homologyIso` と `strictToD_homologyIso` を追加した。従来の頂点ごとの `EInfinityTheory.restrictD_homology` は同じ呼び出し方で自然同型の成分を読む。P⁰ の零次の式も同じ成分を使う。
- Barratt–Eccles の `restrictD_homologyIso` は、導来係数制限そのものが M13 の未供給欄なので drafts に残した。`strictToD` は既存の `complexOrdinaryDerivedSource` を使う。各頂点の `complexSemifreeResolutionValueAugmentation_quasiIso` と射の `complexOrdinaryDerivedSource_map_weak` は本体にある。全 augmentation とその成分をホモロジー上で照合する自然同型の証明は `drafts/Shared/BarrattEcclesTheory.lean` に残した。
- P⁰ は半線形変換をホモロジーに送り、係数制限の自然比較を使う。π₀ の環、離散代数の Frobenius、余単体的可換環の Tot の Frobenius は同じ界面から読む。可換環の Tot は `strictToD_homologyIso` で零延長した交代余面複体の Hⁱ と比較する。
- A1 の二本は後回し（`CrystallineInput.lean`・`HodgeTateMap.lean`）。厳密な `formsCDGAFunctor` からの形式の実現は `CrystallineSite` の `theoryFormsCAlg` と `theoryFormsVertex` を使う。増大は厳密 cdga の射を `ofCdga` で送り、`ofCdga_discrete` の成分を後合成した同じホモトピー類の辺を選ぶ。元の de Rham の span は `theoryPdDeRhamFunctorIso` に残し、行 0 への射影の可逆性は、余単体的 cdga の Tot の射の忘却像と総複体の射の比較待ち。ここで必要なのは各項の擬同型性ではなく、総複体の射の擬同型性。`totEInfinity_cohomologyRing : True` は元のまま。
- A0・A3 は ⑤c。例外の `A0/CechAlexander.lean` にも変更なし。KL-W1 と重なる `IsPresentable` と import の 5 本（A2/DerivedPrismaticCohomology、A5/PerfectSiteComparison、A6/ArcSheafProperty、Shared/CosimplicialEInfinity、Sheaves/CAlgValued）は承認どおり現在の main の名前を使った。KL-W1 取り込み時に配布される `kl-module-map.json` と `kl-namespace-map.json` で合わせる。

### 変更した BS の drafts（33 本）

| 場所 | ファイル |
| --- | --- |
| A1 | CrystallineSite、DeRhamComparisonPoly、HodgeTateComparison |
| A2 | AnimatedAlgebra、BaseChangeAndTensor、DerivedPrismaticCohomology、HodgeTateFiltration |
| A4 | AfterComparison、InterfaceFields、Perfectoidization |
| A5 | InterfaceLimitCone、PerfectSite、PerfectSiteComparison、SemiperfectoidCase、StrongDescent、WeaklyInitialAndDescent |
| A6 | ArcSheafProperty、Excision、SheafOfSetsExcision |
| A7 | AnimatedDomain、AnimatedPerfectoidization、DiscreteCore、UniversalProperty |
| A8 | AlmostConnectivity、AlmostPurityConnectivity、IntegralDiscreteness |
| A9 | Assembly |
| DerivedGeneral | CompletionFunctor、ScalarRestriction |
| Shared | CosimplicialEInfinity、Descendable、EInfinityPowerOperation |
| Sheaves | CAlgValued |

実例用の `Shared/BarrattEcclesTheory.lean` はこの表とは別。静的検査では、コメントと文字列、後回しの A1 二本、⑤c の担当範囲、実例用 draft を除いて、旧 `CAlg_R`・忘却・離散埋め込み・G1′、Barratt–Eccles・Operad の直接 API と import のヒットは **0**。変更したモジュールのリポジトリ内 import の解決と、担当外の差分 0 を確認。drafts の規約に従い、drafts 自体の Lean ビルド・監査は行っていない。

`--wait 1800` で共有鍵を取り、`EInfinity.Interface.Theory` と `EInfinity.Perfectoidization.TheoryInterface` の対象ビルドに成功。限定監査は停止点 1 の 4 モジュールで **128 宣言**、G1′ で **63 宣言**。いずれも標準三公理のみで、本体の新規 `sorry`・公理は 0。新規の本体モジュールはないので、今回の追加登録候補はなし。
