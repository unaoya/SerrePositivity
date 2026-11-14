# SC-W1 2g-1：幾何の供給の実装記録

2026-11-14。承認された Rydh 3.10 経路。外枠 **25,000 行**、約 **12,000 行**で止まらず途中報告。G1・G2 の完成後に停止点 2g-1 を報告し、G3 へ進む。このファイルは現時点では途中記録で、完成報告ではない。B4 の指示で main の凍結は解除され、追従を完了した。数学の作業とコミットは worktree SerrePositivity-scheme・枝 math/scheme で行う。

## G1 の最初の束：型つき一覧（着手前）

G0 の環とスキームの付値判定から、Rydh の subtrusive な持ち上げへ進む。最初は次の型に絞る。

1. `exists_valuation_specialization_diagram`：Y は任意のスキーム、p⤳q は点の特殊化。κ(p) の付値部分環 W と k:Spec W→Y が存在し、k は閉点を q へ送り、Spec κ(p)→Spec W→Y は p の標準剰余体射と一致する。
2. `IsSchemeVCover.liftsSpecializations`：f:X→Y が G0 の IsSchemeVCover を満たすとき、p⤳q に対し x⤳z、f(x)=p、f(z)=q となる x,z が存在する。特定の x を固定した generalizing/specializing map の性質とは区別する。

1 は Mathlib の stalkSpecializes、局所環から体への射の付値部分環による因子化、fromSpecStalk の既存の法則を使う。2 は 1 の付値環へ G0 の付値持ち上げを適用し、忠実平坦拡大の閉点と一般点を取る。式の分割・自然性・Spec の係数移送は本数で区切らず、型をここへ追記する。200 行を超えた宣言・証明分割は行数を記録する。

この束は Rydh 3.10 の完成ではない。非 proper な有限表示射の strict transform の平坦化、付値判定から strict transform の全射性への接続、非 Noether affine 基底の模型は引き続き必要。

型の照合に使う補助法則 `specMap_zeroPrime_of_injective` は、整域間の単射 f:R→S に対し、Spec(f) が S の零素点を R の零素点へ送る型。これは ker(f)=0 という既存の判定を Spec の式に読む分割である。

## 最初の束の対象ビルド

`ValuationSpecializationDiagram` と `SchemeVCoverSpecializations` の対象は **2,846 jobs 成功**。二ファイルの本体は **107 行**。原典の subtrusive 性との一般同値を完成したとは主張せず、必要な特殊化の鎖の持ち上げを実際の付値判定から証明した。入口登録と標準監査の結果は確定後に追記する。

実際に検証した型：

```lean
exists_valuation_specialization_diagram (Y : Scheme.{u}) {p q : Y} (h : p ⤳ q) :
  ∃ (W : ValuationSubring (Y.residueField p))
    (k : Spec (CommRingCat.of W) ⟶ Y),
    k (IsLocalRing.closedPoint W) = q ∧
      Spec.map (CommRingCat.ofHom (algebraMap W (Y.residueField p))) ≫ k =
        Y.fromSpecResidueField p

specMap_zeroPrime_of_injective {R S : Type u}
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  (f : R →+* S) (hf : Function.Injective f) :
  Spec.map (CommRingCat.ofHom f) (⟨⊥, inferInstance⟩ : PrimeSpectrum S) =
    (⟨⊥, inferInstance⟩ : PrimeSpectrum R)

IsSchemeVCover.liftsSpecializations {X Y : Scheme.{u}} {f : X ⟶ Y}
  (hf : IsSchemeVCover f) {p q : Y} (h : p ⤳ q) :
  ∃ x z : X, x ⤳ z ∧ f x = p ∧ f z = q
```

## 次の平坦化の接続で照合する箇所

2d の `flat_openImage_pullback_of_affineSourceCover`、`flat_strictTransformπ_of_flatPurePullbacks_affineCover`、`exists_admissible_flat_strictTransformπ_proper_affineBase` は、現在の型では `IsProper f` を要求する。本文には始域の準コンパクト性・局所有限型性から Noether 性を得る箇所があり、Rydh の有限表示射へ再利用するにはこれらを分離する必要がある。既存宣言の仮定・本文は変更せず、新規ファイルでより一般的な入口を供給する。古い証明の一部にある高い heartbeat 設定はコピーせず、必要な可換式・被覆比較を小さな補題に分けて既定の上限で検証する。

これは次の束の依存の調査であり、その新しい主定理の一覧は着手前に別途載せる。上限や範囲に達したための停止ではなく、2g-1 の作業を継続する。

## 次の束：有限型射の狭義変換の局所性（着手前の型つき一覧）

以下は旧宣言の変更ではなく、新しいファイルで供給する型。

- `strictTransformAmbient_noetherian_of_finiteType`：S が Noether、f:X→S が局所有限型かつ準コンパクト、J が S のイデアル層なら、strictTransformAmbient f J は Noether。f の固有性は要求しない。
- `flat_strictTransformπ_iff_of_openCover_of_finiteType`：同じ入力と開 U、blowup J の開被覆 𝒰 に対し、strictTransformπ f U J の平坦性と、各 𝒰 上の引き戻した開部分のスキーム論的閉包の構造射の平坦性は同値。

この二つは既存の狭義変換の局所性を、実際に使用する有限型性・準コンパクト性の仮定で使う入口。Noether 性を未証明の入力に追加せず、blowup 後の周辺空間から供給する。一般の有限型射の平坦化の主定理や strict transform の全射性は、この二補題だけで完成とはしない。

最初の特殊化の束の入口ビルドは **4,798 jobs 成功**、別実行の標準監査は **10,681 宣言・標準三公理のみ**。本体 107 行と入口 4 行、計 111 行を G1 の実測として数える。G0 の 710 行とは分ける。2g-1 の約 12,000 行の途中報告点にはまだ達していない。

有限型の局所性の証明分割として、`flat_openImage_iff_on_targetCover`（準コンパクトな開包含 W→Y、その像から S への射 p、S の開被覆 𝒰 について、像の射の平坦性と各引き戻しの開部分の像の射の平坦性の同値）を新しいファイルの補助 API にする。旧ファイルの対応する補題は private のため直接 import して使えない。旧宣言を公開に変えず、同じスキーム論的像と平坦底変換の可換式で分割して証明する。

同じ比較の分割 `ker_pullback_openInclusion` の型は、開 W⊆Y と g:T→Y に対し `(pullback.snd W.ι g).ker = (g ⁻¹ᵁ W).ι.ker`。旧ファイルの private な核の補題を変更せず、pullback の対称性と制限の同型で同じ法則を供給する。

有限型の局所性の束は対象 **2,822 jobs 成功**、本体 **78 行・4 宣言**。固有性を要求せず、局所有限型性と準コンパクト性から周辺空間の Noether 性を供給し、同じ像の平坦性を終域の開被覆で判定する。旧 private 補題を変更していない。新しい heartbeat・再帰・探索上限の引き上げはない。このファイルの入口登録と標準監査は、続く平坦化の束の登録時に合わせて行い、上記 10,681 宣言の監査に含めたとはしない。

この時点の G1 本体は **185 行**（特殊化 107、局所性 78）、既存入口の追加 4 行込み **189 行**。G0 の 710 行は別計上。G1 の平坦化、3.10 の細分、G2 の被覆模型は引き続き未完。

## 次の束：アフィン始域被覆からの有限型射の平坦化（着手前の型）

- `flat_openImage_pullback_of_affineSourceCover_of_finiteType`：R→A、A は Noether、f:X→Spec R は局所有限型かつ準コンパクト、𝒰 は X の affine 開被覆、t∈R。各 𝒰 のチャートの A 上の t による純変換が平坦なら、X×Spec R Spec A の t の逆像のスキーム論的閉包から Spec A への射は平坦。
- `flat_strictTransformπ_of_flatPurePullbacks_affineCover_of_finiteType`：R は Noether、同じ f・𝒰、正則な a∈R、中心 J。全ての始域チャートが blowupπ J に対し HasFlatPurePullbacks を満たすなら strictTransformπ f (D(a)) J は平坦。

既存の固有射用の宣言は変更しない。最初の補題は始域の開被覆への局所性、二つ目は blowup 基底の開被覆への局所性として分ける。同じ pullback の比較同型・係数移送・開集合の逆像の法則の分割は、本数で区切らず型を記録して使う。既定の heartbeat・再帰上限のまま検証する。

## 次の束：Noether アフィン基底上の平坦化中心（着手前の型）

`exists_admissible_flat_strictTransformπ_finiteType_affineBase`：R は Noether、f:X→Spec R は局所有限型かつ準コンパクト、a∈R は正則、f|D(a) は平坦。このとき D(a) を保つ許容中心 J が存在し、strictTransformπ f D(a) J は平坦となる。

始域の有限アフィン被覆ごとに、2d の `exists_affine_flatPure_center_of_finiteType` で中心を取り、既存の許容中心の共通細分を使う。前の束の固有性を要求しない平坦性の接続へ渡す。元の f が全射であっても、strict transform の全射性をこの段では結論に入れない。その供給は v 判定による別の接続で行う。

## 次の束：v 判定による狭義変換の全射性（着手前の型）

- `exists_specialization_from_denseOpen`：Noether かつ sober なスキーム Y、稠密開 U、y∈Y に対し、p∈U で p⤳y となる p が存在する。有限個の既約成分の一般点を使う。
- `surjective_openImage_of_vCover`：f:X→Y は IsSchemeVCover、Y は Noether、U は稠密開、(f⁻¹U) の開包含は準コンパクト。このとき (f⁻¹U) のスキーム論的像から Y への射は全射。G1 の鎖の持ち上げとスキーム論的像の台を使う。
- `strictTransformπ_surjective_of_vCover`：Noether 基底 S 上の局所有限型・準コンパクトな v 被覆 f、稠密開 U、任意の中心 J に対し strictTransformπ f U J は全射。

元の射 f に固有性を仮定しない。これは Rydh 3.10 の必要な全射性を付値判定から直接得る接続であり、単に通常の全射性だけから結論するものではない。

## 次の束：Noether 被約アフィン基底の fppf–blowup 細分（着手前の型）

- `strictTransformπ_finiteType_properties`：任意の基底、局所有限型かつ準コンパクトな f に対し strictTransformπ f U J も局所有限型かつ準コンパクト。閉包含と底変換の合成から供給する。
- `exists_fppf_blowup_refinement_of_flat_strictTransform_vCover`：S は Noether、f は有限型 v 被覆、U は稠密開、J は U に許容、strict transform は平坦。このとき blowupπ J は固有全射で U 上同型、strict transform の射 g は平坦・全射・局所有限表示・準コンパクトで、元の f の細分の可換式を満たす。g の固有性は結論に入れない。
- `exists_fppf_blowup_refinement_vCover_affineNoetherianReduced`：R は被約 Noether 環、f:X→Spec R は有限型 v 被覆。このとき上の形の許容 blowup と fppf 射の細分が存在する。中心や平坦な狭義変換の存在を仮定せず、前の束と一般平坦性から供給する。

非被約 Noether 基底と非 Noether affine 基底への接続はこの後に行う。この束だけを Rydh 3.10 全体の完成とはしない。

## 次の束：被約化による一般の Noether アフィン基底への接続（着手前の型）

`exists_fppf_proper_refinement_vCover_affineNoetherian`：R は任意の Noether 環、f:X→Spec R は局所有限型・準コンパクトな v 被覆。このとき T、固有全射・局所有限表示・準コンパクトな q:T→Spec R、平坦全射・局所有限表示・準コンパクトな g:X'→T、k:X'→X が存在し、k≫f=g≫q。

nilradical による商の被約環へ f を底変換し、前の被約 Noether の出力を使う。商射は G0 の nil の v 判定と既存の閉埋め込みの性質で処理する。これは Rydh 3.10 の Noether アフィン基底の形であり、非 Noether affine 基底への模型を完成したとは主張しない。


## 2026-11-14：Noether アフィン基底の細分までの検証

一覧：済み 6／全体 11（うち追加 2）

ID は [2g-1 の主項目台帳](scheme-w1-2g-1-checklist.md) に対応づけた。法則と証明分割は数えない。G0 の準備は別計上。

A03 の有限型射の平坦化中心、A04 の v 判定による狭義変換の全射性、A05 の被約 Noether アフィン基底の fppf–blowup 細分、A06 の一般の Noether アフィン基底の fppf–proper 細分まで通った。A06 は nilradical による被約化と G0 の nil の判定を実際の pullback と合成に使い、基底の被約性を外した。元の f に固有性を追加していない。

A06 の実際の出力は、Noether 環 R、局所有限型・準コンパクトな f:X→Spec R、IsSchemeVCover f に対し、T、X'、q:T→Spec R、g:X'→T、k:X'→X が存在し、q は固有・全射・局所有限表示・準コンパクト、g は平坦・全射・局所有限表示・準コンパクト、k≫f=g≫q。Noether 基底上なので各有限型の始域も Noether となり、有限表示に必要な準分離性も既存の Noether 性の API から得られる。

- 個別対象：純変換からの平坦性 2,915 jobs、平坦化中心 3,918 jobs、像の全射性と狭義変換 3,003 jobs、被約基底の細分 3,931 jobs、非被約基底の細分 3,934 jobs、全て成功。
- 登録後の対象と直接 importer `SerrePositivity.AlgebraicGeometry`：**4,808 jobs 成功**。
- 別実行の標準監査：**10,700 宣言、propext・Classical.choice・Quot.sound のみ**。前の未登録だった FiniteTypeStrictTransformLocality も今回含む。
- 今回の新規九ファイルは **552 行**。以前の局所性 78 行と特殊化 107 行を合わせ、G1 の本体は **737 行**、入口追加 24 行込み **761 行**。G0 の 710 行、文書、下書きは 2g-1 の実測と分ける。約 12,000 行の途中報告点と外枠 25,000 行には未到達。
- 既存の宣言の型・本文は変更していない。高い heartbeat 設定のコピーはせず、既定の上限で通した。sorry・admit・新しい公理なし。共有鍵 --wait 3600 を各実行中だけ使用し、待ちは一つ。以後の呼び出しは新しい共通規則の明示形 --class impl --wait 3600 にそろえる。

この区切りは Rydh 3.10 全体の完成ではない。A07（非 Noether affine 基底）と G2 の模型は未完。非 Noether の場合を、未証明の「Noether なモデルがある」という入力仮定に移して完成扱いにしない。2g-2 の外枠が **16,000 行**に決まったこと、2g-2 の後は 2h の段 0 の紙を出して止まることも、新しい goal の正本に合わせて記録する。

補助的な pullback の比較の法則 finiteType_congrHom_hom_snd の型は、f:X→Y、g=h:T→Y に対し (pullback.congrHom rfl (g=h)).hom≫pullback.snd f h = pullback.snd f g。旧 private 宣言を変更せず、新ファイルの private な証明分割として使った。今回の個別宣言・分割に 200 行を超えるものはない。

## 2026-11-14：非 Noether 基底の独立構成の境界

一覧：済み 6／全体 12（うち追加 3）

数学の区切りは `10bb96c88` のまま。A07 で一般点集合が準コンパクトな整全射の供給が別に必要と分かった。候補の型を C01 として台帳に記録したが、実装・承認済みとはしない。新しい独立構成で止める共通規則に従い、この線の Lean を止め、[境界報告](scheme-w1-2g-1-boundary.md) と代わりの作業である [2h の段 0](scheme-w1-2h-route.md) を作成した。2g-1 の完成報告ではない。今回の文書のみの変更では、ビルド・監査を再実行していない。

## 2026-11-14：BS17 §2 の事前照合と C01 の再開

一覧：済み 6／全体 12（うち追加 3）

指示書の追記を受け、[帰着の事前照合と C01 の型つき一覧](scheme-w1-2g-bs17-reduction.md) を記録した。Lemma 2.12 の模型の被覆性は Thm. 2.4 の非 Noether affine 基底の細分を使うため、帰着だけで A07・C01 の依存は外れない。条件 (b) で C01.1〜C01.3（500〜1,500 行見込み）に進む。親子の ID を全体で二重計上しない。2g-1 の外枠は 25,000 行のまま。

## A07 の次の小束：特殊化による像の全射性（着手前の型）

一覧：済み 6／全体 12（うち追加 3）

C01 の次に、既存の狭義変換の全射性の証明で Noether 性を使う箇所を分ける。この束は A07 内の既存の構成の法則・証明分割として全体 ID を増やさない。

- `surjective_openImage_of_vCover_of_specializations`：任意のスキーム Y、v 被覆 f:X→Y、開 U、全ての y∈Y に対し U のある点 p から p⤳y があるとする。(f⁻¹U) の開包含が準コンパクトなら、そのスキーム論的像から Y への射は全射。既存の Noether 版の証明の、特殊化の選択後の部分を再利用する。
- `surjective_openImage_of_vCover_affine_of_contains_minimalPrimes`：Y=Spec R、U が全ての極小素点を含むなら、上の全射性が成り立つ。Noether 性や R の被約性は不要。各素イデアルの下の極小素イデアルを選ぶ。

この束は平坦な稠密開や模型を供給する定理ではない。それらの A07・G2 の残りを、この全射性だけで完成扱いにしない。見込み 60〜140 行。

同じ A07 の小束で使う既存の開の選択の法則：`exists_compact_denseOpen_of_contains_minimalPrimes` は、Spec R の極小素点集合が準コンパクトで、開 V がそれを含むとき、V の内側の準コンパクトな稠密開 U で全極小素点を含むものを選ぶ。Mathlib の prespectral 空間の準コンパクト開の選択を再利用する。平坦性はこの法則の入力にも出力にも入れず、平坦な開を供給する A07 の残りと混同しない。

## 2026-11-14：C01 と非 Noether の特殊化の小束

一覧：済み 7／全体 12（うち追加 3）

C01 内の一覧：済み 3／全体 3（うち追加 0）。数学の四ファイルの新規本体は **234 行**（C01 が 165 行、A07 の法則・分割が 69 行）、入口 4 行。G1 累計は本体 **971 行**、入口込み **999 行**。G0（入口込み 710 行）は別計上。約 12,000 行の途中報告点と 25,000 行の外枠には未到達。

宣言と主張（四ファイルの明示的な宣言 10 本。法則・証明分割の本数で主項目を増やさない）：

- `ResidueFieldProduct`：全素点の剰余体の積。
- `reducedResidueProductMap`：各剰余体への標準射をまとめた環準同型。
- `reducedResidueProductMap_injective`：被約環の標準射は単射。
- `isIntegral_of_mul_self_eq`：冪等元は任意の基底環上整。X(X−1) のモニック多項式を使う。
- `comap_integralClosure_productFields_isMinimal`：体の積の素点の、その積内の整閉包への縮約は極小素点。
- `isCompact_minimalPrimes_integralClosure_productFields`：その整閉包の極小素点集合は準コンパクト。稠密像の極小素点の持ち上げで連続像の逆包含を証明。
- `exists_integral_injective_reduced_compact_minimalPrimes`：C01 の要求どおりの被約な単射整拡大を同じ証人で供給。
- `surjective_openImage_of_vCover_of_specializations`：開の点からの特殊化が基底全体を覆うとき、v 被覆の開部分のスキーム論的像は基底へ全射。
- `surjective_openImage_of_vCover_affine_of_contains_minimalPrimes`：全極小素点を含む開から、同じ全射性を得る。Noether 性・被約性は不要。
- `exists_compact_denseOpen_of_contains_minimalPrimes`：極小素点集合が準コンパクトなら、それを含む開の内側に、全極小素点を含む準コンパクトな稠密開を選べる。

C01 は零環・空の積を含み、TIC 全体や絶対整閉性は主張しない。積全体が基底上整であるという誤った仮定を使わず、その中の整閉包を取った。新規の resource limit、sorry、追加公理は導入していない。全ファイル 200 行以下。

対象 `CompactMinimalPrimeIntegralExtension` は 2,103 jobs、四ファイルを登録した直接の importer `SerrePositivity.AlgebraicGeometry` は **4,812 jobs 成功**。全プロジェクトの root ビルドと全体監査は今回行っていない。対象ログは `scheme-drafts/2g-c01-third-build.log` と `2g-c01-registered-check-2.log`。

残り：A07 の平坦な稠密開の存在と Noether 段への降下・平坦化・整全射の近似、B01〜B04 の実際のモデル構成。今回の開の選択の法則は、平坦な開そのものの存在を証明してはいない。この区切りを停止点 2g-1 の完成とはしない。

小さい監査は `scheme-drafts/audit-c01.lean` によって新規四モジュールを宣言元で抽出し、生成宣言を含む **12 宣言**を再帰的に検査して成功。許される依存は `propext`・`Classical.choice`・`Quot.sound` のみ。ログ `scheme-drafts/2g-c01-small-audit.log`。監査の初回のカウンタの型推論エラーは Nat の明示で直し、入口ビルド成功後に監査だけを再実行した。鍵は全て `--class impl --wait 3600`、同時の待ちは一つとした。

## A07 の次の小束：極小素点の近傍での有限関係の消去（着手前の型）

一覧：済み 7／全体 12（うち追加 3）

A07 の平坦な稠密開の供給に使う既存の局所化・有限生成の法則の接続。主項目を追加計上しない。見込み 100〜250 行。

- `exists_annihilator_notMem_minimalPrime`：R は被約、p は極小素イデアル、x∈p。このとき s∉p かつ s*x=0 となる s がある。極小素点での局所化が体になる Mathlib の API と、局所化での零判定を使う。
- `exists_common_annihilator_finset_minimalPrime`：p に含まれる有限集合に対して、p の外の同じ s が全要素を消す。
- `exists_common_annihilator_fg_minimalPrime`：有限生成イデアル J≤p に対して、p の外の同じ s が J 全体を消す。

使い方の案：有限表示模型の係数の Noether な部分環から極小素点の剰余体への核は有限生成なので、その有限個の関係を基本開で同時に消す。模型の整域商に対する既存の一般平坦性を、その基本開へ底変換する。模型そのものの構成や可換図式は別に供給する必要があり、この消去の法則だけで A07 が完成したとはしない。

同じ小束の係数移送：`exists_away_quotient_factor_of_minimalPrime` は、環準同型 f:S→R、R は被約、p は R の極小素点、(p.comap f).FG に対して、s∉p と l:S/(p.comap f)→Localization.Away s を返し、`l.comp (Ideal.Quotient.mk _) = (algebraMap R _).comp f` を満たす。Noether な S では FG は自動。これは有限個の係数の関係を同時に消した後の実際の商の普遍性による移送で、被覆モデルの存在を仮定に移すものではない。追加見込み 40〜100 行。

## A07 のアフィン局所の模型の接続（着手前の型）

一覧：済み 7／全体 12（うち追加 3）

`exists_finitePresentation_noetherian_model`：有限表示 R-代数 S に対し、ℤ 上有限型の Noether 環 R₀、R₀→R、有限表示 R₀-代数 S₀、実際の R-代数同型 `R ⊗[R₀] S₀ ≃ₐ[R] S` を返す。係数環の包含は Mathlib の `Algebra.Presentation.Core`、模型と同型は `ModelOfHasCoeffs`・`tensorModelOfHasCoeffsEquiv` を再利用する。見込み 40〜150 行。

これは A07 の既存の有限表示対象のアフィン局所モデルの具体化。固有スキームの貼り合わせと固有性・全射性の同時降下までを完成したものではなく、G2 の B01〜B04 を完了扱いにしない。

## 2026-11-14：有限関係の消去と実際の Noether 模型の検証

一覧：済み 7／全体 12（うち追加 3）

上の着手前の五宣言を検証した。新規本体 **137 行**（65・37・35 行の三ファイル）、入口 3 行、G1 累計は本体 **1,108 行**、入口込み **1,139 行**。全ファイル 200 行以下。

- `exists_annihilator_notMem_minimalPrime`：被約環の極小素点で零となる関係を、その素点の外の元で消す。
- `exists_common_annihilator_finset_minimalPrime`：有限個の関係の共通の消去元。
- `exists_common_annihilator_fg_minimalPrime`：有限生成イデアル全体の共通の消去元。
- `exists_away_quotient_factor_of_minimalPrime`：係数環の縮約素イデアルによる商から、実際の基本開の環への射と可換式。係数環と基底環の宇宙を別に取る。
- `exists_finitePresentation_noetherian_model`：ℤ 上有限型 Noether 環、有限表示代数の模型、元の代数との実際のテンソル積同型。Mathlib の Core を再利用。

対象ビルドは順に 2,239・2,240・1,982 jobs 成功。登録後の直接の importer `SerrePositivity.AlgebraicGeometry` は **4,815 jobs 成功**。新規三モジュールだけの小さい監査は **5 宣言・標準三公理のみ**で成功。ログは `scheme-drafts/2g-a07-minimal-relations-build.log`、`2g-a07-quotient-factor-build.log`、`2g-a07-noetherian-model-build.log`、`2g-a07-model-registered-check.log`。共有鍵は `--class impl --wait 3600`、待ちは一つ。root ビルドと大きい監査は行っていない。

A07 と G2 は未完。Noether 模型は affine な有限表示代数の模型であり、有限アフィン開被覆の重なりの貼り合わせ、固有性、全射性、filtered な被覆模型を一括して供給したという意味ではない。次は整域商上の一般自由性の開を実際の基底へ引き戻す係数・局所化の比較を組む。

## A07 の次の係数移送：整域商の主開を元の基底へ戻す（着手前の型）

一覧：済み 7／全体 12（うち追加 3）

`exists_away_quotient_localization_factor_of_minimalPrime`：f:S→R、R は被約、p∈minimalPrimes R、(p.comap f).FG、t:S/(p.comap f)、t≠0 に対し、r∉p と `Localization.Away t →+* Localization.Away r` を構成する。S から両辺への自然な射が可換であることも返す。前の有限関係の消去で得た s と t の代表 a から r=s*f(a) を取る。既存の商と局所化の構成の係数移送であり、主項目の追加には数えない。見込み 50〜120 行。

同じ A07 の一般平坦性の束の出口（着手前の型）：`exists_free_basicOpen_at_minimalPrime_of_finitePresentation` は、被約環 R、有限表示 R-代数 B、極小素点 p に対し、r∉p と `Module.Free (Localization.Away r) (Localization.Away r ⊗[R] B)` を返す。上の実際の Noether 模型、整域商の主開の係数移送、既存の整域上の一般自由性、テンソル積の cancelBaseChange をつなぐ。これは A07 の予定済みの平坦な稠密開の供給のアフィン局所であり、主項目の追加ではない。見込み 100〜300 行。

A07 の一般平坦性の次の出口（着手前の型）：`exists_compact_dense_open_flat_restrict_specMap_of_finitePresentation` は、被約環 R、極小素点集合の準コンパクト性、有限表示 R-代数 B に対し、全極小素点を含む準コンパクト稠密開 U と Spec B→Spec R の U 上の平坦性を返す。上の極小素点ごとの自由な基本開の和を取り、準コンパクト開の選択の法則を適用する。flat の target-local な貼り合わせ・制限と、自由な局所化の環の比較は既存の構成の法則として再利用・分割する。見込み 100〜220 行。

A07 の一般平坦性の有限開被覆への貼り合わせ（着手前の型）：`exists_compact_dense_open_flat_restrict_of_compact_generics` は、被約環 R と準コンパクトな極小素点集合、準コンパクトな始域 X、局所有限表示の f:X→Spec R に対し、全極小素点を含む準コンパクト稠密開上の平坦性を返す。アフィン版を有限アフィン開被覆で適用し、基底の開を共通に狭めて source-local に貼る。一般平坦性の予定済みの束の貼り合わせであり、主項目の追加ではない。見込み 100〜220 行。

## 2026-11-14：準コンパクトな一般点集合から一般平坦性への接続

一覧：済み 7／全体 12（うち追加 3）

予定した四ファイルの対象・入口・小さい監査が通った。追加は本体 **267 行**、入口 4 行。G1 累計は本体 **1,375 行**、入口込み **1,410 行**（G0 は別計上）。各ファイルは 200 行以下。

- `exists_away_quotient_localization_factor_of_minimalPrime`：整域商の非零元の主開から、元の被約環の極小素点を避ける主開への射を、係数環からの可換式つきで供給。
- `exists_free_basicOpen_at_minimalPrime_of_finitePresentation`：被約環上の有限表示代数は、各極小素点の近くの基本開で自由。Noether 模型・整域商・係数移送・テンソル積の cancelBaseChange を実際につないだ。
- private `flat_restrict_iSup_generic`：各開で平坦なら、その和の開で平坦。既存の target-local な貼り合わせの法則。
- `exists_compact_dense_open_flat_restrict_specMap_of_finitePresentation`：極小素点集合が準コンパクトな被約環上の有限表示アフィン射は、全極小素点を含む準コンパクト稠密開で平坦。
- private `exists_compact_generic_flat_of_isAffine`：同じアフィン射の結果を、始域の canonical な isoSpec で移送。
- `exists_compact_dense_open_flat_restrict_of_compact_generics`：始域が準コンパクトな局所有限表示射について、有限アフィン開被覆で上の結果を貼り合わせる。元の基底の Noether 性・元の射の固有性は仮定しない。

一般点集合から平坦開を得る際、一般の平坦性の開性の定理を新しく仮定せず、有限表示の係数模型と既存の整域上の一般自由性で供給した。局所化のスカラー作用は元の標準作用を保持し、Spec の点と PrimeSpectrum の点の所属の照合では明示した集合の等式を使った。新しい resource limit、sorry、追加公理は導入していない。

対象ビルドは `GenericFreeAtMinimalPrime` が **2,359 jobs**、`CompactGenericFlatnessAffine` が **2,986 jobs**、`CompactGenericFlatness` が **2,987 jobs** 成功。直接の importer `SerrePositivity.AlgebraicGeometry` は **4,819 jobs 成功**。新規四モジュールのみの小さい監査は **6 宣言、標準三公理のみ**で成功。ログは `scheme-drafts/2g-a07-generic-minimal-build-3.log`、`2g-a07-compact-generic-flatness-build.log`、`2g-a07-compact-generic-flatness-scheme-build-3.log`、`2g-a07-compact-generic-registered-check.log`。共有鍵は全て `--class impl --wait 3600`、待ちは一つ。

残りの主項目は **5 件**（A07 と B01〜B04）。A07 では今得た平坦な準コンパクト稠密開と射を共通の Noether 段へ移すこと、中心を構成して戻すこと、整全射の有限表示近似と細分の有限段への降下が残る。G2 のスキーム模型の構成は未完。この束は一般平坦性の入口であり、一般基底の fppf–proper 細分の完成ではない。約 12,000 行の時点で C01・A07・G2 を合わせて再見積もりする指示は維持する。

## A07 の整全射の近似：着手前の型つき小一覧

一覧：済み 7／全体 12（うち追加 3）

[Stacks 09YZ](https://stacks.math.columbia.edu/tag/09YZ) の整射の有限・有限表示な近似の affine 部分を作る。これは A07 の予定済みの整全射の近似であり、独立の外枠を増やさない。下の子 ID は親 A07 と二重に全体計上しない。

整射近似内の一覧：済み 0／全体 4（うち追加 0）

| 子 ID | 型・出口 | 見込み（新規行） |
| --- | --- | ---: |
| I01 | R-代数 B の有限個の整元 bᵢ に対し、有限かつ有限表示の R-代数 C と g:C→ₐ[R]B で全 bᵢ が g の像に入るものを供給。有限 R-代数 B 全体には同じ性質を持つ C からの全射を得る | 150〜450 |
| I02 | B への射つき有限・有限表示 R-代数の、小さい表示による添字圏を構成し filtered を証明。二対象にはテンソル積、平行射には有限個の生成元の像の差による商を使う | 400〜1,000 |
| I03 | B が R 上整なら、この filtered 図式の実際の環の cocone が IsColimit であることを示す。元の表示と有限段での一致判定を保持 | 400〜1,000 |
| I04 | Spec の逆系と実際の極限比較へ移し、整全射の場合は各有限・有限表示段を全射にそろえる | 150〜400 |
| 合計 | A07 の細分の有限段への移送自体は別の残り | **1,100〜2,850** |

I01 の最初の型：`exists_finite_finitePresentation_model_of_integral_family` は、R,B:Type u、可換環、Algebra R B、n:ℕ、b:Fin n→B、各 bᵢ の整性に対し、C:Type u、CommRing C、Algebra R C、Module.Finite R C、Algebra.FinitePresentation R C、g:C→ₐ[R]B と全 bᵢ の像への所属を返す。単なる有限生成部分代数では有限表示性が保証されないため、モニック多項式の根を順に加える。

その有限代数版 `exists_finite_finitePresentation_surjective_model` は、Module.Finite R B から上の C と全射な g を返す。有限個の加群生成元を I01 の像へ入れ、線形写像の像が全体となることを示す。いずれも元の係数環の Noether 性は要求しない。

I02 の最初の定義と法則の型：`IntegralModelCategory R B` は `FGAlgCat R` から `CommAlgCat R` への包含の B への costructured arrow のうち、始域が有限・有限表示である充満部分圏。`integralModelObj` は実際の有限・有限表示代数 C と C→ₐ[R]B をその対象へ入れる。`integralModelHomMk` は B と可換な代数準同型から模型の射を作る。`integralModelDiagram` と `integralModelCocone` は実際の環の図式と B への cocone。Mathlib の FGAlgCat の essential smallness と structured arrow の smallness を再利用し、`IntegralModelIndex R B : Type u` と small diagram・cocone へ移す。filtered 性はこの定義の段ではまだ主張しない。

I02 の二対象の法則の型：`integralModelCategory_cocone_objs` は任意の模型 X,Y から、共通の模型 Z と X→Z・Y→Z を返す。始域のテンソル積に、B への二射から誘導される射を入れる。有限表示性は有限表示の baseChange と trans、有限性はテンソル積での有限性を使う。これは先に記録した I02 の filtered 性のうち二対象の条件を分割したもの。

I02 の平行射の法則の型：`exists_finite_finitePresentation_coequalizing_quotient` は有限 R-代数 C、有限かつ有限表示の R-代数 D、f,g:C→ₐ[R]D、h:D→ₐ[R]B、h.comp f=h.comp g から、有限・有限表示の商 Q、全射 q:D→ₐ[R]Q、h':Q→ₐ[R]B、h'.comp q=h と q.comp f=q.comp g を返す。有限個の加群生成元の像の差で有限生成イデアルを作り、商と線形写像の生成元上の外延性を使う。I02 の filtered 性の二つ目の条件の証明分割であり、別の主項目には計上しない。

I02 の filtered 性への組立て：`integralModelCategory_cocone_maps` は模型の平行射 f,g:X→Y を、B への可換式と上の有限生成商で等しくする。模型の圏とその `SmallModel` に `IsFiltered` を入れる。既存の category の同値による filtered 性の移送を再利用する。

## 2026-11-14：B4 前の検証済み区切り（整射近似 I01・I02）

一覧：済み 7／全体 12（うち追加 3）

整射近似内の一覧：済み 2／全体 4（うち追加 0）。I01 の有限個の整元の有限・有限表示模型と有限代数への全射、I02 の模型の圏・同じ宇宙の添字・実際の環の cocone・filtered 性までを検証した。I03 の IsColimit と I04 の Spec への極限比較は未完。

追加は五ファイル **309 行**、入口 5 行。G1 累計は本体 **1,684 行**、入口込み **1,724 行**（G0 別計上）。全ファイル 200 行以下。

- `exists_finite_finitePresentation_model_of_integral_family`：有限個の整元を有限・有限表示代数の像で同時に表示する。
- `exists_finite_finitePresentation_surjective_model`：有限代数へ有限・有限表示代数からの全射を供給。
- `integralModelFGInclusion`・`integralModelProperty`・`IntegralModelCategory`：B への射を持つ有限・有限表示模型の圏。
- 二つの有限性 instance と essential smallness の instance：対象の性質を射の構成に使い、既存の FGAlgCat と costructured arrow の結果から小ささを得る。
- `integralModelObj`・`integralModelHomMk`：実際の代数と射・可換式から模型の対象と射を作る。
- 非空性の instance：基底環自体を模型にする。
- `integralModelDiagram`・`integralModelCocone`：実際の可換環の図式と B への cocone。
- `IntegralModelIndex`・`integralModelSmallDiagram`・`integralModelSmallCocone`：同じ宇宙の小さい模型への移送。
- private `finitePresentation_tensor_integralModel`・`integralModelCategory_cocone_objs`：二対象をテンソル積の模型へ送る。
- `exists_finite_finitePresentation_coequalizing_quotient`：有限個の加群生成元の像の差を消す有限生成イデアルの商と、実際の可換式。
- `integralModelCategory_cocone_maps` と二つの IsFiltered instance：模型と小さい添字の filtered 性。

入口 `SerrePositivity.AlgebraicGeometry` は **4,824 jobs 成功**、新規五モジュールの小さい監査は生成宣言を含む **26 宣言、標準三公理のみ**で成功。ログ `scheme-drafts/2g-pre-b4-registered-check.log`。新しい resource limit・sorry・追加公理はない。B4 の指示を受けたので、この区切りをコミットし、原ソースの collect/rewrite を優先する。


## I03：実際の小さい環の cocone の余極限（型つきの束、2026-11-14）

B4 は e9ca4d5d4 で完了し、main ad523c511 を取り込んだ。続いて既報の I03 の証明分割を実装する。R・B は同じ宇宙の可換環、B は R-代数とする。

- `integralModelSmallCocone_exists_rep [Algebra.IsIntegral R B] (b : B)`：`∃ i x, ((integralModelSmallCocone R B).ι.app i).hom x = b`。I01 の一元の模型を SmallModel の単位で運び、実際の cocone の自然性で表示を保つ。
- `integralModelSmallCocone_eq_eventually i x y h`：同じ構造射で像が一致すれば、`∃ j (f : i ⟶ j), ((integralModelSmallDiagram R B).map f).hom x = ... y`。元の模型を span{x-y} で割り、有限・有限表示の商模型の射を SmallModel の逆関手の充満性で小さい射にする。この法則に B の整性は不要。
- `integralModelSmallCoconeIsColimit [Algebra.IsIntegral R B]`：`IsColimit (integralModelSmallCocone R B)`。Mathlib の Types.FilteredColimit.isColimitOf' に二条件を渡し、forget CommRingCat の colimit の反映で実際の環の cocone の普遍性を得る。

三宣言は package と同じ relaxedAutoImplicit=false・maxSynthPendingDepth=3 の下書き検証で成功した。本体と入口への登録後のビルド・監査はこれから行う。新しい主項目は追加せず、既存の I03 の証明分割とする。G2 の Noether 模型そのものを作ったとは扱わない。

一覧：済み 7／全体 12（うち追加 3）。


### I03 の検証結果と宣言一覧

本体 `IntegralModelColimit.lean` **110 行**と入口の import 1 行。登録した入口 `SerrePositivity.AlgebraicGeometry` と新規モジュールの対象ビルドは **4,826 ジョブ成功**。新規モジュールの小監査は生成宣言を含む **7 宣言、標準三公理のみ**、終了コード 0。ログは `scheme-drafts/2g-i03-registered-build.log` と `scheme-drafts/2g-i03-small-audit.log`。共有鍵は `--class impl --wait 3600`、待ちは常に一つ。新しい resource limit・sorry・追加公理はない。

- `integralModelSmallCocone_exists_rep`：整な B の各元を、有限・有限表示の小さい模型の実際の構造射の像として表す。
- `integralModelSmallCocone_eq_eventually`：同じ模型の二元の B での一致を、有限・有限表示の商模型への射で実現し、小さい添字の実際の射へ移す。
- `integralModelSmallCoconeIsColimit`：整な B を、固定した小さい模型の環の cocone の filtered colimit として、実際の普遍性で示す。

整射近似内の一覧：済み **3／全体 4（うち追加 0）**。I03 を完了し、I04 の Spec の逆系・実際の極限比較・各段の有限性と有限表示性・全射性への接続が残る。一般の A07 の細分と G2 の Noether 模型は未完。

この束までの G1 本体は **1,794 行**、入口込み **1,835 行**（G0 の入口込み 710 行は別計）。25,000 行の外枠と約 12,000 行での途中報告を保つ。残る主項目は A07 と B01〜B04 の五つで、次の作業は A07 内 I04。今回の 110 行は I03 の見込み 400〜1,000 行より小さく、Mathlib の colimit の反映を再利用した結果である。

一覧：済み 7／全体 12（うち追加 3）。

## I04：Spec の逆系（実装前の型）

`integralModelSpecDiagram : (IntegralModelIndex R B)ᵒᵖ ⥤ Scheme` は環の図式の op と Spec の合成。`integralModelSpecCone : Cone (integralModelSpecDiagram R B)` は既存の cocone の op を Spec で写した実際の cone。`integralModelSpecConeIsLimit [Algebra.IsIntegral R B] : IsLimit (integralModelSpecCone R B)` は I03 と右随伴 Spec の極限保存を使う。射影は各模型の B への環準同型の Spec.map と一致する。

各段から Spec R への実際の構造射 `integralModelSpecBaseMap i` について、有限性・局所有限表示性と、射影との合成が Spec(algebraMap R B) であるという式を示す。後者と元の射の全射性から各段の全射性を得る。これらは既報 I04 内の構成とその法則で、追加主項目ではない。見込み 150〜400 行を維持する。

一覧：済み 7／全体 12（うち追加 3）。

## A07 の次の既存構成の法則：有限型射の閉包と共通中心

I04 の検証待ちの間に、固有射用の既存構成の法則を有限型射にも供給する分割を用意する。既存宣言の型は変更しない。以下では f:X→S は局所有限型かつ準コンパクト、U は S の開。

- `hasFlatOpenClosure_comp_iff_of_finiteType f U p g [IsNoetherian V]`：`HasFlatOpenClosure f U (g ≫ p) ↔ HasFlatOpenClosure (pullback.snd f p) (p ⁻¹ᵁ U) g`。既存の二段 pullback の比較と、有限型・準コンパクト射の Noether 始域を使う。
- `HasFlatOpenClosure.comp_of_dominant_of_finiteType h g [IsNoetherian V] [IsSchemeTheoreticallyDominant (g ⁻¹ᵁ p ⁻¹ᵁ U).ι]`：`HasFlatOpenClosure f U (g ≫ p)`。同じ閉包の稠密底変換の法則を再利用する。
- `exists_admissible_flat_strictTransformπ_of_affine_local_of_finiteType`：Noether 基底 S、有限アフィン被覆 𝒰、局所許容中心 J_i と各 `Flat (strictTransformπ (pullback.snd f (𝒰.f i)) (𝒰.f i ⁻¹ᵁ U) (J_i))` から、`∃ K, centerComplement K = U ∧ Flat (strictTransformπ f U K)`。既存の局所中心の map・共通細分と、有限型版の閉包の法則を組む。

この束は既存の構成の合成則・貼り合わせの法則と証明の分割であり、主項目の数を増やさない。見込み 140〜260 行。準コンパクト開を Noether 模型へ降ろす構成はこの束の出力ではない。

一覧：済み 7／全体 12（うち追加 3）。

同じ法則の次の合成：`exists_admissible_flat_strictTransformπ_of_finiteType` は Noether 基底 S 上の局所有限型・準コンパクト射 f と `Flat (f ∣_ U)` から、`∃ J, centerComplement J = U ∧ Flat (strictTransformπ f U J)` を返す。既存の固有射版で用いた初期中心・正則主境界の有限被覆・局所平坦化・中心の貼り合わせ・合成の共通細分を、上記有限型版の法則で接続する。既存構成の合成の法則として追加計上しない。見込み 90〜160 行、直前の三法則と合わせて 230〜420 行。原典が必要とする指定開 U を一つの主開へ狭めない。検証前は下書きに置く。

## I04 と有限型射の閉包・中心の法則：検証結果

新規四モジュールは計 **339 行**（I04 88 行、有限型版三本 63・104・84 行）、入口 import 4 行。package と同じ設定の下書き検証の後、本体と直接の importer の入口 `SerrePositivity.AlgebraicGeometry` を対象ビルドし、**4,830 ジョブ成功**。小監査は四モジュールを全て読み込み、生成宣言を含む **15 宣言、標準三公理のみ**、終了コード 0。共有鍵は `--class impl --wait 3600`、同時の待ちは一つ、ビルドと監査の束は 30 分以内。新しい resource limit・sorry・追加公理はない。長い行と letI の style 警告は残っているが、数学的な未解決の goal はない。

ログは `scheme-drafts/2g-i04-combined-check-3.log`（下書き）、`2g-i04-native-build.log`（本体と入口）、`2g-i04-small-audit.log`（小監査）。下書きの前二回のエラーは、SpecMap_iff の引数・透明性・模型の元の R-代数構造の明示で解消した。取り込み前後の refactor 用の古い索引は使っていない。

### 宣言と主張（一行ずつ）

- `integralModelSpecDiagram`：有限・有限表示 R-代数の小さい filtered 図式の Spec の逆系。
- `integralModelSpecCone`：点を実際の Spec B、射影を各模型の構造射の Spec とする cone。
- `integralModelSpecConeIsLimit`：B が R 上整なら、この実際の cone は極限。
- `integralModelSpecBaseMap`：各模型の元の R-代数構造による Spec R への射。
- `integralModelSpecBaseMap_isFinite`：この基底への射は有限（固有性は Mathlib の有限射からの instance へ接続する）。
- `integralModelSpecBaseMap_locallyOfFinitePresentation`：同じ基底への射は局所有限表示。
- `integralModelSpecCone_projection`：各射影は、既存の環の cocone の同じ脚の Spec.map。
- `integralModelSpecCone_projection_comp`：射影と各段の基底への射の合成は、元の R→B の Spec.map。
- `integralModelSpecBaseMap_surjective`：元の Spec B→Spec R が全射なら、各段の Spec→Spec R も全射。忠実平坦性は仮定しない。
- `hasFlatOpenClosure_comp_iff_of_finiteType`：有限型・準コンパクト射の閉包の平坦性を、二段と一段の底変換で比較する。
- `HasFlatOpenClosure.comp_of_dominant_of_finiteType`：境界がスキーム論的稠密な支配射に沿って、同じ閉包の平坦性を保つ。
- `exists_admissible_flat_strictTransformπ_of_affine_local_of_finiteType`：有限型射を平坦化する有限個のアフィン局所中心を、一つの基底中心へ貼り合わせる。
- `finiteType_flat_restrict_pullback_snd_of_flat`（private）：平坦な制限を底変換した射の対応する制限も平坦。
- `exists_admissible_flat_strictTransformπ_of_finiteType`：Noether 基底上の有限型・準コンパクト射について、指定した平坦開 U を保つ一つの許容中心で狭義変換を平坦化する。

I04 を完了し、整射近似内の一覧は **済み 4／全体 4（うち追加 0）**。有限型版の三モジュールは既存構成の合成則・貼り合わせとその証明分割であり、主項目を追加計上しない。既存の固有射用の宣言の名前・型は変更していない。

G1 本体の累計は **2,133 行**、入口込み **2,178 行**（G0 の入口込み 710 行は別計）。25,000 行の外枠と約 12,000 行での途中報告を維持する。今回の法則は一般の指定開を保つ Noether 段での平坦化を供給するが、有限表示スキームとその準コンパクト開・平坦性を同じ Noether 模型へ降ろす構成、ならびに G2 の一般の固有有限表示模型そのものは未完。A07 と B01〜B04 を完了扱いにしない。

一覧：済み 7／全体 12（うち追加 3）。

## A07 の次の係数移送：一般平坦開を模型にも保存する（着手前の型）

既存の一般自由性の証明は、Noether 係数環 A₀ の整域商 Q の一般自由開から、R の極小素点近傍へ係数を移した。次は同じ移送の有限個の消去関係を、R の有限生成 A₀-部分代数へ保存する。原典の一般の平坦射の降下を仮定するのではなく、選んだ一般自由開の模型を実際に供給する。

- 私有の `quotientToAwayOfAnnihilator f J s hann`：`hann : ∀ a ∈ J, s * f a = 0` から `S ⧸ J →+* Localization.Away s` を作り、商写像との合成が局所化の構造射と f の合成になる。既存の商・局所化の普遍性の証明分割。
- `exists_fg_subalgebra_quotient_localization_factor`：被約 R、S-代数構造、極小素点 p、`(p.comap (algebraMap S R)).FG` から、有限生成 `T : Subalgebra S R`、`s : T` で `↑s ∉ p` と、`S ⧸ p.comap (algebraMap S R) →+* Localization.Away s` を得る。同じ構造射との可換式を保持する。T は既存の共通消去元一つを adjoin した部分代数。見込み 50〜120 行。

後続の接続の型案：固定した Noether 係数模型 A₀・S₀ と、R の各極小素点に対する上の有限生成部分代数・整域商の一般自由開を使い、有限生成 A₀-部分代数 T と t:T を選び、`Module.Free (Localization.Away t) (Localization.Away t ⊗[A₀] S₀)` を実現する。極小素点集合の準コンパクト性で有限個を選び、部分代数の有限 join へ運ぶ。T 上の指定開はその有限個の基本開の和で、R への逆像が全極小素点を含む。T 上の有限表示模型に対して、その指定開での平坦性と実際の tensor 底変換同型を保つ。係数移送と有限被覆の貼り合わせの接続として見込み 600〜1,800 行。一般の固有射の模型 B01 を、これだけで完了扱いにはしない。

一覧：済み 7／全体 12（うち追加 3）。

次の係数移送の具体的な型：`exists_fg_subalgebra_free_basicOpen_at_minimalPrime` は、同じ宇宙の可換環 A・R・S、Noether 環 A、被約 A-代数 R、有限型 A-代数 S と p∈minimalPrimes R に対して、`∃ T : Subalgebra A R, T.FG ∧ ∃ t : T, ↑t ∉ p ∧ Module.Free (Localization.Away t) (Localization.Away t ⊗[A] S)` を返す。上の商への因子化を T 上で実現し、整域商の一般自由性を同じ tensor cancelBaseChange で戻す。既存の一般自由性の係数移送を、有限生成部分代数にも保存する法則。見込み 80〜180 行。

### 有限生成係数部分代数への商の因子化：検証結果

`GenericFlatNoetherianCoefficients.lean` **51 行**、入口 1 行。下書き検証、本体と入口の対象ビルド **4,831 ジョブ成功**、小監査 **3 宣言・標準三公理のみ**、終了コード 0。ログは `scheme-drafts/2g-coefficient-factor-check.log`、`2g-coefficient-factor-native.log`、`2g-coefficient-factor-audit.log`。共有鍵 `--class impl --wait 3600` を使用し、同時の待ちは一つ。新しい resource limit・sorry・追加公理はない。

- `quotientToAwayOfAnnihilator`（private）：共通消去元の反転により、係数射を指定イデアルの商経由にする。
- `exists_fg_subalgebra_quotient_localization_factor`：極小素点の消去元を adjoin した有限生成部分代数 T の局所化で、縮約イデアルによる商からの射と実際の可換式を得る。

G1 累計は本体 **2,184 行**、入口込み **2,230 行**。次の一般自由開を同じ T 上で実現する下書きは未検証。一般平坦開を伴う Noether 模型の有限個の貼り合わせ、A07 と G2 の完成は未達。

一覧：済み 7／全体 12（うち追加 3）。

## A07：有限個の一般自由開の係数を共通にする法則（着手前）

- `free_away_tensor_of_algHom f b`：A-代数射 f:B→C に対し、`Module.Free (Localization.Away b) (Localization.Away b ⊗[A] S)` なら、同じ式の B,b を C,f(b) へ移した自由性が成り立つ。既存の局所化の mapₐ と tensor の係数移送。
- `fg_finset_sup_subalgebra T h s`：全 T_i が有限生成なら、有限 join `s.sup T` も有限生成。既存の FG.sup の反復。
- `exists_common_fg_subalgebra_generic_free_charts A R S hmin`：Noether A、被約 A-代数 R、有限型 A-代数 S、R の極小素点集合の準コンパクト性から、有限生成部分代数 T と有限族 `t : Fin n → T` を得る。各 `Localization.Away (t i) ⊗[A] S` はその局所化上自由で、R 上の基本開 D(t_i) は全極小素点を覆う。直前の局所的な一般自由開を有限 join へ運ぶ、有限被覆の貼り合わせの法則。

この束は既存の係数移送・有限被覆の貼り合わせの法則で主項目を増やさない。見込み 100〜240 行。T⊗[A]S の実際の Noether 模型と元の有限表示代数との比較は、この束の後に既存の tensor 同型と組む。

一覧：済み 7／全体 12（うち追加 3）。

### 一般自由開の有限生成係数部分代数への移送：検証結果

`GenericFlatCoefficientFreeChart.lean` **81 行**、入口 1 行。下書き検証、本体と入口の対象ビルド **4,832 ジョブ成功**、小監査 **1 宣言・標準三公理のみ**、終了コード 0。最初の下書きの有限型性の底変換 instance の不足は Mathlib.RingTheory.FiniteStability の import で解決した。ログは `scheme-drafts/2g-coefficient-free-chart-check-2.log`、`2g-coefficient-free-chart-native.log`、`2g-coefficient-free-chart-audit.log`。共有鍵 `--class impl --wait 3600`、待ちは一つ。新しい resource limit・sorry・追加公理はない。

- `exists_fg_subalgebra_free_basicOpen_at_minimalPrime`：既存の Noether 係数環 A と有限型 A-代数 S に対し、被約 A-代数 R の各極小素点の一般自由開を、R の有限生成 A-部分代数 T 上で実現する。基本開の元を R へ移した像は指定した極小素点を避ける。

G1 累計は本体 **2,265 行**、入口込み **2,312 行**。次は有限個の開を共通係数部分代数へ運び、実際の Noether 模型と tensor 比較をまとめる。A07 と B01〜B04 は未完。

一覧：済み 7／全体 12（うち追加 3）。

次の既存模型との係数比較の型：`exists_generic_free_noetherian_model R B hmin` は、被約 R、有限表示 R-代数 B、極小素点集合の準コンパクト性から、ℤ 上有限型の Noether 環 A、有限表示 A-代数 S、実際の `R ⊗[A] S ≃ₐ[R] B` と有限族 `t : Fin n → A` を返す。各 `Localization.Away (t i) ⊗[A] S` は自由で、R へ移した基本開は全極小素点を覆う。既存の有限表示 Noether 模型の係数を共通部分代数へ移し、tensor cancelBaseChange で同型と自由性を輸送する係数比較。見込み 60〜140 行。一般の固有模型や任意の指定開の降下そのものをこの型へ置き換えない。

一般自由開を幾何の平坦開へ読む既存比較の法則：`flat_restrict_iSup_of_flat_restrict f V h` は各開 V_i での平坦性を和の開へ貼り合わせる。`flat_restrict_iSup_basicOpen_of_free_tensor A S t hfree` は有限族 t に対し、各 away tensor の自由性から `Flat (Spec.map (algebraMap A S) ∣_ ⨆ i, PrimeSpectrum.basicOpen (t i))` を得る。既存の Spec の主開の比較・局所化と tensor の比較と、開上の平坦性の局所性の法則を使う。見込み 50〜100 行。

幾何の指定開を添える比較の型：`exists_generic_flat_noetherian_model R B hmin` は同じ被約 R・有限表示代数 B と hmin に対し、既存の Noether 模型 A・S と実際の tensor 同型に、`U : (Spec A).Opens`、U の準コンパクト性、模型の射の U 上の平坦性を添える。`g = Spec(algebraMap A R)` に対し g⁻¹U が準コンパクトかつ稠密で全極小素点を含むことも返す。有限個の一般自由基本開を和にし、既存の平坦性の局所性と、一般点を含む開の稠密性を使う比較の法則。見込み 70〜150 行。ブローアップへの更なる底変換の稠密性までは主張しない。
