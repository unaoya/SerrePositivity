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

## 実際の tensor 模型からファイバー積の図式への比較（着手前の型）

`e : R ⊗[A] S ≃ₐ[R] B` に対し、`affineTensorModelIso e : Spec B ≅ pullback (Spec(A→S)) (Spec(A→R))` を既存の pullbackSpecIso・Spec の同型・対称性の合成で作る。その `hom_fst` は `Spec(S→R⊗[A]S→B)`、`hom_snd` は元の `Spec(R→B)` と一致する。`isPullback_affineTensorModel e` で同じ実際の四辺の IsPullback を得る。既存の tensor 同型の Spec への係数移送と射影の法則であり、独立した模型の存在定理は追加しない。見込み 70〜140 行。

一覧：済み 7／全体 12（うち追加 3）。

### 共通係数環と有限個の一般自由開：検証結果

`GenericFlatCommonCoefficients.lean` **86 行**、入口 1 行。下書き検証、本体と入口の対象ビルド **4,833 ジョブ成功**、小監査 **3 宣言・標準三公理のみ**、終了コード 0。ログは `scheme-drafts/2g-common-coefficients-check.log`、`2g-common-coefficients-native.log`、`2g-common-coefficients-audit.log`。共有鍵 `--class impl --wait 3600`、待ちは常に一つ。本体と小監査の束の後に実行した次の未検証の模型比較は、ℤ→A₀→T の scalar tower の instance 不足で停止した。この後続の下書きの失敗を、本体・小監査の成功と混同しない。模型比較は instance を明示して再検証へ回す。

- `free_away_tensor_of_algHom`：基本開上の tensor の自由性を、同じ元を送る代数射に沿って移す。
- `fg_finset_sup_subalgebra`：有限生成係数部分代数の有限 join は有限生成。
- `exists_common_fg_subalgebra_generic_free_charts`：全極小素点を覆う一般自由基本開を有限個選び、一つの有限生成係数部分代数上で実現する。

G1 累計は本体 **2,351 行**、入口込み **2,399 行**。既存の比較の法則・有限被覆の貼り合わせとして、主項目の数は不変。新しい resource limit・sorry・追加公理はない。実際の Noether 模型への tensor 比較と幾何の平坦開、および固有模型上の全射性の接続は、この時点ではまだ未完。

一覧：済み 7／全体 12（うち追加 3）。

## 一般自由開を伴う実際の Noether 模型と Spec の図式：検証結果

新規四モジュールは計 **244 行**（GenericFreeNoetherianModel 54 行、GenericFlatNoetherianOpen 59 行、GenericFlatNoetherianModel 57 行、AffineTensorModelPullback 74 行）、入口 4 行。最初の三本と入口の対象ビルド **4,836 ジョブ成功**、三本の小監査 **4 宣言・標準三公理のみ**。Spec の射影の比較の下書きを直して検証した後、本体と入口の対象ビルド **4,837 ジョブ成功**、同モジュールの小監査は生成宣言を含む **8 宣言・標準三公理のみ**。束全体の終了コード 0。

ログは `scheme-drafts/2g-generic-flat-model-combined-check-3.log`、`2g-generic-flat-model-native.log`、`2g-generic-flat-model-audit.log`、`2g-affine-tensor-pullback-check-4.log`、`2g-affine-tensor-pullback-native.log`、`2g-affine-tensor-pullback-audit.log`。共有鍵は `--class impl --wait 3600`、同時の待ちは一つ、検証束は一回 30 分以内。ℤ の scalar tower は、標準の zsmul の型を暗黙に使うのでなく、代数構造による三つの作用を持つ instance を明示して整合させた。Spec の射影の証明は Iso.symm_hom の展開を明示した。新しい resource limit・sorry・追加公理はない。

### 宣言と主張（一行ずつ）

- `exists_generic_free_noetherian_model`：有限表示 R-代数 B を、ℤ 上有限型の Noether 模型 S/A の実際の tensor 底変換として表し、全極小素点を覆う有限個の一般自由基本開を模型上に添える。
- `flat_restrict_iSup_of_flat_restrict`：各開での平坦性を和の開へ貼り合わせる。添字の宇宙はスキームの宇宙と独立。
- `flat_restrict_iSup_basicOpen_of_free_tensor`：基本開ごとの away tensor の自由性から、その和での Spec の射の平坦性を得る。
- `exists_generic_flat_noetherian_model`：実際の Noether 模型と tensor 同型に準コンパクトな平坦開 U を添え、元の基底へのその逆像が準コンパクト・稠密で全極小素点を含むことを示す。
- `affineTensorModelIso`：実際の R-代数同型 R⊗[A]S≃B を、同じ係数射の Spec のファイバー積との同型へ移す。
- `affineTensorModelIso_hom_fst`：第一射影は S→R⊗[A]S→B の Spec と一致する。
- `affineTensorModelIso_hom_snd`：第二射影は元の R→B の Spec と一致する。
- `isPullback_affineTensorModel`：同じ実際の四辺が pullback square を与える。

G1 累計は本体 **2,595 行**、入口込み **2,647 行**。この束は既存模型の係数移送と開の貼り合わせ・射影の法則であり、主項目の数は変えない。既存の宣言の型・名前は変更していない。

A07 の一般平坦開を伴うアフィン Noether 模型への接続は得た。引き戻した固有模型上の全射性と、有限表示を保つ細分の構成、整全射の有限段への refinement の移送は未完。G2 の一般の固有有限表示スキームの模型を、このアフィン模型で完成扱いにはしない。

一覧：済み 7／全体 12（うち追加 3）。

## 次の存在構成の境界（C02 候補）

85507998e の検証済みをコミットした後、固有模型の平坦射の像の中に、指定された閉部分スキームを含む有限表示の閉包絡を作る構成が必要になった。既存の係数比較だけではなく新しい存在構成に当たると判断し、[有限表示の閉包絡の境界報告](scheme-w1-2g-1-fp-envelope-boundary.md) に型・不足・原典・代替経路・規模を記録した。C02 は未承認で、一覧に追加していない。この構成の Lean には入らず、既定の代わりの仕事である 2h の紙の照合へ移る。2g-1 の完成報告ではない。

一覧：済み 7／全体 12（うち追加 3）。

## C02 再開：型つきの小一覧と見込み（2026-11-14 夕）

main の scheme-w1.md の追記とユーザーの指示を確認し、main を math/scheme へ取り込んだ（1f61ece49）。C02 は一般の固有・局所有限表示の Y のまま進める。ブローアップ限定・Proj の極限の経路は採らない。新しい標準存在補題の枠は、G1・G2 内、原典の Tag・番号付き、一つの見込み 4,000 行以下。外枠 25,000 行は不変。

まず `IsFiniteTypeIdealSheaf K := ∀ U : X.affineOpens, (K.ideal U).FG` を局所的な有限型性の入口とする。C02 の三分割は次の型で、親 C02 と二重計上しない。

| 子項目 | 型・主張 | 原典 | 見込み |
| --- | --- | --- | --- |
| C02.(i) | qcqs X、K:X.IdealSheafData、有限族のアフィン開 U_i とその上の有限集合 s_i⊆K(U_i) に対し、J≤K、IsFiniteTypeIdealSheaf J、かつ全 i で s_i⊆J(U_i) を満たす J が存在する | Stacks 01PF (28.23.2)、01PG (28.23.3) | 1,200〜3,000 行 |
| C02.(ii) | IsFiniteTypeIdealSheaf K なら LocallyOfFinitePresentation K.subschemeι | Stacks 01TV (29.22.7)、商環の有限表示 | 100〜300 行 |
| C02.(iii) | p:Y→Spec R が固有・局所有限表示、K.support⊆V に対し、J≤K、LocallyOfFinitePresentation J.subschemeι、J.support⊆V を満たす J が存在する | 01PF・01PG・01TV の有限選択による帰結 | 150〜400 行 |

定義・入口登録・小監査等 50〜200 行を含めて C02 全体は 1,500〜4,000 行の見込みを維持する。最初に (ii) の既存の商環の比較を供給し、続いて (i) のアフィンでの有限選択と有限被覆による延長を構成し、(iii) へ渡す。i を未証明の入力に置いた条件付きの (iii) だけで C02 の完成とはしない。

Z⊆V と Z の全射性の接続は、準コンパクト開の閉包での特殊化・v 判定による特殊化の持ち上げ・固有射の閉像による法則として進める（見込み 200〜600 行、C02 の存在構成の子項目と混同しない）。

一覧：済み 7／全体 13（うち追加 4）。

C02.(i) のアフィン局所の有限選択の法則：`exists_fg_subideal_localization_contains` は、任意の環 A のイデアル I と局所化 A→B、有限集合 s⊆I B に対し、有限生成 J≤I で s⊆JB となる J を選ぶ。Stacks 01PF (28.23.2) のアフィンでの分母と分子の有限選択に対応する。既存の IsLocalization.mem_map_algebraMap_iff で各切断の分子を選び、その有限個の分子の span を使う。見込み 40〜100 行。大域の延長 C02.(i) の完成とは区別する。

### C02 の有限型閉包含とアフィンでの有限選択：検証結果

FiniteTypeIdealSheaf と FiniteIdealLocalizationApproximation の二モジュールは各 43 行、計 **86 行**、入口 2 行。下書き検証後、本体と直接の importer の入口の対象ビルド **4,839 ジョブ成功**。小監査は **3 宣言・標準三公理のみ**、終了コード 0。ログは `scheme-drafts/2g-c02-finite-type-ideal-check-3.log`、`2g-c02-localization-approximation-check.log`、`2g-c02-foundation-native.log`、`2g-c02-foundation-audit.log`。共有鍵 `--class impl --wait 3600`、待ちは一つ。新しい resource limit・sorry・追加公理はない。

- `IsFiniteTypeIdealSheaf`：全アフィン開上の切断イデアルの有限生成性。
- `locallyOfFinitePresentation_subschemeι_of_finiteType`：同じイデアル層の実際の閉包含は局所有限表示（C02.(ii)）。
- `exists_fg_subideal_localization_contains`：局所化先の有限個のイデアル切断を、元の有限生成部分イデアルの像に同時に含める。

C02 内の主三項目は済み **1／全体 3**（(ii) のみ）。(i) の大域の有限型部分イデアルと (iii) の閉包絡は未完で、局所化の有限選択だけで (i) の完成とはしない。G1 累計は本体 **2,681 行**、入口込み **2,735 行**。

一覧：済み 7／全体 13（うち追加 4）。

次の C02.(i) のアフィン比較の法則：`exists_fg_subideal_map_contains_finset f I s hs` は任意の環準同型 f:A→B と有限集合 s⊆Ideal.map f I に対し、有限生成 J≤I で s⊆Ideal.map f J を得る。これは Stacks 01PF のアフィンでの有限選択を、生成イデアルへの所属の有限性で扱う分割で、局所化の仮定を要しない。見込み 60〜140 行。この法則を K.map_ideal と組み、アフィン基底上の有限個のアフィン開の切断を同じ有限生成イデアルへ含める。

C02.(i) の有限型性の係数比較の法則：`isFiniteTypeIdealSheaf_of_fg_top` はアフィン X において K の全体切断イデアルの有限生成性から IsFiniteTypeIdealSheaf K を得る。`isFiniteTypeIdealSheaf_ofIdealTop` は有限生成な大域切断イデアルから作る既存の ofIdealTop の有限型性、`IsFiniteTypeIdealSheaf.sup` は有限和による安定性。原典 01TV のアフィン局所判定と 01PG の有限和の部分。いずれも既存の map_ideal・FG.map・FG.sup の法則で、見込み 40〜100 行。

C02.(i) のアフィン部分の具体的な型：`exists_finiteType_subideal_containing_affine_sections_of_isAffine` はアフィン X、K、有限族のアフィン開 U_i と有限集合 s_i⊆K(U_i) から、J≤K、IsFiniteTypeIdealSheaf J、全 i で s_i⊆J(U_i) を得る。Stacks 01PF (28.23.2) のアフィン部分。全体の切断イデアルから U_i への map_ideal と有限選択を使い、有限個の部分イデアルを和にして equivOfIsAffine で戻す。見込み 60〜160 行。非アフィン基底への有限被覆の延長はまだ別に残る。

C02.(i) の被覆による有限型性の法則：`isFiniteTypeIdealSheaf_of_affineCover` は X のアフィン開被覆 U_i と全 i での (K.ideal U_i).FG から IsFiniteTypeIdealSheaf K を得る。型は `∀ (U : ι → X.affineOpens), (⨆ i, (U i).1) = ⊤ → (∀ i, (K.ideal (U i)).FG) → IsFiniteTypeIdealSheaf K`。Stacks 01TV の有限型性の局所判定。V と U_i の交叉を基本開で細分し、既存の Submodule.of_localizationSpan' と map_ideal に帰着する（見込み 50〜150 行）。`IsFiniteTypeIdealSheaf.comap_openImmersion` は開埋め込み j:X→Y に沿う制限で有限型性を保存する。既存の ideal_comap_of_isOpenImmersion と切断環の同型による法則（見込み 20〜60 行）。

### C02 の環準同型の有限選択と有限型性の係数移送：検証結果

FiniteIdealMapApproximation（57 行）と FiniteTypeIdealSheafLocality（44 行）、本体計 **101 行**、入口 2 行を追加した。対象ビルドは直接の importer AlgebraicGeometry まで **4,841 ジョブ成功**、小監査は補助宣言を含め **5 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600` をビルドの間だけ取得した。新しい resource limit・sorry・追加公理はない。

- `exists_fg_subideal_map_contains_finset`：任意の環準同型によるイデアルの像の有限集合を、有限生成部分イデアルの像に同時に含める。
- `isFiniteTypeIdealSheaf_of_fg_top`：アフィン基底の全体切断イデアルの有限生成性から有限型イデアル層を得る。
- `isFiniteTypeIdealSheaf_ofIdealTop`：有限生成な大域切断イデアルの既存の層への移送は有限型。
- `IsFiniteTypeIdealSheaf.sup`：有限型イデアル層は二項和で保たれる。

ログ：`2g-c02-map-locality-native.log`、`2g-c02-map-locality-audit.log`。G1 累計は本体 **2,782 行**、入口込み **2,838 行**。アフィンの有限族をまとめる次の補題は下書き検証成功、まだ本体ビルド・監査前。被覆の判定も検証前の作業木にあり、C02.(i) の大域延長の完成とは数えない。

一覧：済み 7／全体 13（うち追加 4）。

C02.(i) の開の重なりの係数移送の法則：`idealSheaf_comap_map_of_isPullback_openImmersion` は pullback square (a:W→X,b:W→Y,j:X→S,v:Y→S)、QuasiCompact j、IsOpenImmersion v に対し `(K.map j).comap v = (K.comap a).map b` を示す。既存の閉部分スキームの comapIso と開基底変換の核の公式による法則（Stacks 01PF の延長の貼り合わせで使用、見込み 40〜120 行）。新しい有限型性の存在構成とは数えない。

C02.(i) の貼り合わせの法則：`exists_subideal_gluing_open_pair` は開埋め込み j:X→S,v:Y→S（ともに準コンパクト）の重なりの pullback (a,b) と、K≤I.comap j、L≤I.comap v、K.comap a=L.comap b に対し、J≤I、J.comap j=K、J.comap v=L を与える。J は既存の像・共通部分 `I ⊓ K.map j ⊓ L.map v` であり、被覆の仮定はこの貼り合わせの等式には不要。開の逆像の共通部分の保存と map/comap の随伴の法則を使う。Stacks 01PF の貼り合わせの分割（見込み 60〜160 行）。有限型性を主張するには、この後に被覆と有限型性の局所判定を使う。

C02.(i) の一般の開被覆の有限型性の法則：`isFiniteTypeIdealSheaf_of_openCover` は実際の X.OpenCover 𝒰 と全 i での IsFiniteTypeIdealSheaf (K.comap (𝒰.f i)) から IsFiniteTypeIdealSheaf K を得る。既存の affineRefinement と切断環同型を通して上のアフィン開被覆の判定へ渡す。原典 01TV の局所判定、見込み 40〜100 行。有限型性を仮定から結論へ移す法則で、新しい存在項目とは数えない。

C02.(iii) の有限選択への分割：`exists_finite_affine_sections_support_subset` は CompactSpace X、K.support⊆V に対して、K のアフィン切断から有限族 t を選び、t をすべて含む任意のイデアル層 J の支持が V に含まれることを示す。型は `∃ t : Finset (Σ U : X.affineOpens, K.ideal U), ∀ J, (∀ a ∈ t, (a.2 : Γ(X,a.1.1)) ∈ J.ideal a.1) → (J.support : Set X) ⊆ V`。01PF・01PG の有限型近似の支持への適用を、補集合のコンパクト性と basicOpen/zeroLocus の既存の比較で分割する（見込み 50〜130 行）。この有限選択だけで閉包絡の完成とはしない。

C02.(i) のアフィン有限族との一致への分割：`exists_finiteType_subideal_eq_on_affine_family_of_isAffine` はアフィン X、有限族 U_i、全 i での (K.ideal U_i).FG に対して、J≤K、IsFiniteTypeIdealSheaf J、全 i で J.ideal U_i=K.ideal U_i を得る。各切断イデアルの有限生成元を先のアフィン有限選択へ渡す法則（原典 01PF のアフィン延長の部分、見込み 40〜100 行）。

C02.(i) の貼り合わせの等式検出の法則：`idealSheaf_ext_of_openCover` は実際の開被覆上の comap の一致から大域の一致を得る。`idealSheaf_comap_eq_iff_affine_sections` はアフィン開 U への二つの comap の一致を、元の U 上の切断イデアルの一致と同値にする。既存の affineRefinement・アフィンでの ext・開の切断環同型による法則（原典 01PF の貼り合わせで使用、見込み 40〜100 行）。

C02.(i) のアフィン基底から準コンパクト開への一致：`exists_finiteType_subideal_eq_on_quasiCompact_open_of_isAffine` はアフィン X、準コンパクト開 W、IsFiniteTypeIdealSheaf (K.comap W.ι) に対し、J≤K、IsFiniteTypeIdealSheaf J、J.comap W.ι=K.comap W.ι を得る。01PF のアフィン基底の場合そのものを、既存の基底の有限選択、前の有限アフィン族との一致、開被覆による等式検出に分割する。見込み 70〜180 行。次の非アフィンの二つの開の貼り合わせへの入力。

C02.(i) の二開集合の延長への分割：`exists_finiteType_subideal_extending_open_pair` は j:X→S,v:Y→S が準コンパクトな開埋め込み、Y がアフィン、両者が S を覆うとき、H≤K.comap j、IsFiniteTypeIdealSheaf H から、J≤K、IsFiniteTypeIdealSheaf J、J.comap j=H を得る。重なり上で E=K⊓H.map j の制限を計算し、Y 上で有限型の N≤E.comap v を重なりと一致させてから既存の像・共通部分で貼る。01PF の有限アフィン被覆の帰納の一段（見込み 150〜350 行）。

上の二開集合の一段は、先に `exists_subideal_extending_to_affine_open` として被覆の仮定を外し、結論を `J≤K ∧ IsFiniteTypeIdealSheaf (J.comap v) ∧ J.comap j=H` とする証明分割で進める。その後で被覆の仮定がある場合の大域有限型性を得る。有限被覆の帰納は基底 S を固定し、既に扱った準コンパクト開の和への制限を保ちながら、次のアフィン開上の有限型性を追加する。

C02.(i) の有限被覆の帰納の分割：`exists_subideal_finiteType_on_finite_affine_family_extending` は準分離 S、準コンパクト開 W、H≤K.comap W.ι、有限型 H と有限アフィン族 (U_i)_{i∈t} に対し、J≤K、J.comap W.ι=H、各 i∈t で IsFiniteTypeIdealSheaf (J.comap U_i.ι) を得る。基底 S 上のイデアルを保ったまま二開集合の延長の法則を有限帰納する（01PF、見込み 120〜300 行）。その前提の法則 `isFiniteTypeIdealSheaf_comap_iSup` は開の和上の有限型性を各開への制限から得る。いずれも C02.(i) の既定の有限被覆の帰納の証明分割。

C02.(i) の有限被覆の帰納の出口：`exists_finiteType_subideal_extension` の型は qcqs X、準コンパクト開 W、H≤K.comap W.ι、IsFiniteTypeIdealSheaf H から、J≤K、IsFiniteTypeIdealSheaf J、J.comap W.ι=H。Stacks 01PF (28.23.2) をイデアル層に適用した形で、前の有限族の帰納に X の有限アフィン被覆を渡す証明分割（見込み 60〜150 行）。既定の C02.(i) の有限切断族への出口は、この延長を各切断イデアルの有限生成部分へ適用し有限和を取る。

C02.(i) の切断への出口：`idealSheaf_comap_opens_top` はアフィン開の制限の全体切断イデアルを topIso による元の切断イデアルの像と比較する法則。`exists_finiteType_subideal_containing_affine_finset` は qcqs X、アフィン U、有限集合 s⊆K(U) に対し J≤K、有限型 J、s⊆J(U) を得る。topIso で span(s) を U の全体切断へ移し、既定の延長 01PF を適用する分割（見込み 70〜170 行）。`exists_finiteType_subideal_containing_affine_sections` は既定の C02.(i) の有限族の型で、各アフィンの有限集合にこの延長を適用し有限和を取る（見込み 50〜120 行）。

C02.(iii) の出口：`exists_finitePresentation_closedEnvelope` は qcqs X、K.support⊆V に対して J≤K、LocallyOfFinitePresentation J.subschemeι、J.support⊆V を得る（01PF・01PG・01TV、見込み 50〜120 行）。`exists_finitePresentation_closedEnvelope_of_proper` は基底 Spec R 上の一般の固有・局所有限表示 Y に同じ結論を与える指定の型へのラッパーであり、ブローアップ・射影性に制限しない。下書き段階であり、C02 の完成扱いは全ての対象ビルド・小監査の後に行う。

### C02 のアフィン有限選択・被覆の判定・開基底変換：検証結果

AffineFiniteTypeSubideal（63 行）、FiniteTypeIdealSheafCover（60 行）、IdealSheafOpenBaseChange（36 行）の三モジュール、計 **159 行**と入口 3 行を追加。対象ビルドは直接の importer AlgebraicGeometry まで **4,844 ジョブ成功**、小監査は補助宣言込み **5 宣言・標準三公理のみ**。ログは `2g-c02-affine-cover-native.log`、`2g-c02-affine-cover-audit.log`。共有鍵 `--class impl --wait 3600` をビルドの間だけ取得。resource limit の追加・sorry・追加公理なし。

- `exists_finiteType_subideal_containing_affine_sections_of_isAffine`：アフィン基底の有限個のアフィン開の切断を同時に含む有限型部分イデアル層を選ぶ。
- `isFiniteTypeIdealSheaf_of_affineCover`：アフィン開被覆上の切断イデアルの有限生成性から大域の有限型性を判定する。
- `IsFiniteTypeIdealSheaf.comap_openImmersion`：開埋め込みへの制限は有限型性を保存する。
- `idealSheaf_comap_map_of_isPullback_openImmersion`：準コンパクト射によるイデアル層の像は、実際の開 pullback square の基底変換と整合する。

G1 累計は本体 **2,941 行**、入口込み **3,000 行**。C02.(i) の非アフィンの有限被覆の帰納と (iii) の一般の閉包絡は下書き段階。個別の下書きでは IdealSheafOpenPairGluing・AffineFiniteTypeSubidealFamily・FiniteIdealSupportSelection が検証成功したが、まだ本体ビルドと監査を通していないのでこの実測には加えない。C02 内は (ii) のみ完了のまま。

一覧：済み 7／全体 13（うち追加 4）。

## C02 完了：一般の有限表示閉包絡（2026-11-14）

指定の一般の固有・局所有限表示 p:Y→Spec R に対し、K.support⊆V から
`∃ J, J ≤ K ∧ LocallyOfFinitePresentation J.subschemeι ∧ (J.support : Set Y) ⊆ V`
を構成した。J≤K は、指定された K の閉部分スキームを J の閉部分スキームが含む向きである。元の Y に Noether 性・射影性・ブローアップの形を仮定していない。内部では、より一般に qcqs スキーム上で同じ結論を得た。C02 の (i)〜(iii) は **3／3 完了**。

原典は Stacks **01PF (28.23.2)**・**01PG (28.23.3)** の有限型部分イデアル層の延長と有限選択、および **01TV (29.22.7)** の有限型閉包含の有限表示性。新しい独立した存在項目は既定の C02 のままで、下の被覆・係数移送・貼り合わせ・有限帰納はその証明分割として数える。

### 今回の検証と登録

新規十三モジュール **681 行**、入口 13 行。下書き一式の検証後、個々の本体モジュールと直接の importer `SerrePositivity.AlgebraicGeometry` の対象ビルド **4,857 ジョブ成功**。新規十三モジュールだけの小監査は補助宣言込み **27 宣言・標準三公理のみ**、終了コード 0。共有鍵 `--class impl --wait 3600` は一つの待ちで、ビルドと監査の間だけ取得した。新しい resource limit・sorry・追加公理なし。ログ：`scheme-drafts/2g-c02-draft-batch-check-3.log`、`2g-c02-envelope-native.log`、`2g-c02-envelope-audit.log`。ルート・下流の全ビルドは行っていない。

| 登録モジュール | 行数 |
| --- | ---: |
| IdealSheafOpenPairGluing | 53 |
| FiniteTypeIdealSheafOpenCover | 51 |
| AffineFiniteTypeSubidealFamily | 36 |
| FiniteIdealSupportSelection | 44 |
| IdealSheafOpenCoverExt | 66 |
| AffineFiniteTypeSubidealOpen | 55 |
| FiniteTypeIdealSheafOpenUnion | 29 |
| FiniteTypeIdealOpenPairExtension | 91 |
| FiniteTypeIdealFiniteFamilyExtension | 73 |
| FiniteTypeIdealExtension | 42 |
| FiniteTypeIdealSectionExtension | 53 |
| FiniteTypeIdealApproximation | 38 |
| FinitePresentationClosedEnvelope | 50 |

### 宣言と主張（一行ずつ）

- `idealSheaf_comap_inf_of_openImmersion`：開への逆像はイデアル層の二項共通部分を保存する。
- `exists_subideal_gluing_open_pair`：重なりで一致する二つの部分イデアル層を、指定した大域イデアル層の中で貼る。
- `fg_ideal_image_of_comap_openImmersion`：開への逆像の有限生成な切断イデアルを、その像のアフィン開へ戻す。
- `isFiniteTypeIdealSheaf_of_openCover`：開被覆上の有限型性から大域有限型性を判定する。
- `exists_finiteType_subideal_eq_on_affine_family_of_isAffine`：アフィン基底の指定有限族上で元のイデアルと一致する有限型部分を選ぶ。
- `exists_finite_affine_sections_support_subset`：支持を指定開に含めるための有限個のアフィン切断を選ぶ。
- `idealSheaf_ext_of_openCover`：開被覆上の逆像の等式から大域等式を検出する。
- `idealSheaf_comap_opens_top`：アフィン開への制限の全体切断イデアルを topIso による像と比較する。
- `idealSheaf_comap_eq_iff_affine_sections`：アフィン開への逆像の一致と切断イデアルの一致を比較する。
- `fg_ideal_of_comap_opens_top`：制限の全体切断の有限生成性を元のアフィン切断へ戻す。
- `exists_finiteType_subideal_eq_on_quasiCompact_open_of_isAffine`：アフィン基底上で準コンパクト開への制限を保つ有限型部分を選ぶ。
- `isFiniteTypeIdealSheaf_comap_iSup`：開の和上の有限型性を各開への制限から得る。
- `exists_subideal_extending_to_affine_open`：指定開への制限を保ち、別のアフィン開上の有限型性を加える。
- `exists_finiteType_subideal_extending_open_pair`：二つの開が全体を覆う場合、アフィン側を加えて有限型部分イデアル層を延長する。
- `exists_subideal_finiteType_on_finite_affine_family_extending`：指定開への制限を保ちながら、有限アフィン族上の有限型性を帰納的に加える。
- `exists_finiteType_subideal_extension`：qcqs スキームの準コンパクト開上の有限型部分イデアル層を、同じ大域イデアルの中で延長する。
- `exists_finiteType_subideal_containing_affine_finset`：一つのアフィン開の有限個の切断を含む大域有限型部分イデアル層を選ぶ。
- `exists_finiteType_subideal_containing_affine_sections`：有限個のアフィン開の有限切断族を同時に含む大域有限型部分イデアル層を選ぶ（C02.(i)）。
- `exists_finitePresentation_closedEnvelope`：qcqs スキーム上で指定閉部分スキームを含み指定開に入る有限表示閉包絡が存在する（C02.(iii)）。
- `exists_finitePresentation_closedEnvelope_of_proper`：一般の固有・局所有限表示の Y 上の指定された C02 の型を供給する。

C02 の本体は先の基礎を含め **1,027 行**、入口 20 行で、当初の 1,500〜4,000 行の見込みの上端内。G1 累計は本体 **3,622 行**、入口込み **3,694 行**。A07 は未完：閉包が平坦射の像の開 V に含まれることと閉包の全射性を、特殊化・v 判定により接続し、整全射の有限表示段との細分へ渡す。G2 の一般の固有有限表示モデルも未完。C02 の閉包絡の完成を A07 や一般の平坦化の完成とは呼ばない。

一覧：済み 8／全体 13（うち追加 4）。

## A07 続行：閉包と v 判定の特殊化の接続の法則

C02 の完了コミットは 24dcb59d9。次の法則は既定の A07 の Z⊆V と全射性の接続の分割で、独立な存在項目を追加しない。

- `exists_specialization_from_compactOpen_closure`：qcqs スキーム Y、準コンパクト開 U、y∈closure U に対し、u∈U、u⤳y を得る。Rydh Proposition 3.7 の閉包の特殊化の部分。既存の構成可能位相のコンパクト性（Mathlib、Stacks 0901）を使い、U と y の準コンパクト開近傍の有限交叉性から選ぶ。見込み 80〜200 行。
- `mem_range_comp_of_vCover_specialization`：v 判定を満たす f:X→Y、閉埋め込み i:Z→X、f⁻¹U⊆range i、u∈U、u⤳y から y∈range(i≫f)。既存の liftsSpecializations と閉像の特殊化による安定性の法則。見込み 30〜80 行。
- `closure_subset_range_comp_of_vCover_closedRestriction`：上に qcqs Y と U の準コンパクト性を加え、closure U⊆range(i≫f) を得る。前の二つを合成する法則（見込み 10〜30 行）。

一覧：済み 8／全体 13（うち追加 4）。

A07 の全射性の法則：`surjective_of_isProper_of_denseRange` は固有射 f の稠密像から全射性を得る。`surjective_imageι_comp_of_denseRange` は準コンパクト j:X→Y、固有 p:Y→S、DenseRange(j≫p) から、実際のスキーム論的像の構造射 j.imageι≫p の全射性を得る。Rydh Proposition 3.7 の固有閉像による法則で、既存の toImage_imageι と固有射の閉像を使う（見込み 30〜90 行）。新しい存在項目としては数えない。

A07 の閉包絡と平坦被覆の接続：`exists_fppf_closedEnvelope_refinement_of_flat_closedRestriction` の入力は p:Y→Spec R 固有・局所有限表示、v 判定を満たす f:X→Y、閉埋め込み i:Z→X、g=i≫f が平坦・局所有限表示・準コンパクト、準コンパクト開 U⊆Y、f⁻¹U⊆range i、DenseRange(U.ι≫p)。結論は T,W、固有・局所有限表示・全射 r:T→Spec R、平坦・局所有限表示・準コンパクト・全射 q:W→T、a:W→X と a≫f≫p=q≫r。C02 の実際の J.subscheme を T とし、W は g の底変換。Rydh Proposition 3.7 の閉包・閉包絡・平坦像による既存の構成の接続（見込み 80〜220 行）。この条件付きの図式の接続だけで A07 の一般の細分の完成とはしない。入力となる Noether 模型とその実際の閉部分への適用、整全射の有限表示段との移送は別に残る。

### A07 の閉包・特殊化・固有閉像：検証結果

CompactOpenSpecialization（58 行）、VCoverClosedRestrictionSpecializations（42 行）、ProperClosedImageSurjectivity（40 行）、計 **140 行**と入口 3 行。対象ビルドは直接の importer AlgebraicGeometry まで **4,861 ジョブ成功**。三モジュールの小監査は補助宣言込み **6 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログは `2g-closed-restriction-check-3.log`、`2g-closed-restriction-native.log`、`2g-closed-restriction-audit.log`。

- `exists_specialization_from_compactOpen_closure`：qcqs スキームの準コンパクト開の閉包の各点を、その開の点の特殊化として選ぶ。
- `mem_range_comp_of_vCover_specialization`：v 判定の特殊化の持ち上げと閉像の安定性で、指定開の点の特殊化を閉部分の像へ入れる。
- `closure_subset_range_comp_of_vCover_closedRestriction`：指定開の逆像を含む閉部分は、その開の閉包の全点を v 判定で覆う。
- `surjective_of_isProper_of_denseRange`：稠密像を持つ固有射は全射。
- `surjective_imageι_comp_of_denseRange`：合成の像が稠密なら、固有な構造射を持つ実際のスキーム論的像は基底へ全射。

この閉包の特殊化の補題は Noether 性を要求せず、U が基底全体で稠密であるとも仮定しない。生のブローアップの底変換上で U が稠密だという誤った主張を使わない。G1 累計は本体 **3,762 行**、入口込み **3,837 行**。C02 と合わせる図式の接続は引き続き下書き検証中で、A07 自体は未完。

一覧：済み 8／全体 13（うち追加 4）。

### C02 と平坦な閉部分の fppf 細分の接続：検証結果

ClosedEnvelopeFlatRefinement **76 行**、入口 1 行を追加。`exists_fppf_closedEnvelope_refinement_of_flat_closedRestriction` は上に記した入力の図式から、実際の閉包絡の T=J.subscheme と W の pullback、固有・局所有限表示・全射 r、平坦・局所有限表示・準コンパクト・全射 q、および元の射との可換式を同時に供給する。r は固有なので準コンパクト・準分離でもあり、有限表示の固有全射である。

対象ビルドは直接の importer AlgebraicGeometry まで **4,862 ジョブ成功**、新モジュールの小監査 **1 宣言・標準三公理のみ**。ログ：`2g-closed-envelope-flat-refinement-check-3.log`、`2g-closed-envelope-flat-refinement-native.log`、`2g-closed-envelope-flat-refinement-audit.log`。共有鍵 `--class impl --wait 3600`、一つの待ち、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。

これで C02 後の閉包・特殊化・全射性・平坦な閉部分との接続は四モジュール **216 行**、入口 4 行、小監査 **7 宣言・標準三公理のみ**。G1 累計は本体 **3,838 行**、入口込み **3,914 行**。

A07 自体は未完。次は GenericFlatNoetherianModel の実際の模型、FiniteTypeFlatteningNoetherian の中心、strictTransformι・strictTransformπ、AffineTensorModelPullback の pullback 比較を、この図式の入力へ渡す。用いる平坦な閉部分は Noether 模型上の狭義変換の底変換であり、非 Noether 基底上の生の狭義変換を平坦と仮定しない。その後、整全射の有限・有限表示段への模型の移送と、G2 の一般の固有有限表示模型を接続する。条件付きの図式の接続を一般の Rydh 3.10 の完成とは数えない。

一覧：済み 8／全体 13（うち追加 4）。

## A07 の Noether 模型の実際の底変換への接続：次の型つきの法則

- `closedRestrictionBaseChangeMap f i v`：i:Z→X、f:X→S、v:T→S に対し、既存の pullback.lift による pullback(i≫f,v)→pullback(f,v)。二射影の式を持つ。
- `isPullback_closedRestrictionBaseChangeMap`：この射と元の i の四辺は pullback square。
- `isClosedImmersion_closedRestrictionBaseChangeMap`：元の i が閉埋め込みなら、同じ実際の底変換射も閉埋め込み。
- `closedRestrictionBaseChangeMap_properties`：i≫f の平坦・局所有限表示・準コンパクト性を、底変換射と第二射影の合成へ渡す。
- `closedRestrictionBaseChangeMap_contains_preimage`：f⁻¹U⊆range i なら、底変換後も第二射影の v⁻¹U の逆像は底変換した i の像に入る。

以上は Noether 模型上の strictTransformι をそのまま底変換する法則。原典 Rydh Proposition 3.7、既存の Cartesian な底変換の標準性質。見込み 80〜180 行で、独立な存在構成として数えない。

- `iteratedModelBaseChangeMap`：IsPullback a x f₀ g（元の affine tensor 模型）と IsPullback v p p₀ g（固有模型の底変換）から、pullback(pullback.snd f₀ p₀,v)→X を普遍性で構成する。
- `isPullback_iteratedModelBaseChangeMap`：同じ射、第二射影、x、p の四辺は pullback square。
- `isSchemeVCover_iteratedModelBaseChange`：IsSchemeVCover x を、その第二射影へ渡す。

二つ目の束は pullback の貼り合わせと既存の IsSchemeVCover.baseChange の法則（見込み 80〜180 行）。AffineTensorModelPullback からの v 判定を、閉包絡へ渡す周辺空間の v 判定へ接続する。A07 の完成とは区別する。

一覧：済み 8／全体 13（うち追加 4）。

模型上の指定開の像と稠密性の法則：`range_contains_open_of_isIso_restrict` は IsIso(f∣U) から U⊆range f を得る。`denseRange_openRestriction_of_model_baseChange` は IsPullback v p p₀ g、U₀⊆range p₀、Dense(g⁻¹U₀) から DenseRange((p⁻¹(g⁻¹U₀)).ι≫p) を得る。Rydh Proposition 3.7 の、模型上で同型な開と元の基底上の稠密開を比較する法則（見込み 40〜100 行）。

模型の底変換と閉包絡の組立ての法則：`exists_fppf_proper_refinement_of_flat_model` は、IsSchemeVCover x:X→Spec R、実際の IsPullback a x f₀ g、固有・局所有限表示 p₀:Y₀→S₀、平坦・局所有限表示・準コンパクトな閉部分 i₀:Z₀→pullback(f₀,p₀)、指定開 U₀⊆range p₀、g⁻¹U₀ の準コンパクト性と稠密性、指定開上の閉部分の包含を入力にする。結論は同じ x の、有限表示の固有全射 r:T→Spec R と fppf 被覆 q:W→T による細分 a':W→X（a'≫x=q≫r）。模型の周辺空間・閉部分・基底を全て実際の pullback として構成し、直前の法則と C02 を合成する（Rydh Proposition 3.7、見込み 100〜250 行）。入力の模型の存在そのものを仮定した A07 の完成とはしない。次に GenericFlatNoetherianModel と Noether 平坦化からその模型を供給する。

A07 の被約・極小素点集合が準コンパクトな場合の出口：`exists_fppf_proper_refinement_vCover_affineReduced_compact_minimalPrimes` は、任意の被約環 R、有限表示 R-代数 B、IsCompact{q:Spec R | q∈minimalPrimes R} と Spec B→Spec R の v 判定から、有限表示の固有全射 r:T→Spec R、fppf q:W→T、b:W→Spec B、b≫(Spec B→Spec R)=q≫r を構成する。GenericFlatNoetherianModel の実際の係数模型と一般平坦開、FiniteTypeFlatteningNoetherian の中心・strictTransformι、AffineTensorModelPullback を前の組立てへ渡す。Rydh Proposition 3.7 のこの場合の適用（見込み 100〜300 行）。A07 の任意の R の主張は変えず、C01 の整拡大と有限表示段への移送は引き続き残る。

### 実際の Noether 模型と平坦な閉部分の底変換：検証結果

五モジュール計 **345 行**、入口 5 行。下書き一式の検証後、個々の本体と直接の importer AlgebraicGeometry の対象ビルド **4,867 ジョブ成功**。五モジュールの小監査は補助宣言込み **28 宣言・標準三公理のみ**、終了コード 0。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`scheme-drafts/2g-flat-model-batch-check-3.log`、`2g-flat-model-native.log`、`2g-flat-model-audit.log`。

| 登録モジュール | 行数 |
| --- | ---: |
| ClosedRestrictionBaseChange | 78 |
| IteratedModelBaseChange | 69 |
| DenseOpenModelBaseChange | 48 |
| FlatModelBaseChangeRefinement | 73 |
| CompactMinimalPrimeVCoverRefinement | 77 |

- `closedRestrictionBaseChangeMap`：閉部分を同じ底変換で運ぶ実際の pullback.lift。
- `closedRestrictionBaseChangeMap_fst`・`_assoc`：模型側への第一射影の可換式。
- `closedRestrictionBaseChangeMap_snd`・`_assoc`：元の基底への第二射影の可換式。
- `isPullback_closedRestrictionBaseChangeMap`：同じ底変換射と元の閉部分の射は Cartesian。
- `isClosedImmersion_closedRestrictionBaseChangeMap`：元の閉埋め込みの実際の底変換も閉埋め込み。
- `closedRestrictionBaseChangeMap_properties`：平坦・局所有限表示・準コンパクトな構造射の三性質を同じ底変換へ渡す。
- `closedRestrictionBaseChangeMap_contains_preimage`：指定開の逆像が閉部分の像に入る条件を同じ底変換へ渡す。
- `iteratedModelBaseChangeMap`：tensor 模型と固有模型の二つの pullback square から、元の空間へ戻す実際の射。
- `iteratedModelBaseChangeMap_fst`・`_assoc`：元の模型の第一射影との可換式。
- `iteratedModelBaseChangeMap_base`・`_assoc`：元の基底の構造射との可換式。
- `isPullback_iteratedModelBaseChangeMap`：同じ射と周辺空間の第二射影は元の射の底変換を与える。
- `isSchemeVCover_iteratedModelBaseChange`：元の v 判定を底変換した周辺空間へ渡す。
- `range_contains_open_of_isIso_restrict`：制限が同型な開の全点は元の射の像に入る。
- `denseRange_openRestriction_of_model_baseChange`：模型の指定開の像と元の基底上の稠密性から、同じ底変換の開の稠密像を得る。
- `exists_fppf_proper_refinement_of_flat_model`：実際の平坦な閉部分を持つ模型、tensor 比較、指定開の条件を C02 へ渡し、元の射の fppf–proper 細分を組み立てる。
- `exists_fppf_proper_refinement_vCover_affineReduced_compact_minimalPrimes`：被約 R と極小素点集合の準コンパクト性を仮定し、任意の有限表示 R-代数 B の v 判定から、有限表示の固有全射と fppf 被覆による実際の細分を構成する。

最後の出口は模型の存在を追加仮定にせず、GenericFlatNoetherianModel と Noether 基底上の有限型射の平坦化から実際に模型を選ぶ。元の射に平坦性・固有性を仮定しない。模型上の指定開が稠密であるとは仮定せず、元の基底への逆像の稠密性を使う。平坦な閉部分は Noether 模型上の狭義変換の底変換であり、非 Noether 基底上の生の狭義変換の平坦性を使わない。

G1 累計は本体 **4,183 行**、入口込み **4,264 行**。A07 の任意の基底の主張は未完：C01 の整拡大後のこの細分を有限・有限表示段へ降ろし、固有性・全射性・因子化を同じ段でそろえる接続が残る。G2 の一般の有限表示固有模型の構成と使う部品を共有して進める。

一覧：済み 8／全体 13（うち追加 4）。

## C03：有限型イデアルの有限段への降下（11-14 の標準存在補題の枠で追加）

A07 の C01 の整拡大後の閉包絡を有限表示段へ移すため、有限型イデアルの降下を C03 として追加する。11-14 夕の「標準の代数幾何の存在の補題は一つの見込み 4,000 行以下なら一覧へ追加して進む」の承認による。外枠 25,000 行は変えない。C03 は G1 のこの移送と G2 の模型の双方で使い、二重には作らない。

原典：[Stacks 32.10.3 (3), Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)。有限型準連接イデアルの降下で、イデアル層の pullback は実際の IdealSheafData.comap（閉部分スキームの底変換の定義）を使う。底変換の忠実平坦性は仮定しない。一般の有限表示対象の降下は [01ZM](https://stacks.math.columbia.edu/tag/01ZM)、固有性の有限段への降下は [081F](https://stacks.math.columbia.edu/tag/081F)、既定の固有近似の原典は [0A0P](https://stacks.math.columbia.edu/tag/0A0P)。B01 の一般の固有有限表示模型をブローアップだけに狭めない。

| 子項目 | 型・主張 | 見込み |
| --- | --- | ---: |
| C03.(i) | J が filtered、F:J→CommRingCat、c が実際の colimit cocone、I:Ideal c.pt が有限生成なら、ある j の有限生成 I_j が存在し、Ideal.map (c.ι.app j).hom I_j=I | 180〜500 行 |
| C03.(ii) | 同じ ring colimit の二段の有限生成イデアルが colimit で同じ像を持つなら、ある共通の後段で実際の像イデアルが一致する | 200〜600 行 |
| C03.(iii) | D:J→Scheme が cofiltered、各段 qcqs、遷移射 affine、c:Cone D が実際の IsLimit を持つとき、c.pt 上の有限型 K に対し ∃j,I_j, IsFiniteTypeIdealSheaf I_j ∧ I_j.comap(c.π.app j)=K | 850〜2,100 行 |

定義・入口・小監査等を含め C03 全体 **1,300〜3,400 行**の見込み。C02 の有限型性の局所判定とイデアル層の貼り合わせを共用し、準連接加群の圏全体を新しく作らない。(iii) は一般の qcqs な図式のまま、用途を射影模型へ限定しない。

最初の宣言 `exists_fg_ideal_model_of_isColimit` は (i) の型。既存の forget CommRingCat の filtered colimit の保存、Types.jointly_surjective_of_isColimit、IsFiltered.sup_objs_exists で有限生成元を同じ段へ持ち上げ、その span を取る。有限個の元を同じ段へ戻すことはこの構成の分割で、別の主項目には数えない。

一覧：済み 8／全体 14（うち追加 5）。

C03.(ii) の所属の有限段への移送の分割：`exists_ideal_map_rep_of_colimit_mem` は x∈Ideal.map(c.ι.app i) I に対し、ある f:i→j と y∈Ideal.map(F.map f) I で c.ι.app j y=x を得る。`exists_ideal_map_mem_of_colimit_mem` は x:F.obj i が colimit で同じ段の I の像に入るなら、ある f:i→j で F.map f x∈Ideal.map(F.map f) I を得る。ここは I の有限生成性を要しない。既存の span の帰納法と filtered colimit の等式の有限段での一致を使う、0B8W (3) のアフィンの所属の比較（見込み 120〜300 行）。

C03.(ii) の有限生成性を使う出口：`exists_finset_ideal_map_mem_of_colimit_mem` は同じ段の有限集合について、colimit でのイデアルへの所属を一つの後段へ同時に降ろす。`exists_ideal_map_le_of_colimit_map_le` は有限生成な左辺のイデアルの、colimit の像での包含を一つの後段の包含へ移す。`exists_ideal_map_eq_of_colimit_map_eq` は同じ段の二つの有限生成イデアルの像の等式をある後段へ移す。`exists_ideal_maps_eq_of_colimit_maps_eq` は異なる二段の有限生成イデアルから始め、二つの実際の遷移射を持つ共通段で一致させる（0B8W (3) のアフィンの等式、見込み 100〜250 行）。`ideal_map_map_functor`・`ideal_map_mem_functor_comp` はその合成の係数移送の法則。

### C03.(i)：環の colimit の有限生成イデアルの模型

FiniteIdealColimitModel **53 行**、入口 1 行を追加。`exists_fg_ideal_model_of_isColimit` は、任意の filtered な CommRingCat の図式の実際の colimit cocone に対して、有限生成イデアルを一つの段の有限生成イデアルの像として構成する。Noether 性・忠実平坦性・遷移射の単射性を仮定していない。

対象ビルドは直接の importer AlgebraicGeometry まで **4,868 ジョブ成功**、新モジュールの小監査 **1 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-c03-finite-ideal-colimit-check-2.log`、`2g-c03-colimit-model-native.log`、`2g-c03-colimit-model-audit.log`。

C03 内は **1／3 完了**（(i)）。(ii) の後段での等式と (iii) のスキーム上の有限型イデアル層の降下は未完。G1 の共用部品込み累計は本体 **4,236 行**、入口込み **4,318 行**。A07 の一般の基底と G2 は未完。

一覧：済み 8／全体 14（うち追加 5）。

C03.(iii) の実装の分割（全体の型・見込みは維持）：有限アフィン被覆の生成元を環の colimit から同じ段へ戻す。その段の K.map π の有限型部分イデアルに、C02 の `exists_finiteType_subideal_containing_affine_sections` で生成元を同時に含める。map/comap の随伴の単位・余単位とアフィン被覆上の包含の判定で、pullback が元の K に一致することを示す。この存在の構成には局所イデアルの重なりの等式の降下を重ねて作らない。C03.(ii) の等式の有限段への降下は、模型の比較の法則としてそのまま供給する。

分割の型 `exists_finiteType_ideal_model_of_affine_generators`：qcqs Y と affine f:X→Y、有限アフィン被覆 U_i、K:X.IdealSheafData に対し、K.map f の各 U_i の有限集合 s_i が pullback 上の K を生成すれば、Y 上の有限型 J で J.comap f=K が存在する。これは C02 の有限個の生成元の包含と随伴の合成であり、新しい親項目は足さない。

### C03.(ii)：環の colimit の所属・包含・等式を同じ後段へ移す

FiniteIdealColimitMembership **96 行**、FiniteIdealColimitEquality **99 行**、入口 2 行。上記の所属の二宣言・有限集合の所属・有限生成イデアルの包含・同じ段および異なる段の等式の六宣言と、係数移送の二法則を実装。忠実平坦性・遷移射の単射性・Noether 性を要求しない。

対象ビルドは直接の importer AlgebraicGeometry まで **4,870 ジョブ成功**。新二モジュールの小監査は補助宣言込み **11 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-c03-equality-batch-check-2.log`、`2g-c03-colimit-equality-native.log`、`2g-c03-colimit-equality-audit.log`。

C03 内は **2／3 完了**（(i)・(ii)）。(iii) のスキーム上の有限型イデアル層の降下は未完。G1 共用部品込み本体 **4,431 行**、入口込み **4,515 行**。A07 の一般の基底と G2 は未完。

一覧：済み 8／全体 14（うち追加 5）。

C03.(iii) の環からアフィン開への移送の分割：`exists_fg_ideal_family_model_of_isColimit` は同じ filtered な添字を持つ有限個の環の図式の有限生成イデアルを、一つの共通段へ移す。`exists_fg_ideal_family_model_of_affineOpen_limit` は、ある段 i の有限個のアフィン開 U_a に対し、極限の逆像の全体切断上の有限生成イデアル K_a を、ある j:Over i の各 D(j→i)⁻¹U_a の全体切断上の有限生成イデアル L_a の像として同時に表示する。実際の opensCone の IsLimit と Γ による colimit の保存を使う。これらは (iii) の証明の分割で、新しい親項目を足さない。

係数移送の法則 `ideal_model_resLE_top_comparison`：f:X→Y、U⊆Y、V⊆f⁻¹U と L⊆Γ(U,⊤)、K⊆Γ(X,V) に対し、制限射の appTop での L の像が K.map(topIso.inv) なら、L.map(topIso.hom) の f.appLE での像は K。これは制限射の appTop と topIso の合成の比較で、平坦性を使わない。

### C03.(iii) の局所模型と有限型部分イデアルへの接続

FiniteTypeIdealAffineGeneratorModel **61 行**、FiniteIdealColimitFamilyModel **37 行**、AffineOpenLimitIdealModel **41 行**、入口 3 行。`exists_finiteType_ideal_model_of_affine_ideal_models` は有限アフィン被覆上の有限生成な局所イデアルの像が K に一致する場合を、K.map f の有限型部分イデアルへ渡す。前述の有限族の模型と opensCone の三分割と合わせ **4 宣言**。

対象ビルドは直接の importer AlgebraicGeometry まで **4,873 ジョブ成功**、三モジュールの小監査は **4 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-c03-geometry-batch-check-2.log`、`2g-c03-local-model-native.log`、`2g-c03-local-model-audit.log`。

G1 共用部品込み本体 **4,570 行**、入口込み **4,657 行**。C03.(iii) の一般の降下の出口は下書き検証中で未完。

一覧：済み 8／全体 14（うち追加 5）。

C03 の閉部分スキームへの係数移送の法則 `exists_finitePresentation_closed_model_of_isLimit` の型：一般の C03.(iii) と同じ D・c・K に対し、ある段 j の有限型 L、LocallyOfFinitePresentation L.subschemeι、および実際の同型 K.subscheme≅pullback(c.π.app j)(L.subschemeι) が存在し、第一射影との合成は K.subschemeι。C03 のイデアル模型と既存の comapIso を合成する分割で、独立の存在項目は増やさない（見込み 30〜80 行）。これだけで周辺空間の模型、射の因子化、全射性の降下を完成扱いにはしない。

### C03 完了：一般の qcqs 極限上の有限型イデアル層の降下

IdealModelRestrictionComparison **41 行**、FiniteTypeIdealLimitModel **66 行**、入口 2 行。`ideal_model_resLE_top_comparison` と `ideal_model_appLE_of_eq_preimage` は制限射の全体切断と元の開の切断環の比較。`exists_finiteType_ideal_model_of_isLimit` は C03.(iii) の一般の型そのままの出口：D:J→Scheme が cofiltered、各段 qcqs、遷移射 affine、c が実際の IsLimit を持つなら、c.pt の有限型イデアル層 K は、ある段 j の有限型 L の comap(c.π.app j) として実際に一致する。Noether 性・射影性・遷移射の単射性・忠実平坦性を仮定しない。

有限アフィン被覆のイデアルの局所模型を一つの段へそろえ、C02 で (K.map π) の有限型部分イデアルに全ての生成元を含める。随伴とアフィン被覆上の包含で元の K との一致を得た。準連接加群の圏全体を追加せず、原典 0B8W (3) のこの存在の型を保っている。

対象ビルドは直接の importer AlgebraicGeometry まで **4,875 ジョブ成功**、今回の二モジュールの小監査 **4 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-c03-limit-batch-check-2.log`、`2g-c03-scheme-limit-native.log`、`2g-c03-scheme-limit-audit.log`。

C03 は **3／3 完了**。C03 本体は **494 行**、入口 8 行、計 **502 行**（当初見込み1,300〜3,400行内）。C02 の部分イデアルの延長を共用して縮めた。C03 各束の小監査は計 **20 宣言・標準三公理のみ**。G1 共用部品込み本体 **4,677 行**、入口込み **4,766 行**。2g-1 の12,000行の途中報告点・25,000行の外枠には未到達。A07 の一般の基底と G2 は未完で、細分の周辺模型・因子化・全射性を同じ段へ移す接続を続ける。一般の Rydh 3.10 の完成とは呼ばない。

一覧：済み 9／全体 14（うち追加 5）。

A07 の周辺模型への接続の次の型つきの法則（見込み 100〜260 行）：`stageBaseChangeDiagram D i p : Over i→Scheme` は p:Y→D(i) を各段へ実際に底変換する図式。`stageBaseChangeCone` の頂点は pullback(c.π.app i)p。`isLimit_stageBaseChangeCone` は cofiltered な元の実際の IsLimit から底変換後の実際の IsLimit を得る。`isPullback_stageBaseChangeDiagram_map` は遷移射と第一射影の Cartesian 性。遷移射の affine 性、各段の準コンパクト性・準分離性を元の図式と p の準コンパクト性・準分離性から渡す。Over.pullback の連結極限の保存と底変換の法則であり、新しい親の存在項目は足さない。C03 をこの周辺図式に適用し、整拡大後の閉包絡を有限段に降ろす用途。

C03 の閉部分スキームへの比較を検証：FinitePresentationClosedLimitModel **33 行**、入口 1 行。上記 `exists_finitePresentation_closed_model_of_isLimit` が実際の底変換同型と第一射影の可換式まで返す。対象ビルドは直接の importer AlgebraicGeometry まで **4,876 ジョブ成功**、小監査 **1 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-c03-closed-model-check.log`、`2g-c03-closed-model-native.log`、`2g-c03-closed-model-audit.log`。

この追加の比較を含め C03 関連は本体527行＋入口9行、G1 共用部品込み本体 **4,710 行**、入口込み **4,800 行**。A07・G2 は未完のまま。

一覧：済み 9／全体 14（うち追加 5）。

A07 の実際の周辺模型と C03 の合成の法則 `exists_proper_closed_baseChange_model_of_isLimit` の型（見込み 50〜140 行）：同じ qcqs・affine 遷移の極限と固定段 i、固有・局所有限表示 p:Y→D(i)、pullback(c.π.app i)p 上の有限型 K に対し、ある j:Over i の実際の底変換空間上の有限型 L が存在する。L の閉包含から D(j.left) への構造射は固有・局所有限表示で、K.subscheme は L の閉部分スキームの実際の底変換と同型になる。閉部分の型と同じ射の固有性・有限表示性をそろえる、C03 と底変換の法則の合成。全射性の降下や元の X への因子化はこの出口に含めず、後続の接続で処理する。

## A07 の有限段での全射性の比較：次の型（着手前）

次の二つは、既存の全射性の判定と模型の底変換の法則の接続として進める。独立の親項目は増やさない。原典は [Stacks 32.8.15, Tag 081C](https://stacks.math.columbia.edu/tag/081C)、構成可能な像は Mathlib の `Scheme.Hom.isConstructible_image`（054J）。見込みは合わせて120〜400行。

- `exists_surjective_proper_pullback_of_isLimit`：qcqs・affine 遷移の実際の cofiltered 極限 D,c,hc、ある段 i への固有・局所有限表示 p:Y→D(i) に対し、pullback.snd p(c.π.app i) が全射なら、ある j→i で pullback.snd p(D.map(j→i)) が全射。既存の `exists_surjective_pullback_snd_of_isLimit` の Noether 段という仮定を変えず、新しい宣言で、像の補開が構成可能ゆえ準コンパクトであることを使う。忠実平坦な遷移射を仮定しない。
- `exists_surjective_flat_pullback_of_isLimit`：同じ極限と、ある段 i への平坦・局所有限表示・準コンパクト p:Y→D(i) に対し、極限への底変換が全射なら、ある j→i への同じ底変換が全射。平坦・局所有限表示の射の像が開であることと `exists_map_eq_top` を使う。これは fppf 側の全射性の有限段への移送。

この二つで固有側と平坦側の全射性を降ろした後、共通の後段へ運ぶことと、元の有限表示アフィン X への射の因子化・可換式をそろえる。因子化には既存の `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` を使い、同じ有限表示の射の降下を作り直さない。

一覧：済み 9／全体 14（うち追加 5）。

全射性の比較の位相の分割 `isCompact_of_isConstructible_scheme`：qcqs X の構成可能集合 s は準コンパクト。既存の構成可能位相のコンパクト性（0901）から、構成可能位相での閉集合の連続像として比較する法則。`exists_surjective_proper_pullback_of_isLimit` では Mathlib の Chevalley（054J）の構成可能な像の補集合にこの法則を使い、既存の `exists_preimage_eq_bot_of_isLimit` へ渡す。見込みは直前の二つの全射性の比較120〜400行の中。

### A07：周辺模型の底変換図式と有限表示の閉部分の模型

StageBaseChangeLimit **83 行**、ProperClosedBaseChangeLimitModel **46 行**、入口 2 行。前述の `stageBaseChangeDiagram`・`stageBaseChangeCone`・`isLimit_stageBaseChangeCone`・`isPullback_stageBaseChangeDiagram_map` と、遷移射の affine 性・各段の準コンパクト性・準分離性を検証。`exists_proper_closed_baseChange_model_of_isLimit` は、元の極限への底変換上の有限型閉部分を、ある段で固有・局所有限表示の構造射を持つ実際の閉部分の模型へ移す。一般の qcqs な図式と固有・局所有限表示の周辺射の型を保ち、遷移射の忠実平坦性は仮定しない。

対象ビルドは直接の importer AlgebraicGeometry まで **4,878 ジョブ成功**、二モジュールの小監査は補助宣言込み **11 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-stage-basechange-batch-check-3.log`、`2g-stage-basechange-native.log`、`2g-stage-basechange-audit.log`。

G1 共用部品込み本体 **4,839 行**、入口込み **4,931 行**。一般の A07 の模型の全射性・因子化を同じ段へそろえる接続、G2 の一般の模型は未完。

一覧：済み 9／全体 14（うち追加 5）。

A07 のこの後の組立て（既定の A07 の証明分割、型は保つ）：(1) 極小素点集合が準コンパクトな被約基底の細分の既存構成から、固有な Noether 周辺模型とその底変換上の有限型閉イデアルの証人を保持する。既存の出口の名前・型は変えず、元の構成が選んだ証人を返す補助出口を足す（見込み150〜450行）。(2) Noether 係数環 A は有限生成 ℤ-代数なので、A→B∞ を整射の有限・有限表示段へ因子化する。既存の RingHom の有限表示の colimit の因子化を使い、ℤ を大きい Scheme の宇宙へ直接置く代わりに、必要なら ULift ℤ の初期環と ringEquiv を使う（係数移送・因子化の法則、見込み60〜180行）。(3) 固定した段の固有周辺模型と C03 から閉イデアルを降ろし、同じ段で固有・局所有限表示の閉部分の模型を取る。(4) 平坦側は Noether 模型上の平坦な射の実際の底変換として保ち、二つの全射性の比較を共通の後段へそろえる。(5) 元の有限表示 X への射と可換式を既存の因子化・一致判定で有限段へ降ろし、各有限・有限表示段の基底への固有全射と合成する。

ここで得る A07 の特殊な模型の供給を、B01 の一般の有限表示の固有射の模型の代わりにしない。B01〜B04 は別に残り、C03 と有限段の比較を共用する。

C02 の既存構成から有限型性の証人を保持する法則 `exists_finiteType_closedEnvelope` の型（見込み30〜70行）：qcqs X、K、指定開 V、support K⊆V に対し、J≤K、IsFiniteTypeIdealSheaf J、support J⊆V を同時に返す。既存の閉包絡の証明で選んだ同じ有限型部分イデアルの証人を返し、旧宣言の型・名前は変えない。C03 の入力となる有限型性を保持する、前記の証人を返す分割の一部。

### A07：固有側・平坦側の全射性を有限段へ降ろす比較

ConstructibleCompactness **43 行**、ProperFinitePresentationSurjectivityLimit **44 行**、FlatSurjectivityLimit **41 行**、入口 3 行。`isCompact_of_isConstructible_scheme` は構成可能位相の閉集合の連続像で元の位相の準コンパクト性を比較する。`exists_surjective_proper_pullback_of_isLimit` は既存の Noether 版の型を変更せず、新しい宣言として qcqs な段の固有・局所有限表示の射の全射性を有限段へ降ろす。`exists_surjective_flat_pullback_of_isLimit` は平坦・局所有限表示・準コンパクトな射の開像から同じ結論を得る。どちらも、遷移射の全射性・忠実平坦性を要求しない。

対象ビルドは直接の importer AlgebraicGeometry まで **4,881 ジョブ成功**、三モジュールの小監査は補助宣言込み **4 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-surjectivity-limit-batch-check-2.log`、`2g-surjectivity-limit-native.log`、`2g-surjectivity-limit-audit.log`。

G1 共用部品込み本体 **4,967 行**、入口込み **5,062 行**。未検証の `FiniteTypeClosedEnvelopeWitness` は作業木の scheme-drafts に置き、コミットには含めない。次は、細分の構成で選んだ Noether 周辺模型と有限型閉イデアルの証人を保持し、整射の有限表示段の図式・今回の二つの全射性の比較・元の X への因子化を同じ段へそろえる。A07 の一般の基底と G2 は未完。

一覧：済み 9／全体 14（うち追加 5）。

A07 の証人の保持の法則 `exists_closedEnvelope_refinement_witness_of_flat_closedRestriction` の型：既存の `exists_fppf_closedEnvelope_refinement_of_flat_closedRestriction` と同じ p,f,hf,i,U の仮定から、Y 上の有限型 J と、J.subschemeι≫p の全射性、pullback.snd(i≫f)(J.subschemeι) の全射性を返す。同じ閉包絡と二つの全射性の証明を使い、固有・平坦・局所有限表示の性質は既存の合成・底変換から渡す。見込み60〜120行、前記の証人を返す補助出口150〜450行の中。旧宣言の型・名前は変えない。

A07 の模型の証人を返す法則 `exists_flat_model_closed_refinement_witness` の型：既存の `exists_fppf_proper_refinement_of_flat_model` と同じ実際の tensor pullback hX と p₀,i₀,U₀ の仮定から、pullback(p₀,g) 上の有限型 J、J.subschemeι≫pullback.snd p₀g の全射性、Noether 側の平坦射 i₀≫pullback.snd f₀p₀ の底変換を J.subschemeι でさらに引いた射の全射性、元の X への実際の射 b と b≫x=q≫J.subschemeι≫pullback.snd p₀g を返す。同じ底変換と閉包絡の構成の証人を保持する分割（見込み90〜160行、証人を返す束150〜450行の中）。元の出口の型・名前は変えない。

係数の因子化の法則の実装名は `exists_ringHom_factor_of_finiteType_int`。filtered な F:J→CommRingCat.{u}、実際の cocone c と IsColimit、有限型 ℤ-代数 A:Type u、g:A→c.pt に対し、∃j,g₀:A→F(j), g=(c.ι.app j).hom.comp g₀ を返す。前記60〜180行の分割の型そのままで、ULift ℤ と環同型の有限型性・Noether 性の移送を使う。

証人を保持した compact minimal primes の出口 `exists_noether_flat_closed_refinement_model_compact_minimalPrimes`：被約 R、極小素点集合準コンパクト、有限表示 R-代数 B の affine v 判定から、有限型 ℤ-係数環 A（Noether）、有限表示 A-代数 C、固有・局所有限表示 p₀:Y₀→Spec A、Noether 平坦化の閉部分 i₀:Z₀→Spec C×Spec A Y₀（g₀=i₀≫snd は平坦・局所有限表示・準コンパクト）、pullback(p₀,Spec R→Spec A) 上の有限型 J を実際に選ぶ。J の構造射 r と、g₀ を底変換して J で引いた q は全射で、元の Spec B への b と b≫(Spec B→Spec R)=q≫r を返す。元の compact minimal primes の細分の構成で選んだ証人を保持する分割（見込み100〜180行、証人の束150〜450行の中）。元の出口の名前・型は保つ。

A07 の因子化した係数写像を持つ底変換図式の法則（見込み140〜300行）：i∈J、γ:D(i)→S、p:Y→S に対し、`compositeStageBaseChangeDiagram` は j:Over i を pullback(D.map j.hom≫γ)p に送る。`compositeStageBaseChangeCone` の頂点は pullback(c.π.app i≫γ)p で、元の IsLimit からこの cone の IsLimit を得る。さらに g:c.pt→S と h:c.π.app i≫γ=g があれば、`compositeStageBaseChangePointIso` で元の構成の pullback p g をその頂点と同型にし、同じ頂点 pullback p g を持つ実際の極限 cone に移す。閉イデアルの型を別の空間へ置き換えず C03 を適用するため、cone を同型で移す。遷移射の Cartesian 性・affine 性と qcqs 性は前の StageBaseChangeLimit と同じ底変換・極限の法則で渡す。親 ID は増やさない。

合成係数の cone の法則には、`compositeStageBaseChangeConeWithPoint_π_fst`・`_π_snd`（元の基底への射影と周辺模型への射影の可換式）、`isPullback_compositeStageBaseChangeConeWithPoint_π`（各射影が元の図式の射影の実際の底変換）を含める。これにより、C03 の閉部分の pullback 比較と貼り合わせて、閉部分の構造射も元の基底の同じ射影の底変換と示す。

C03 と合成係数の底変換の接続 `exists_proper_closed_compositeStage_model` の型（見込み70〜160行）：同じ D,c,hc、γ:D(i)→S、固有・局所有限表示 p:Y→S、g:c.pt→S、c.π.app i≫γ=g、pullback p g 上の有限型 K から、ある j:Over i の閉部分 L、固有・局所有限表示 r_j=L.subschemeι≫fst、元の閉部分からの a:K.subscheme→L.subscheme を取り出す。a と K.subschemeι≫snd、r_j と c.π.app j.left の正方形は Cartesian、a と周辺模型 Y への射は可換。C03 と二つの底変換正方形の貼り合わせの法則で、新しい親の存在項目は足さない。これで固有側の全射性の有限段への移送に、同じ r_j の模型を渡す。

係数の因子化の I04 へのアダプター（前記60〜180行の中）：`exists_integral_model_stage_factor_of_finiteType_int` は整な R→B、有限型 ℤ-代数 A、g:A→B を入力し、I01〜I04 の実際の IntegralModelIndex R B のある i と g₀:A→(integralModelSmallDiagram R B)(i)、g=(integralModelSmallCocone R B).ι(i)∘g₀ を返す。`exists_integral_model_spec_factor_of_finiteType_int` はその同じ因子化を、実際の Spec の極限 cone の射影と γ:D(i)→Spec A の合成が Spec.map g と一致する形で返す。新しい模型の存在を入力に加えず、I03 の実際の IsColimit と反変 Spec の合成の法則を使う。

### A07：Noether 平坦模型・閉包絡の証人の保持と係数の因子化

下書きの一式の検証後、個別の五モジュールと直接の importer AlgebraicGeometry の対象ビルド **4,886 ジョブ成功**、小監査 **5 宣言・標準三公理のみ**。

| 登録モジュール | 行数 | 宣言と主張 |
| --- | ---: | --- |
| FiniteTypeClosedEnvelopeWitness | 37 | `exists_finiteType_closedEnvelope`：C02 の同じ閉包絡の有限型イデアルの証人を保持する |
| ClosedEnvelopeRefinementWitness | 70 | `exists_closedEnvelope_refinement_witness_of_flat_closedRestriction`：有限型閉包絡と固有側・平坦側の全射性を保持する |
| FlatModelClosedRefinementWitness | 87 | `exists_flat_model_closed_refinement_witness`：実際の底変換上の有限型 J と、二つの全射性、元の X への b と可換式を返す |
| CompactMinimalPrimeClosedRefinementModel | 99 | `exists_noether_flat_closed_refinement_model_compact_minimalPrimes`：被約・極小素点集合準コンパクトな場合に、有限型 ℤ-係数環・Noether 平坦模型・底変換上の有限型 J・二つの全射性・元の射への因子化を実際に選ぶ |
| FiniteTypeIntRingColimitFactor | 50 | `exists_ringHom_factor_of_finiteType_int`：有限型 ℤ-係数環から実際の環の filtered colimit への射を一段へ因子化する |

本体 **343 行**、入口 5 行。証人を保持する四モジュールは293行（150〜450行の見込み内）、係数の因子化は50行（60〜180行の見込み内）。旧宣言の型・名前は変更していない。係数のファイルの個別ビルドで ℤ の Noether 性の明示 import 不足を検出し、`Mathlib.RingTheory.Int.Basic` を加えて個別ビルドを通した。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-closed-model-witness-batch-check-2.log`、`2g-closed-model-witness-native-2.log`、`2g-closed-model-witness-audit.log`。合成係数の底変換図式の下書きはこの監査に含めない。

G1 共用部品込み本体 **5,310 行**、入口込み **5,410 行**。A07 の一般の基底への移送は未完：I04 の実際の図式へ係数因子化を渡し、C03 の固有閉部分模型の Cartesian 性、平坦側の模型、二つの全射性、元の X への因子化を同じ有限段でそろえる。G2 の一般の有限表示の固有模型を、この特殊な模型の証人で完成扱いにはしない。

一覧：済み 9／全体 14（うち追加 5）。

I04 の実際の整射の図式に渡す法則 `exists_proper_closed_integral_model` の型（見込み90〜220行）：整な R→B、有限型 ℤ-係数環 A、g:A→B、固有・局所有限表示 p:Y→Spec A、pullback(p,Spec.map g) 上の有限型 K から、ある実際の IntegralModelIndex R B の段 i、スキーム T、固有・局所有限表示 r:T→D(i)、a:K.subscheme→T、β:T→Y を得る。a と元の閉部分の構造射、r と I04 の実際の射影の正方形は Cartesian、a≫β=K.subschemeι≫fst を満たす。I03 の colimit の係数因子化、C03、合成係数の底変換の正方形の合成で、新しい親項目を足さない。ここでは模型の r の全射性はまだ結論にせず、検証済みの全射性の有限段への移送を後続で適用する。

有限段の全射性の比較を実際の模型の射に渡す法則（見込み90〜180行）：`exists_surjective_proper_stage_model` と `exists_surjective_flat_stage_model` は、qcqs・affine 遷移の実際の極限 D,c,hc、全射 x:X→c.pt、ある段 i の模型 r:T→D(i)、a:X→T、IsPullback a x r(c.π.app i) を入力する。固有・局所有限表示の場合、または平坦・局所有限表示・準コンパクトの場合に、それぞれある j→i の実際の底変換 r_j を全射にし、a_j:X→pullback(r,D.map(j→i)) と同じ基底の射影に関する IsPullback、および a_j≫fst=a を同時に返す。新しい模型を仮定せず、既存の全射性の有限段への比較と pullback.lift、正方形の貼り合わせを合成する法則。周辺模型への写像は fst との合成でそのまま保持する。親 ID は増やさない。

I04 上の全射な固有閉部分模型への接続 `exists_surjective_proper_closed_integral_model`（前記の整射への接続90〜220行の中）：`exists_proper_closed_integral_model` の仮定に元の K.subscheme→Spec B の全射性を加え、同じ実際の IntegralModelIndex のある段 i に、固有・局所有限表示・全射 r:T→D(i)、元の閉部分からの Cartesian な a、周辺模型への β と a≫β の可換式を得る。有限段の全射性の模型比較の法則を適用し、後段への実際の pullback の第一射影との合成で β を運ぶ。元の構造射・係数写像への忠実平坦性を追加せず、同じ模型の法則として進める。

### A07：I04 の実際の有限・有限表示段への固有閉部分模型

| 登録モジュール | 行数 | 宣言と主張 |
| --- | ---: | --- |
| CompositeStageBaseChangeLimit | 149 | `compositeStageBaseChangeDiagram`・`compositeStageBaseChangeCone`：因子化した係数写像による実際の底変換図式と cone |
| 同上 | 同上に含む | `isLimit_compositeStageBaseChangeCone`：同じ cone の実際の極限性 |
| 同上 | 同上に含む | `compositeStageBaseChangePointIso`・`compositeStageBaseChangeConeWithPoint`・`isLimit_compositeStageBaseChangeConeWithPoint`：選んだ閉イデアルの元の空間を頂点として保つ同型と極限性 |
| 同上 | 同上に含む | `isPullback_compositeStageBaseChangeDiagram_map` と三つの型クラス入口：遷移射の Cartesian 性・affine 性、各段の qcqs 性 |
| 同上 | 同上に含む | `compositeStageBaseChangeConeWithPoint_π_fst`・`_π_snd`・`isPullback_compositeStageBaseChangeConeWithPoint_π`：元の基底・周辺模型への射影の可換式と、同じ基底の射影の底変換であること |
| ProperClosedCompositeStageModel | 63 | `exists_proper_closed_compositeStage_model`：C03 と上の正方形を貼り、元の構造射と Cartesian な固有・局所有限表示の閉部分模型と、周辺への可換式を得る |
| IntegralModelCoefficientFactor | 44 | `exists_integral_model_stage_factor_of_finiteType_int`：係数写像を I03 の実際の有限・有限表示段に因子化する |
| 同上 | 同上に含む | `exists_integral_model_spec_factor_of_finiteType_int`：同じ因子化を I04 の実際の Spec の射影の可換式へ移す |
| IntegralProperClosedModel | 47 | `exists_proper_closed_integral_model`：I04 の実際の段の固有・局所有限表示模型 r と、元の閉部分からの Cartesian な a、周辺模型への β と可換式を実際に選ぶ |

本体 **303 行**、入口 4 行。対象ビルドは直接の importer AlgebraicGeometry まで **4,890 ジョブ成功**、四モジュールの小監査は補助宣言込み **34 宣言・標準三公理のみ**。一般の固有・局所有限表示の周辺射を保ち、整射の単射性・忠実平坦性を仮定しない。模型の実際の底変換の型を cone の同型移送で保ち、有限型閉イデアルの型を別の空間に置き換えていない。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-composite-closed-model-batch-check-2.log`、`2g-integral-closed-model-native.log`、`2g-integral-closed-model-audit.log`。

G1 共用部品込み本体 **5,613 行**、入口込み **5,717 行**。I04 上の全射な固有模型への接続、平坦側の模型、元の X への因子化を同じ段にそろえる接続は未完。A07・G2 は未完のまま。

一覧：済み 9／全体 14（うち追加 5）。

A07 の残りの有限段の選択順を明確にする：まず固有側を全射にした段 i と T_i,r_i,a,β_i を取る。次に Over i 上で T_j=pullback(D(j→i),r_i)、β_j=snd≫β_i、W_j=pullback(g₀,β_j) を実際に作る。g₀ は元の Noether 平坦模型の閉部分の射で、f₀:Spec C→Spec A が affine、i₀ が閉埋め込みなので g₀ も affine。したがって W_j→T_j は affine・平坦・局所有限表示で、両図式は qcqs な affine 遷移を持つ。元の T_B と W_B の頂点を同型で保った極限 cone を使い、平坦側の全射性をある後段へ降ろす（図式・Cartesian 性・極限性の法則、見込み180〜450行）。

その全射な段より後の図式に制限してから、元の X_R への W_B の射を `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` で降ろす（基底 Spec R 上の有限表示な射の因子化の法則、見込み80〜220行）。この既存 API は、段への因子化と **基底上の可換式そのもの**を同時に返すので、b≫f=q≫r のために別の一致判定を重ねる必要はない。さらに後の段で全射性は底変換により保たれ、各 I04 段→Spec R は元の整全射から全射である。有限・局所有限表示なその射と固有側を合成する（合成の法則、見込み60〜160行）。

一般の A07 の始域を affine に限定しない。有限アフィン開被覆を有限積の Spec にまとめる際は Mathlib の `sigmaSpec`（有限族では同型）を使い、付値環の閉点の像を含むチャートへの因子化は `preimage_eq_top_of_closedPoint_mem` と `IsOpenImmersion.lift` を使う。元の有限表示 v 被覆への射を保持し、最後にその射へ合成する。これは有限アフィン被覆の細分の法則として進め、G0 の有限族・一射の橋の型を変えない。

### A07：I04 のある段で全射な固有閉部分模型を取る

PullbackStageSurjectivity **77 行**、IntegralSurjectiveProperClosedModel **57 行**、入口 2 行。

- `exists_surjective_proper_stage_model`：固有・局所有限表示の模型の全射性が降りる段で、元の空間からの実際の射と Cartesian 性、前段の模型への第一射影の可換式を保持する。
- `exists_surjective_flat_stage_model`：平坦・局所有限表示・準コンパクトの模型について、同じ実際の射・Cartesian 性・前段への可換式を保持する。
- `exists_surjective_proper_closed_integral_model`：I04 の実際のある有限・有限表示段に、固有・局所有限表示・全射 r:T→D(i)、元の閉部分からの Cartesian な a、周辺模型への β と可換式を実際に選ぶ。元の K.subscheme→Spec B の全射性は、保持した閉包絡の証人から供給する。

対象ビルドは直接の importer AlgebraicGeometry まで **4,892 ジョブ成功**、二モジュールの小監査は private な証明分割を含め **5 宣言・標準三公理のみ**。原典の有限段への全射性の比較を、実際の模型と可換式へつなぐ法則として実装し、遷移射の忠実平坦性は要求しない。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-pullback-stage-surjectivity-check.log`、`2g-integral-surjective-model-batch-check.log`、`2g-surjective-integral-model-native.log`、`2g-surjective-integral-model-audit.log`。

G1 共用部品込み本体 **5,747 行**、入口込み **5,853 行**。今回の継続では11モジュール780行＋入口11行を検証した。約12,000行の途中報告点・25,000行の外枠には未到達。平坦側の模型の図式と全射性の接続、元の X への基底上の因子化、C01 の整拡大・一般の始域との組立てが残る。A07・G2 は未完で、Rydh 3.10 の一般の場合や 2g-1 の完成とは報告しない。

一覧：済み 9／全体 14（うち追加 5）。

## A07：平坦側の模型の極限図式の分割（着手前の型）

既定の図式の法則180〜450行の中で、まず `stageModelOverPointIso`・`stageModelOverCone`・`isLimit_stageModelOverCone` を作る。D,c,hc、段 i、r:T→D(i)、a:X→T、x:X→c.pt、IsPullback a x r(c.π.app i) に対し、Over.post D⋙Over.pullback r の実際の極限 cone を Over T の中で取り、頂点を元の a:X→T に保つ。`stageModelCone` はその忘却で、元の X を頂点に持つ。二つの射影との可換式と、各射影が c.π.app j の底変換であることも同時に供給する。同じ pullback の比較同型と既存の極限の法則で、親 ID は増やさない。後で Over.map β と Over.pullback g₀ を合成し、元の平坦被覆の空間を頂点に保つ。

同じ図式の次の分割 `flatStageModelDiagram`・`flatStageModelCone`・`isLimit_flatStageModelCone` は、Over.post D⋙Over.pullback r⋙Over.map β⋙Over.pullback q の忘却で平坦側の図式を作る。q:Z→Y、β:T→Y と、元の X→T の Cartesian な模型比較を入力する。`flatStageModelPointIso`・`flatStageModelConeWithPoint`・`isLimit_flatStageModelConeWithPoint` は、元の写像 b:X→Y と a≫β=b があれば、頂点を元の pullback q b に保つ。`flatStageModelProjection` は各段 W_j→T_j、各遷移・極限 cone の射影はこの射に関して Cartesian。affine 遷移と qcqs 性も渡す。前記180〜450行の図式の法則の中で、新しい親項目は足さない。

平坦側の図式の性質の法則：各 `flatStageModelProjection ... .app j` に q の平坦性・局所有限表示性・準コンパクト性・準分離性・affine 性を底変換で渡す。図式の遷移射は、元の D の遷移射が affine なら affine。各段の qcqs 性は D の各段の qcqs 性、r と q の準コンパクト性・準分離性から渡す。これらは前記の図式の法則180〜450行の中の性質の移送で、新しい親 ID は足さない。

平坦側の全射性を図式の実際の成分へ渡す法則 `exists_surjective_component_of_cartesian_flat_model`（見込み40〜100行、前記の平坦模型の図式の束の中）：cofiltered な qc・affine 遷移の実際の極限 D,c,hc、図式 W、自然変換 q:W→D、全ての遷移の q の正方形が Cartesian、各 q_i が平坦・局所有限表示・準コンパクトとする。全射 x:X→c.pt と、各段に関して IsPullback(w_i,x,q_i,c.π.app i) があれば、ある段 j で実際の q_j が全射となる。既存の固定した射の全射性の有限段への移送を、同じ Cartesian な図式の成分と比較する法則。`surjective_component_of_cartesian_model_map` はその段より後の成分の全射性の底変換の法則。新しい親項目は足さない。

次の適用の型：`exists_surjective_flat_stage_of_model` は上の実際の W_j→T_j の図式と元の pullback q b の全射性から、ある j:Over i で実際の射 `flatStageModelProjection ... .app j` が全射と返す。前記の成分の比較への適用で、親項目を増やさない。

基底上の因子化の法則80〜220行の分割：`stageModelBaseMap` と `flatStageModelBaseMap` は D→const S を T_j・W_j の基底への射に運ぶ。`flatStageModelConeWithPoint_π_base` は元の基底への構造射との可換式。`exists_surjective_flat_stage_factor` は、S 上局所有限表示 f:V→S と、元の pullback q b から V への基底上の射 l∞ に対し、ある全射な平坦側の段 j の射 l:W_j→V を取り、実際の射影との合成が l∞ に一致し、l≫f がその段の構造射に一致することを同時に返す。全射となった段の後の図式へ制限してから、既存の `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` を使う。新しいモデルの存在の入力や一致判定の公理を追加しない。

### A07：平坦側の実際の図式と元の被覆を頂点に保つ極限

| 登録モジュール | 行数 | 宣言・主張 |
| --- | ---: | --- |
| StageModelOverLimit | 98 | `stageModelOverPointIso`・`stageModelOverCone`・`isLimit_stageModelOverCone`：元の a:X→T を Over T の頂点に保つ比較同型・cone・実際の極限性 |
| 同上 | 同上に含む | `stageModelOverCone_pt_hom`：Over の cone の構造射は元の a そのもの |
| 同上 | 同上に含む | `stageModelCone`・`isLimit_stageModelCone`：忘却後も元の X を頂点に保つ実際の極限 cone |
| 同上 | 同上に含む | `stageModelCone_π_snd`・`_π_fst`・`isPullback_stageModelCone_π`：模型 T と元の基底への可換式、各射影の Cartesian 性 |
| FlatStageModelLimit | 139 | `flatStageModelDiagram`・`flatStageModelCone`・`isLimit_flatStageModelCone`：固定した射 q の係数移送・底変換による実際の W_j の図式と極限性 |
| 同上 | 同上に含む | `flatStageModelPointIso`・`flatStageModelConeWithPoint`・`isLimit_flatStageModelConeWithPoint`：元の pullback q b を頂点に保つ同型・cone・極限性 |
| 同上 | 同上に含む | `flatStageModelProjection`：各段の実際の射 W_j→T_j |
| 同上 | 同上に含む | `isPullback_flatStageModelDiagram_map`・`flatStageModelConeWithPoint_π_fst`・`_π_snd`・`isPullback_flatStageModelConeWithPoint_π`：遷移と極限射影の Cartesian 性・二つの射影の可換式 |
| FlatStageModelProperties | 80 | 八つの instance：各段の q_j に q の平坦性・局所有限表示性・準コンパクト性・準分離性・affine 性を渡す。図式の affine 遷移と各段の qcqs 性を渡す |
| CartesianFlatModelSurjectivity | 45 | `surjective_component_of_cartesian_model_map`：全射な成分の後段も全射 |
| 同上 | 同上に含む | `exists_surjective_component_of_cartesian_flat_model`：極限で全射な Cartesian な平坦模型の、ある実際の成分を全射にする |

本体 **362 行**、入口 4 行。対象ビルドは直接の importer AlgebraicGeometry まで **4,896 ジョブ成功**、四モジュールの小監査は補助宣言込み **64 宣言・標準三公理のみ**。実際の図式・cone の IsLimit を構成し、模型の存在や忠実平坦性を追加仮定にしていない。q には固有性を仮定しない。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-flat-stage-model-batch-check-2.log`、`2g-flat-stage-model-native.log`、`2g-flat-stage-model-audit.log`。

G1 共用部品込み本体 **6,109 行**、入口込み **6,219 行**。全射な平坦側の実際の段への適用と、元の X への基底上の因子化は下書き検証中で、この監査には含めない。A07・G2 は未完。

一覧：済み 9／全体 14（うち追加 5）。

I04 の基底への写像の自然性の法則（既定の基底への合成60〜160行の分割）：`integralModelSpecBaseMap_naturality` は任意の遷移 f:j→k に対し D.map f≫baseMap k=baseMap j を示す。`integralModelSpecBaseNatTrans` は同じ構造射の D→const(Spec R) の自然変換、`integralModelSpecCone_base` は各 cone の射影との合成が元の Spec B→Spec R に一致する法則。模型の射が R-代数準同型であることと I04 の既存の射影の可換式を使い、因子化 API に同じ基底を渡す。親 ID は増やさない。

同じ有限段での細分の合成 `exists_fppf_proper_refinement_of_integral_closed_flat_model` の型（既定の基底への合成60〜160行の分割）：整な R→B で Spec B→Spec R が全射、有限型 ℤ-係数環 A、g:A→B、固有・局所有限表示 p:Y→Spec A、平坦・局所有限表示・準コンパクト・準分離 q:Z→Y、pullback(p,Spec g) 上の有限型 K を入力する。元の閉部分の構造射と q をその閉部分で引いた射が全射、元の V→Spec R（局所有限表示）への基底上の射があるとき、有限段の固有全射と fppf 射による V→Spec R の細分を返す。前の実際の模型・全射性・因子化の法則を合成し、I04 の有限・局所有限表示な基底への全射と固有側を合成する。ここで模型を追加仮定にした A07 の完成とはせず、入力は保持した Noether 平坦模型の証人から後続で実際に供給する。親 ID は増やさない。

C01 の被約化との合成の法則 `exists_integral_surjective_reduced_compact_minimalPrimes` の型（見込み60〜180行）：任意の可換環 R に対し、被約な B と g:R→B を実際に取り、g が整、Spec B→Spec R が全射、B の極小素点集合が準コンパクトであることを同時に返す。R_red へ C01 の既存の単射整拡大を適用し、nilradical による商と合成する。g の単射性は主張せず、I01〜I04 は非単射の整射にも適用できる。既存の被約化・C01 の構成の合成で、新しい親項目は足さない。

### A07：全射な平坦模型の同じ段での基底上の因子化

| 登録モジュール | 行数 | 宣言と主張 |
| --- | ---: | --- |
| FlatStageModelSurjective | 37 | `exists_surjective_flat_stage_of_model`：元の被覆が全射なら、ある段の実際の W_j→T_j が全射 |
| FlatStageModelBase | 49 | `stageModelBaseMap`・`flatStageModelBaseMap`：実際の模型の図式を元の S の上の図式へ運ぶ |
| 同上 | 同上に含む | `flatStageModelConeWithPoint_π_base`：元の被覆の構造射と cone の各射影の基底上の可換式 |
| FlatStageModelFactorization | 66 | `exists_surjective_flat_stage_factor`：ある全射な平坦側の実際の段で、元の S 上の射を因子化し、射影との合成と S 上の可換式を同時に保持する |
| IntegralModelBaseNaturality | 44 | `integralModelSpecBaseMap_naturality`：I04 の基底への構造射は全ての遷移と可換 |
| 同上 | 同上に含む | `integralModelSpecBaseNatTrans`：I04 の実際の図式を Spec R 上の自然変換にまとめる |
| 同上 | 同上に含む | `integralModelSpecCone_base`：各射影と基底への構造射の合成は元の Spec B→Spec R |

本体 **196 行**、入口 4 行。対象ビルドは直接の importer AlgebraicGeometry まで **4,900 ジョブ成功**、四モジュールの小監査は補助宣言込み **13 宣言・標準三公理のみ**。既存の `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` を全射な段の Over に適用し、元の射の因子化と基底上の可換式を同じ段で得た。忠実平坦性・新しい模型の存在・可換式の一致判定を仮定に足していない。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-flat-stage-factor-batch-check-3.log`、`2g-flat-stage-factor-native.log`、`2g-flat-stage-factor-audit.log`。整全射の有限段と合成する IntegralClosedFlatRefinement は下書き検証のみで、今回の監査には含めない。

G1 共用部品込み本体 **6,305 行**、入口込み **6,419 行**。入力の模型を実際の C01 の整拡大・Noether 平坦模型の証人から供給し、一般の始域へ戻す A07 の組立てと G2 は未完。

一覧：済み 9／全体 14（うち追加 5）。

A07 の一般の affine 基底・affine 始域の出口 `exists_fppf_proper_refinement_vCover_affineRing` の型（見込み120〜300行）：任意の可換環 R、有限表示 R-代数 C、Spec C→Spec R の v 判定から、固有・局所有限表示・全射 r:T→Spec R、平坦・局所有限表示・準コンパクト・全射 q:W→T、l:W→Spec C と l≫f=q≫r を返す。被約化と C01 で実際の整全射 B を選び、有限表示代数を tensor 底変換し、保持した Noether 平坦閉部分模型の証人を選んでから前の有限段の合成へ渡す。模型・平坦性を追加仮定にしない。これは既定の A07 の affine 始域の場合で、一般の始域への有限アフィン被覆の接続までは A07 を完了扱いにしない。親 ID は増やさない。

### A07：整全射後の細分を元の基底へ戻す合成と、一般の基底の C01 への帰着

IntegralClosedFlatRefinement **75 行**、CompactMinimalPrimeIntegralCover **47 行**、入口 2 行。

- `exists_fppf_proper_refinement_of_integral_closed_flat_model`：実際の整全射後の有限型閉部分と平坦模型の証人、元の V→Spec R への基底上の射を、ある有限段の固有全射と fppf 射による実際の細分へ合成する。模型を入力とする接続であり、これだけを A07 の完成とはしない。
- `exists_integral_surjective_reduced_compact_minimalPrimes`：任意の R を被約化して C01 を適用し、被約かつ極小素点集合が準コンパクトな B、整な R→B、Spec B→Spec R の全射性を実際に供給する。R→B の単射性は主張しない。

対象ビルドは直接の importer AlgebraicGeometry まで **4,902 ジョブ成功**、二モジュールの小監査は補助宣言込み **5 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-integral-closed-flat-refinement-check.log`、`2g-compact-minimal-integral-cover-check.log`、`2g-integral-refinement-assembly-native.log`、`2g-integral-refinement-assembly-audit.log`。

G1 共用部品込み本体 **6,427 行**、入口込み **6,543 行**。A07 の affine 始域の出口は、これらの実際の証人を組み合わせる下書きを検証中で、この監査には含めない。一般の始域への接続と G2 も未完。

一覧：済み 9／全体 14（うち追加 5）。

A07 の一般の始域への接続の型（既定の有限アフィン被覆の分割、見込み180〜450行）：`isSchemeVCover_sigmaDesc_openCover` は開被覆の余積から元の空間への射が v 判定を持つことを、付値環の閉点の像を含む一つの開へ写像全体を因子化して示す。`isSchemeVCover_of_isIso` は同型の v 判定の法則。`exists_affine_finitePresentation_vCover_refinement` は、任意の affine 基底への局所有限表示・準コンパクトな v 被覆 f:X→Spec R に対し、有限アフィン開被覆の余積（Mathlib では affine）から有限表示 R-代数 B と k:Spec B→X、Spec B→Spec R の v 判定、k≫f=Spec.map(algebraMap R B) を返す。`exists_fppf_proper_refinement_vCover_affineBase` はこれに affine 始域の出口を適用し、任意の始域の A07 の型をそのまま閉じる。元の f に平坦性・固有性・Noether 性を追加しない。親 ID は増やさない。


## A07 完了：一般の affine 基底と任意の始域の出口

| 登録モジュール | 行数 | 宣言・主張 |
| --- | ---: | --- |
| AffineRingVCoverRefinement | 93 | `exists_fppf_proper_refinement_vCover_affineRing`：任意の環 R 上の有限表示代数の v 被覆を、実際の C01 整全射・Noether 閉模型・全射な有限段の証人を組み合わせて固有全射と fppf 射で細分する |
| SchemeVCoverOpenCover | 43 | `isSchemeVCover_of_isIso`：同型の v 判定。付値環の拡大は恒等射 |
| 同上 | 同上に含む | `isSchemeVCover_sigmaDesc_openCover`：開被覆の余積の v 判定。付値環の閉点を含む開への因子化を使う |
| AffineOpenVCoverRefinement | 63 | `exists_affine_finitePresentation_vCover_refinement`：任意の始域を有限アフィン被覆の余積で細分し、有限表示 R-代数と元の被覆への実際の射・可換式・v 判定を返す |
| AffineBaseVCoverRefinement | 36 | `exists_fppf_proper_refinement_vCover_affineBase`：任意の affine 基底、局所有限表示・準コンパクトな v 被覆に対し、固有・局所有限表示・全射 r:T→Spec R と、平坦・局所有限表示・準コンパクト・全射 q:W→T、k:W→X と k≫f=q≫r を返す |

本体 **235 行**、入口 4 行。affine 始域の対象・入口ビルド **4,903 ジョブ成功**、小監査 **1 宣言・標準三公理のみ**。一般の始域への三モジュールと直接 importer AlgebraicGeometry の対象ビルド **4,906 ジョブ成功**、小監査は private な証明分割込み **5 宣言・標準三公理のみ**。新規四本は合わせて **6 宣言**を監査した。元の基底への Noether 性・被約性、元の射への固有性・平坦性、近似の遷移への忠実平坦性を追加していない。

Rydh 3.10 の承認済み affine 基底版 A07 はこれで完了。G1 の一覧 A01〜A07・C01〜C03 が済み。**G2 の B01〜B04 は未完で、停止点 2g-1 ではない。**

G1 共用部品込み本体 **6,662 行**、入口込み **6,782 行**。約12,000行の途中報告点と25,000行の外枠には未到達。G2 は有限型 F_p 上の一般の有限表示固有模型、同じ段での固有性・全射性、被覆模型の filtered 図式と Čech 図式への移送を残す。係数模型の法則から着手する。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-affine-ring-vcover-refinement-check-3.log`、`2g-affine-ring-refinement-native.log`、`2g-affine-ring-refinement-audit.log`、`2g-affine-base-refinement-batch-check-2.log`、`2g-affine-base-refinement-native.log`、`2g-affine-base-refinement-audit.log`。

一覧：済み 10／全体 14（うち追加 5）。

## G2 の最初の分割：係数体を保つ affine 模型（着手前の型）

B01 の affine 局所の係数移送として `exists_finitePresentation_model_over_noetherian_coefficients` を作る（見込み50〜130行）。Noether 環 k、k-代数 R、有限表示 R-代数 S に対し、k 上有限生成な部分代数 A⊆R と有限表示 A-代数 S₀、実際の R-代数同型 R⊗[A]S₀≃ₐ[R]S を返す。`exists_finitePresentation_noetherian_model` が使った Mathlib の有限表示の Core の計算を、ℤ から指定した k へ移す法則。k=F_p にすれば係数体を保ち、B01 の有限型 F_p の affine 局所を供給する。有限表示の対象の降下は Stacks [01ZM](https://stacks.math.columbia.edu/tag/01ZM) の affine の場合（Algebra 10.127.8）。親 ID は増やさない。

一般の固有射については、対象の模型の存在（01ZM）と、得られた模型が後の段で固有になること（[081F](https://stacks.math.columbia.edu/tag/081F)）を別に証明する。原典081Fの証明はChowの補題32.12.1を経由する。[0A0P](https://stacks.math.columbia.edu/tag/0A0P)の一般の固有射の逆極限表示は、この二つを合わせる。現在のMathlibと本レーンにChowの補題の宣言は見つかっていない。これは依存の調査であり、一般の模型を既存の射の因子化だけで完成とするものではない。B01〜B04の未完の型は保持する。

同じ affine 局所の幾何への係数移送として `exists_affine_finitePresentation_coefficient_model`（見込み35〜90行）を作る。上記の A と S₀ に加え、実際の射 a:Spec S→Spec S₀ と、元の Spec S→Spec R・Spec S₀→Spec A・Spec R→Spec A による IsPullback を返す。既存の `isPullback_affineTensorModel` の適用であり、一般の固有模型の B01 はこれだけで完了としない。

有限アフィン被覆を同じ係数環へそろえる法則 `exists_common_finitePresentation_coefficient_models`（見込み60〜150行）：有限個の有限表示 R-代数 Sᵢ に対し、一つの k 上有限生成部分代数 A⊆R と、全ての Sᵢ の有限表示 A-模型・実際の tensor 比較同型を返す。有限個の関係式の係数集合の和集合を取り、同じ `ModelOfHasCoeffs` を適用する。これは既存の係数模型の有限族への移送で、B01 の一般の対象の貼り合わせは別に残る。


### G2：指定係数環を保つ affine 模型の最初の束

| 登録モジュール | 行数 | 宣言・主張 |
| --- | ---: | --- |
| FinitePresentationCoefficientModel | 35 | `exists_finitePresentation_model_over_noetherian_coefficients`：Noether 係数環 k を保ち、有限表示 R-代数の有限生成係数部分代数 A⊆R・有限表示 A-模型・実際の tensor 比較同型を取る |
| AffineFinitePresentationCoefficientModel | 36 | `exists_affine_finitePresentation_coefficient_model`：同じ模型を Spec 上の実際の射と Cartesian な比較に移す |
| FiniteFamilyCoefficientModels | 38 | `exists_common_finitePresentation_coefficient_models`：有限個の有限表示 R-代数の模型を、同じ有限生成係数部分代数 A⊆R 上で取る |

本体 **109 行**、入口 3 行。係数環 k の宇宙は元の環 R と独立なので、F_p を大きな宇宙の R の係数にそのまま使える。有限族の添字の宇宙も独立。既存宣言の型は変更していない。Mathlib の `ModelOfHasCoeffs` と tensor 同型、既存の Spec の pullback 比較を再利用し、係数模型の法則・有限族への移送として実装した。

対象ビルドは直接 importer AlgebraicGeometry まで **4,909 ジョブ成功**、三モジュールの小監査は **3 宣言・標準三公理のみ**。共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-coefficient-model-batch-check-2.log`、`2g-coefficient-models-native.log`、`2g-coefficient-models-audit.log`。

G1・G2共用部品込み本体 **6,771 行**、入口込み **6,894 行**。G2 の一般の固有模型は未完で、この affine 局所の三本だけを B01 完了とは数えない。約12,000行の途中報告点・25,000行の外枠には未到達。

一覧：済み 10／全体 14（うち追加 5）。

### B01 の次の分割：一般の有限表示対象の模型（着手前の型）

`exists_finitePresentation_scheme_coefficient_model` の型案：Noether 係数環 k、k-代数 R、f:X→Spec R が局所有限表示・準コンパクト・準分離なら、有限生成 k-部分代数 A⊆R、p:Y→Spec A が局所有限表示・準コンパクト・準分離、a:X→Y が存在し、元の f と Spec R→Spec A を含む正方形が IsPullback。Noether 性は A の有限生成から供給し、元の R には要求しない。原典は Stacks 01ZM (1)、この分割の見込み **1,800〜3,600行**（前記の係数模型109行を含む）。B01 に含めていた一般の対象の降下の分割で、新しい親項目は増やさない。

紙の順序：有限アフィン被覆の模型を共通係数環へそろえる。重なりの準コンパクトな開を有限個の基本開で表示し、その元・有限個の射・等式を後の同じ係数部分代数へ移す。既存の局所有限表示の射の因子化・有限型の射の一致判定を使い、gluing datum とその余極限を作り、元の X との実際の pullback 比較を得る。固有性はこの構成だけでは結論にしない。固有性の有限段への移送081Fと一般の固有射の模型0A0Pの未完部分を保持する。Chowを経由する依存の実装量は引き続き照合し、4,000行を超える新しい標準存在補題が要ると判明した時点では指示どおり報告する。


B01 の有限段を取る既定の係数模型の分割（見込み120〜300行）：`coefficientSubalgebraDiagram k R` は添字 Finset R の各 s を k[ s ]⊆R に送り、遷移を実際の包含とする。`coefficientSubalgebraCocone` は頂点 R・構造射は包含、`coefficientSubalgebraCoconeIsColimit` はその実際の filtered colimit 性を返す。各段は k 上有限型、k が Noether なら Noether。`coefficientSpecDiagram`・`coefficientSpecCone`・`coefficientSpecConeIsLimit` は同じ包含の Spec による実際の極限。有限表示対象の模型と後の段への射を、この具体的な図式にそろえる。01ZM の係数環の directed union の分割で、B01 の親 ID は増やさない。


B01 の貼り合わせの法則の分割（見込み80〜180行）：`glueDataToBase` は D:Scheme.GlueData と pᵢ:D.U i→S、重なり上の可換式から実際の D.glued→S を作る。`glueDataToBase_ι` は各チャートで pᵢ に一致する式、`locallyOfFinitePresentation_glueDataToBase` は各 pᵢ の局所有限表示性から貼り合わせた射の局所有限表示性を返す。有限な affine Noether チャートの glue data なら貼り合わせは Noether であり、QC・QS 性も供給する。既存の gluing の構造射・局所性の法則で、新しい親項目は増やさない。模型の gluing datum の存在自体は別に残す。


B01 の重なりの開の有限族への移送（見込み70〜170行）：`exists_finite_opens_model_of_isLimit` は qcqs な affine 遷移の実際の極限 D,c,hc と有限個の準コンパクト開 Uₐ⊆c.pt に対し、一つの段 i と全ての準コンパクト開 Vₐ⊆D(i)、c.πᵢ⁻¹Vₐ=Uₐ を返す。`exists_finite_open_equalities_of_isLimit` は一つの段の有限個の準コンパクト開の対 Uₐ,Vₐ が極限で等しいなら、一つの後の段への射 f で全ての逆像が等しいと返す。Stacks 01Z4 の既存の単独の開の模型・等式判定を、有限 cone・wide cospan に沿って移す法則。重なりの開と有限個の貼り合わせの等式を同じ係数段へそろえるためで、親項目は増やさない。


B01 の元の対象の有限アトラスの分割（見込み80〜180行）：`exists_finite_affine_presentation_atlas` は f:X→Spec R が局所有限表示・準コンパクトなら、有限個の可換環 Bᵢ、有限表示な構造射 R→Bᵢ、開埋め込み kᵢ:Spec Bᵢ→X、kᵢ≫f=Spec(R→Bᵢ)、全射な有限族を返す。有限アフィン開被覆と元の構造射の同じ Spec の逆像を保持する法則。Noether 性・v 判定は仮定しない。有限族の係数模型の入力を元のスキームから実際に供給する。


B01・B02 で共用する有限個の射・等式の同じ段への移送（見込み80〜200行）：`exists_finite_stage_maps_of_isLimit` は共通の cofiltered 添字 J を持つ有限個の qcqs・affine 遷移図式 Dₐ と実際の極限 cₐ、S 上局所有限表示の Xₐ、基底上の射 cₐ.pt→Xₐ に対し、一つの j と全ての段での射 Dₐ(j)→Xₐ、その実際の射影との合成式と基底上の可換式を返す。`exists_finite_stage_equalities_of_isLimit` は同じ段の有限個の射の等式が極限で成立するとき、一つの共通する後の段で成立することを返す。既存の単独の射の因子化・一致判定を有限 cone・wide cospan へ移す法則で、親項目は増やさない。


B01 の元の有限アトラスと共通係数模型の組立て（見込み50〜130行）：`exists_finite_affine_atlas_coefficient_model` は Noether 係数環 k、k-代数 R、f:X→Spec R が局所有限表示・準コンパクトなら、一つの k 上有限生成部分代数 A⊆R、元の有限表示 affine アトラス Spec Bᵢ→X と、その全チャートの有限表示 A-代数 Cᵢ・実際の Cartesian な比較 Spec Bᵢ→Spec Cᵢ を同時に返す。原典01ZM (1)の有限アトラスの係数移送で、既存の有限アトラスと有限族の係数模型の組立て。親項目は増やさない。重なりと gluing datum の存在は次に残す。


### G2：有限アトラス・重なりの有限段・貼り合わせの法則の束

| 登録モジュール | 行数 | 宣言・主張 |
| --- | ---: | --- |
| CoefficientSubalgebraDiagram | 65 | `coefficientSubalgebraDiagram`：Finset R を添字とし、実際の k[s]⊆R と包含からなる図式 |
| 同上 | 同上に含む | `coefficientSubalgebraCocone`：元の R と同じ包含からなる実際の cocone |
| 同上 | 同上に含む | `coefficientSubalgebraDiagram_algebra`：各段の実際の k-代数構造 |
| 同上 | 同上に含む | `coefficientSubalgebraDiagram_finiteType`：各段は k 上有限型 |
| 同上 | 同上に含む | `coefficientSubalgebraDiagram_noetherian`：k が Noether なら各段も Noether |
| 同上 | 同上に含む | `coefficientSubalgebraCoconeIsColimit`：元の R が同じ包含の実際の filtered colimit |
| CoefficientSpecLimit | 38 | `coefficientSpecDiagram`：同じ係数包含の Spec の逆系 |
| 同上 | 同上に含む | `coefficientSpecCone`：元の Spec R と同じ係数包含の Spec からなる cone |
| 同上 | 同上に含む | `coefficientSpecConeIsLimit`：同じ cone の実際の極限性 |
| 同上 | 同上に含む | `coefficientSpecCone_projection`：各射影は選んだ係数包含の Spec そのもの |
| FiniteOpenModels | 53 | `exists_finite_opens_model_of_isLimit`：有限個の準コンパクト開を、一つの段の準コンパクト開から同時に復元 |
| 同上 | 同上に含む | `exists_finite_open_equalities_of_isLimit`：極限で等しい有限個の準コンパクト開の対を、一つの後の段で同時に等しくする |
| FiniteStageMorphisms | 64 | `exists_finite_stage_maps_of_isLimit`：共通添字を持つ有限個の極限から局所有限表示の対象への基底上の射を、実際の合成式を保ち一つの段へ降ろす |
| 同上 | 同上に含む | `exists_finite_stage_equalities_of_isLimit`：有限個の射の極限での等式を、一つの共通する後の段へ降ろす |
| FinitePresentationGluingBase | 62 | `glueDataToBase`：glue data のチャート上の可換な基底への射を、貼り合わせの実際の構造射にする |
| 同上 | 同上に含む | `glueDataToBase_ι` と生成した `_assoc`：各チャートで元の構造射に一致 |
| 同上 | 同上に含む | `locallyOfFinitePresentation_glueDataToBase`：チャート上の局所有限表示性を構造射へ渡す |
| 同上 | 同上に含む | `isNoetherian_glueData_of_finite_affine`：有限 affine Noether チャートの貼り合わせは Noether |
| 同上 | 同上に含む | `finitePresentation_glueDataToBase_of_noetherian_charts`：同じ有限チャートの局所有限表示射から、qcqs な局所有限表示の構造射を得る |
| FiniteAffinePresentationAtlas | 59 | `exists_finite_affine_presentation_atlas`：元の有限表示対象の実際の有限アフィンアトラス、有限表示環写像、同じ構造射との可換式・共同全射性 |
| FiniteAffineAtlasCoefficientModel | 45 | `exists_finite_affine_atlas_coefficient_model`：元の全チャートの有限表示代数の模型を、同じ有限生成 k-部分代数 A⊆R 上で取り、各チャートの実際の Cartesian な比較を供給 |

本体 **386 行**、入口 7 行。対象ビルドは直接 importer AlgebraicGeometry まで **4,916 ジョブ成功**。七モジュールの小監査は補助宣言込み **44 宣言・標準三公理のみ**（内訳18・5・4・4・10・2・1）。実際の IsColimit・IsLimit を構成し、単なる存在するはずの模型を入力にしていない。個々の宣言に200行を超えるものはない。係数環 k の宇宙は独立で、元の R の Noether 性・近似の遷移の忠実平坦性・元の射の v 判定を要求しない。既存宣言の型は変更していない。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-coefficient-descent-batch-check-4.log`、`2g-coefficient-descent-native.log`、`2g-coefficient-descent-audit.log`。

G1・G2共用部品込み本体 **7,157 行**、入口込み **7,287 行**。一般の有限表示対象の係数模型の分割は、前の係数模型109行と今回386行を合わせて **495 行**。その全体の1,800〜3,600行の見込みは変えず、以下の重なり・gluing datum・元の対象との Cartesian 比較が残る。**B01 は未完で、2g-1 の停止点ではない。** 約12,000行の途中報告点・25,000行の外枠には未到達。

次の接続の紙の順序：

1. 一つの共通する係数環上の全チャートの模型を、具体的な係数部分代数の図式の後の段へ底変換する。元の X の準分離性から、各重なりは準コンパクトな開である。
2. 重なりの開を各チャートの模型の一つの後の段へ降ろす。重なりの同型とその逆は、模型のチャートへの有限個の射として降ろす。必要な開への因子化と三重の重なりの開の等式を、同じ後の段でそろえる。各段が Noether なので、この段の準コンパクト性は元の R から要求せずに供給できる。
3. 逆写像との合成・恒等射・cocycle の有限個の等式を同じ後の段で成立させ、実際の Scheme.GlueData を作る。貼り合わせの構造射の有限表示性は今回の法則へ渡す。
4. 元の有限アフィン開被覆と同じ重なりを用い、貼り合わせの底変換と元の X の比較を作り、チャート上の Cartesian な比較から全体の IsPullback を示す。比較を仮定に置き換えない。

一般の固有模型の B01 と、同じ段での固有性・全射性 B02、被覆模型の実際の filtered 図式 B03・B04 は引き続き未完。固有性の有限段への移送081Fと、一般の固有射の近似0A0Pの型を維持する。

一覧：済み 10／全体 14（うち追加 5）。


B01 の貼り合わせの Cartesian 比較の法則（着手前の型、見込み120〜300行）：D:Scheme.GlueData、元の X の同じ添字 D.J による開被覆 Uᵢ→X、局所比較 aᵢ:Uᵢ→D.U i と、元の二重交叉 Uᵢ×ₓUⱼ→D.V(i,j) を入力する。二重交叉の第一射影・aᵢ・D.f i j の正方形が Cartesian、第二射影は D.t i j と両立するとき、`gluingAtlasMap` は実際の X→D.glued を作る。`gluingAtlasMap_preimage_opensRange` は D の各チャートの逆像が元の開そのもの、`isPullback_gluingAtlasMap_chart` は元の各開包含との正方形の Cartesian 性を返す。さらに元の f:X→T、g:T→S、D の構造射 pᵢ:D.U i→S について各 aᵢ が基底上 Cartesian なら、`isPullback_gluingAtlasMap_toBase` は全体の正方形も Cartesian と返す。既存の gluing・開包含・pullback の法則で、親項目を増やさない。二重交叉の模型の存在とこれらの入力を実際の有限段から供給する部分は別に残す。


B01 の gluing datum の有限個の法則への分割（着手前の型、見込み150〜400行）：Uᵢ、Vᵢⱼ、開埋め込み fᵢⱼ:Vᵢⱼ→Uᵢ、対角 fᵢᵢ の同型性、tᵢⱼ:Vᵢⱼ→Vⱼᵢ と tᵢᵢ=id、tᵢⱼ≫tⱼᵢ=id を入力する。三重交叉 Cᵢⱼₖ=Vᵢⱼ×[Uᵢ]Vᵢₖ から Vⱼₖ への Lᵢⱼₖ があり、L≫fⱼₖ=pr₁≫tᵢⱼ≫fⱼᵢ と、L≫tⱼₖ≫fₖⱼ=pr₂≫tᵢₖ≫fₖᵢ が成立するとき、`openTransitionGlueData` は実際の Scheme.GlueData を作る。`openTransitionTripleMap` は (L,pr₁≫tᵢⱼ) の pullback lift で、`openTransitionTripleMap_cycle` はその三重の合成が恒等射であることを、二つの射影と開埋め込みの mono 性で証明する。既存の gluing の構造を、同じ有限段へ降ろせる有限個の射と等式から組み立てる法則で、親項目は増やさない。


B01 の実際の係数図式への接続の法則（着手前の型、見込み100〜220行）：`exists_coefficient_spec_factor_of_fg` は A⊆R が k 上有限生成なら、具体的な係数図式のある段 s と Spec(k[s])→Spec A、元の Spec R の射影との合成が同じ包含 Spec R→Spec A に一致することを返す。`cartesianCompositeStageCone` は、元のチャート X から模型 Y と Spec R への実際の Cartesian な比較を入力し、既存の合成係数の底変換図式の極限 cone の頂点を元の X そのものに保つ。実際の IsLimit・二つの射影の可換式・各射影の Cartesian 性も返す。係数模型・底変換・比較同型の法則で、親項目は増やさない。これにより元のチャートの重なりの開を、既存の有限個の開の降下へ直接渡す。


同じ三重交叉の構成の法則（見込み40〜100行）：`openTransitionTripleLift` は、pr₁≫tᵢⱼ≫fⱼᵢ の像が fⱼₖ の像に入るという有限個の開の包含から、IsOpenImmersion.lift で実際の Lᵢⱼₖ を作る。`openTransitionTripleLift_fac` はその可換式、`openTransitionGlueDataOfRange` はこの実際の lift を前記の gluing datum の構成へ渡す。三重交叉の射の存在を別入力にせず、有限段で満たす開の包含へ帰着する法則で、親項目は増やさない。


### B01：貼り合わせの実際の Cartesian 比較と有限個の式からの gluing datum

| 登録モジュール | 行数 | 宣言・主張 |
| --- | ---: | --- |
| AtlasGluingMap | 95 | `gluingAtlasCover`：模型 D と同じ添字で元の X の実際の開被覆を保持 |
| 同上 | 同上に含む | `gluingAtlasMap_compat`：二重交叉の模型の可換式から局所比較の貼り合わせ条件を得る |
| 同上 | 同上に含む | `gluingAtlasMap`：元の局所比較を貼り合わせた実際の X→D.glued |
| 同上 | 同上に含む | `gluingAtlasMap_ι` と生成した `_assoc`：各元の開で指定した比較射に一致 |
| 同上 | 同上に含む | `gluingAtlasMap_preimage_range`：各模型チャートの像の逆像は元の対応する開の像そのもの |
| 同上 | 同上に含む | `gluingAtlasMap_preimage_opensRange`：同じ逆像の等式をスキームの開として保持 |
| 同上 | 同上に含む | `isPullback_gluingAtlasMap_chart`：元の各開包含と模型のチャートの比較は Cartesian |
| AtlasGluingBaseChange | 49 | `isPullback_gluingAtlasMap_toBase`：各チャートの基底上の Cartesian な比較から、貼り合わせ全体の実際の IsPullback を得る |
| OpenTransitionGlueData | 95 | `openTransitionTripleMap`：三重交叉の射を二つの実際の射の pullback lift として作る |
| 同上 | 同上に含む | `openTransitionTripleMap_fst` と `_assoc`：第一射影は指定した L |
| 同上 | 同上に含む | `openTransitionTripleMap_snd` と `_assoc`：第二射影は pr₁≫tᵢⱼ |
| 同上 | 同上に含む | `openTransitionTripleMap_cycle`：遷移の逆と三重交叉上の式から、実際の triple map の三重合成が恒等射と示す |
| 同上 | 同上に含む | `openTransitionGlueData`：有限個の射・対角・逆・三重交叉上の式から実際の Scheme.GlueData を構成 |

本体 **239 行**、入口 3 行。直接 importer AlgebraicGeometry までの対象ビルド **4,919 ジョブ成功**。三モジュールの小監査は補助宣言込み **27 宣言・標準三公理のみ**（内訳11・1・15）。元の開の逆像は、元の二重交叉と模型の二重交叉の Cartesian 性から点の持ち上げを使って証明した。全体の Cartesian 比較を追加仮定にしていない。ここで入力している実際の重なりの模型・有限個の法則を有限段で成立させる存在の部分は次に残る。

G1・G2共用部品込み本体 **7,396 行**、入口込み **7,529 行**。一般の有限表示対象の係数模型の分割は **734 行**まで検証。B01〜B04 は未完、2g-1 の停止点ではない。約12,000行の途中報告点・25,000行の外枠には未到達。200行を超える宣言はない。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-atlas-gluing-batch-check-3.log`、`2g-atlas-gluing-native.log`、`2g-atlas-gluing-audit.log`。

一覧：済み 10／全体 14（うち追加 5）。


B01 の降ろした開から実際の重なりの比較への接続（着手前の型、見込み40〜100行）：a:X→Y、元の開埋め込み u:U→X、模型の開 V⊆Y と a⁻¹V=u.opensRange に対し、`openModelComparison` は実際の U→V を IsOpenImmersion.lift で作る。`openModelComparison_fac` は基底への可換式、`isPullback_openModelComparison` は同じ比較の Cartesian 性。有限個の開の模型から、前記の貼り合わせの二重交叉の入力を実際に供給する法則で、親項目は増やさない。


B01 の有限アトラスの全重なりを同じ段へそろえる法則（着手前の型、見込み100〜240行）：`isCompact_atlas_overlap` は元の準分離空間 X の準コンパクトな開被覆の二重交叉の開が準コンパクトであることを供給する。`exists_finite_atlas_opens_model_of_isLimit` は、同じ cofiltered 添字の有限個のチャート図式 Dᵢ と、その各極限上の有限個の準コンパクト開について、一つの共通段と全ての開の模型を同時に返す。`exists_finite_atlas_open_equalities_of_isLimit` は全チャート上の有限個の開の等式を一つの後の段へ移す。既存の有限族の開の模型を、有限個のチャートに沿ってさらに移す法則で、親項目は増やさない。元の重なりの準コンパクト性は仮定に置き換えない。


B01 の実際のアトラスと二重交叉の開の模型の組立て（着手前の型、見込み200〜450行）：`OpenAtlasModelData k U j f` は、一つの有限生成 k-部分代数 A⊆R、全チャートの affine な qcqs 局所有限表示模型 Uᵢ⁰→Spec A、元の Uᵢ との実際の Cartesian な比較、二重交叉の模型の開 Vᵢⱼ⊆Uᵢ⁰ と、その逆像が元の Uᵢ∩Uⱼ である等式を保持する具体的な証人。`exists_openAtlasModel_of_common_affine_models` は、既に供給した共通係数環 A₀ 上の全 affine チャートの模型から、この証人を実際に構成する。有限生成部分代数の具体的な係数図式への因子化、元のチャートを頂点に保つ極限、全重なりの開を同じ有限段へ降ろす法則を使う。共通 affine 模型の入力は既存の `exists_finite_affine_atlas_coefficient_model` が無条件に供給するもので、一般の模型の存在を仮定で置き換える出口ではない。重なりの遷移・逆・cocycle の有限段への供給は次に残す。B01 の既定の存在の証明の分割で、親項目は増やさない。

同じ実際の模型の組立ての出口 `exists_finite_openAtlasModel`（上記200〜450行の分割の中）：Noether 係数環 k、任意の k-代数 R、局所有限表示・準コンパクト・準分離な f:X→Spec R に対し、有限 affine 開被覆 𝒰 と、実際の `OpenAtlasModelData k 𝒰.X 𝒰.f f` を返す。既存の無条件の共通 affine 模型を前記の構成に渡す。R の Noether 性や既存の模型の存在は仮定しない。全体の模型の存在には、重なりの遷移・逆・cocycle を同じ段へ降ろす部分が依然残る。


次の遷移の降下で使う有限表示性：k が Noether なら、選んだ有限生成 A₀ と全模型 Uᵢ⁰ は Noether。重なりの模型 Vᵢⱼ⁰ はその開なので、Spec A₀ 上 qcqs・局所有限表示である。このため、元の二重交叉から Vⱼᵢ⁰ への反転の射を、固定した局所有限表示の対象への射としてそのまま降ろせる（模型のチャートへの射だけを降ろしてから像の包含を別に処理する必要はない）。三重交叉の模型は Vᵢⱼ⁰×[Uᵢ⁰]Vᵢₖ⁰ とし、元の三重交叉との Cartesian な比較は二重交叉の比較の貼り合わせで作る。元の三重交叉から Vⱼₖ⁰ への射も同じ既存の有限個の射の降下に渡す。対角の逆・tᵢⱼ・Lᵢⱼₖ を同じ段で取り、基底上の可換式を保持するので、固定した元の模型の射影への有限個の等式を降ろすだけで、段の射そのものの逆・恒等射・三重交叉の式を証明できる。これは既定の gluing datum の有限段への供給の紙の具体化で、一般の固有性の降下を代用するものではない。


同じアトラス模型の法則（着手前の型、見込み80〜180行）：`OpenAtlasModelData.isNoetherian_coefficients` と `isNoetherian_obj` は k の Noether 性から係数環 A と全模型チャートの Noether 性を供給する。`overlapComparison` は元の二重交叉から模型の重なりへの実際の射を、逆像の開の等式から作る。`isPullback_overlapComparison` と `isPullback_overlapComparison_toBase` はそのチャート上・係数基底上の Cartesian 性。`finitePresentation_overlap` は模型の全重なりが Spec A 上 qcqs・局所有限表示であることを供給し、遷移・逆・三重交叉の射を固定した有限表示の対象へ直接降ろす入力になる。既存の Noether 性・開包含・底変換・合成の法則で、親項目は増やさない。


### B01：元のチャートを保つ実際の係数図式と開の比較への接続

| 登録モジュール | 行数 | 宣言・主張 |
| --- | ---: | --- |
| CoefficientSubalgebraFactor | 31 | `exists_coefficient_spec_factor_of_fg`：有限生成係数部分代数への構造射を、具体的な係数図式の実際の段で同じ包含のまま因子化 |
| CartesianCompositeStageLimit | 54 | `cartesianCompositeStageCone`：元の Cartesian なチャート X を頂点に保つ、合成係数の底変換図式の cone |
| 同上 | 同上に含む | `isLimit_cartesianCompositeStageCone`：同じ cone の実際の極限性 |
| 同上 | 同上に含む | `cartesianCompositeStageCone_π_snd` と `_assoc`：模型への射影との合成は元の比較射 |
| 同上 | 同上に含む | `cartesianCompositeStageCone_π_fst` と `_assoc`：基底への射影との合成は元の構造射と基底図式の射影の合成 |
| 同上 | 同上に含む | `isPullback_cartesianCompositeStageCone_π`：各射影は同じ基底の射影の底変換 |
| OpenTransitionTripleLift | 42 | `openTransitionTripleLift`：三重交叉の開への像の包含から実際の射 L を lift で作る |
| 同上 | 同上に含む | `openTransitionTripleLift_fac` と `_assoc`：同じ三重交叉の射の可換式 |
| 同上 | 同上に含む | `openTransitionGlueDataOfRange`：実際の lift を有限個の逆・cocycle の式と合わせ Scheme.GlueData にする |
| OpenModelComparison | 44 | `openModelComparison`：元の開と降ろした開の逆像の等式から、実際の比較射を lift で作る |
| 同上 | 同上に含む | `openModelComparison_fac` と `_assoc`：元の射と同じ可換式 |
| 同上 | 同上に含む | `isPullback_openModelComparison`：この実際の開の比較は Cartesian |

本体 **171 行**、入口 4 行。直接 importer AlgebraicGeometry まで対象ビルド **4,923 ジョブ成功**。四モジュールの小監査は補助宣言込み **23 宣言・標準三公理のみ**（内訳1・10・6・6）。最初の単独ビルドで不足した Restrict の import を明示し、同じ対象ビルドと監査を完了した。実際の cone の IsLimit と pullback 比較の可換式を保ち、忠実平坦性や元の環の Noether 性を追加仮定にしていない。

G1・G2共用部品込み本体 **7,567 行**、入口込み **7,704 行**。一般の有限表示対象の模型の分割は **905 行**まで検証。全チャートと重なりの開の模型の実際の供給は下書き検証中で、この監査には含めない。重なりの遷移・逆・cocycle、一般の固有性の降下と被覆模型は未完で、B01〜B04 は未完。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-coefficient-atlas-connection-check-2.log`、`2g-coefficient-atlas-connection-native-2.log`、`2g-coefficient-atlas-connection-audit.log`。

一覧：済み 10／全体 14（うち追加 5）。


B01 の遷移の射を実際の段の射として同時に供給する法則（着手前の型、見込み100〜240行）：`compositeStageStructureMap` は合成係数の底変換図式から固定した係数基底 S₀ への実際の自然変換。`exists_finite_compositeStage_maps_of_isLimit` は、同じ基底図式 D,c,hc、段 i と D(i)→S₀ の因子化、有限個の元の対象から源模型 Yₐ⁰→S₀ への Cartesian な比較、固定した局所有限表示の標的 Xₐ⁰→S₀、元の基底上の射 lₐ:源∞→Xₐ⁰ に対し、一つの j:Over i と、実際の両模型の底変換の間の射 Yₐ,j→Xₐ,j を返す。その射は段の基底 D(j.left) 上にあり、元の極限射影と標的模型の射影との合成は lₐ に一致する。既存の有限個の射の因子化を pullback lift へ渡す法則で、親項目は増やさない。重なりの反転・対角の逆・三重交叉の射にまとめて適用する。


B01 の三重交叉の模型への Cartesian 比較の法則（着手前の型、見込み100〜220行）：同じ基底射 w:B→C と二つの Cartesian な正方形 aᵢ:Xᵢ→Yᵢ、fᵢ:Xᵢ→B、gᵢ:Yᵢ→C に対し、`cartesianPullbackMap` は実際の X₁×[B]X₂→Y₁×[C]Y₂ を作り、`isPullback_cartesianPullbackMap` は二つの構造射との正方形も Cartesian と返す。pullback の lift の普遍性による既存の底変換・有限極限の法則。元の二重交叉と模型の重なりの二つの Cartesian な比較から、元の三重交叉と模型の三重交叉の係数比較を供給する。親項目は増やさない。


### B01：全チャートと二重交叉の開の模型の実際の供給

| 登録モジュール | 行数 | 宣言・主張 |
| --- | ---: | --- |
| FiniteAtlasOpenModels | 65 | `isCompact_atlas_overlap`：準分離な元の空間の準コンパクト開チャートの二重交叉の開が準コンパクト |
| 同上 | 同上に含む | `exists_finite_atlas_opens_model_of_isLimit`：全チャートの有限個の準コンパクト開の模型を一つの共通段へ降ろす |
| 同上 | 同上に含む | `exists_finite_atlas_open_equalities_of_isLimit`：全チャート上の有限個の開の極限での等式を一つの後の段へ降ろす |
| OpenAtlasModelData | 155 | `OpenAtlasModelData`：有限生成係数部分代数、全 affine チャートの模型と構造射の fp・qc・qs 性、元の比較射と IsPullback、二重交叉の開と実際の逆像の等式を保持する具体的な証人 |
| 同上 | 同上に含む | `exists_openAtlasModel_of_common_affine_models`：共通 affine 模型を具体的な係数図式へ移し、元のチャートと全二重交叉の開の同じ有限段上の模型を実際に取る |
| 同上 | 同上に含む | `exists_finite_openAtlasModel`：任意の k-代数 R 上の qcqs・局所有限表示な対象から、有限 affine 開被覆とその実際の OpenAtlasModelData を無条件に供給（k は Noether） |
| OpenAtlasModelProperties | 63 | `isNoetherian_coefficients`：係数環 A の Noether 性を k と有限生成性から供給 |
| 同上 | 同上に含む | `isNoetherian_obj`：全模型チャートの Noether 性を供給 |
| 同上 | 同上に含む | `overlapComparison`：元の二重交叉から模型の重なりへの実際の比較射を、開の逆像の等式から構成 |
| 同上 | 同上に含む | `isPullback_overlapComparison`：元の二重交叉と模型の重なりはチャート上 Cartesian |
| 同上 | 同上に含む | `isPullback_overlapComparison_toBase`：同じ重なりの比較は係数基底上でも Cartesian |
| 同上 | 同上に含む | `finitePresentation_overlap`：模型の全重なりは係数基底上 qcqs・局所有限表示 |

本体 **283 行**、入口 3 行。直接 importer AlgebraicGeometry まで対象ビルド **4,926 ジョブ成功**。三モジュールの小監査は補助宣言込み **46 宣言・標準三公理のみ**（内訳5・31・10）。模型の存在を入力にした出口ではなく、既存の無条件の共通 affine 模型・具体的な係数図式・実際の極限・有限個の開の降下を組み合わせて証人を供給した。元の R の Noether 性・v 判定・元の射の固有性を要求しない。有限被覆の添字は ULift で元のスキームと同じ宇宙へ置き、係数環 k の宇宙は独立に保った。

下書きから本体への移動前に、検証した束と三本の完全一致と各 SHA-256 を照合し、共有鍵による再確認の Lean 終了状態 **0** を記録した。対象ビルドと監査はその同じソースで成功。既存の本体宣言の型を変更していない。200行を超える宣言はない。

G1・G2共用部品込み本体 **7,850 行**、入口込み **7,990 行**。一般の有限表示対象の模型の分割は **1,188 行**まで検証。全チャートと重なりの開を実際に供給する部分は済んだが、重なりの反転・対角の逆・三重交叉の射と有限個の式を同じ段で成立させる部分、貼り合わせによる全体の模型の供給、一般の固有性の降下と被覆模型は未完。B01〜B04 は未完、2g-1 の停止点ではない。

次の二本（`FiniteCompositeStageMaps`・`CartesianPullbackComparison`）は作業木の下書きのみで、この監査・実測には含めない。前者は元の有限個の射を同じ段の両模型の間の実際の射にし、後者は二重交叉の Cartesian な比較から三重交叉の比較を供給する。型と見込みは上記の着手前の記録どおり。

共有鍵 `--class impl --wait 3600`、待ちは一つ、ビルドと監査の間だけ取得。resource limit の追加・sorry・追加公理なし。ログ：`2g-open-atlas-models-batch-check-4.log`、`2g-open-atlas-models-native.log`、`2g-open-atlas-models-audit.log`。

一覧：済み 10／全体 14（うち追加 5）。
