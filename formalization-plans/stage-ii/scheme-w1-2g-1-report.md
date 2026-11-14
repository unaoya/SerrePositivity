# SC-W1 2g-1：幾何の供給の実装記録

2026-11-14。承認された Rydh 3.10 経路。外枠 **25,000 行**、約 **12,000 行**で止まらず途中報告。G1・G2 の完成後に停止点 2g-1 を報告し、G3 へ進む。このファイルは現時点では途中記録で、完成報告ではない。main は凍結中、自分の枝 math/scheme だけで作業する。

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
