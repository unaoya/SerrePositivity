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
