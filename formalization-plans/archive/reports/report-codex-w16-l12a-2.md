# BS-W16 の報告（report-codex-w16.md） — L12a 後半（全 arity の対合まで）（§292〜§381、2026-11-15）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 292. 同じ指定面の族から元の斉次実テンソルへの接続（法則の型、実装前）

一覧：済み 12／全体 48（うち追加 4）

C451の等式を、元の各正規化生成元と右括弧テンソルへ適用する。
以下は既存構成の法則・証明分割。新しい作用やテンソル模型を定義しない。
ここで二段側は同じ指定面を合成して平坦に読んだ斉次テンソルである。
実際の余代入の括弧替え・二つの係数移動を評価したとの主張にはしない。
各証明200行以内の見込み。

```lean
lemma faceFamily_tensor_heq (A : Type u) [CommRing A] (S : SSet.{0}) {r q : ℕ}
    (F G : Fin r → Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) (h : F = G)
    (x : S _⦋q⦌) (a b : ℤ) (hab : a = b) :
    HEq
      (a • tensorValue (chains A S) r (fun i => (F i).1)
        (fun i => gen A S (F i).1 (S.map (SimplexCategory.mkHom (F i).2).op x)))
      (b • tensorValue (chains A S) r (fun i => (G i).1)
        (fun i => gen A S (G i).1 (S.map (SimplexCategory.mkHom (G i).2).op x)))

lemma positiveComposite_signedCutTensor_heq_nested
    (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) (x : S _⦋q⦌) :
    HEq
      ((Surjection.compositionSign u v k c.1 *
        cutSign c.2 (positiveCompositeCutWord u v k c.1).val) •
        cutTensor A S c.2 (positiveCompositeCutWord u v k c.1) x)
      (positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c) •
        tensorValue (chains A S) (m + (n + 1))
          (fun a => (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1)
          (fun a => gen A S
            (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
            (S.map (SimplexCategory.mkHom
              (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x)))

lemma gen_map_comp_faces (A : Type u) [CommRing A] (S : SSet.{0})
    {a b q : ℕ} (f : Fin (b + 1) →o Fin (q + 1))
    (g : Fin (a + 1) →o Fin (b + 1)) (x : S _⦋q⦌) :
    gen A S a (S.map (SimplexCategory.mkHom (f.comp g)).op x) =
      gen A S a (S.map (SimplexCategory.mkHom g).op
        (S.map (SimplexCategory.mkHom f).op x))
```

第一はF=Gとa=bを消去する。第二は元のC451・C452を第一に渡すだけ。
第三は同じ単体圏の射の合成とSの関手則を読む。
異なる総次数の要素をHEqで記すのは既存 `tensorValue_heq_degree` と同じ証明上の型移送であり、
ホモトピー圏への変更ではない。最終的な `compositeBalanceTerm` の共通次数へのeqToHomと
実際の余代入の評価は別に残し、それらをこの型の仮定として隠さない。


## 293. 元のappendIsoと余代入を同じ斉次ベクトルで評価する法則（実装前）

一覧：済み 12／全体 48（うち追加 4）

§292の平坦な出力を、実際の余代入と照合する次の法則。
既存 `IntervalCuts.coInsertionBlocks_apply` はKが任意なのでそのまま使える。
一方、既存 `appendIso_tensorVectorAt` はinterval Aの面ベクトルに限られる。
同じappendIsoを既存の `vectorTensorAt` で評価する法則を次の型で作る。
既存構成の法則・証明分割で、新しい余代入・新しい作用・複体を定義しない。
以下では `K C : Complex A`、`V := Σ d : ℕ, K.X (-(d : ℤ))`。
各証明200行以内の見込み。

```lean
lemma vectorDegree_append (K : Complex A) (m n : ℕ) (f : Fin m → V) (g : Fin n → V) :
    vectorDegree K (m + n) (Fin.append f g) = vectorDegree K m f + vectorDegree K n g

lemma vectorTensorAt_arity_transport (K : Complex A) {m n : ℕ} (h : m = n)
    (f : Fin m → V) (t : ℤ) (hf : -(vectorDegree K m f : ℤ) = t) :
    (eqToHom (congrArg (power K) h)).f t (vectorTensorAt K m f t hf) =
      vectorTensorAt K n (f ∘ Fin.cast h.symm) t (by subst n; exact hf)

lemma appendIso_vectorTensor (K : Complex A) (m n : ℕ)
    (f : Fin m → V) (g : Fin n → V) (t : ℤ)
    (ht : -(vectorDegree K m f : ℤ) + -(vectorDegree K n g : ℤ) = t) :
    (appendIso K m n).hom.f t
      (ιTensorObj (power K m) (power K n)
        (-(vectorDegree K m f : ℤ)) (-(vectorDegree K n g : ℤ)) t ht
        (vectorTensor K m f ⊗ₜ[A] vectorTensor K n g)) =
      vectorTensorAt K (m + n) (Fin.append f g) t
        (by rw [vectorDegree_append]; omega)

lemma appendIso_vectorTensorAt (K : Complex A) (m n : ℕ)
    (f : Fin m → V) (g : Fin n → V) (r s t : ℤ)
    (hr : -(vectorDegree K m f : ℤ) = r) (hs : -(vectorDegree K n g : ℤ) = s)
    (ht : r + s = t) :
    (appendIso K m n).hom.f t
      (ιTensorObj (power K m) (power K n) r s t ht
        (vectorTensorAt K m f r hr ⊗ₜ[A] vectorTensorAt K n g s hs)) =
      vectorTensorAt K (m + n) (Fin.append f g) t
        (by rw [vectorDegree_append]; omega)

lemma appendIso_inv_vectorTensorAt (K : Complex A) (m n : ℕ)
    (f : Fin m → V) (g : Fin n → V) (r s t : ℤ)
    (hr : -(vectorDegree K m f : ℤ) = r) (hs : -(vectorDegree K n g : ℤ) = s)
    (ht : r + s = t) :
    (appendIso K m n).inv.f t
      (vectorTensorAt K (m + n) (Fin.append f g) t
        (by rw [vectorDegree_append]; omega)) =
      ιTensorObj (power K m) (power K n) r s t ht
        (vectorTensorAt K m f r hr ⊗ₜ[A] vectorTensorAt K n g s hs)

lemma coInsertionBlocks_vector_apply (K C : Complex A) (s n t : ℕ)
    (θ : C ⊗ K ⟶ power K n) (c q z : ℤ)
    (f : Fin s → V) (g : Fin n → V) (h : Fin t → V)
    (hz : c + (-(vectorDegree K s f : ℤ) + (q + -(vectorDegree K t h : ℤ))) = z)
    (a : C.X c) (y : K.X q) (hg : -(vectorDegree K n g : ℤ) = c + q)
    (r : ℤ) (hθ : θ.f (c + q) (ιTensorObj C K c q (c + q) rfl (a ⊗ₜ[A] y)) =
      r • vectorTensorAt K n g (c + q) hg) :
    (IntervalCuts.coInsertionBlocks K C s n t θ).f z
      (ιTensorObj C (power K s ⊗ (K ⊗ power K t))
        c (-(vectorDegree K s f : ℤ) + (q + -(vectorDegree K t h : ℤ))) z hz
        (a ⊗ₜ[A] ιTensorObj (power K s) (K ⊗ power K t)
          (-(vectorDegree K s f : ℤ)) (q + -(vectorDegree K t h : ℤ))
          (-(vectorDegree K s f : ℤ) + (q + -(vectorDegree K t h : ℤ))) rfl
          (vectorTensor K s f ⊗ₜ[A] ιTensorObj K (power K t)
            q (-(vectorDegree K t h : ℤ)) (q + -(vectorDegree K t h : ℤ)) rfl
            (y ⊗ₜ[A] vectorTensor K t h)))) =
      (c * -(vectorDegree K s f : ℤ)).negOnePow • (r •
        vectorTensorAt K (s + (n + t)) (Fin.append f (Fin.append g h)) z
          (by rw [vectorDegree_append, vectorDegree_append]; omega))
```

最初の二つは同じ有限和の分解と等式の消去。
連結の順方向は `IntervalCuts.appendIso_tensorVector` と同じ帰納法で、
既存 `vectorTensorAt_cons`・`vectorTensorAt_succ`、左単位子・結合子の評価を使う。
逆方向はその同型の往復。最後は既存 `coInsertionBlocks_apply` で実際の交換符号を取り出し、
同じappendIsoの評価を二回使う。係数の移動の符号を仮定や新しい規約に置き換えない。
この後には出力族のprefixFamily・suffixFamilyへの再添字付けと、外側係数の移動の評価が残る。
nullaryもまだこの正の語の比較で完了には数えない。


## 294. 同じ指定面の族の斉次実テンソルへの移送：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§292の三つの型を実装した。`positiveComposite_signedCutTensor_heq_nested` は
同じ面の合成で平坦に読んだ二段の斉次テンソルと、元の合成側の符号付きcutTensorを比較する。
同じ総次数の型の移送をHEqで表すもので、ホモトピー圏の等式ではない。
`gen_map_comp_faces` は元の単体圏の射の合成と関手則そのもの。
実際の余代入の括弧替え・外側係数の移動の評価を、この比較で済んだとは数えない。

`m14-composite-signed-tensors-01.log`：3,014 jobs成功、対象警告0。
別の一回の鍵の `audit-m14-composite-signed-tensors.log`：
**2モジュール・3宣言、標準三公理のみ**、sorry・独自公理0。
終了コード0を確認し、鍵は返却した。全体ビルド・共有入口・共有監査・他レーンは変更なし。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| FaceFamilyTensors | 43 |
| CompositeSignedTensors | 43 |
| **計** | **86** |

検証済みM14実測は**23,492行**、L12aは**8,285行**。
§293のappendIsoの法則はこの取り込み点には含めず、対象ビルドで検証中。
L12aの実際の余代入・共通次数・nullary、後続のL13以降は残る。
一覧12/48（追加4）、goalはactive、外枠31,000行は据え置き。


## 295. 元の指定因子での余代入の斉次評価（法則の型、実装前）

一覧：済み 12／全体 48（うち追加 4）

§293のブロック評価を元のtensorCoInsertionActionに戻す。
既存のprefixFamily・suffixFamily・insertionFamilyとその同じ有限添字の法則は再利用する。
残る型は下記。既存構成の次数・結合子・自然性の法則と証明分割で、各証明200行以内。
ここではopen CategoryTheory MonoidalCategory HomologicalComplex、TensorPowers、
DifferentialGraded、IntervalCutsの同名の族の記法、`{A : Type u} [CommRing A]`を用いる。

```lean
lemma vectorDegree_arity_transport (K : Complex A) {m n : ℕ} (h : m = n)
    (f : Fin m → Σ d : ℕ, K.X (-(d : ℤ))) :
    vectorDegree K n (f ∘ Fin.cast h.symm) = vectorDegree K m f

lemma vectorDegree_family_blocks (K : Complex A) {m : ℕ}
    (f : Fin (m + 1) → Σ d : ℕ, K.X (-(d : ℤ))) (i : Fin (m + 1)) :
    vectorDegree K (m + 1) f = vectorDegree K i.val (prefixFamily f i) +
      (f i).1 + vectorDegree K (m - i.val) (suffixFamily f i)

lemma vectorDegree_insertionFamily (K : Complex A) {m n : ℕ}
    (f : Fin (m + 1) → Σ d : ℕ, K.X (-(d : ℤ)))
    (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (i : Fin (m + 1)) :
    vectorDegree K (m + n) (insertionFamily f g i) =
      vectorDegree K i.val (prefixFamily f i) + vectorDegree K n g +
        vectorDegree K (m - i.val) (suffixFamily f i)

lemma vectorTensorAt_family_blocks (K : Complex A) {m : ℕ}
    (f : Fin (m + 1) → Σ d : ℕ, K.X (-(d : ℤ))) (i : Fin (m + 1))
    (r : ℤ) (hr : -(vectorDegree K (m + 1) f : ℤ) = r) :
    vectorTensorAt K (m + 1) f r hr =
      (eqToHom (congrArg (power K)
        (by omega : i.val + (m - i.val + 1) = m + 1))).f r
        ((appendIso K i.val (m - i.val + 1)).hom.f r
          (ιTensorObj (power K i.val) (power K (m - i.val + 1))
            (-(vectorDegree K i.val (prefixFamily f i) : ℤ))
            (-((f i).1 : ℤ) + -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ))
            r (by have := vectorDegree_family_blocks K f i; omega)
            (vectorTensor K i.val (prefixFamily f i) ⊗ₜ[A]
              ιTensorObj K (power K (m - i.val))
                (-((f i).1 : ℤ)) (-(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ))
                (-((f i).1 : ℤ) +
                  -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ)) rfl
                ((f i).2 ⊗ₜ[A] vectorTensor K (m - i.val) (suffixFamily f i)))))

lemma tensorCoInsertionAction_vector_apply (K C : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ K ⟶ power K n)
    (c z : ℤ) (f : Fin (m + 1) → Σ d : ℕ, K.X (-(d : ℤ)))
    (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (hz : c + (-(vectorDegree K i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ))) = z)
    (a : C.X c) (hg : -(vectorDegree K n g : ℤ) = c + -((f i).1 : ℤ))
    (r : ℤ) (hθ : θ.f (c + -((f i).1 : ℤ))
      (ιTensorObj C K c (-((f i).1 : ℤ))
        (c + -((f i).1 : ℤ)) rfl (a ⊗ₜ[A] (f i).2)) =
      r • vectorTensorAt K n g (c + -((f i).1 : ℤ)) hg) :
    (tensorCoInsertionAction K C m n i θ).f z
      (ιTensorObj C (power K (m + 1)) c
        (-(vectorDegree K i.val (prefixFamily f i) : ℤ) +
          (-((f i).1 : ℤ) + -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ)))
        z hz (a ⊗ₜ[A] vectorTensorAt K (m + 1) f _ (by
          have := vectorDegree_family_blocks K f i; omega))) =
      (c * -(vectorDegree K i.val (prefixFamily f i) : ℤ)).negOnePow •
        (r • vectorTensorAt K (m + n) (insertionFamily f g i) z (by
          rw [vectorDegree_insertionFamily]; omega))
```

次数は元の連結式と等式消去。ブロック表示は元のappendIsoを二回評価する。
余代入の評価は既存 `tensorCoInsertionAction_on_blocks` と§293の元の交換符号を使い、
同じ有限添字の `family_eq_blocks`・`insertionFamily_eq_blocks` で元の出力順に戻す。
この型には内側射θの一項の評価だけが仮定として露出し、
新しいCAlgの作用やBFのoperad法則を仮定に足していない。
L12aの適用では内側射の切断和を実際に展開する工程と外側係数移動がまだ要る。


## 296. 完備化後のP⁰：有限原始元を使う案(a)の必要条件をさらに分ける（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§267・282の(a)(b)(c)の比較を、一覧L43bの指定有限原始元に照らして詰める。
以下は紙の検討で、完備化の新しいLean・新しい仮定・界面変更は作らない。

### 296.1 (a)に対して、連続性だけでなく閉元への適用を検収する

L43bは、同じW係数・BF切断・外側shuffleの明示的な有限原始元を指定している。
その式が閉元の選択に依存せず、全鎖の上の有限な多重線形式の対角評価として書ければ、
同じB多重線形写像Tについてx-yがd^r倍なら
T(x,…,x)-T(y,…,y)もd^r倍になる。望遠和の各項に差を一箇所ずつ置くためである。
正規化スカラーはκにあり、新しいdの逆元を使わない。
この同じ合同を有限和へ足すことで、固定次数での原始元の式のd進連続性を示す筋がある。
これは原始元の存在だけを選ぶ場合には使えない。

ただし、鎖の稠密性から閉元の稠密性は従わない。
「rawな閉元で差が境界」「原始元の式は連続」の二つだけでも、完備化した全閉元にはまだ届かない。
L43bの境界計算で閉条件によって消す項を保持し、全鎖aについて

    d H(a) = May(a) - F(a) + （daを少なくとも一つ含む同じ有限展開）

という同じ式をまず読む必要がある。係数微分・shuffle境界・BF切断境界を残すという
元のL43bの規約は、この検収に対応する。誤差項がda=0で消えることだけでなく、
その同じ多重線形式のd進合同を全鎖で確かめる。
その全鎖の式を完備化へ延ばせれば、完備化した閉元に適用でき、
rawな閉元の稠密性やπ_n上の完備化単位の全射性は要らない。
これはまだL43bの実装・検収前であり、原始元の式が条件を満たすと断定しない。
無限のshuffle展開を有限と読み替えず、固定次数の式が実際に定義済みの多重線形写像で
あることと、完成した模型の同じBE作用との比較を確認する。

さらに、項別の通常完備化をderived completionと比較するには、§267のとおり
termwise-flatかつK-flatな厳密BE模型、係数の有界d-torsion、指定単位とFrobeniusの比較が要る。
既存 `CellularCarrierKFlat` を調べ直したが、公開APIで直接得られるのはK平坦性であり、
各次数の平坦性が無料で付くという宣言は見つかっていない。
普通の完備化を直接 `directPerfectionValue` と定義し直してこの穴を消さない。

### 296.2 (b)との違い

(b)の完備化単位の全射・同型による消去は、§267の反例のため一般には使えない。
coconnective性だけでπ_0の全射性は出ない。
Koszul商への射影を使う別案でも、H⁰(K//d^r)にはH¹(K)のd^r-torsionが入り得るため、
H⁰の普通の商だけへ勝手に置き換えない。指定射・Frobenius・同じ演算の比較が必要なまま。
したがって(a)の全鎖の明示式が閉じる場合には、(b)の単位の全射という偽の一般原理を使わずに
完備化後へ運べる可能性がある。

### 296.3 (c)の判定

現在は(a)の模型比較と全鎖の原始元の検収、(b)のderived商と指定射の比較が未供給である。
それをcoherentなP⁰が必要との結論へ取り違えない。
同じ式が全鎖で連続に延びず、指定完備化対象・Frobeniusとの比較も(a)(b)で作れないと
判明した場合は、D79の前提に触れる(c)として§32どおり報告して止める。
今はその判定には至っていない。仮定を足すことによる回避は行っていない。


## 297. 同じappendIso・元の余代入の斉次評価：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§293・295の法則の型をすべて検証した。
元のappendIsoの順方向・逆方向、同じ前方・指定因子・後方のブロック表示、
実際の `IntervalCuts.coInsertionBlocks` と `tensorCoInsertionAction` の評価を証明した。
任意の複体の同じ斉次因子の族を使う。元のparameterCrossから出る
係数次数×前方次数のKoszul符号を保ち、同じ二つのappendIsoを評価して元の出力順へ戻した。
内側射θの一項の評価はこの一般の法則の入力であり、BFの内側切断和の展開はまだ残す。

既存のIntervalCutsの同名の区間の面ベクトルの法則と同じ帰納証明を、
同じ右括弧テンソルへ適用した。新しいappendIsoや余代入は定義していない。
最初に略記のinterval Aを残した箇所をKへ直し、補助ファイルのopenを
そのimportに実在する宣言だけに絞った。連鎖した未解決名のエラーが消え、
心拍数・再帰上限を増やさずに全対象が通った。元の公開宣言の型・定義は変更していない。
全ファイル・各証明200行以内。空白の警告も修正し、最終対象警告0。

対象ビルド（/tmp/bsw16/）：

- `m14-vector-tensor-append-02.log`：2,252 jobs成功、連結の順逆を含む。
- `m14-vector-co-insertion-02.log`：2,822 jobs成功、元のブロック余代入。
- `m14-vector-co-insertion-action-03.log`：直接importerまで2,826 jobs成功、対象警告0。

別の一回の鍵の `audit-m14-vector-co-insertion-action.log`：
**5モジュール・45宣言、標準三公理のみ**、sorry・独自公理0。
すべての終了コード0を確認し、鍵は対象ビルド/小監査の終了ごとに返した。
編集・報告の間の鍵の保持、常駐セッション、rootビルド、大きい監査なし。
main作業木・共有入口・共有監査・他レーン・drafts・界面は変更していない。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| VectorTensorAppendTransport | 36 |
| VectorTensorAppend | 128 |
| VectorCoInsertionEvaluation | 59 |
| VectorTensorFamilyBlocks | 90 |
| VectorCoInsertionActionEvaluation | 87 |
| **計** | **400** |

M14実測は**23,892行**、L12aは**8,685行**。
§291・294と合わせ、この作業分は新規16モジュール・901行、
小監査は計92宣言、標準三公理のみ。
C451・C452・C453と平坦な斉次テンソルの一致に加え、元の余代入の一項の評価まで進んだ。
L12aの残りは内側切断和の実評価・外側係数の移動・共通次数・nullaryの接続である。
L12a全体・L13以降は未完で、一覧12/48（追加4）、goalはactive。
外枠31,000行まで実測7,108行。約25,000行での出し直しの報告は引き続き行う。
既報の後続の残りの見込みを無料に減らさず、完成見込みの上端の超過リスクを残す。

完備化後のP⁰は§296に紙で追記した。(a)ではL43bの有限原始元を全鎖上の式で検収する必要を
追加で切り分け、閉元の稠密性を仮定しない。(b)の単位の全射の一般原理は使えず、
derived商の比較の穴は残る。(c)が必要との結論にはまだ至っていない。
G10の供給者側の部品は作らず、3b-4aがmainへ入ったら§33のTot九欄を優先する。


## 298. 内側の全有限和を元の余代入へ代入する法則（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§293・295の一項の評価を、実際の内側切断和へ適用するため有限和の法則を追加する。
既存の同じテンソルの加法性・係数移送の法則で、一覧には加算しない。
共通のopenと係数変数は§295のとおり。各証明200行以内の見込み。

```lean
lemma coInsertionBlocks_vector_sum_apply {ι : Type v} [Fintype ι] (K C : Complex A) (s n t : ℕ)
    (θ : C ⊗ K ⟶ power K n)
    (c q z : ℤ) (f : Fin s → Σ d : ℕ, K.X (-(d : ℤ)))
    (g : ι → Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (h : Fin t → Σ d : ℕ, K.X (-(d : ℤ)))
    (hz : c + (-(vectorDegree K s f : ℤ) + (q + -(vectorDegree K t h : ℤ))) = z)
    (a : C.X c) (y : K.X q) (hg : ∀ j, -(vectorDegree K n (g j) : ℤ) = c + q)
    (r : ι → ℤ) (hθ : θ.f (c + q) (ιTensorObj C K c q (c + q) rfl (a ⊗ₜ[A] y)) =
      ∑ j, r j • vectorTensorAt K n (g j) (c + q) (hg j)) :
    (IntervalCuts.coInsertionBlocks K C s n t θ).f z
      (ιTensorObj C (power K s ⊗ (K ⊗ power K t))
        c (-(vectorDegree K s f : ℤ) + (q + -(vectorDegree K t h : ℤ))) z hz
        (a ⊗ₜ[A] ιTensorObj (power K s) (K ⊗ power K t)
          (-(vectorDegree K s f : ℤ)) (q + -(vectorDegree K t h : ℤ))
          (-(vectorDegree K s f : ℤ) + (q + -(vectorDegree K t h : ℤ))) rfl
          (vectorTensor K s f ⊗ₜ[A] ιTensorObj K (power K t)
            q (-(vectorDegree K t h : ℤ)) (q + -(vectorDegree K t h : ℤ)) rfl
            (y ⊗ₜ[A] vectorTensor K t h)))) =
      (c * -(vectorDegree K s f : ℤ)).negOnePow •
        ∑ j, r j • vectorTensorAt K (s + (n + t)) (Fin.append f (Fin.append (g j) h)) z
          (by rw [vectorDegree_append, vectorDegree_append]; have := hg j; omega)

lemma tensorCoInsertionAction_vector_sum_apply {ι : Type v} [Fintype ι] (K C : Complex A)
    (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ K ⟶ power K n)
    (c z : ℤ) (f : Fin (m + 1) → Σ d : ℕ, K.X (-(d : ℤ)))
    (g : ι → Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (hz : c + (-(vectorDegree K i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ))) = z)
    (a : C.X c) (hg : ∀ j, -(vectorDegree K n (g j) : ℤ) = c + -((f i).1 : ℤ))
    (r : ι → ℤ) (hθ : θ.f (c + -((f i).1 : ℤ))
      (ιTensorObj C K c (-((f i).1 : ℤ))
        (c + -((f i).1 : ℤ)) rfl (a ⊗ₜ[A] (f i).2)) =
      ∑ j, r j • vectorTensorAt K n (g j) (c + -((f i).1 : ℤ)) (hg j)) :
    (tensorCoInsertionAction K C m n i θ).f z
      (ιTensorObj C (power K (m + 1)) c
        (-(vectorDegree K i.val (prefixFamily f i) : ℤ) +
          (-((f i).1 : ℤ) + -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ)))
        z hz (a ⊗ₜ[A] vectorTensorAt K (m + 1) f _ (by
          have := vectorDegree_family_blocks K f i; omega))) =
      (c * -(vectorDegree K i.val (prefixFamily f i) : ℤ)).negOnePow •
        ∑ j, r j • vectorTensorAt K (m + n) (insertionFamily f (g j) i) z (by
          rw [vectorDegree_insertionFamily]; have := hg j; omega)
```

既存の元のブロック評価に内側の全有限和を代入し、TensorProductと射のmap_sumで分配する。
各項は§293・295の同じappendIsoの評価である。空和・零項も含める。
θの値の全和は前提として明示するが、BFの適用ではcochainActionの実生成元の値から供給し、
新しい公理やBFの合成法則の仮定にはしない。外側係数の移動とnullaryの接続はなお残る。


## 299. 同じ切断和とcochainActionの基底値（法則の型、実装前）

一覧：済み 12／全体 48（うち追加 4）

共通次数の等式移送を明示して、§298のθの値を元のcochainActionから供給する。
以下は既存構成の法則と同じ生成元の照合で、一覧に追加しない。
各証明200行以内の見込み。open・係数変数は§295と同じ。

```lean
lemma module_eqToHom_apply_heq (M N : ModuleCat A) (h : M = N) (x : M) :
    HEq ((eqToHom h).hom x) x

lemma vectorTensorAt_heq (K : Complex A) (r : ℕ)
    (f : Fin r → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (ht : -(vectorDegree K r f : ℤ) = t) :
    HEq (vectorTensorAt K r f t ht) (vectorTensor K r f)

lemma cutTensorAt_heq_vectorTensor (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut m q) (w : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    HEq (cutTensorAt A S s w x)
      (vectorTensor (chains A S) r (fun a =>
        ⟨outputDegree s w a, gen A S (outputDegree s w a) (S.map (face s w a).op x)⟩))

lemma cutSum_eq_sum_vectorTensorAt (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q : ℕ} (u : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    cutSum A S u x = ∑ s : Cut (r + d) q, cutSign s (positiveWord u).val •
      vectorTensorAt (chains A S) (r + 1)
        (fun a => ⟨outputDegree s (positiveWord u) a,
          gen A S (outputDegree s (positiveWord u) a) (S.map (face s (positiveWord u) a).op x)⟩)
        (-((d + q : ℕ) : ℤ))
        (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]; congr 1; congr 1; omega)

lemma cochainAction_basis_generator (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q : ℕ} (u : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    (cochainAction A S (r + 1)).f (-((d + q : ℕ) : ℤ))
      (ιTensorObj (Surjection.complex A (r + 1)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-((d + q : ℕ) : ℤ)) (by omega)
        ((Surjection.complexXIso A (r + 1) d).inv
          (Surjection.basis A (r + 1) d (ULift.up u)) ⊗ₜ[A] gen A S q x)) =
      cutSum A S u x
```

最初の三つは同じeqToHomの等式消去であり、元を選び直さない。
切断和ではmap_sum・map_zsmulで分配し、各項の同じ次数移送を比較する。
最後は既存 `ι_cochainAction`・`positiveIntegerBilinear_neg`・`positiveComponent_generator` を使う。
これでθを任意の射の仮定として残さず、実際のBFの内側切断和を供給する前段に届く。


## 300. θの実評価を元のBF切断和から供給する（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§299の元の複体射の値を任意の指定全次数で読み、§298へ適用する二つの法則。
既存構成の同じ生成元での評価・係数移送。証明200行以内の見込み。
以下ではprefixFamily・suffixFamily・insertionFamilyは既存IntervalCutsのもの。

```lean
lemma cochainAction_basis_cut_sum (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q : ℕ} (u : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌)
    (t : ℤ) (ht : -(d : ℤ) + -(q : ℤ) = t) :
    (cochainAction A S (r + 1)).f t
      (ιTensorObj (Surjection.complex A (r + 1)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) t ht
        ((Surjection.complexXIso A (r + 1) d).inv
          (Surjection.basis A (r + 1) d (ULift.up u)) ⊗ₜ[A] gen A S q x)) =
      ∑ s : Cut (r + d) q, cutSign s (positiveWord u).val •
        vectorTensorAt (chains A S) (r + 1)
          (fun a => ⟨outputDegree s (positiveWord u) a,
            gen A S (outputDegree s (positiveWord u) a)
              (S.map (face s (positiveWord u) a).op x)⟩) t
          (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]
              have hnat : r + d + q + 1 - (r + 1) = d + q

lemma tensorCoInsertionAction_cochain_cut_sum (A : Type u) [CommRing A] (S : SSet.{0})
    {m n e : ℕ} (v : Surjection.BasisWord (n + 1) e) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (x : S _⦋(f i).1⦌) (hx : (f i).2 = gen A S (f i).1 x) (z : ℤ)
    (hz : -(e : ℤ) + (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ))) = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A (n + 1)) m (n + 1) i
      (cochainAction A S (n + 1))).f z
      (ιTensorObj (Surjection.complex A (n + 1)) (power (chains A S) (m + 1))
        (-(e : ℤ))
        (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
          (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ)))
        z hz ((Surjection.complexXIso A (n + 1) e).inv
          (Surjection.basis A (n + 1) e (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f _
            (by have h := vectorDegree_family_blocks (chains A S) f i; omega))) =
      (-(e : ℤ) * -(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ)).negOnePow •
        ∑ s : Cut (n + e) (f i).1, cutSign s (positiveWord v).val •
          vectorTensorAt (chains A S) (m + (n + 1))
            (insertionFamily f (fun a => ⟨outputDegree s (positiveWord v) a,
              gen A S (outputDegree s (positiveWord v) a)
                (S.map (face s (positiveWord v) a).op x)⟩) i) z
            (by rw [vectorDegree_insertionFamily]
                have hs := outputDegree_sum s (positiveWord v)
                rw [← degreeSum_eq_sum] at hs
                have hnat : n + e + (f i).1 + 1 - (n + 1) = e + (f i).1
```

前者は指定全次数の等式を消去して§299に戻る。
後者は内側射を同じcochainActionへ固定し、実際の基底語・指定生成元での全切断和を
前者で供給する。零項を除かず全Cutを足す。各項の次数は元のoutputDegree_sum。
fの指定因子が元のgenであるというhxは、外側切断の出力で定義どおりに供給できる条件であり、
cochainActionの評価や合成法則を仮定に足すものではない。
この法則の後にも外側係数の移動とnullary・全添字の相殺への接続は残る。


## 301. 同じ共通整数次数での符号付き項の比較（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§292の斉次テンソルのHEqを、元のcutTensorAtと同じ共通次数の等式へ戻す。
既存構成の次数・同じ指定面の法則、証明分割。各証明200行以内の見込み。

```lean
lemma positiveComposite_nested_degreeSum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    degreeSum (m + (n + 1))
      (fun a => (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1) =
        m + n + (d + e) + q + 1 - (m + (n + 1))

lemma positiveComposite_signedCutTerm_eq_nested (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) (x : S _⦋q⦌) :
    (Surjection.compositionSign u v k c.1 *
      cutSign c.2 (positiveCompositeCutWord u v k c.1).val) •
      cutTensorAt A S c.2 (positiveCompositeCutWord u v k c.1) x =
      positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c) •
        vectorTensorAt (chains A S) (m + (n + 1))
          (fun a =>
            ⟨(positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1,
              gen A S
                (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
                (S.map (SimplexCategory.mkHom
                  (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x)⟩)
          (-((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ))
          (by rw [vectorDegree, positiveComposite_nested_degreeSum])
```

前者はC451の次数の射影と元のoutputDegree_sum。
後者はC452の元の整数係数の等式、C451の同じ面の族、§299の同じ次数移送を使う。
両辺は元の圏の同じ加群成分の等式である。係数の規約や退化項の扱いを変えない。
この型は非退化性を保持し、退化時の零項の比較と全有限添字の相殺は別に接続する。


## 302. 元のcochainActionから内側全切断和の実評価へ：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§298〜300の六本を検証した。任意のθの評価を追加前提として残す段から、
元の `cochainAction` の基底語・正規化生成元での値を供給する段へ接続した。
`tensorCoInsertionAction_cochain_cut_sum` は実際のBFの内側射を固定し、
元の全Cut（退化する項も含む）の符号付き和へ展開する。
指定生成元である条件hxは外側の切断の因子で定義どおり供給するもの。
合成法則や指数の合同を追加仮定にはしていない。

対象ビルド（/tmp/bsw16/）：

- `m14-vector-co-insertion-sums-01.log`：2,828 jobs成功、対象警告0。
- `m14-cochain-action-generator-01.log`：2,657 jobs成功、対象警告0。
- `m14-cochain-insertion-cut-sum-02.log`：3,004 jobs成功、対象警告0。

型の検証では全次数を消すsubstに、選ぶ等式を明示した。
内部次数の関数をメタ変数でchangeする代わりに、同じoutputDegreeとdegreeSumを明示した。
それ以外の数学・元の公開宣言・符号規約は変更していない。
各証明・ファイル200行以内、心拍数・再帰上限の増加なし。

別々の一回の鍵の小監査：

- `audit-m14-vector-co-insertion-sums.log`：2モジュール・15宣言。
- `audit-m14-cochain-action-generator.log`：3モジュール・11宣言。
- `audit-m14-cochain-insertion-cut-sum.log`：1モジュール・13宣言。

**計6モジュール・39宣言、標準三公理のみ**、sorry・独自公理0。
全ハンドルの終了コード0を確認した。鍵は一回の対象ビルド/小監査の間だけ取って返し、
整理券は一枚ずつ。main作業木・共有入口・共有監査・drafts・界面・他レーンは変更なし。
rootビルド・大きい監査・常駐セッションなし。`git diff --check`成功。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| VectorCoInsertionSums | 66 |
| VectorCoInsertionActionSums | 91 |
| CutTensorDegreeTransport | 44 |
| CutSumVectorExpansion | 44 |
| CochainActionGenerator | 41 |
| CochainInsertionCutSum | 95 |
| **計** | **381** |

検証済みM14実測は**24,273行**、L12aは**9,066行**。
外枠31,000行まで実測6,727行。約25,000行での実測と完成見込みの出し直しを維持する。
§301の共通次数の項の比較はこの取り込み点に数えず、対象ビルド中。
外側係数の移動・元の全添字の相殺・nullaryと後続のL13以降は残る。
L12a全体は未完、一覧12/48（追加4）、goalはactiveのまま。
完備化後のP⁰は§296の検収箇所を保持する。(c)が必要との判定には至っていない。
3b-4aはまだmain未受領なので、Tot九欄の実装は始めていない。


## 303. 共通次数の比較を符号なし・退化零項へ分ける（法則の型、実装前）

一覧：済み 12／全体 48（うち追加 4）

§301の証明は中間の型を明示して通った。次に符号を付ける前の同じテンソルの等式を
証明分割として取り出し、退化時は元のcutTensor_eq_zeroで消す。
以下は同じ指定面・同じ零項の既存構成の法則で、独立の数学の項目ではない。
各証明200行以内。§301の非退化版の型は変えず、この二つを追加する。

```lean
lemma positiveComposite_cutTensorAt_eq_nested (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    cutTensorAt A S c.2 (positiveCompositeCutWord u v k c.1) x =
      vectorTensorAt (chains A S) (m + (n + 1))
          (fun a =>
            ⟨(positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1,
              gen A S
                (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
                (S.map (SimplexCategory.mkHom
                  (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x)⟩)
          (-((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ))
          (by rw [vectorDegree, positiveComposite_nested_degreeSum])

lemma positiveComposite_signedCutTerm_eq_nested_all (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    (Surjection.compositionSign u v k c.1 *
      cutSign c.2 (positiveCompositeCutWord u v k c.1).val) •
      cutTensorAt A S c.2 (positiveCompositeCutWord u v k c.1) x =
      positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c) •
        vectorTensorAt (chains A S) (m + (n + 1))
          (fun a =>
            ⟨(positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1,
              gen A S
                (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
                (S.map (SimplexCategory.mkHom
                  (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x)⟩)
          (-((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ))
          (by rw [vectorDegree, positiveComposite_nested_degreeSum])
```

符号なしの等式はC451だけを使い、非退化性は不要。
非退化時は元のC452、退化時は同じcutTensorAtの零と符号なしの等式を使う。
退化した項に整数係数そのものの一致を強制しない。


## 304. 正の全有限添字の符号付き相殺への接続（次の型、紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§303の全切断の比較を、既存positiveCompositeNestedEquivの両側で読む。
これは§112のL12aの正の内側arityの枝であり、一般のnullaryの枝は別に残す。
次の名前はまだ実装・型検査していない。各証明200行以内の見込み。
実際の合成側の係数と元の二段側の係数を使い、値を対応から逆算して定義しない。

```lean
lemma positiveNested_degreeSum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    degreeSum (m + (n + 1)) (fun a => (positiveNestedFaceFamily u v k c a).1) =
      m + n + (d + e) + q + 1 - (m + (n + 1))

def positiveCompositeBalancePerm {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) :
    Equiv.Perm (PositiveCompositeCutIndex u v k q ⊕ PositiveNestedCutIndex u v k q) :=
  (Equiv.sumCongr (positiveCompositeNestedEquiv u v k q)
    (positiveCompositeNestedEquiv u v k q).symm).trans (Equiv.sumComm _ _)

lemma positiveCompositeBalancePerm_involutive {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) :
    Function.Involutive (positiveCompositeBalancePerm u v k q)

lemma positiveCompositeBalancePerm_ne {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ)
    (i : PositiveCompositeCutIndex u v k q ⊕ PositiveNestedCutIndex u v k q) :
    positiveCompositeBalancePerm u v k q i ≠ i

def positiveCompositeBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ)
    (i : PositiveCompositeCutIndex u v k q ⊕ PositiveNestedCutIndex u v k q) (x : S _⦋q⦌) :
    (power (chains A S) (m + (n + 1))).X
      (-((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ)) :=
  match i with
  | Sum.inl c => (Surjection.compositionSign u v k c.1 *
      cutSign c.2 (positiveCompositeCutWord u v k c.1).val) •
      cutTensorAt A S c.2 (positiveCompositeCutWord u v k c.1) x
  | Sum.inr c => -(positiveNestedCutCoefficient u v k c •
      vectorTensorAt (chains A S) (m + (n + 1))
        (fun a => ⟨(positiveNestedFaceFamily u v k c a).1,
          gen A S (positiveNestedFaceFamily u v k c a).1
            (S.map (SimplexCategory.mkHom (positiveNestedFaceFamily u v k c a).2).op x)⟩)
        (-((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ))
        (by rw [vectorDegree, positiveNested_degreeSum]))

lemma positiveCompositeBalancePerm_neg (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ)
    (i : PositiveCompositeCutIndex u v k q ⊕ PositiveNestedCutIndex u v k q) (x : S _⦋q⦌) :
    positiveCompositeBalanceTerm A S u v k q (positiveCompositeBalancePerm u v k q i) x =
      -positiveCompositeBalanceTerm A S u v k q i x

lemma sum_positiveCompositeBalanceTerm_eq_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) (x : S _⦋q⦌) :
    ∑ i : PositiveCompositeCutIndex u v k q ⊕ PositiveNestedCutIndex u v k q,
      positiveCompositeBalanceTerm A S u v k q i x = 0
```

次数和は既存の同値の全射性で§301の次数和を任意の二段切断へ運ぶ。
対合は同じ有限同値と逆の交換だけで、固定点はSumの両枝の違いにより存在しない。
項の比較は§303の全切断の比較と同じ同値の往復を使う。
最後はL09で使った既存Finset.sum_ninvolutionと同じ相殺則。
零項・退化語・退化面は除外せず保持する。

この正の枝の相殺を、nullaryを含むL12a全体の完成とは数えない。
また二段側の指数に含まれるd*eの係数交換を実際の外側合成射で評価する工程は別に残す。
§300の内側の実評価と合わせて元の合成射へ戻してからL12/L12aに適用する。


## 305. 元の共通整数次数での全切断の項の厳密な一致：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§301・303を検証した。符号なしの同じcutTensorAtの等式は全ての切断で成立する。
元のC452を使う非退化の場合と、元のcutTensor_eq_zeroを使う退化の場合に分け、
`positiveComposite_signedCutTerm_eq_nested_all` で零項も保持した全項の等式へ接続した。
両辺は元の圏の同じ加群成分であり、ホモトピー圏の等式ではない。
退化項の整数係数そのものに等式を要求していない。

`m14-composite-signed-terms-02.log`で中間の型を明示した比較が通った。
さらに同じ符号なしの比較を証明分割として取り出し、
`m14-composite-signed-terms-all-02.log`で直接importerまで3,020 jobs成功、対象警告0。
初回の型推論が心拍数上限に達したが、型を明示し、元の比較を分割して閉じた。
心拍数・再帰上限は増やしていない。各証明・ファイル200行以内。

別の一回の鍵の `audit-m14-composite-signed-terms-all.log`：
**3モジュール・8宣言、標準三公理のみ**、sorry・独自公理0。
全ハンドルの終了コード0を確認し、鍵は対象ビルド/小監査の間だけ使用して返した。
共有入口・共有監査・main作業木・drafts・界面・他レーンは変更なし。
rootビルド・大きい監査・常駐セッションなし。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| CompositeTensorAtComparison | 71 |
| CompositeSignedTerms | 43 |
| CompositeSignedTermsAll | 45 |
| **計** | **159** |

検証済みM14実測は**24,432行**、L12aは**9,225行**。
外枠31,000行まで実測6,568行。約25,000行での残りの見込みの出し直しを維持する。
§304の正の全有限添字の相殺はこの取り込み点には数えず、対象ビルドで検証中。
外側係数移動の実評価とnullary・後続のL13以降も未完。
L12a全体は未完、一覧12/48（追加4）、goalはactive。
完備化後のP⁰の未供給箇所は§296のまま保持し、(c)との判定はまだしていない。


## 306. 正の全有限添字の実項の対合と相殺：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§304の型をすべて実装した。同じpositiveCompositeNestedEquivと逆を交換する対合を作り、
元の合成側の符号付きcutTensorAtと、負号を付けた元の二段の指定面のテンソルの和を比較した。
値を対応の逆算で定義せず、両側とも元の整数係数と元の正規化生成元を保持する。
退化語・退化面の零項を除かず、全有限添字を保って相殺した。
正の内側arityの枝であり、nullaryを含むL12a全体とは数えない。

`m14-positive-composite-balance-03.log`：3,023 jobs成功、対象警告0。
初回は有限同値の適用と元の写像の記法を明示する必要があった。
逆向きの依存する次数証明を直接書き換えず、原像で読む形にしたが、
大きい式の展開が心拍数上限に達したため、同じ順向きの比較と対合の往復から逆向きを導いた。
元の項の選択・符号・型を変えていない。心拍数・再帰上限の増加なし。
各証明・ファイル200行以内。

別の一回の鍵の `audit-m14-positive-composite-balance.log`：
**3モジュール・26宣言、標準三公理のみ**、sorry・独自公理0。
終了コード0を確認し、鍵は対象ビルド/小監査の間だけ使用して返した。
共有入口・共有監査・main作業木・drafts・界面・他レーンは変更なし。
rootビルド・大きい監査・常駐セッションなし。`git diff --check`成功。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| PositiveCompositeBalancePerm | 52 |
| PositiveCompositeBalanceTerms | 40 |
| PositiveCompositeBalanceCancellation | 68 |
| **計** | **160** |

M14実測は**24,592行**、L12aは**9,385行**。
§302・305・306のこの作業分は計12モジュール・700行、
新規分の小監査は計73宣言、標準三公理のみ。
外枠31,000行まで実測6,408行。約25,000行の報告で完成の残りを出し直す指定を維持する。
L12aの外側係数移動の実評価・元の合成射への接続・nullaryが残る。
後続L13以降も未完で、一覧12/48（追加4）、goalはactive。
正の枝の相殺を根拠にL12aを済みへ移していない。

次のnullaryの検収では、既存 `overlapPartition_empty_eq`・`count_eq_one_of_empty` と
同じ `nullaryAction`・`AlexanderWhitney.cochainCounit` を使う。
IntervalCutsの `nullaryOuterCutEquiv`・`nullaryNestedCutEquiv`・`nullary_edgeSign` は
辺の場合のAPIなので、任意qの全切断の同値としてそのまま流用しない。
削除したraw語が退化する場合、削除色が複数回現れる場合、出力arityが零の場合を残す。
これらの型と同じ有限点検を確認してからLeanへ進める。

完備化後のP⁰は§296の全鎖の有限原始元・指定完備化対象の比較を未供給のまま保持する。
(c)が必要との判定には至っていない。3b-4aもmain未受領のままで、Tot九欄はまだ始めない。


## 307. 実際の外側係数の交換と四射の合成（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§112のL12の右辺そのものを記法としてまとめる。新しい作用や模型を選ぶものではなく、
元のbraiding・associator・外側cochainAction・tensorCoInsertionActionの四射をそのまま保つ。
IntervalCutsの `coactionComposition_apply` はP,Q,K,W,Xが任意なので再利用する。
定義の記法と適用の法則の型は次。各証明200行以内。

```lean
def iteratedCochainAction (S : SSet.{0}) (m n : ℕ) (i : Fin (m + 1)) :
    (Surjection.complex A (m + 1) ⊗ Surjection.complex A n) ⊗ chains A S ⟶ power (chains A S) (m + n) :=
  ((β_ (Surjection.complex A (m + 1)) (Surjection.complex A n)).hom ▷ chains A S) ≫
    (α_ (Surjection.complex A n) (Surjection.complex A (m + 1)) (chains A S)).hom ≫
    (Surjection.complex A n ◁ cochainAction A S (m + 1)) ≫
    tensorCoInsertionAction (chains A S) (Surjection.complex A n) m n i (cochainAction A S n)


lemma iteratedCochainAction_apply (S : SSet.{0}) (m n : ℕ) (i : Fin (m + 1)) (r s t z : ℤ)
    (hz : r + s + t = z) (x : (Surjection.complex A (m + 1)).X r) (y : (Surjection.complex A n).X s)
    (w : (chains A S).X t) :
    (iteratedCochainAction A S m n i).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A n) (chains A S) (r + s) t z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A n) r s (r + s) rfl
          (x ⊗ₜ[A] y) ⊗ₜ[A] w)) =
      (r * s).negOnePow •
        (tensorCoInsertionAction (chains A S) (Surjection.complex A n) m n i (cochainAction A S n)).f z
          (ιTensorObj (Surjection.complex A n) (power (chains A S) (m + 1)) s (r + t) z (by omega)
            (y ⊗ₜ[A] (cochainAction A S (m + 1)).f (r + t)
              (ιTensorObj (Surjection.complex A (m + 1)) (chains A S) r t (r + t) rfl
                (x ⊗ₜ[A] w))))
```

符号は元のbraidingから出るr*sのnegOnePowである。
語基底へ適用したr=-d,s=-eの符号を、あとで二段切断の元のd*eの指数と照合する。
これは正のarityに限るための新しい仮定を付けず、全arityの同じ射の評価として置く。


## 308. 外側の実切断和と二つの係数交換（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§307の同じ四射を基底語・正規化生成元で読み、外側の全切断和へ展開する。
元の既存構成の加法性・係数移動・生成元の評価で、各証明200行以内。
Aは共通の係数環変数。型は次。

```lean
lemma positiveNestedCutCoefficient_eq_koszul {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    positiveNestedCutCoefficient u v k c =
      ((-(d : ℤ) * -(e : ℤ)).negOnePow : ℤ) *
        (cutSign c.1 (positiveWord u).val *
          (((-(e : ℤ) * -(positiveNestedPrefixDegree u k c.1 : ℤ)).negOnePow : ℤ) *
            cutSign c.2 (positiveWord v).val))

lemma iteratedCochainAction_basis_outer_cut_sum (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -(q : ℤ) = z) :
    (iteratedCochainAction A S m (n + 1) k).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A (n + 1)) (chains A S)
        (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A (n + 1))
          (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
          ((Surjection.complexXIso A (m + 1) d).inv
            (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (Surjection.complexXIso A (n + 1) e).inv
              (Surjection.basis A (n + 1) e (ULift.up v))) ⊗ₜ[A] gen A S q x)) =
      (-(d : ℤ) * -(e : ℤ)).negOnePow •
        ∑ s : Cut (m + d) q, cutSign s (positiveWord u).val •
          (tensorCoInsertionAction (chains A S) (Surjection.complex A (n + 1)) m (n + 1) k
            (cochainAction A S (n + 1))).f z
            (ιTensorObj (Surjection.complex A (n + 1)) (power (chains A S) (m + 1))
              (-(e : ℤ)) (-(d : ℤ) + -(q : ℤ)) z (by omega)
              ((Surjection.complexXIso A (n + 1) e).inv
                (Surjection.basis A (n + 1) e (ULift.up v)) ⊗ₜ[A]
                vectorTensorAt (chains A S) (m + 1)
                  (fun a => ⟨outputDegree s (positiveWord u) a,
                    gen A S (outputDegree s (positiveWord u) a)
                      (S.map (face s (positiveWord u) a).op x)⟩)
                  (-(d : ℤ) + -(q : ℤ))
                  (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]
                      have hnat : m + d + q + 1 - (m + 1) = d + q
```

係数の法則は負次数の積を自然数の積へ戻し、元の二つの冪をまとめる。
外側の展開は§307と§300の同じcochainActionの全切断和の評価、map_sum・map_zsmul。
正の語で全Cutを保ち、退化項を勝手に削除しない。
内側の余代入の共通次数・面の合成・二段全添字への再添字付けを続けて接続する。


## 309. 内側余代入の指定入力次数と同じ生成元の族（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§308の外側切断項に§300を適用するため、入力テンソルの次数をpと指定する。
同じ次数移送・合成面の関手則の法則で、各証明200行以内の見込み。

```lean
lemma tensorCoInsertionAction_cochain_cut_sum_at (A : Type u) [CommRing A] (S : SSet.{0})
    {m n e : ℕ} (v : Surjection.BasisWord (n + 1) e) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (x : S _⦋(f i).1⦌) (hx : (f i).2 = gen A S (f i).1 x) (p z : ℤ)
    (hp : -(vectorDegree (chains A S) (m + 1) f : ℤ) = p)
    (hz : -(e : ℤ) + p = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A (n + 1)) m (n + 1) i
      (cochainAction A S (n + 1))).f z
      (ιTensorObj (Surjection.complex A (n + 1)) (power (chains A S) (m + 1))
        (-(e : ℤ))
        p
        z hz ((Surjection.complexXIso A (n + 1) e).inv
          (Surjection.basis A (n + 1) e (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f p hp)) =
      (-(e : ℤ) * -(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ)).negOnePow •
        ∑ s : Cut (n + e) (f i).1, cutSign s (positiveWord v).val •
          vectorTensorAt (chains A S) (m + (n + 1))
            (insertionFamily f (fun a => ⟨outputDegree s (positiveWord v) a,
              gen A S (outputDegree s (positiveWord v) a)
                (S.map (face s (positiveWord v) a).op x)⟩) i) z
            (by rw [vectorDegree_insertionFamily]
                have hs := outputDegree_sum s (positiveWord v)
                rw [← degreeSum_eq_sum] at hs
                have hnat : n + e + (f i).1 + 1 - (n + 1) = e + (f i).1 := by omega
                rw [hnat] at hs
                change -((vectorDegree (chains A S) i.val (prefixFamily f i) +
                  degreeSum (n + 1) (outputDegree s (positiveWord v)) +
                  vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℕ) : ℤ) = z
                rw [hs]
                have hf := vectorDegree_family_blocks (chains A S) f i
                omega)

lemma positiveNested_vectorFamily_eq_insertion (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) (x : S _⦋q⦌) :
    (fun a =>
      (⟨(positiveNestedFaceFamily u v k c a).1,
        gen A S (positiveNestedFaceFamily u v k c a).1
          (S.map (SimplexCategory.mkHom (positiveNestedFaceFamily u v k c a).2).op x)⟩ :
        Σ d : ℕ, (chains A S).X (-(d : ℤ)))) =
      insertionFamily
        (fun a => ⟨outputDegree c.1 (positiveWord u) a,
          gen A S (outputDegree c.1 (positiveWord u) a)
            (S.map (face c.1 (positiveWord u) a).op x)⟩)
        (fun b => ⟨outputDegree c.2 (positiveWord v) b,
          gen A S (outputDegree c.2 (positiveWord v) b)
            (S.map (face c.2 (positiveWord v) b).op
              (S.map (face c.1 (positiveWord u) k).op x))⟩) k
```

前者はpと元の三ブロックの次数の和の等式を消去して§300へ戻る。
後者は同じoperadInsertionEquivの残り色・挿入色に場合分けし、
既存gen_map_comp_facesで同じ合成面の生成元を読む。新しい面や新しい作用を選ばない。


## 310. 実際の二段余作用を元の二段全切断和で読む（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

元の外側・内側の切断和と二つの係数交換を、同じ二段全添字の和へまとめる。
既存構成の加法性・係数移送・合成面・有限和の再添字付けの法則。証明200行以内の見込み。

```lean
lemma iteratedCochainAction_basis_nested_cut_sum (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -(q : ℤ) = z) :
    (iteratedCochainAction A S m (n + 1) k).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A (n + 1)) (chains A S)
        (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A (n + 1))
          (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
          ((Surjection.complexXIso A (m + 1) d).inv
            (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (Surjection.complexXIso A (n + 1) e).inv
              (Surjection.basis A (n + 1) e (ULift.up v))) ⊗ₜ[A] gen A S q x)) =
      ∑ c : PositiveNestedCutIndex u v k q, positiveNestedCutCoefficient u v k c •
        vectorTensorAt (chains A S) (m + (n + 1))
          (fun a => ⟨(positiveNestedFaceFamily u v k c a).1,
            gen A S (positiveNestedFaceFamily u v k c a).1
              (S.map (SimplexCategory.mkHom (positiveNestedFaceFamily u v k c a).2).op x)⟩) z
          (by rw [vectorDegree, positiveNested_degreeSum]
              have hn : m + n + (d + e) + q + 1 - (m + (n + 1)) = d + e + q := by omega
              rw [hn]; omega)
```

§308で外側を展開し、各項に§309の指定入力次数での同じ内側評価を適用する。
生成元の族の一致は§309、整数係数の一致は§308。
Fintype.sum_sigmaで元の全二段添字へ戻し、退化した切断も保つ。
この法則に、合成側の実際の係数合成の評価と§304の相殺を続けて接続する。
nullaryの枝は含まず、その完成をこの型の前提には置かない。


## 311. 合成側の実際の係数合成の全切断和（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

元のcompositionOnWordsを同じ複体射cochainActionへ入れ、全合成切断項で読む。
既存の語長・次数移送・加法性・生成元の評価の法則で、各証明200行以内の見込み。

```lean
lemma positiveWord_compositeBasisWord {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    positiveWord (Surjection.compositeBasisWord u v k r (by omega)) =
      positiveCompositeCutWord u v k r

lemma positiveCompositeCutTerm_eq_vectorTensorAt (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    positiveCompositeCutTerm A S u v k c x =
      Surjection.compositionSign u v k c.1 •
        (cutSign c.2 (positiveCompositeCutWord u v k c.1).val •
          vectorTensorAt (chains A S) (m + (n + 1))
            (fun a => ⟨outputDegree c.2 (positiveCompositeCutWord u v k c.1) a,
              gen A S (outputDegree c.2 (positiveCompositeCutWord u v k c.1) a)
                (S.map (face c.2 (positiveCompositeCutWord u v k c.1) a).op x)⟩)
            (-((d + e + q : ℕ) : ℤ))
            (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]
                have hn : m + n + (d + e) + q + 1 - (m + (n + 1)) = d + e + q

lemma cochainAction_composition_cut_sum (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) :
    (cochainAction A S (m + (n + 1))).f (-((d + e + q : ℕ) : ℤ))
      (ιTensorObj (Surjection.complex A (m + (n + 1))) (chains A S)
        (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) (-((d + e + q : ℕ) : ℤ)) (by omega)
        ((Surjection.complexXIso A (m + (n + 1)) (d + e)).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) =
      ∑ c : PositiveCompositeCutIndex u v k q, positiveCompositeCutTerm A S u v k c x
```

語長は同じEq.mpの証明無関係性。合成項の次数移送は元のeqToHomを保持する。
全和はcompositionOnWordsの定義、正arityのcompositeGenerator_eq_basis、§300の基底値を使う。
元の全分割と全Cutを足し、退化項を除くことや合成符号の再定義は行わない。
この後に同じ総次数の相殺を実際の左右の値へ適用する。nullaryはなお別に残す。


## 312. 実際の外側係数交換と元の全二段切断和：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§307〜310の五本を検証した。元の四射の合成を、一般S・全語次数・任意の入力単体で
同じpositiveNestedCutCoefficientと同じ生成元の全二段切断和へ展開した。
d*eの外側係数交換と、内側係数が前方の出力を越える交換の双方を実際の射から評価した。
整数係数を定義し直したり、二段の式を前提として置いたりしていない。

型の接続で古い略記を正しいSurjection.complexとchains A Sへ直した。
同じ前方族の部分適用と次数射影の展開差は、元の前方次数がrflで同じであることを
明示して閉じた。既存の公開宣言・符号・仮定は変更していない。
各証明・ファイル200行以内、心拍数・再帰上限の増加なし。

対象ビルド（/tmp/bsw16/）：

- `m14-iterated-outer-cut-sum-01.log`：3,117 jobs成功、直接importerまで対象警告0。
- `m14-nested-degrees-and-generators-01.log`：3,073 jobs成功、対象警告0。
- `m14-iterated-nested-cut-sum-03.log`：3,224 jobs成功、対象警告0。

別々の一回の鍵の小監査：

- `audit-m14-iterated-outer-and-families.log`：4モジュール・29宣言。
- `audit-m14-iterated-nested-cut-sum.log`：1モジュール・7宣言。

**計5モジュール・36宣言、標準三公理のみ**、sorry・独自公理0。
全ハンドルの終了コード0を確認し、鍵は対象ビルド/小監査の終了ごとに返した。
main作業木・共有入口・共有監査・drafts・界面・他レーンは変更なし。
rootビルド・大きい監査・常駐セッションなし。`git diff --check`成功。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| IteratedCochainAction | 61 |
| IteratedOuterCutSum | 70 |
| CochainInsertionCutDegrees | 61 |
| NestedGeneratorFamilies | 51 |
| IteratedNestedCutSum | 74 |
| **計** | **317** |

検証済みM14実測は**24,909行**、L12aは**9,702行**。
外枠31,000行まで実測6,091行。§311の合成側の実評価は未検証なのでここには数えない。
その実評価と相殺を元の左右の値へ戻す工程、nullary・後続L13以降は残る。
L12a全体は未完、一覧12/48（追加4）、goalはactive。
約25,000行の区切りの見込みの出し直しは、次の合成側の検証の区切りで報告する。
完備化後のP⁰は§296の未供給箇所を保持し、(c)が必要との判定にはまだ至っていない。
3b-4aはmain未受領のままで、Tot九欄の実装はまだ始めていない。


## 313. 合成側の実際の係数合成の全切断和：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§311を検証した。元のcompositionOnWordsを同じ複体射cochainActionへ入れた値は、
元の全分割と全CutのpositiveCompositeCutTermの和そのものである。
合成基底語のarityと次数を明示し、テンソルの係数を外へ動かす向きを揃えた。
基底値の書き換えでは同じarityの定義展開を許し、残る同じ括弧の差はrflで閉じた。
元の係数合成・切断項・符号規約・公開宣言は変更していない。

`m14-composite-cochain-cut-sum-04.log`：3,225 jobs成功、対象警告0。
別の一回の鍵の `audit-m14-composite-cochain-cut-sum.log`：
**1モジュール・11宣言、標準三公理のみ**、sorry・独自公理0。
各証明・ファイル200行以内、心拍数・再帰上限の増加なし。
終了コード0を確認し、鍵は対象ビルド/小監査の間だけ使用して返した。
main作業木・共有入口・共有監査・drafts・界面・他レーンは変更なし。
rootビルド・大きい監査・常駐セッションなし。`git diff --check`成功。

登録対象：`SerrePositivity.EInfinity.SimplexCuts.CompositeCochainCutSum`、**93行**。
§312と合わせ、この作業分は6モジュール・410行、監査47宣言・標準三公理のみ。
M14実測は**25,002行**、L12aは**9,795行**。L09a・L09の8,991行は不変。
L12a全体と後続は未完、一覧12/48（追加4）、goalはactive。
次は元の合成側と二段側の和を、証明済みの正の枝の相殺へ渡す。

## 314. 約25,000行の途中報告：残りの見込みの出し直し

一覧：済み 12／全体 48（うち追加 4）

§32の指定の途中報告。検証済み実測**25,002行**、外枠**31,000行**、残り枠**5,998行**。
完成済みのMay4,128行を含む同じ数え方。旧coherent経路の保持分10,216行は加えない。
実測の伸びをL12a全体の完成やL13以降の実装として控除しない。

### 314.1 L12aの残り

正の全有限添字・C451/C452/C453・同じ共通次数の全項の比較・有限和の相殺は検証済み。
実際の左右の射の生成元での全和も§312・313まで検証済み。
その生成元での値の等式を相殺から取り出す工程、nullaryの任意qの全切断、
一般nへの枝の接続は未完である。

| L12aの残り | 新しい粗い見込み |
| --- | ---: |
| 正の枝の相殺を同じ指定総次数の実際の左右の値へ戻す | 80〜140 |
| nullary：複数出現・削除raw語の退化・任意qの全切断・出力arity零 | 350〜650 |
| nullaryを含む元の一般nの添字・固定零項の包装 | 35〜65 |
| **L12a残り** | **465〜855** |

nullaryの既存 `IntervalCuts.nullaryNestedCutEquiv` は辺の場合なので任意qへ無料に広げない。
既存の空語分割の一意性・count_eq_one_of_empty・元のnullaryActionとAW余単位は再利用する。
削除語が退化する枝と出力arity零を落とさず、次の型と有限点検で検収する。

### 314.2 L12〜L28の残りの見込み

§177の2,504〜4,664行をそのまま機械的に足さず、現在の実装と再利用APIを読み直した。
下記は未証明の部分の紙の見込みで、数学的な行数の下限や保証された上限ではない。
L12aの上の残りとの二重計上を避け、ここでは実複体射への線形延長や後続の作用を数える。

| 残る行 | 見込み | 再利用するもの・未供給の接続 |
| --- | ---: | --- |
| L12 | 80〜160 | 同じ相殺・全和からの切断和の合成則の包装。nullaryの幾何は上のL12aで数える |
| L13 | 80〜160 | unaryの唯一の切断、元のoneIsoと生成元。全qの式は未供給 |
| L14 | 150〜300 | 既存NullaryActionの前段46行は控除済み。余単位の実評価・nullaryの射の延長は残す |
| L15 | 90〜160 | 既存CutNaturality・SignedNaturalityと同じ複体成分の生成元外延性 |
| L16 | 150〜280 | 元のcomplexPartialCompositionの基底値、全整数・三重テンソルの外延性 |
| L17 | 120〜240 | L11の切断和の置換とL13の単位を同じ複体射へ延長 |
| L18 | 50〜100 | restrictCoalgebraObj・restrictCoalgebraMapと同じTableReduction.operadMap。一般operad法則を作り直さない |
| L19〜L21 | 450〜850 | 正規化の核・微分・自然性と反対圏のDold–Kanの同じ指定包含のホモトピー逆 |
| L22〜L26 | 900〜1,700 | convolutionFunctor/convolutionPreは再利用。等化子・恒等単体での評価/復元・次数符号・指定比較は未供給 |
| L27〜L28 | 350〜650 | 同じ作用の射影と全係数の切断評価。convolutionAlgebraの法則は再利用するが評価符号は残す |
| **計** | **2,420〜4,600** | |

`Operad.CoalgebraRestriction` のrestrictCoalgebraObj/Map/Functor、
`ConvolutionAlgebra` のconvolutionAlgebra、`ConvolutionFunctor` のconvolutionFunctor/convolutionPreを
読み直した。これらの一般operad法則を新設しない分を反映したが、
評価/復元や実際のBF作用の式を証明済みとして引いていない。

### 314.3 M14全体と31,000行との照合

| 残る部分 | 下端 | 上端 |
| --- | ---: | ---: |
| L12a | 465 | 855 |
| L12〜L28（L12a以外、上の表） | 2,420 | 4,600 |
| L29〜L37 | 1,200 | 2,000 |
| G10後の指定比較への適用 | 500 | 900 |
| filtered塔 | 300 | 550 |
| 同じ二重模型の作用・有限原始元・実現の比較 | 1,500 | 2,800 |
| **既知の残りの計** | **6,385** | **11,705** |
| **実測25,002行を含む完成見込み** | **31,387** | **36,707** |

L29以降は§177の粗い見込みを据え置き、未供給のものを完成として減らしていない。
**完備化後のP⁰の模型・単位・同じFrobeniusとの比較は、この数値にまだ含めていない。**
§296の(a)(b)の検収が済んでおらず、新規分を0行とも、上の二重模型の枠で収まるとも扱わない。
したがって表の31,387〜36,707行だけでM14全体が閉じるという意味ではない。

紙の見込みの下端でも外枠より387行多く、上端は5,707行多い。
**現状では31,000行以内に完成する見通しが立っていない。**
見込みは数学的下限ではないが、旧見込み30,745行を完成上端として再掲することはしない。
外枠を自分で上げたり、残る範囲を削って完成と定義し直したりしない。

§32の「約25,000行で止まらずに途中報告」に従い、この途中報告点そのものでは止まらず、
型つきの一覧の同じ既存構成の法則の接続を続ける。
外枠に届くとき、新しい構成/定理・範囲外が必要なとき、または完備化の(c)が必要と判明したときは
検証済みを保存して報告し止める規則を維持する。現在は外枠まで実測5,998行ある。
(c)の必要性は未判定。3b-4aがmainへ入ったら§33どおりTot九欄を優先する。


## 315. 同じ総次数の実際の左右の基底値の接続（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§313の合成側と§312の二段側の実際の値を、同じ有限同値と全項の比較へ渡す。
既存構成の次数移送・係数移送・有限和の再添字付けの法則。各証明200行以内。

```lean
lemma vectorTensorAt_target_transport (K : Complex A) (n : ℕ)
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t u : ℤ)
    (ht : -(vectorDegree K n f : ℤ) = t) (hu : -(vectorDegree K n f : ℤ) = u)
    (htu : t = u) :
    (eqToHom (congrArg (fun z : ℤ => (power K n).X z) htu)).hom
      (vectorTensorAt K n f t ht) = vectorTensorAt K n f u hu

lemma positiveCompositeCutTerm_eq_nested_tensor (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    positiveCompositeCutTerm A S u v k c x =
      positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c) •
        vectorTensorAt (chains A S) (m + (n + 1))
          (fun a => ⟨(positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1,
            gen A S (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
              (S.map (SimplexCategory.mkHom
                (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x)⟩)
          (-((d + e + q : ℕ) : ℤ))
          (by rw [vectorDegree, positiveComposite_nested_degreeSum]
              have hn : m + n + (d + e) + q + 1 - (m + (n + 1)) = d + e + q

lemma cochainAction_composition_basis_eq_iterated (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) :
    (cochainAction A S (m + (n + 1))).f (-((d + e + q : ℕ) : ℤ))
      (ιTensorObj (Surjection.complex A (m + (n + 1))) (chains A S)
        (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) (-((d + e + q : ℕ) : ℤ)) (by omega)
        ((Surjection.complexXIso A (m + (n + 1)) (d + e)).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S m (n + 1) k).f (-((d + e + q : ℕ) : ℤ))
        (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A (n + 1)) (chains A S)
          (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) (-((d + e + q : ℕ) : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A (n + 1))
            (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
            ((Surjection.complexXIso A (m + 1) d).inv
              (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A (n + 1) e).inv
                (Surjection.basis A (n + 1) e (ULift.up v))) ⊗ₜ[A] gen A S q x))
```

最初は元のeqToHomの等式消去。第二は§303の同じ全項の等式を同じ全次数へ送る。
第三は元の全合成切断和と全二段切断和を、同じpositiveCompositeNestedEquivのsum_compで読む。
退化零項・全語次数・任意qを保持する。nullaryや全複体射の外延性をここで完成に数えない。


## 316. nullaryの全単体次数の有限点検と零次元色の法則（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

同じCutを水平・垂直の経路で読み、一般qのnullaryの準備を有限点検した。
`/tmp/bsw16/check-nullary-all-simplex-cuts.py`、語長1〜5・arity1〜3・q=0〜3、**9,794組**。
削除色が複数回現れる5,402組では、その色の出力次数は常に正。
出力次数零は2,617組（うち出力arity零の単位の場合1組）。
残り2,616組で同じ一頂点を削除・復元し、全ての残り色の元の頂点列が一致した。
削除語が退化する890組も保持し、両側の退化性を確認した。
同じ2,616組で符号指数の整数値そのものが一致した。有限点検はLeanの全称証明ではない。

一頂点削除の写像へ進む前に、零次元の指定色を元のCutで特定する法則を次の型で置く。
既存構成の有限位置・濃度・次数の法則で、各証明200行以内の見込み。

```lean
lemma outputDegree_zero_occurrenceCount {m q r : ℕ} (s : Cut m q)
    (w : Surjection.Word r (m + 1)) (k : Fin r) (h : outputDegree s w k = 0) :
    Surjection.occurrenceCount w.val k = 1

lemma outputDegree_zero_hi_eq_lo {m q r : ℕ} (s : Cut m q)
    (w : Surjection.Word r (m + 1)) (k : Fin r) (h : outputDegree s w k = 0)
    (p : Fin (m + 1)) (hp : w.val p = k) : hi s p = lo s p

lemma outputDegree_zero_iff_unique_position_and_point {m q r : ℕ} (s : Cut m q)
    (w : Surjection.Word r (m + 1)) (k : Fin r) :
    outputDegree s w k = 0 ↔
      ∃ p : Fin (m + 1), w.val p = k ∧
        (∀ j : Fin (m + 1), w.val j = k → j = p) ∧ hi s p = lo s p
```

出現回数の法則は既存の色別順位区間の厳密な順序を使う。
高さは同じ区間の位置集合が色別位置集合に含まれることと元のcard=hi-lo+1。
最後は色別位置集合の濃度1と水平射影の全射性、逆向きは同じ集合の等式。
削除の実際のCutの構成は、これらの法則の検証後に同じ元の座標で型を記録して進める。


## 317. 正の実際の左右の基底値の厳密な一致：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§315を検証した。同じ元の係数合成をcochainActionに入れた値と、元の四射の二段余作用の値が、
任意の可換環A・一般S・全語次数・任意q・実際の正規化生成元で一致した。
同じpositiveCompositeNestedEquivと全項の比較を使う。退化項を除かず、
元の圏の同じ加群成分の厳密な等式である。余代数の合成則を仮定していない。

全次数の移送では終点と両端の次数証明を明示し、元のeqToHomを保持した。
`m14-cochain-composition-basis-02.log`：3,228 jobs成功、対象警告0。
別の一回の鍵の `audit-m14-cochain-composition-basis.log`：
**3モジュール・12宣言、標準三公理のみ**、sorry・独自公理0。
各証明・ファイル200行以内、心拍数・再帰上限の増加なし。
全ハンドルの終了コード0を確認し、鍵は対象ビルド/小監査の間だけ使用して返した。
共有入口・共有監査・main作業木・drafts・界面・他レーンは変更なし。
rootビルド・大きい監査・常駐セッションなし。`git diff --check`成功。

登録対象（接頭辞 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 行数 |
| --- | ---: |
| VectorTensorTargetTransport | 32 |
| CompositeNativeTerms | 60 |
| CochainCompositionBasis | 59 |
| **計** | **151** |

M14実測は**25,153行**、L12aは**9,946行**。
§314の「正の枝の相殺を実際の左右の値へ戻す」80〜140行に対し151行で、上端より11行多い。
同じ次数移送の法則とその型を明示した分で、別の数学の項目を加えてはいない。
nullary・一般nの包装・全複体射への外延性はまだ残す。
L12a全体は未完、一覧12/48（追加4）、goalはactive。
外枠31,000行と§314の完成見込みの超過リスクは据え置き、残る範囲を削らない。
§316のnullaryの法則はこの取り込み点に数えず、対象ビルドで検証中。


## 318. nullaryの一頂点削除・挿入は既存の水平辺の同値で読む（次の型、紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§316の有限点検を辺集合にも拡張した。同じ全9,794組のうち、非空出力の一頂点削除2,616組で、
以下の削除辺番号・挿入辺位置が一致し、元の水平辺集合を厳密に復元した。
削除点が始点・終点の場合も含めた。新しい経路の模型は作らず、
既存 `BarrattEccles.horizontalInsertionEquiv` と元の `cutHorizontalEdge` を使う。
次はL12aの同じ有限対応の定義の記法と法則の型。まだ実装・型検査済みには数えない。
各証明200行以内の見込み。

```lean
def nullaryPointEraseCut {m q : ℕ} (s : Cut (m + 1) q) (p : Fin (m + 2)) : Cut m q :=
  let i : Fin (m + 1) := ⟨min p.val m, by have h := Nat.min_le_right p.val m; omega⟩
  (BarrattEccles.horizontalInsertionEquiv m q (cutHorizontalEdge s i)).symm
    ⟨s, s.val.orderEmbOfFin_mem s.property i⟩

def nullaryPointInsertionEdge {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    Fin (m + 1 + q) :=
  if hzero : p.val = 0 then ⟨0, by omega⟩
  else if htop : p.val = m + 1 then ⟨m + q, by omega⟩
  else
    let i : Fin m := ⟨p.val - 1, by have hp := p.isLt; omega⟩
    ⟨(cutHorizontalEdge t i).val + 1, by have hb := (cutHorizontalEdge t i).isLt; omega⟩

def nullaryPointInsertCut {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) : Cut (m + 1) q :=
  (BarrattEccles.horizontalInsertionEquiv m q (nullaryPointInsertionEdge t p) t).val

lemma nullaryPointInsertCut_hi_eq_lo {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    hi (nullaryPointInsertCut t p) p = lo (nullaryPointInsertCut t p) p

lemma nullaryPointEraseCut_insert {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    nullaryPointEraseCut (nullaryPointInsertCut t p) p = t

lemma nullaryPointInsertCut_erase {m q : ℕ} (s : Cut (m + 1) q) (p : Fin (m + 2))
    (h : hi s p = lo s p) :
    nullaryPointInsertCut (nullaryPointEraseCut s p) p = s

def nullaryPointCutEquiv (m q : ℕ) (p : Fin (m + 2)) :
    Cut m q ≃ {s : Cut (m + 1) q // hi s p = lo s p}
```

削除する水平辺の番号はmin(p,m)。内部では一頂点の直後の辺、終端では直前の辺を削る。
挿入位置は始点で0、終点でm+q、内部では元の直前の水平辺の直後。
この同じ辺集合を読む点検は成功したが、Leanの逆性・hi/loの全称証明はまだ供給していない。
区間の色の削除と残りの頂点列・元のcutSignへの適用は、この同値の後の法則として型を記す。
出力arity零はこのCutの型の外なので、元のnullaryAction・AW余単位の枝で別に扱い、捨てない。


## 319. nullaryの零次元色の三法則：検証済み、取り込み点

一覧：済み 12／全体 48（うち追加 4）

§316の三つの法則を実装した。元の色の出力次数が零なら、語の出現は一回だけであり、
指定された区間のhiとloは一致する。逆に唯一の出現の同じ一頂点なら出力次数は零。
同じ色別位置集合と同じ水平射影を使い、退化性を追加仮定にしていない。
依存するFinの型を書き換える代わりに、元の順位と零次数を数値として比較した。

`m14-nullary-zero-color-02.log`：1,142 jobs成功、対象警告0。
別の一回の鍵の `audit-m14-nullary-zero-color.log`：
**1モジュール・11宣言、標準三公理のみ**、sorry・独自公理0。
各証明・ファイル200行以内、心拍数・再帰上限の増加なし。
有限点検は§316・318の全9,794組で別に記録し、Leanの全称証明と混同しない。
終了コード0を確認し、鍵は対象ビルド/小監査の間だけ使用して返した。
共有入口・共有監査・main作業木・drafts・界面・他レーンは変更なし。
rootビルド・大きい監査・常駐セッションなし。`git diff --check`成功。

登録対象：`SerrePositivity.EInfinity.SimplexCuts.NullaryZeroColor`、**80行**。
M14実測は**25,233行**、L12aは**10,026行**。
§312・313・317・319のこの作業分は計10モジュール・641行、
小監査は計70宣言、標準三公理のみ。
§318の一頂点の有限対応は紙の型のままであり、実装や逆性の証明済みへ数えない。
nullaryの全対応・実余単位の評価・一般nの包装、後続の全複体射などは未完。
L12a全体は未完、一覧12/48（追加4）、goalはactive。

約25,000行の途中報告と完成見込みは§314。外枠31,000行は変更しない。
既知の工程の見込みでも外枠超過のリスクがあり、完備化後のP⁰はその数字にまだ含まれない。
完備化の(a)(b)の未供給の比較を仮定に足さず、(c)が必要と判明した場合の停止規則を保持する。
3b-4aのmain取り込みは未受領のまま。次は§318の同じ水平辺の挿入/削除による有限対応。


## 320. 同じ水平辺の前後の挿入と既存の全水平境界（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§318の内部の挿入は元の辺の直後、既存horizontalBoundaryFaceEquivは直前に挿入する。
元の辺が属しているので二つの大きい辺集合は同じであり、同じCutの厳密な一致として照合する。
まず有限辺集合でこの既存構成の法則を証明する。N=1〜7・全部分集合・全所属辺の769例で
前後のinsertPositionが同じ集合になることを点検した。各証明200行以内の見込み。

```lean
lemma insertPosition_adjacent_of_mem {N : ℕ} (S : Finset (Fin N)) (a : Fin N) (ha : a ∈ S) :
    BarrattEccles.insertPosition S a.castSucc = BarrattEccles.insertPosition S a.succ

lemma horizontalInsertionEquiv_adjacent_of_mem {m q : ℕ} (t : Cut m q)
    (a : Fin (m + q)) (ha : a ∈ t.val) :
    (BarrattEccles.horizontalInsertionEquiv m q (Fin.cast (by omega) a.castSucc) t).val =
      (BarrattEccles.horizontalInsertionEquiv m q (Fin.cast (by omega) a.succ) t).val
```

その後の照合・一頂点の法則の型は次。いずれも既存の同じ有限対応の法則である。

```lean
lemma nullaryPointInsertCut_eq_horizontalBoundaryFace {m q : ℕ}
    (t : Cut m q) (p : Fin (m + 2)) :
    nullaryPointInsertCut t p = (horizontalBoundaryFaceEquiv m q (p, t)).val.1

lemma horizontalBoundaryFaceEquiv_hi_eq_lo (m q : ℕ) (p : Fin (m + 2)) (t : Cut m q) :
    hi (horizontalBoundaryFaceEquiv m q (p, t)).val.1 p =
      lo (horizontalBoundaryFaceEquiv m q (p, t)).val.1 p
```

最初と最後の挿入は既存のendpointの同値そのもの。
内部では同じ昇順の水平辺の前後の挿入の等式を使い、元のCutに一致させる。
一頂点の法則は既存boundaryVertexKind_eq_horizontal_gapと
horizontalBoundaryFaceEquiv_horizontalから読む。
置き換えて済ませず、§318の元の挿入位置のCutとの厳密な等式を供給してから再利用する。


## 321. 挿入辺の三位置の評価と元の水平辺番号（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§318・320の逆性を同じ挿入辺で読むため、既存構成の三つの評価と水平辺の昇順番号を
証明分割として取り出す。各証明200行以内の見込み。

```lean
lemma nullaryPointInsertionEdge_first {m q : ℕ} (t : Cut m q) :
    nullaryPointInsertionEdge t 0 = 0

lemma nullaryPointInsertionEdge_last {m q : ℕ} (t : Cut m q) :
    nullaryPointInsertionEdge t (Fin.last (m + 1)) = (⟨m + q, by omega⟩ : Fin (m + 1 + q))

lemma nullaryPointInsertionEdge_interior {m q : ℕ} (t : Cut m q) (i : Fin m) :
    nullaryPointInsertionEdge t i.castSucc.succ =
      Fin.cast (by omega) (cutHorizontalEdge t i).succ

lemma cutHorizontalEdge_eq_of_horizontal {m q : ℕ} (s : Cut m q)
    (a : Fin (m + q)) (ha : a ∈ s.val) (i : Fin m)
    (hi : s.horizontal a.castSucc = i.castSucc) : cutHorizontalEdge s i = a

lemma nullaryPointInsertionEdge_mark_val {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    (horizontalBoundaryFaceEquiv m q (p, t)).val.2.val =
      (nullaryPointInsertionEdge t p).val + if p.val = m + 1 then 1 else 0
```

三つの辺位置は元の定義の条件分岐を評価するだけ。
番号の法則は元の辺集合のorderIsoOfFinの逆とhorizontal_before_cutHorizontalEdge。
最後は同じ始点・内部・終点の水平境界の指定頂点を読み、元の挿入辺位置へ合わせる。
辺を選び直したり、別の有限対応を同値として代用したりしない。


## 322. 元の挿入辺の番号と一頂点の全Cutの逆性（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§318の両逆と同値を実装する前に、同じ有限対応の二つの証明分割を記す。
既存構成の昇順番号と全射性の法則で、各証明200行以内の見込み。

```lean
lemma nullaryPointInsertCut_edge {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    cutHorizontalEdge (nullaryPointInsertCut t p)
      ⟨min p.val m, by have h := Nat.min_le_right p.val m; omega⟩ =
        nullaryPointInsertionEdge t p

lemma nullaryPointInsertCut_surjective {m q : ℕ} (s : Cut (m + 1) q) (p : Fin (m + 2))
    (h : hi s p = lo s p) : ∃ t : Cut m q, nullaryPointInsertCut t p = s
```

最初は§321の同じ指定頂点を、終端では挿入辺の直後、他では直前として読む。
既存step_of_memと水平辺の昇順番号の法則から、削除する辺が元の挿入辺と厳密に一致する。
これでhorizontalInsertionEquivの同じ左逆を適用する。
全射性は元の区間のmin'の頂点を水平境界として読み、既存horizontalBoundaryFaceEquivの逆へ渡す。
その同値が保つ元の水平座標がpであるため、同じ指定位置へ戻る。
右逆はこの全射性と左逆から得る。別のCutや選び直した対応を逆として置くものではない。


## 323. 元の削除辺の等式を所属証明つきの逆へ移す（法則の型、実装前）

一覧：済み 12／全体 48（うち追加 4）

§322の左逆で同じ水平辺の等式を使う際、逆写像の入力の所属証明も依存する。
その移送を、次の既存構成の法則として分割する。証明は辺の等式の消去で200行以内。

```lean
lemma horizontalInsertionEquiv_symm_congr {m q : ℕ} (s : Cut (m + 1) q)
    (a b : Fin (m + 1 + q)) (ha : a ∈ s.val) (hb : b ∈ s.val) (h : a = b) :
    (BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩ =
      (BarrattEccles.horizontalInsertionEquiv m q b).symm ⟨s, hb⟩
```

辺の番号を選び直さず、§322で証明する同じ挿入辺の等式を渡す。
右逆のための既存水平境界の逆像は、同じ等式を持つ変数に一般化して扱い、
大きい同値の定義を証明の途中で展開し続けない。


## 324. 削除しない色の全頂点列と退化raw語の零項（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§318の両逆を元の頂点列へ適用する。既存の同じ削除座標と色選択の法則で、各証明200行以内。
§316の全9,794組（削除の前後2,616組、退化削除890組を含む）の有限点検に対応する型は次。

```lean
lemma nullaryPointInsertCut_verticesList_remaining {m q r : ℕ} (t : Cut m q)
    (p : Fin (m + 2)) (v : Fin (m + 2) → Fin r) (c : Fin r) (hc : v p ≠ c) :
    verticesList t (Surjection.erase v p) c = verticesList (nullaryPointInsertCut t p) v c

lemma nullaryPointEraseCut_verticesList_remaining {m q r : ℕ} (s : Cut (m + 1) q)
    (p : Fin (m + 2)) (h : hi s p = lo s p)
    (v : Fin (m + 2) → Fin r) (c : Fin r) (hc : v p ≠ c) :
    verticesList (nullaryPointEraseCut s p) (Surjection.erase v p) c = verticesList s v c

lemma erased_word_nondegenerate_of_point_cut_nondegenerate {m q r : ℕ}
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2)) (p : Fin (m + 2))
    (hpoint : hi s p = lo s p) (hcut : Nondegenerate s v.val) :
    Surjection.Nondegenerate (Surjection.erase v.val p)
```

元の水平境界の全削除座標とdeletedTrace_eq_of_horizontal_coordinatesを再利用し、
削除色以外ではdeletedVerticesListが元の全verticesListであることを使う。
削除語の退化については既存other_face_not_mono_horizontal_degenerateが同じ残り色の
非単射面を与えるので、元のfaces_mono_iffと矛盾する。新しい退化の幾何を作り直さない。
色をまだrenumberせず元の同じ色で述べる。nullaryの実出力のarityへ移すときに
同じ残り色の埋め込みと照合する工程は別に残す。

## 325. 一頂点の全Cutの同値と残り色の全頂点列（検証済み）

一覧：済み 12／全体 48（うち追加 4）

§318〜324の元の挿入・削除の両逆、水平境界との厳密な一致、残り色の全頂点列、退化削除の零項を検証した。
新規9本487行。M14実測25,720行、うちL12a 10,513行、外枠31,000行まで5,280行。
L12aは未完了。nullaryはここまで567行で、端点・caesura・符号、色の番号の移送、実際の余単位と全arityの包装が残る。
§314の完成見込みが外枠に収まらないという注意はそのまま。完備化後のP⁰の未評価分も含め、収まるとの主張はしていない。

登録候補（すべて `SerrePositivity.EInfinity.SimplexCuts.`）：

|モジュール|行数|
|---|---:|
|NullaryPointCuts|34|
|AdjacentHorizontalInsertions|58|
|NullaryPointInsertionValues|50|
|HorizontalEdgeRanks|30|
|NullaryPointBoundaryComparison|71|
|NullaryPointMark|44|
|NullaryPointInverse|113|
|NullaryPointVertexLists|52|
|NullaryPointNondegenerate|35|

対象ビルドは `m14-nullary-point-inverse-02.log`（2,271 jobs）と
`m14-nullary-point-vertices-01.log`（2,314 jobs）まで成功、対象の警告0。
小監査 `audit-m14-nullary-point-equivalence.log`（7本62宣言）と
`audit-m14-nullary-point-vertices.log`（2本4宣言）は標準三公理のみ、sorry・独自公理0。
各ビルド・監査ごとに鍵を取り返却。共有の入口・監査は編集していない。

次の符号の照合に先立ち、surjective・nondegenerateを仮定しないraw語でも有限点検した。
長さ2〜5、色数1〜3、q=0〜2、一度だけ出る削除色で区間が一点となる5,090組について、
残る全区間の両端、全caesura、元の整数の符号指数が削除後と一致した。
これはLeanの証明の代用ではなく、次の型を元の構成の法則として切り出す前の点検。

## 326. 一点削除の全区間の両端と区切り（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

§325の5,090組の点検に対応し、同じ切断の両端と同じraw語のcaesuraを比較する。
以下は既存構成の法則・証明分割で、一覧の項目を増やさない。各証明200行以内。

```lean
lemma lo_eq_of_coordinate_cover {m n q : ℕ} (s : Cut m q) (t : Cut n q)
    (ρ : Fin (n + q + 1) → Fin (m + q + 1)) (φ : Fin (n + 1) → Fin (m + 1))
    (hφ : Function.Injective φ)
    (hh : ∀ j, s.horizontal (ρ j) = φ (t.horizontal j))
    (hv : ∀ j, s.vertical (ρ j) = t.vertical j)
    (i : Fin (n + 1))
    (hcover : ∀ j, s.horizontal j = φ i → ∃ k, ρ k = j) : lo t i = lo s (φ i)

lemma lo_eq_of_horizontal_deleted_coordinates {m q : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hh : ∀ j : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) =
        a.succAbove (t.horizontal j))
    (hv : ∀ j : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) = t.vertical j)
    (i : Fin (m + 1)) : lo t i = lo s (a.succAbove i)

lemma nullaryPointEraseCut_endpoints {m q : ℕ} (s : Cut (m + 1) q) (p : Fin (m + 2))
    (h : hi s p = lo s p) (i : Fin (m + 1)) :
    lo (nullaryPointEraseCut s p) i = lo s (p.succAbove i) ∧
      hi (nullaryPointEraseCut s p) i = hi s (p.succAbove i)

lemma not_caesura_of_unique {l r : ℕ} (v : Fin (l + 1) → Fin r) (p : Fin (l + 1))
    (hu : ∀ j, v j = v p → j = p) : ¬ Surjection.Caesura v p

lemma caesura_erase_unique {l r : ℕ} (v : Fin (l + 1) → Fin r) (p : Fin (l + 1))
    (hu : ∀ j, v j = v p → j = p) (i : Fin l) :
    Surjection.Caesura (Surjection.erase v p) i ↔ Surjection.Caesura v (p.succAbove i)
```

左端は既存右端の証明を同じfiberのmin'とlo_eq_of_boundで読むだけ。
両端は元のhorizontalBoundaryFaceEquivの全削除座標を使う。
区切りはcaesura_erase_iff_witnessを使い、唯一の削除色は将来の同色位置にならないことを読む。

## 327. 一点削除の区間重みと元の整数符号（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

§326の全端点・caesuraから、同じ元の整数の指数を比較する。各証明200行以内。
有限点検は§325の5,090組で指数の完全な等式まで行った。偶奇だけへの弱化はしない。
以下で `hu : ∀ j, v j = v p → j = p` は、元の削除色が一度だけ出ること。

```lean
lemma intervalLength_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) : intervalLength s v p = 0

lemma intervalLength_erase_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) (i : Fin (m + 1)) :
    intervalLength (nullaryPointEraseCut s p) (Surjection.erase v p) i =
      intervalLength s v (p.succAbove i)

lemma positionExponent_erase_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) :
    positionExponent (nullaryPointEraseCut s p) (Surjection.erase v p) = positionExponent s v

lemma permutationExponent_erase_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) :
    permutationExponent (nullaryPointEraseCut s p) (Surjection.erase v p) =
      permutationExponent s v

lemma cutSign_erase_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) :
    cutSign (nullaryPointEraseCut s p) (Surjection.erase v p) = cutSign s v
```

削除位置の位置指数はcaesuraでないため零。二重和の削除位置の全項は区間重み零で消える。
残りの順序は元のFin.succAboveのstrictMono、色の値は同じerase_apply。
新しい符号規約や別の写像へ置き換えず、元の有限和の再添字だけを使う。


## 328. 一点削除の全端点・区切り・元の整数符号（検証済み）

一覧：済み 12／全体 48（うち追加 4）

§326〜327の法則6本を検証した。元の順序・全区間の端点・全caesuraを保ち、
位置指数と逆転指数はそれぞれ自然数として厳密に一致する。
符号の偶奇やホモトピー圏の等式への置き換えはしていない。L12aは未完了。

|登録候補（すべてSimplexCuts）|行数|
|---|---:|
|DeletedIntervalMinima|38|
|HorizontalDeletionMinima|44|
|NullaryPointEndpoints|33|
|NullaryPointCaesuras|35|
|NullaryPointWeights|32|
|NullaryPointSigns|54|

今回236行。M14実測25,956行、L12a 10,749行、外枠31,000行まで5,044行。
対象ビルド m14-nullary-point-endpoints-01.log（2,311 jobs）と
m14-nullary-point-signs-02.log（2,313 jobs）は成功。未使用simp引数は修正し対象警告0。
小監査 audit-m14-nullary-point-signs.log は6本14宣言・標準三公理のみ、sorry・独自公理0。
ビルドと監査は各回で鍵を返却。共有の入口・監査は変更していない。

## 329. 残り色を元の順序で番号づけ直す法則（実装前）

一覧：済み 12／全体 48（うち追加 4）

nullaryの出力arityへ戻すとき、色の順序単射で元の符号と頂点列を比較する。
削除色kの補集合にはFin.succAboveOrderEmb kを使う。
まず以下を一般の順序単射の既存構成の法則として切り出す（各証明200行以内）。
有限点検：色数1〜3、移し先は4まで、長さ1〜4の全raw語と全昇順の色埋め込み940組で、
全caesuraと全色対の狭義順序が保存されることを確認した。

```lean
lemma caesura_comp_injective {l r R : ℕ} (v : Fin l → Fin r) (φ : Fin r → Fin R)
    (hφ : Function.Injective φ) (i : Fin l) :
    Surjection.Caesura (φ ∘ v) i ↔ Surjection.Caesura v i

lemma intervalLength_comp_injective {m q r R : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (φ : Fin r → Fin R) (hφ : Function.Injective φ)
    (i : Fin (m + 1)) : intervalLength s (φ ∘ v) i = intervalLength s v i

lemma cutSign_comp_strictMono {m q r R : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (φ : Fin r → Fin R) (hφ : StrictMono φ) :
    cutSign s (φ ∘ v) = cutSign s v

lemma verticesList_comp_injective {m q r R : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (φ : Fin r → Fin R) (hφ : Function.Injective φ)
    (c : Fin r) : verticesList s (φ ∘ v) (φ c) = verticesList s v c
```

区切りは同色の単射性、逆転指数はhφ.lt_iff_lt、頂点列は元のcolorPositionsの等式だけを使う。
Surjection.Wordの全射性を、色数を増やすこの補助に要求しない。

## 330. 実際の空語合成の位置と色を同じ削除へ戻す（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

§329の色の埋め込みと実際のnullaryRawWordをつなぐため、既存の二つの位置の表示を比較する。
新しい有限対応を選ばず、元のcompositeOuterPositionの狭義単調性と有限自己順序単射の一意性を使う。
削除色が一度だけ出る場合の型を明示する。各証明200行以内。

```lean
lemma succAbove_remainingPosition_nullary (m : ℕ) (k : Fin (m + 1))
    (a : {j : Fin (m + 1) // j ≠ k}) :
    k.succAbove (BarrattEccles.remainingPosition m 0 k a) = a.val

lemma compositeOuterPosition_nullary_erase {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (p : Fin (m + 1 + d)) (hu : ∀ j, u.val j = k → j = p) (i : Fin (m + d))
    (hne : u.val (Fin.cast (by omega : m + d + 1 = m + 1 + d)
      ((Fin.cast (by omega : m + 1 + d = m + d + 1) p).succAbove i)) ≠ k) :
    IntervalCuts.compositeOuterPosition u v k r
      (Fin.cast (by omega : m + d + 1 = m + 1 + d)
        ((Fin.cast (by omega : m + 1 + d = m + d + 1) p).succAbove i)) hne = i
```

hneqは残る位置が削除色でないことの証明で、huから証明する同じ命題。
それを別の数学的な条件として最終定理へ足さない。
残り全位置を元の順序でcompositeOuterPositionへ送り、同じFin(m+d)の自己順序単射を得る。
既存StrictMono.apply_eqからその写像は各iを固定する。色はremainingPositionの元の番号公式を読むだけ。

## 331. 完備化後のP⁰の三案：有限arityで延ばす作用とprimitiveを分ける（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§267・282・296の続き。A4の定義を読み直したが、directPerfectionValueは依然として
実際の反射prismCAlgCompletionを施した頂点であり、普通の完備化した複体を定義として
差し替えることはできない。仮定・drafts・界面・完備化のLeanは追加していない。

### 331.1 (a) 有限arityの作用の連続延長に必要な一様性

項別平坦かつK平坦な厳密B線形BE模型Kが得られた場合を検収する。
固定したarity、operad次数、入力の各次数に対する作用はB多重線形写像である。
入力x_iとy_iがそれぞれd^rを法として一致するなら、有限の望遠和

    T(x_1,…,x_s)-T(y_1,…,y_s)
      = Σ_i T(y_1,…,y_{i-1},x_i-y_i,x_{i+1},…,x_s)

の各項はd^r倍。この合同の指数は入力元に依存しない。
同じd進完備化の普遍性を各固定次数で使えば、有限個の入力の積上で同じ作用を延ばす候補となる。
operadの鎖の入力は有限の線形結合なので、operad全体の無限和を完備化の外で足す必要はない。
元の作用の単位・置換・合成・微分の有限の恒等式も、同じ合同と分離性で検収する筋がある。
ただしこれは候補の証明の筋であり、必要な厳密BE完備化の構成・分離性・nativeな比較の
新定理を48本の「法則」として自己承認して実装したという意味ではない。

P⁰そのものはB線形である必要はない。p入力の対角評価ではb倍がb^p倍になる。
元のFrobeniusのd↦d^pも、商の添字r↦prの共終な変更として記録する。
B線形自己射であるとの追加条件を置いて一致させない。

### 331.2 (a) primitiveの延長では「閉元だけ」の恒等式は不足

上の有限多重線形の合同は、L43bの同じ明示的原始元が**全鎖の有限式**であり、
微分にdaを含む項を残した恒等式まで供給する場合に適用する。
閉元ごとに境界の逆像を選んだ関数へは適用できない。
また、完成した鎖の任意の閉元をrawな閉元の極限と仮定しない。
全鎖の式を延ばしてから閉条件を入れる必要があるという§296の穴は残る。
元のnativeなFrobeniusの辺をこの同じ模型の射で表す比較も未供給。
作用を延ばせることと、その比較が同じ辺を表すことを分けて検収する。

### 331.3 (b) 単位での消去が代わりに使えるか

κ[t]→κ[[t]]のπ_0での非全射性は変わらず、coconnective性だけでの単位の消去はできない。
商の塔への射による検出は別案だが、Tor由来の元とlim¹を扱う§223.3の義務が残る。
特に(a)の作用の連続性だけから、π_nを逆極限と交換したり、商での同じP⁰の比較を
無料で得たりはしない。この案に追加のtorsion消滅仮定を足さない。

### 331.4 (c) coherentなP⁰が必要と判明したか

今確認できる不足は、(a)の模型と指定辺の比較および全鎖のprimitiveの検収、
(b)の実際のderived商での同じ演算・同じFrobeniusの比較である。
有限arityの連続延長の筋はcoherentなSp値P⁰を前提としていないので、
現時点では両案が不可能との結論や(c)への移行は出さない。
全鎖の式が作れない／指定対象と辺へ比較できないと分かった時点では、§32どおり止める。
これらの未実装分は§314の完成見込みの数値にも未計上で、外枠に収まると見込んで隠さない。

## 332. 実際の空語のraw合成語の値を同じ削除色へ戻す（実装前）

一覧：済み 12／全体 48（うち追加 4）

§330の元の位置の等式を、同じnullaryRawWord_outerPositionへ適用する。
以下は既存構成の値の法則で、証明200行以内。huから残る位置の色≠kを証明し、
§330のhneを最終主張の仮定として残さない。

```lean
lemma nullaryRawWord_erase_value {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (p : Fin (m + 1 + d)) (hu : ∀ j, u.val j = k → j = p) (i : Fin (m + d)) :
    k.succAbove (IntervalCuts.nullaryRawWord u v k r i) =
      u.val (Fin.cast (by omega : m + d + 1 = m + 1 + d)
        ((Fin.cast (by omega : m + 1 + d = m + d + 1) p).succAbove i))
```

符号の照合には§329の順序単射の法則を使う。
compositeOuterPositionの式を結果の添字iの下へ依存するまま書き換えず、
同じraw語へ評価する合同の等式を通してから元の色の値を読む。

## 333. 削除後の実際の色づけへ移す符号と全頂点列（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

§327・329を同じ残り色の族へ適用する。hvは§332で実際のnullaryRawWordに対して
証明した色の値の等式に対応する条件で、任意の別の族の選択を結論にしない。
型のサイズを保つためraw語の長さの自然数をここではm+2と書く。
各証明200行以内、同じ既存構成の値と符号の照合法則。

```lean
lemma nullaryPointEraseCut_cutSign_relabel {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin (r + 1)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1))
    (hpoint : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p)
    (hv : ∀ i, k.succAbove (w i) = v (p.succAbove i)) :
    cutSign (nullaryPointEraseCut s p) w = cutSign s v

lemma nullaryPointEraseCut_verticesList_relabel {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin (r + 1)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v p = k)
    (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w i) = v (p.succAbove i)) (c : Fin r) :
    verticesList (nullaryPointEraseCut s p) w c = verticesList s v (k.succAbove c)
```

元の圏の値の等式であり、符号も全頂点列も新しい選択へ変えない。

## 334. 一点削除の前後の正規化零項（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

元の正規化零項を保つため、同じ削除座標によるpairの単射性を両方向へ移す。
これはL12aの既存の非退化性の定義を同じ有限集合の削除で読む法則。各証明200行以内。
有限点検は§316の元の全切断の退化判定と、§325のraw語の一点削除に対応する。

```lean
lemma nondegenerate_iff_horizontal_deleted_coordinates {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Fin (m + 2) → Fin r)
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hh : ∀ j : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) =
        a.succAbove (t.horizontal j))
    (hv : ∀ j : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) = t.vertical j)
    (hu : ∀ j, v j = v a → j = a) :
    Nondegenerate t (Surjection.erase v a) ↔ Nondegenerate s v

lemma nullaryPointEraseCut_nondegenerate_iff {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2)) (hpoint : hi s p = lo s p)
    (hu : ∀ j, v j = v p → j = p) :
    Nondegenerate (nullaryPointEraseCut s p) (Surjection.erase v p) ↔ Nondegenerate s v
```

元のpairの削除位置以外はhh・hvで同じ削除後のpairへ対応する。
削除頂点の色が残るpairの色と一致すればhuによってa.succAboveの値がaとなり矛盾する。
従って正規化で零となる場合も含めた同値を得る。

## 335. 残り色の番号を詰め直した正規化零項（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

§334の同値を、実際の色の番号を詰め直した語へ適用するための既存構成の法則。
§329と同じ単射を使い、各証明200行以内。新しい非退化性を定義しない。

```lean
lemma nondegenerate_comp_injective {m q r R : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (φ : Fin r → Fin R) (hφ : Function.Injective φ) :
    Nondegenerate s (φ ∘ v) ↔ Nondegenerate s v

lemma nullaryPointEraseCut_nondegenerate_relabel {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin (r + 1)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1))
    (hpoint : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p)
    (hv : ∀ i, k.succAbove (w i) = v (p.succAbove i)) :
    Nondegenerate (nullaryPointEraseCut s p) w ↔ Nondegenerate s v
```

最初はpairの第一成分だけへの単射の合成。後者はその同値を元のFin.succAboveへ適用し、
hvで同じ削除語へ戻して§334を使うだけ。


## 336. 実際の空語合成の位置・色・元の正規化零項（検証済み、取り込み点）

一覧：済み 12／全体 48（うち追加 4）

§329〜335の型を検証した。実際のnullaryRawWordとcompositeOuterPositionを使い、
同じ一出現を削除する位置の厳密な一致、元の順序で詰めた残り色の値、
同じ全頂点列と元の整数符号、元の正規化零項の両方向の同値までつながった。
実際の余単位を作用の四つの射へ通す計算と全arityの包装はまだ残り、L12a完了とはしない。

|登録候補（すべてSerrePositivity.EInfinity.SimplexCuts）|行数|
|---|---:|
|OrderedColorEmbeddings|47|
|NullaryRawPositions|72|
|NullaryRawValues|44|
|NullaryPointRelabel|50|
|HorizontalDeletionNondegenerate|63|
|NullaryPointNormalization|31|
|NullaryPointRelabelNormalization|45|

今回352行、M14実測26,308行、L12a 11,101行、外枠31,000行まで4,692行。
対象ビルドはm14-ordered-color-embeddings-03.log（1,140 jobs）、
m14-nullary-raw-positions-03.log（2,802 jobs）、m14-nullary-raw-values-01.log（2,803 jobs）、
m14-nullary-point-relabel-01.log（2,316 jobs）、
m14-nullary-point-normalization-01.log（2,309 jobs）、
m14-nullary-point-relabel-normalization-02.log（2,310 jobs）まで成功、対象警告0。
小監査audit-m14-nullary-relabel-normalization-02.logは7本31宣言・標準三公理のみ、sorry・独自公理0。
それぞれ有限の一回のビルド・監査ごとに鍵を取り返却した。共有入口・監査の変更なし。

完備化後のP⁰の三案の追加の紙の検討は§331。
(a)の固定arity・次数の有限多重線形式の合同と、全鎖のprimitiveの延長を区別した。
指定native対象とFrobeniusの比較は未証明。(b)の単位の全射性は依然として一般に偽。
両方が不可能と判明した(c)とはまだ判定していない。追加仮定で穴を隠していない。

## 337. 零arityの実際の作用を元の余単位へ戻す（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

nullaryの二段余作用を計算する前に、全整数のcomponentから作った実際のcochainActionの
零arityが、定義で指定した元のnullaryActionと同じ複体射であることを取り出す。
これはcomponentの定義とtensorLiftの斉次成分を読む既存構成の法則で、各証明200行以内。

```lean
lemma cochainAction_zero_eq_nullaryAction (A : Type u) [CommRing A] (S : SSet.{0}) :
    cochainAction A S 0 = nullaryAction A S
```

同じ直和の全整数の斉次成分で比較し、元のcurryされた加群テンソル射へ戻す。
ホモトピー圏へ移さず、実際の複体射の等式で使う。

## 338. 同じ空語係数の零次augmentationの値（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

元のAW余単位へ通す係数の値を取り出す。次数延長の指定比較と、
元のChainComplex.toSingle₀Equivの零次成分の法則だけを使う。各証明200行以内。

```lean
lemma nullaryCoefficientAugmentation_zero_apply (A : Type u) [CommRing A]
    (w : Surjection.degreeModule A 0 0) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((nullaryCoefficientAugmentation A).f 0 ((Surjection.complexXIso A 0 0).inv w)) =
      Surjection.zeroAugmentation A 0 w

lemma nullaryCoefficientAugmentation_basis_zero (A : Type u) [CommRing A]
    (v : Surjection.BasisWord 0 0) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((nullaryCoefficientAugmentation A).f 0 ((Surjection.complexXIso A 0 0).inv
        (Surjection.basis A 0 0 (ULift.up v)))) = (1 : A)
```

複体の台の選び直しや係数のaugmentationの変更は行わない。

## 339. 零arityの実際の複体射と空語係数の値（検証済み、取り込み点）

一覧：済み 12／全体 48（うち追加 4）

§337〜338の3法則を検証した。全整数のtensorLiftの零arityは元のnullaryActionと
同じ複体射であり、指定次数延長とsingleの比較で元の空語係数のaugmentation値を読む。
元の圏での厳密な等式を使い、ホモトピー圏へ弱めていない。

登録候補（すべてSerrePositivity.EInfinity.SimplexCuts）：

|モジュール|行数|
|---|---:|
|CochainNullaryAction|36|
|NullaryCoefficientValues|48|

今回84行。M14実測26,392行、L12a 11,185行、外枠31,000行まで4,608行。
L12aは未完了で、実際のnullaryの余単位の二段適用の値・全有限和・全arityの包装が残る。
一覧の法則の証明分割であり、新しいIDは追加していない。

対象ビルドm14-cochain-nullary-action-01.log（2,612 jobs）、
m14-nullary-coefficient-values-03.log（2,342 jobs）が成功し、対象警告0。
小監査audit-m14-cochain-nullary-values.logは2本4宣言・標準三公理のみ、sorry・独自公理0。
ビルド・監査ごとに鍵を取り返却。mainの作業木・共有入口・共有監査は変更していない。
§325以降の登録候補は計24本、今回の検証はすべて各対象と小監査だけで行った。

並行する完備化の三案は§331に記した。(c)が必要との判定にはまだ至っていない。
§314の完成見込みが外枠に収まらない懸念と完備化の未評価分は残し、
完成を主張したり追加仮定で隠したりしていない。次は元の余単位の実際の二段値から再開する。

## 340. 実際の空語作用の基底値をAW余単位へ戻す（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

§337〜338を使い、同じ空語基底の全整数の作用を元のAW余単位へ戻す。
以下は同じ構成の評価の法則で、各証明200行以内。新しい作用は定義しない。

```lean
lemma cochainAction_nullary_basis_apply (A : Type u) [CommRing A] (S : SSet.{0})
    (v : Surjection.BasisWord 0 0) (t : ℤ) (y : (chains A S).X t) :
    (cochainAction A S 0).f t
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 t t (zero_add t)
        ((Surjection.complexXIso A 0 0).inv
          (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] y)) =
      (AlexanderWhitney.cochainCounit A S).f t y

lemma cochainAction_nullary_basis_generator_zero (A : Type u) [CommRing A] (S : SSet.{0})
    (v : Surjection.BasisWord 0 0) (x : S _⦋0⦌) :
    (cochainAction A S 0).f 0
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 0 0 rfl
        ((Surjection.complexXIso A 0 0).inv
          (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] gen A S 0 x)) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)

lemma cochainAction_nullary_basis_eq_zero_of_ne_zero (A : Type u) [CommRing A]
    (S : SSet.{0}) (v : Surjection.BasisWord 0 0) (t : ℤ) (ht : t ≠ 0)
    (y : (chains A S).X t) :
    (cochainAction A S 0).f t
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 t t (zero_add t)
        ((Surjection.complexXIso A 0 0).inv
          (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] y)) = 0
```

最初はaugmentationの基底値一を左単位子の逆の式へ戻す。
零次生成元は同じcochainCounit_generator_zero、零以外の次数は元のsingle複体の零対象で消す。
指定した係数、同じ入力の全次数、同じ元の複体射を保持する。

## 341. 元の出力族への実際の空語作用の代入（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

内側作用の値を仮定として残さず、§340の実際の値を既存の斉次テンソル評価へ渡す。
以下は同じ射の評価の法則・証明分割で、各証明200行以内。
零次のhxは選んだ因子が同じ零単体の生成元であるという値の等式。
外側の全切断和へ適用するときは実際のface族から供給し、最終合成則の仮定に足さない。

```lean
lemma tensorCoInsertionAction_cochain_nullary_positive (A : Type u) [CommRing A]
    (S : SSet.{0}) {m : ℕ} (v : Surjection.BasisWord 0 0) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (hpos : 0 < (f i).1) (z : ℤ)
    (hz : 0 + (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ))) = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) m 0 i
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (m + 1)) 0
        (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
          (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ))) z hz
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f _
            (by have h := vectorDegree_family_blocks (chains A S) f i; omega))) = 0
```

零次の版は同じ左辺でhposを `x : S _⦋0⦌` と `hx : f i = ⟨0, gen A S 0 x⟩` に替え、
右辺を次にする（これが Lean の同じ終域の型）：

```lean
vectorTensorAt (chains A S) (m + 0)
  (insertionFamily f (fun j : Fin 0 => Fin.elim0 j) i) z
  (by rw [vectorDegree_insertionFamily]
      have hi : (f i).1 = 0 := congrArg Sigma.fst hx
      change -(vectorDegree (chains A S) i.val (prefixFamily f i) + 0 +
        vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℕ) = z
      omega)
```

正次数はFin 0添字の空和を既存vector_sum_applyへ渡す。
零次は同じvector_applyへ空の族と整数係数一を渡す。
内側係数次数は零なので、元の二つのKoszul交換符号はここで一となる。


## 342. 外側の実際の全切断和を内側の全arityで読む（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

既存iteratedCochainAction_basis_outer_cut_sumの証明は、外側の正arityの作用の
全切断和と、内側の射への線形性だけを使う。内側の正arityを必要としないため、
公開宣言を変更せず同じ法則を全arityの新しい名前で取り出す。各証明200行以内。

```lean
lemma iteratedCochainAction_basis_outer_cut_sum_all (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -(q : ℤ) = z) :
    (iteratedCochainAction A S m n k).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A n) (chains A S)
        (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A n)
          (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
          ((Surjection.complexXIso A (m + 1) d).inv
            (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (Surjection.complexXIso A n e).inv
              (Surjection.basis A n e (ULift.up v))) ⊗ₜ[A] gen A S q x)) =
      (-(d : ℤ) * -(e : ℤ)).negOnePow •
        ∑ s : Cut (m + d) q, cutSign s (positiveWord u).val •
          (tensorCoInsertionAction (chains A S) (Surjection.complex A n) m n k
            (cochainAction A S n)).f z
            (ιTensorObj (Surjection.complex A n) (power (chains A S) (m + 1))
              (-(e : ℤ)) (-(d : ℤ) + -(q : ℤ)) z (by omega)
              ((Surjection.complexXIso A n e).inv
                (Surjection.basis A n e (ULift.up v)) ⊗ₜ[A]
                vectorTensorAt (chains A S) (m + 1)
                  (fun a => ⟨outputDegree s (positiveWord u) a,
                    gen A S (outputDegree s (positiveWord u) a)
                      (S.map (face s (positiveWord u) a).op x)⟩)
                  (-(d : ℤ) + -(q : ℤ))
                  (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]
                      have hnat : m + d + q + 1 - (m + 1) = d + q
```

ここでは内側射の値を計算したとはしない。空語の場合の各項には§341の実際の評価を適用する。
外側・内側の元の係数交換と全切断、全整数の同じ終域を保つ。


## 343. 空語の零次評価のSigma入力を一般化する証明分割（実装前）

一覧：済み 12／全体 48（うち追加 4）

§341のhxを、依存する整数次数の下で直接書き換え続けない。
同じ値の等式を持つ独立なSigma入力yへ一般化し、等式を消去して§340を適用する。
次が局所的な証明分割の型（gは§341の空の族）。新しい数学・仮定・一覧IDはない。

```lean
∀ (y : Σ d : ℕ, (chains A S).X (-(d : ℤ)))
  (hy : y = ⟨0, gen A S 0 x⟩)
  (hg : -(vectorDegree (chains A S) 0 g : ℤ) = 0 + -(y.1 : ℤ)),
  (cochainAction A S 0).f (0 + -(y.1 : ℤ))
    (ιTensorObj (Surjection.complex A 0) (chains A S) 0 (-(y.1 : ℤ))
      (0 + -(y.1 : ℤ)) rfl
      ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] y.2)) =
    (1 : ℤ) • vectorTensorAt (chains A S) 0 g (0 + -(y.1 : ℤ)) hg
```

正次数の分岐では同じ整数次数 `0 + -((f i).1 : ℤ)` の零対象を直接使い、
先に加算を消した別の次数へ変換する過程でgetColimitCoconeの内部を展開しない。


## 344. 元の入力次数で読む空語代入の法則（実装前）

一覧：済み 12／全体 48（うち追加 4）

外側切断和の指定入力次数へ§341を適用するため、同じ全次数の等式を引数に明示する。
既存vectorDegree_family_blocksで二つの入力次数が等しいことを示し、その等式を消去するだけ。
各証明200行以内。正規化零項や空語の値の仮定を新たに足さない。

```lean
lemma tensorCoInsertionAction_cochain_nullary_positive_at (A : Type u) [CommRing A]
    (S : SSet.{0}) {m : ℕ} (v : Surjection.BasisWord 0 0) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (hpos : 0 < (f i).1) (p z : ℤ)
    (hp : -(vectorDegree (chains A S) (m + 1) f : ℤ) = p)
    (hz : 0 + p = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) m 0 i
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (m + 1)) 0 p z hz
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f p hp)) = 0
```

```lean
lemma tensorCoInsertionAction_cochain_nullary_zero_at (A : Type u) [CommRing A]
    (S : SSet.{0}) {m : ℕ} (v : Surjection.BasisWord 0 0) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (x : S _⦋0⦌) (hx : f i = ⟨0, gen A S 0 x⟩) (p z : ℤ)
    (hp : -(vectorDegree (chains A S) (m + 1) f : ℤ) = p)
    (hz : 0 + p = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) m 0 i
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (m + 1)) 0 p z hz
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f p hp)) =
      vectorTensorAt (chains A S) (m + 0)
        (insertionFamily f (fun j : Fin 0 => Fin.elim0 j) i) z
        (by rw [vectorDegree_insertionFamily]
            have hi : (f i).1 = 0 := congrArg Sigma.fst hx
            change -(vectorDegree (chains A S) i.val (prefixFamily f i) + 0 +
              vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℕ) = z
            have hf := vectorDegree_family_blocks (chains A S) f i
            omega)
```



## 345. 削除色が複数出るときの実際の二段余作用の零性（実装前）

一覧：済み 12／全体 48（うち追加 4）

全切断について指定色の出力次数零なら既存outputDegree_zero_occurrenceCountが一出現を与える。
従って一出現でない分岐では全項が§344の正次数の零性で消える。各証明200行以内。
同じ元の四つの射を合成した実際の二段余作用について、型は次。

```lean
lemma iteratedCochainAction_nullary_repeated_basis_eq_zero (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord 0 0)
    (k : Fin (m + 1)) (hcount : Surjection.occurrenceCount u.val k ≠ 1) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(0 : ℤ) + -(q : ℤ) = z) :
    (iteratedCochainAction A S m 0 k).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A 0) (chains A S)
        (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A 0)
          (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
          ((Surjection.complexXIso A (m + 1) d).inv
            (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (Surjection.complexXIso A 0 0).inv
              (Surjection.basis A 0 0 (ULift.up v))) ⊗ₜ[A] gen A S q x)) = 0
```

positiveWordの語長の等式移送は既存positiveWord_occurrenceCountで比較する。
空語合成の左辺も既存compositionOnWords_nullary_of_count_ne_oneで零となるので、
最終の合成則のこの分岐には追加仮定や非零項だけへの制限を入れない。


## 346. 反復出現の分岐の元の圏での実際の合成則（実装前）

一覧：済み 12／全体 48（うち追加 4）

§345の実際の右辺の零性と、既存compositionOnWords_nullary_of_count_ne_oneを連結する。
単に一方の零性を仮定する形でなく、元の係数合成を作用させた左辺と四射の右辺の等式を述べる。
これはL12aの同じ合成則の分岐、各証明200行以内。

```lean
lemma cochainAction_composition_nullary_repeated_eq_iterated (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord 0 0)
    (k : Fin (m + 1)) (hcount : Surjection.occurrenceCount u.val k ≠ 1) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(0 : ℤ) + -(q : ℤ) = z) :
    (cochainAction A S (m + 0)).f z
      (ιTensorObj (Surjection.complex A (m + 0)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) z (by omega)
        ((Surjection.complexXIso A (m + 0) d).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) =
    (iteratedCochainAction A S m 0 k).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A 0) (chains A S)
        (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A 0)
          (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
          ((Surjection.complexXIso A (m + 1) d).inv
            (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (Surjection.complexXIso A 0 0).inv
              (Surjection.basis A 0 0 (ULift.up v))) ⊗ₜ[A] gen A S q x))
```

## 347. 完備化後のP⁰の三案：(a)を完備部分圏の余極限として読む場合（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

A2/DerivedPrismaticCohomology.leanのprismCompleteReflection・prismCompletionUnitを読み直した。
実際のdraftsはL ⊣ Iというnativeな反射の型を置いているが、その反射自体はまだsorryである。
以下は**反射としての仕様からの形式的な検討**で、本体で証明済みの比較とはしない。

(a)で「各項を完備化した模型」を取るとき、二つの余極限を区別する必要がある。

- ambient CAlg_Aで項ごとの完備化の余極限を取る形は、完備化と実現の交換が必要。
  §223の反例・不足はそのままで、項を完備化したというだけでは指定対象にならない。
- 完備部分圏CompleteCAlgの中で余極限を取る形では、同じnative図式Mについて
  L(colim_CAlg M) ≃ colim_CompleteCAlg(L ∘ M) となるのが左随伴の普遍性の筋。
  同じ反射の単位から比較するので、選び直した頂点の単なる同型へ弱めない。
  同じ図式のFrobeniusの辺を関手的に送れば、その指定辺の比較もこの形式論で追う対象となる。

後者は完備化後の頂点を表す**候補の場所**を与えるが、M14のP⁰の比較までは与えない。
忘却・mod p・π_nがこの完備部分圏の幾何学的実現をそのままambientな実現へ送るとは
仮定できないためである。特にMayの演算を項ごとに比較しただけでπ_n上の等式を余極限へ
移すことはできない。完備部分圏の余極限をambientな余極限と読み替えてこの穴を消さない。
従って§331の実現後の項別平坦・K平坦な厳密模型と全鎖のprimitiveを検収する案とは
別の形式的な切り方であり、後者の主要な義務を自動的に短縮するとは数えない。

(b)の単位の全射性の反例は依然として有効で、この形式論は単位のπ_n全射性を証明しない。
(c)については、完備部分圏での模型表示の形式論と演算の計算を分けた結果、
現状の不足をcoherentなP⁰が不可避との判定へ飛躍させない。
全鎖のprimitiveと指定対象・辺の比較、または実際のderived商での検出を閉じられないと
判明した場合には§32どおり止める。反射や実現保存を新しい仮定としてA4へ足さない。
この紙の節のためのLean・界面・drafts・G10の部品は作っていない。


## 348. 実際の空語作用と反復出現分岐の合成則（検証済み、取り込み点）

一覧：済み 12／全体 48（うち追加 4）

§340〜346を検証した。全整数の実際の空語基底の値を元のAW余単位へ戻し、
同じ出力族の零次因子の消去・正次数の零性、内側の全arityの外側切断和まで得た。
指定色が一出現でない分岐は全Cutで指定色の出力次数が正となるため実際の右辺が零。
元の係数合成を作用させた左辺も零なので、同じ二つの実際の射の値が元の圏で一致した。
退化項を捨てる仮定や、内側射の評価の仮定を最終の合成則へ残していない。

|登録候補（すべてSerrePositivity.EInfinity.SimplexCuts）|行数|
|---|---:|
|CochainNullaryValues|88|
|CochainNullaryInsertion|105|
|CochainNullaryInsertionDegrees|68|
|IteratedOuterCutSumAll|56|
|NullaryRepeatedCochainAction|63|
|NullaryRepeatedComposition|48|

今回428行。M14実測26,820行、L12a 11,613行、外枠31,000行まで4,180行。
L12aは未完了。一出現の実際の合成値の全和の比較、零出力arity、
全arityの同じ有限対応の包装が残る。完成見込みが外枠に収まらないという§314以降の注意は残す。

対象ビルドm14-cochain-nullary-values-02.log（2,669 jobs）、
m14-cochain-nullary-insertion-degrees-01.log（3,006 jobs）、
m14-cochain-nullary-insertion-02.logのIteratedOuterCutSumAll（3,072 jobsの対象部分）、
m14-nullary-repeated-composition-02.log（3,082 jobs）まで成功。対象の最終警告0。
小監査audit-m14-nullary-repeated-composition.logは6本30宣言・標準三公理のみ、sorry・独自公理0。
各ビルド・監査ごとに鍵を取り返却し、共有入口・監査・mainの作業木は変更していない。

完備化後のP⁰の三案の追加の紙の比較は§347。反射の仕様からの完備部分圏の余極限表示と、
Mayの演算をπ_nへ運ぶ義務を区別した。(c)が不可避との判定はまだ出していない。

## 349. 一点削除の残り色の指定面を同じSigma型で比較する（実装前）

一覧：済み 12／全体 48（うち追加 4）

一出現の分岐の実際のテンソルを照合するため、§333の全頂点列の等式を
出力次数と指定面の同じSigma型の等式へ戻す。既存構成の法則・証明分割で各証明200行以内。

```lean
lemma faceData_eq_of_vertexList {q : ℕ}
    (F G : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1))
    (h : List.ofFn F.2 = List.ofFn G.2) : F = G

lemma nullaryPointEraseCut_faceData_relabel {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) (c : Fin r) :
    (⟨outputDegree (nullaryPointEraseCut s p) w c,
      vertices (nullaryPointEraseCut s p) w c⟩ : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) =
      ⟨outputDegree s v (k.succAbove c), vertices s v (k.succAbove c)⟩
```

最初は同じ列の長さから始域次数を比較し、List.ofFnの各値で順序写像を比較する。
後者は既存simplexVertexList_faceで元の全頂点列へ戻し、§333を使う。
次数や面を選び直すものではなく、HEqだけを最終出力に残さない。

## 350. 一出現削除の同じ全出力順序と零次因子（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

§349の成分を、元のoperadInsertionEquivによる全出力順序へ戻す。
さらに選んだ零次の面が実際の零単体の生成元を与えることをSigma型で取り出す。
いずれも既存構成の法則で各証明200行以内。

```lean
lemma nullaryPointEraseCut_faceFamily_relabel {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) :
    (fun c : Fin r => (⟨outputDegree (nullaryPointEraseCut s p) w c,
      vertices (nullaryPointEraseCut s p) w c⟩ : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1))) =
      IntervalCuts.insertionFamily
        (fun a => (⟨outputDegree s v a, vertices s v a⟩ :
          Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)))
        (fun j : Fin 0 => Fin.elim0 j) k

lemma faceData_generator_zero (A : Type u) [CommRing A] (S : SSet.{0}) {q : ℕ}
    (F : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) (hF : F.1 = 0) (x : S _⦋q⦌) :
    ∃ y : S _⦋0⦌,
      (⟨F.1, gen A S F.1 (S.map (SimplexCategory.mkHom F.2).op x)⟩ :
        Σ d : ℕ, (chains A S).X (-(d : ℤ))) = ⟨0, gen A S 0 y⟩
```

全出力順序は元のoperadInsertionEquivの逆の全射性を使い、空の内側Fin 0を除く。
残り色の成分は§330の同じremainingPositionをk.succAboveで戻す法則と§349を組み合わせる。
生成元はFの次数を一般化して零次の等式を消去するだけで、逆像を仮定しない。


## 351. 一点削除の同じ生成元の全族と符号付き実テンソル（実装前）

一覧：済み 12／全体 48（うち追加 4）

§350の同じ面の全族を、元の正規化生成元の族と指定整数次数の実テンソルへ運ぶ。
各証明200行以内、既存構成の評価と照合の法則。符号は元の整数で比較し、
終域の同じ全次数の証明ht・ht′は実際の次数和から供給する型を明示する。

```lean
lemma nullaryPointEraseCut_generatorFamily_relabel (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) (x : S _⦋q⦌) :
    (fun c : Fin r =>
      (⟨outputDegree (nullaryPointEraseCut s p) w c,
        gen A S (outputDegree (nullaryPointEraseCut s p) w c)
          (S.map (face (nullaryPointEraseCut s p) w c).op x)⟩ :
        Σ d : ℕ, (chains A S).X (-(d : ℤ)))) =
      IntervalCuts.insertionFamily
        (fun a => ⟨outputDegree s v a,
          gen A S (outputDegree s v a) (S.map (face s v a).op x)⟩)
        (fun j : Fin 0 => Fin.elim0 j) k
```

```lean
lemma nullaryPointEraseCut_signedTensor_relabel (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hpoint : hi s p = lo s p) (hu : ∀ j, v.val j = v.val p → j = p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) (x : S _⦋q⦌) (z : ℤ)
    (ht : -(vectorDegree (chains A S) r
      (fun c => ⟨outputDegree (nullaryPointEraseCut s p) w c,
        gen A S (outputDegree (nullaryPointEraseCut s p) w c)
          (S.map (face (nullaryPointEraseCut s p) w c).op x)⟩) : ℤ) = z)
    (ht' : -(vectorDegree (chains A S) (r + 0)
      (IntervalCuts.insertionFamily
        (fun a => ⟨outputDegree s v a,
          gen A S (outputDegree s v a) (S.map (face s v a).op x)⟩)
        (fun j : Fin 0 => Fin.elim0 j) k) : ℤ) = z) :
    cutSign (nullaryPointEraseCut s p) w.val •
      vectorTensorAt (chains A S) r
        (fun c => ⟨outputDegree (nullaryPointEraseCut s p) w c,
          gen A S (outputDegree (nullaryPointEraseCut s p) w c)
            (S.map (face (nullaryPointEraseCut s p) w c).op x)⟩) z ht =
      cutSign s v.val • vectorTensorAt (chains A S) (r + 0)
        (IntervalCuts.insertionFamily
          (fun a => ⟨outputDegree s v a,
            gen A S (outputDegree s v a) (S.map (face s v a).op x)⟩)
          (fun j : Fin 0 => Fin.elim0 j) k) z ht'
```


## 352. 一点削除の指定面・生成元の全族・符号付き実テンソル（検証済み）

一覧：済み 12／全体 48（うち追加 4）

§349〜351を検証した。元の頂点列の一致から出力次数と指定面の同じSigma型の等式を得て、
元のoperadInsertionEquivの順序で全族へまとめた。同じ正規化生成元の全族と、
同じ指定整数次数の元の整数符号付き実テンソルの厳密な一致までつながる。
同じ零次の面から来る零単体の生成元も存在を証明し、内側作用の値の仮定として残さない。

|登録候補（すべてSerrePositivity.EInfinity.SimplexCuts）|行数|
|---|---:|
|NullaryPointFaceData|49|
|NullaryPointFaceFamilies|43|
|ZeroFaceGenerator|29|
|NullaryPointGeneratorFamilies|49|
|NullaryPointSignedTensors|53|

今回223行。M14実測27,043行、L12a 11,836行、外枠31,000行まで3,957行。
L12aは未完了。実際の一出現のraw合成語への型の移送、正規化零項を含めた全有限和、
零出力arityと全arityの包装は残る。既存構成の法則・証明分割だけで一覧IDは増やしていない。

対象ビルドm14-nullary-point-face-families-01.log（2,917 jobs）、
m14-nullary-point-signed-tensors-02.log（2,920 jobs）は成功、対象警告0。
小監査audit-m14-nullary-point-signed-tensors.logは5本6宣言・標準三公理のみ、sorry・独自公理0。
ビルド・監査ごとに鍵を取り返却。共有入口・監査・mainの作業木は変更していない。
登録候補と実測はこの表のとおり。作業木の未検証のLeanは残していない。

mainはこの時点で391b2a0d2のままで、§33の3b-4a完成の取り込みはまだない。
取り込まれたら指示どおりM14を区切ってTotの9欄を先にする（段0は§260）。
完備化後のP⁰の三案は§347の比較を維持し、(c)への判定はまだ出していない。

## 353. 一出現の零次出力の全Cutの同値と全有限和（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§318の元の挿入・削除を、実際の零次出力という部分型へ包装する。
指定色が一出現のとき、出力次数零と同じ区間が一点であることは既存§316の両方向の式。
以下はL12aの同じ有限対応と再添字の法則。新しい対応を選び直さない。各証明200行以内。
実装前に§316の有限点検を再実行した：全9,794 Cut、零次出力2,617、非空な残り位置の
両逆と指数の完全一致2,616、退化削除890を確認（空の出力の特別な一例は別途残る）。

```lean
lemma outputDegree_zero_iff_point_of_unique {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (p : Fin (m + 2)) (k : Fin r)
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    outputDegree s v k = 0 ↔ hi s p = lo s p

def nullaryOutputCutEquiv (m q r : ℕ) (v : Surjection.Word r (m + 2))
    (p : Fin (m + 2)) (k : Fin r) (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    Cut m q ≃ {s : Cut (m + 1) q // outputDegree s v k = 0}

lemma sum_nullaryOutputCuts {M : Type*} [AddCommMonoid M] {m q r : ℕ}
    (v : Surjection.Word r (m + 2)) (p : Fin (m + 2)) (k : Fin r)
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p)
    (F : Cut m q → M) (G : Cut (m + 1) q → M)
    (hpair : ∀ t, F t = G (nullaryPointInsertCut t p))
    (hzero : ∀ s, outputDegree s v k ≠ 0 → G s = 0) :
    ∑ t, F t = ∑ s, G s
```

同値の順方向は元のnullaryPointInsertCut、逆は元のnullaryPointEraseCut。
和は実際の零次出力の部分型とその補集合に分け、補集合の全項を零として保持する。
hpair・hzeroは再添字の一般法則の入力で、実際の合成則へ仮定として残すものではない。


## 354. 全Cut再添字に元の実際の空語作用の値を入れる（実装前）

一覧：済み 12／全体 48（うち追加 4）

既存cutTensorの入力族にcutGeneratorFamilyという記法を付ける。新しい作用・数学的構成ではない。
§353のhpair・hzeroを、元の符号・面の族の等式と、§344の実際の空語作用の値で供給する。
実際の全和の結論には内側射の評価を仮定として残さない。各証明200行以内。
原典BF §2.2.6、同じ全整数の終域・全Cut・退化零項を保つ。型は次。

```lean
def cutGeneratorFamily (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    Fin r → Σ d : ℕ, (chains A S).X (-(d : ℤ)) :=
  fun a => ⟨outputDegree s v a,
    gen A S (outputDegree s v a) (S.map (face s v a).op x)⟩

```

```lean
lemma vectorDegree_cutGeneratorFamily (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    vectorDegree (chains A S) r (cutGeneratorFamily A S s v x) = m + q + 1 - r
```

```lean
lemma sum_nullary_cochain_cut_terms (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (v : Surjection.Word (r + 1) (m + 2))
    (w : Surjection.Word r (m + 1)) (p : Fin (m + 2)) (k : Fin (r + 1))
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i))
    (ν : Surjection.BasisWord 0 0) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) :
    (∑ t : Cut m q, cutSign t w.val •
      vectorTensorAt (chains A S) r (cutGeneratorFamily A S t w x) z
        (by rw [vectorDegree_cutGeneratorFamily]; exact hz)) =
      ∑ s : Cut (m + 1) q, cutSign s v.val •
        (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) r 0 k
          (cochainAction A S 0)).f z
          (ιTensorObj (Surjection.complex A 0) (power (chains A S) (r + 1)) 0 z z (zero_add z)
            ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up ν)) ⊗ₜ[A]
              vectorTensorAt (chains A S) (r + 1) (cutGeneratorFamily A S s v x) z
                (by rw [vectorDegree_cutGeneratorFamily]
                    have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r
```



## 355. 元のraw合成語の正規化と同じ語長の移送（実装前）

一覧：済み 12／全体 48（うち追加 4）

実際のraw合成語を表す基底または退化零項を、元の係数合成と照合する。
語長と削除位置の移送は同じFinite添字の値で比較する。新しい語や射を選ばない。
ρのcount_eq_one_of_emptyから一出現性を得るため、一出現の条件を余分に仮定しない。
各証明200行以内、同じ既存構成の値と添字の法則。以下の型のW・Vは実際のWordの等式移送。

```lean
lemma succAbove_val_eq_of_vals {l l' : ℕ} (p : Fin (l + 1)) (p' : Fin (l' + 1))
    (i : Fin l) (i' : Fin l') (hp : p.val = p'.val) (hi : i.val = i'.val) :
    (p.succAbove i).val = (p'.succAbove i').val
```

```lean
lemma word_eq_mp_unique {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l)
    (p : Fin l) (k : Fin r) (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val (Fin.cast h p) = k ∧
      ∀ j, (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val j = k →
        j = Fin.cast h p
```

```lean
lemma nullaryRawWord_eq_mp_erase_value {m d N : ℕ} (hN : m + d = N + 1)
    (u : Surjection.BasisWord (m + 1) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (w : Surjection.BasisWord m d) (hw : w.val = IntervalCuts.nullaryRawWord u ν k ρ)
    (p : Fin (m + 1 + d)) (hu : ∀ j, u.val j = k → j = p) (i : Fin (N + 1)) :
    let V := Eq.mp (congrArg (fun L => Surjection.Word (m + 1) L)
      (by omega : (m + 1) + d = N + 2)) u
    let W := Eq.mp (congrArg (fun L => Surjection.Word m L) hN) w
    let P : Fin (N + 2) := Fin.cast (by omega) p
    k.succAbove (W.val i) = V.val (P.succAbove i)
```

```lean
lemma compositionOnWords_nullary_eq_basis_of_raw (A : Type u) [CommRing A] {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (w : Surjection.BasisWord m d) (hw : w.val = IntervalCuts.nullaryRawWord u ν k ρ) :
    Surjection.compositionOnWords A u ν k = Surjection.basis A m d (ULift.up w)
```

```lean
lemma compositionOnWords_nullary_eq_zero_of_raw_degenerate (A : Type u) [CommRing A] {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (h : ¬Surjection.Nondegenerate (IntervalCuts.nullaryRawWord u ν k ρ)) :
    Surjection.compositionOnWords A u ν k = 0
```



## 356. 元の唯一出現位置と全和の型の移送（実装前の法則の型）

一覧：済み 12／全体 48（うち追加 4）

実際の係数合成から一出現位置を供給し、切断区間数の算術的な等式によって
同じ全和を移す。別の位置や頂点を選び直す同値ではなく、元のWordとCutの等式移送だけ。
Tは元の同じ複体射の値を代入できる任意の関数で、この型の移送に線形性は要らない。
各証明200行以内、既存構成の法則・証明分割。

```lean
lemma unique_position_of_occurrenceCount_one {r l : ℕ} (w : Fin l → Fin r) (k : Fin r)
    (h : Surjection.occurrenceCount w k = 1) :
    ∃ p : Fin l, w p = k ∧ ∀ j, w j = k → j = p
```

```lean
lemma word_eq_mp_trans {r l l' l'' : ℕ} (h : l = l') (h' : l' = l'')
    (w : Surjection.Word r l) :
    Eq.mp (congrArg (fun L => Surjection.Word r L) h')
      (Eq.mp (congrArg (fun L => Surjection.Word r L) h) w) =
      Eq.mp (congrArg (fun L => Surjection.Word r L) (h.trans h')) w
```

```lean
lemma sum_cutGenerator_terms_eq_mp (A : Type u) [CommRing A] (S : SSet.{0})
    {M : Type v} [AddCommGroup M] {m n q r : ℕ} (h : m = n)
    (w : Surjection.Word r (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z)
    (T : (power (chains A S) r).X z → M) :
    (∑ s : Cut m q, cutSign s w.val • T
      (vectorTensorAt (chains A S) r (cutGeneratorFamily A S s w x) z
        (by rw [vectorDegree_cutGeneratorFamily]; exact hz))) =
      ∑ s : Cut n q,
        cutSign s (Eq.mp (congrArg (fun L => Surjection.Word r (L + 1)) h) w).val • T
          (vectorTensorAt (chains A S) r
            (cutGeneratorFamily A S s
              (Eq.mp (congrArg (fun L => Surjection.Word r (L + 1)) h) w) x) z
            (by rw [vectorDegree_cutGeneratorFamily]; rw [← h]; exact hz))
```


## 357. 完備化後のP⁰の三案：(b)でperfect性や半線形同型だけから消去しない（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§347の続き。(b)の単位・torsionの条件を、actualなraw対象で期待するperfect性と区別する。
以下は自分の明示的な環・加群の計算であり、A4の実際の対象に余分な条件を足すものではない。
新しいLean・界面・drafts・G10の部品は作らない。

### 357.1 (b) perfectな離散環でも完備化単位のπ_0全射性は出ない

B = F_p[t^{1/p^∞}]、d=tとする。Bは多項式環F_p[t^{1/p^e}]の単射的な和で、
Frobeniusはその上で同型。各非零元のtの最小指数は有限だから、Bはt進分離的。
tは非零因子で、B/t^nの商の塔は全射。従ってこの離散な例の導来t完備化は
同じ商の逆極限で計算できる（正則なprincipal Koszul商を使う）。

逆極限には互換な元 a_n = Σ_{j=0}^{n-1} t^j mod t^n がある。
その値aは(1-t)a=1を満たすが、Bの元の像ではない。
もし像ならt進分離性によってBで(1-t)b=1となる。
bはある有限段F_p[t^{1/p^e}]の多項式で、u=t^{1/p^e}と書けば
(1-u^{p^e})b(u)=1となり、多項式の次数から不可能。

さらにF(t^nB)=t^{pn}Bで、逆Frobeniusも添字を共終に変えれば連続。
この例では完備化後もFrobeniusは同型となるが、単位はπ_0全射でない。
従ってrawのπ_0のperfect性を確認しても、そのことだけで§216の単位のEpiを供給しない。
これは単なるcoconnective性の反例を、perfect性もある場合へ絞り直した点検。

### 357.2 (b) reducedなperfect係数と半線形同型だけではH¹のTate項も消えない

同じBに対してM = B[1/t]/Bを加群として考える。
x_n = t^{-n}+BはM[t^n]の非零元で、t x_{n+1}=x_n。
従ってT_t(M)=lim_n M[t^n]には非零の互換な元(x_n)がある。
BがreducedなためB自身のt冪ねじれが有界であることと、Mのねじれが有界であることは別。

MのFrobenius半線形な加法同型Fから、固定の商の添字で読む写像は

    M[t^n] → M[t^n],  x ↦ t^{(p-1)n} F(x)

となる。この式ではt^nを掛けるとt^{pn}F(x)=F(t^n x)=0。
塔との互換性もt·t^{(p-1)(n+1)}F(x_{n+1}) = t^{(p-1)n}F(t x_{n+1})で直接読める。
上の元ではt^{(p-1)n}F(t^{-n}+B)=t^{-n}+Bなので、非零の互換な元は残る。
従ってrawなH¹の半線形Frobeniusが同型であるという条件だけで、
§223.3のTate項を零としてはいけない。

この加群をA4のH¹だと同定したり、これに同じBE作用・May P⁰を供給したりはしていない。
これは加群と半線形写像の条件だけからtorsion消滅を結論できないという点検で、
A4やMay案の反例ではない。実際のA4のH¹に別の有界性を証明できるかは未確定。

### 357.3 (a)(c)との比較

(a)の同じ全鎖の有限primitiveを完備化へ延ばす案は、上の単位の全射性やTate消滅を使わない。
指定したnative対象・Frobeniusへの比較と全鎖の式の検収は依然として未供給。
(b)でactualなderived商の同じ演算を比較する案も残すが、一般論から得られない有界性を
証明済みの条件として持ち込まない。
(a)(b)のactualな比較が両方不可能と判明したわけではないため、(c)とはまだ判定しない。
判明したときは§32どおり止めて報告する。外枠の完成見込みの未評価分もそのまま残す。


## 358. 実際の非退化raw空語合成を全Cut和へ接続する（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§354の元の全和と§355〜356の同じ語長・係数の移送を接続する。
ρから一出現性と元の唯一位置を供給し、wの値は実際のnullaryRawWordそのものと指定する。
wの非退化性はこの分岐の条件で、退化分岐は零項として別途残す。
これはL12aの同じ合成則の非退化分岐、各証明200行以内。

```lean
lemma cochainAction_composition_nullary_nondegenerate_eq_iterated
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (w : Surjection.BasisWord (m + 1) d) (hw : w.val = IntervalCuts.nullaryRawWord u ν k ρ)
    (x : S _⦋q⦌) :
    (cochainAction A S ((m + 1) + 0)).f (-(d : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A ((m + 1) + 0)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) rfl
        ((Surjection.complexXIso A ((m + 1) + 0) d).inv
          (Surjection.compositionOnWords A u ν k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S (m + 1) 0 k).f (-(d : ℤ) + -(q : ℤ))
        (ιTensorObj (Surjection.complex A (m + 2) ⊗ Surjection.complex A 0) (chains A S)
          (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A (m + 2)) (Surjection.complex A 0)
            (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
            ((Surjection.complexXIso A (m + 2) d).inv
              (Surjection.basis A (m + 2) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S q x))
```

全Cutの再添字の入力hpair・hzero、内側射の評価、唯一位置の存在などを最終主張の仮定に追加しない。
同じ元の係数合成を作用させた左辺と、同じ四射の実際の右辺を比較する。

## 359. 同じ和の依存するWordの等式を運ぶ証明分割（実装前）

一覧：済み 12／全体 48（うち追加 4）

§358の語長の二重移送hwordを、vectorTensorAtの次数の証明の中へ直接rwしない。
同じ和を独立なWord引数の関数Fとして先に型付けし、congrArg F hwordを使う。
これは元の和の値と等式移送の証明分割で、新しい数学・写像の選択・一覧IDではない。

```lean
let F (a : Surjection.Word (m + 2) ((m + d) + 2)) :
    (power (chains A S) ((m + 1) + 0)).X z :=
  ∑ s : Cut ((m + d) + 1) q, cutSign s a.val •
    T (vectorTensorAt (chains A S) (m + 2) (cutGeneratorFamily A S s a x) z
      (by rw [vectorDegree_cutGeneratorFamily]; dsimp only [z]; omega))
```

既存sum_cutGenerator_terms_eq_mpの右辺をFの同じ引数への適用として読む。
その後にcongrArg F hwordを合成するので、固定した語に依存する次数の証明を
別の語へ無理に書き換えるmotiveを作らない。各証明200行以内。


## 360. 一出現の実際の全和と非退化raw空語合成則（検証済み、取り込み点）

一覧：済み 12／全体 48（うち追加 4）

§353〜359を検証した。元の一点挿入・削除を実際の零次出力の全Cut同値へ包装し、
零となる補集合の全項を保持した再添字を得た。対応条件と零性を元の符号・面・実際の
空語作用の値で供給し、小さい全切断和と実際の空語代入の全和が一致した。

実際のnullaryRawWordを表す非退化基底の分岐については、元の係数合成を作用させた左辺と
同じ四射からなる二段作用の右辺の元の圏での一致まで接続した（全入力単体・全次数）。
一出現位置や内側作用の値、Cut再添字の対応条件・零性は結論の追加仮定に残していない。
基底wの値は実際のraw合成語そのものと指定しており、別の語へ置き換えていない。

|登録候補（すべてSerrePositivity.EInfinity.SimplexCuts）|行数|
|---|---:|
|NullaryOutputCutEquiv|39|
|NullaryOutputCutSums|40|
|CutGeneratorFamilies|35|
|NullaryCochainCutSums|83|
|NullaryWordLengths|57|
|NullaryCoefficientWords|40|
|NullaryCutIndexTransport|62|
|NullaryNondegenerateComposition|98|

今回454行、M14実測27,497行、L12a 12,290行、外枠31,000行まで3,503行。
L12aは未完了。実際の退化raw合成語の右辺の零性、零出力arity、
全arityの同じ有限対応とその包装が残る。新しい一覧IDは追加していない。

対象ビルドはm14-nullary-output-cut-sums-01.log（2,278 jobs）、
m14-nullary-cochain-cut-sums-02.log（3,065 jobs）、
m14-nullary-word-lengths-01.log（2,856 jobs）、
m14-nullary-cut-index-transport-01.log（2,232 jobs）、
m14-nullary-nondegenerate-composition-02.log（3,116 jobs）まで成功、対象警告0。
小監査はaudit-m14-nullary-cochain-cut-sums.log（4本13宣言）、
audit-m14-nullary-word-lengths.log（2本11宣言）、
audit-m14-nullary-cut-index-transport.log（1本5宣言）、
audit-m14-nullary-nondegenerate-composition.log（1本10宣言）。
すべて標準三公理のみ、sorry・独自公理0。
ビルド・監査ごとに鍵を取り返却した。共有入口・共有監査・mainの作業木は変更していない。

並行する完備化後のP⁰の三案は§357。perfectなrawのπ_0でも完備化単位は一般に全射でなく、
reducedなperfect係数とH¹の半線形同型だけではTate項は消えないことを具体的に点検した。
この加群の点検をA4のBE模型やP⁰の反例とは扱わない。(a)(b)のactualな比較は未供給で、
(c)が不可避との判定はまだない。追加仮定で消去していない。
§314以降の完成見込みの外枠超過の懸念と、完備化の未評価分も残す。

mainは391b2a0d2のまま。§33の3b-4a完成が取り込まれたらTotの9欄へ先に切り替える。


## 361. 実際の退化raw語の二段作用の零項を保つ（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

退化分岐の実際の右辺を全Cutごとに零とするための既存構成の評価の法則。
元の一点削除のCutが非退化なら削除raw語も非退化となる既存の法則を使う。
指定出力次数零ではその対偶で元のテンソルが零、正次数では実際の空語作用が零となる。
raw語を基底にする仮定や、非零項だけへの制限はしない。各証明200行以内。
§316の有限点検を再実行し、全9,794 Cut・退化削除890・両逆2,616を再確認した。

```lean
lemma not_nondegenerate_of_nullary_raw_degenerate {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w i) = v.val (p.succAbove i))
    (hw : ¬Surjection.Nondegenerate w) : ¬Nondegenerate s v.val
```

```lean
lemma vectorTensorAt_cutGeneratorFamily_eq_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌)
    (h : ¬Nondegenerate s v.val) (z : ℤ)
    (hz : -(vectorDegree (chains A S) r (cutGeneratorFamily A S s v x) : ℤ) = z) :
    vectorTensorAt (chains A S) r (cutGeneratorFamily A S s v x) z hz = 0
```

```lean
lemma sum_nullary_cochain_cut_terms_of_raw_degenerate
    (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (v : Surjection.Word (r + 1) (m + 2)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hv : ∀ i, k.succAbove (w i) = v.val (p.succAbove i))
    (hw : ¬Surjection.Nondegenerate w) (ν : Surjection.BasisWord 0 0)
    (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) :
    (∑ s : Cut (m + 1) q, cutSign s v.val •
      (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) r 0 k
        (cochainAction A S 0)).f z
        (ιTensorObj (Surjection.complex A 0) (power (chains A S) (r + 1)) 0 z z (zero_add z)
          ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up ν)) ⊗ₜ[A]
            vectorTensorAt (chains A S) (r + 1) (cutGeneratorFamily A S s v x) z
              (by rw [vectorDegree_cutGeneratorFamily]
                  have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r
```

```lean
lemma raw_nondegenerate_cast_iff {r l l' : ℕ} (h : l = l') (w : Fin l → Fin r) :
    Surjection.Nondegenerate (fun i : Fin l' => w (Fin.cast h.symm i)) ↔
      Surjection.Nondegenerate w
```

```lean
lemma nullaryRawWord_cast_erase_value {m d N : ℕ} (hN : m + d = N + 1)
    (u : Surjection.BasisWord (m + 1) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (p : Fin (m + 1 + d)) (hu : ∀ j, u.val j = k → j = p) (i : Fin (N + 1)) :
    let V := Eq.mp (congrArg (fun L => Surjection.Word (m + 1) L)
      (by omega : (m + 1) + d = N + 2)) u
    let P : Fin (N + 2) := Fin.cast (by omega) p
    k.succAbove (IntervalCuts.nullaryRawWord u ν k ρ (Fin.cast hN.symm i)) =
      V.val (P.succAbove i)
```



## 362. 実際の退化raw空語合成の元の圏での合成則（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§361の全和の零性を元のraw語へ戻す。左辺は既存の同じ係数合成の退化零性を使う。
語長とCut添字の移送は§355〜359の同じものを使い、非退化基底を選ばない。
L12aの同じ合成則の退化分岐、各証明200行以内。

```lean
lemma cochainAction_composition_nullary_degenerate_eq_iterated
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (hdeg : ¬Surjection.Nondegenerate (IntervalCuts.nullaryRawWord u ν k ρ))
    (x : S _⦋q⦌) :
    (cochainAction A S ((m + 1) + 0)).f (-(d : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A ((m + 1) + 0)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) rfl
        ((Surjection.complexXIso A ((m + 1) + 0) d).inv
          (Surjection.compositionOnWords A u ν k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S (m + 1) 0 k).f (-(d : ℤ) + -(q : ℤ))
        (ιTensorObj (Surjection.complex A (m + 2) ⊗ Surjection.complex A 0) (chains A S)
          (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A (m + 2)) (Surjection.complex A 0)
            (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
            ((Surjection.complexXIso A (m + 2) d).inv
              (Surjection.basis A (m + 2) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S q x))
```

退化性以外の仮定を増やさず、内側射の値や全和の零性を結論の前提にしない。
正の出力arityの全入力単体・全次数で、元の同じ二つの射の値の等式を述べる。


## 363. 正の出力arityの実際の空語合成の全分岐を合わせる（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

同じ元の係数合成と二段作用に、反復出現・一出現の退化・非退化の全分岐を合わせる。
一出現の分割ρはcountの等式から既存single 0を同じ型へ運ぶ。
非退化分岐の基底wは実際のraw語・既存の全射性・その非退化性で構成する。
L12aの同じ合成則の証明分割で、各証明200行以内。

```lean
lemma cochainAction_composition_nullary_positive_output_eq_iterated
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (x : S _⦋q⦌) :
    (cochainAction A S ((m + 1) + 0)).f (-(d : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A ((m + 1) + 0)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) rfl
        ((Surjection.complexXIso A ((m + 1) + 0) d).inv
          (Surjection.compositionOnWords A u ν k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S (m + 1) 0 k).f (-(d : ℤ) + -(q : ℤ))
        (ιTensorObj (Surjection.complex A (m + 2) ⊗ Surjection.complex A 0) (chains A S)
          (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A (m + 2)) (Surjection.complex A 0)
            (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
            ((Surjection.complexXIso A (m + 2) d).inv
              (Surjection.basis A (m + 2) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S q x))
```

ρ・raw語の基底・退化条件・内側射の評価などの仮定を最終主張に残さない。
零出力arityと全体の有限対応の包装は、これで済んだとはしない。


## 364. 退化分岐の二つの零性を元の値で型付けする証明分割（実装前）

一覧：済み 12／全体 48（うち追加 4）

§362の二つの零性をcalcの未指定の元で推論させず、同じ元の左辺・右辺で先に型付けする。
新しい数学や追加仮定ではなく、次の局所的な証明分割。各証明200行以内。

```lean
  have hL : (cochainAction A S ((m + 1) + 0)).f (-(d : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A ((m + 1) + 0)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) rfl
        ((Surjection.complexXIso A ((m + 1) + 0) d).inv
          (Surjection.compositionOnWords A u ν k) ⊗ₜ[A] gen A S q x)) = 0

  have hR : (iteratedCochainAction A S (m + 1) 0 k).f (-(d : ℤ) + -(q : ℤ))
        (ιTensorObj (Surjection.complex A (m + 2) ⊗ Surjection.complex A 0) (chains A S)
          (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A (m + 2)) (Surjection.complex A 0)
            (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
            ((Surjection.complexXIso A (m + 2) d).inv
              (Surjection.basis A (m + 2) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S q x)) = 0
```


## 365. 零出力arityの零単体の同じ境界値（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

零出力arity・係数次数零・入力零単体を元の唯一のCutで評価する。
§316の空出力の特別な一例に対応する。Cut 0 0の元はcard=0から元の空集合のみ。
符号は元の指数で一、選んだ零次因子は既存faceData_generator_zeroと実際の空語作用へ渡す。
左右とも同じsingleObjXSelfの逆で単位元一を読む。L12aの境界分岐、各証明200行以内。

```lean
lemma cochainAction_composition_nullary_output_zero_degree_zero
    (A : Type u) [CommRing A] (S : SSet.{0}) (u : Surjection.BasisWord 1 0)
    (ν : Surjection.BasisWord 0 0) (x : S _⦋0⦌) :
    (cochainAction A S 0).f 0
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 0 0 rfl
        ((Surjection.complexXIso A 0 0).inv
          (Surjection.compositionOnWords A u ν 0) ⊗ₜ[A] gen A S 0 x)) =
      (iteratedCochainAction A S 0 0 0).f 0
        (ιTensorObj (Surjection.complex A 1 ⊗ Surjection.complex A 0) (chains A S) 0 0 0 rfl
          (ιTensorObj (Surjection.complex A 1) (Surjection.complex A 0) 0 0 0 rfl
            ((Surjection.complexXIso A 1 0).inv
              (Surjection.basis A 1 0 (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S 0 x))
```


## 366. 零出力arityの元の合成則を全次数で読む（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

外側arity一の正次数基底は既存IsEmptyで除く。係数次数零の入力正次数は
同じsingle複体の零対象性で左右とも零となり、零単体だけを§365の同じ値へ戻す。
新しい作用を作らず、L12aの同じ全整数の合成則の分岐を閉じる。各証明200行以内。

```lean
lemma cochainAction_composition_nullary_zero_output_eq_iterated
    (A : Type u) [CommRing A] (S : SSet.{0}) {d q : ℕ}
    (u : Surjection.BasisWord 1 d) (ν : Surjection.BasisWord 0 0) (k : Fin 1)
    (x : S _⦋q⦌) :
    (cochainAction A S 0).f (-(d : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A 0) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) rfl
        ((Surjection.complexXIso A 0 d).inv
          (Surjection.compositionOnWords A u ν k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S 0 0 k).f (-(d : ℤ) + -(q : ℤ))
        (ιTensorObj (Surjection.complex A 1 ⊗ Surjection.complex A 0) (chains A S)
          (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A 1) (Surjection.complex A 0)
            (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
            ((Surjection.complexXIso A 1 d).inv
              (Surjection.basis A 1 d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S q x))
```


## 367. 全arity・全係数次数の元のBF合成則の基底値（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

正の内側arityの既存の全Cut比較と、空語の全分岐の実際の射の等式を合わせる。
零arityの正次数基底は既存IsEmpty。出力arity零も§366で含める。
L12aからL12への同じ合成則の証明分割で、各証明200行以内。

```lean
lemma cochainAction_composition_basis_eq_iterated_all
    (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -(q : ℤ) = z) :
    (cochainAction A S (m + n)).f z
      (ιTensorObj (Surjection.complex A (m + n)) (chains A S)
        (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) z (by omega)
        ((Surjection.complexXIso A (m + n) (d + e)).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S m n k).f z
        (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A n) (chains A S)
          (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) z (by omega)
          (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A n)
            (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
            ((Surjection.complexXIso A (m + 1) d).inv
              (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A n e).inv
                (Surjection.basis A n e (ULift.up v))) ⊗ₜ[A] gen A S q x))
```

基底値を全arityで合わせても、元の全有限添字の対合と全複体射の等式まで
完成したとはしない。それらの包装を引き続き残す。


## 368. 零次の唯一Cutを指定して和を読む証明分割（実装前）

一覧：済み 12／全体 48（うち追加 4）

§365でdefaultの選択へ依存しないよう、同じ `s : Cut 0 0 := ⟨∅, rfl⟩` を指定し、
`∀ t : Cut 0 0, t = s` を元のcard=0から供給してFinset.sum_eq_single sを使う。
位置の和の添字もFin 1として型付けし、同じ元の符号指数を計算する。
新しいCut・写像・数学を作らない既存構成の法則の証明分割で、各証明200行以内。

## 369. 完備化後のP⁰の三案：(a)の項別平坦な模型の既存の入口を確認（紙のみ）

一覧：済み 12／全体 48（うち追加 4）

§296・331の(a)で残した項別平坦な厳密BE模型について、既存のセル段階の基底を読み直した。
以下は新しいLeanを実装したとの報告ではなく、既存の宣言からどこを再利用できるかの確認。

### 369.1 本体で既に供給されているもの

EInfinity/BarrattEccles/Theory/CellStageGradedBasis.leanには次がある。

- `Operad.cellStageErasedFreeIso`：実際のセル段階を、元の生成球の余積上の自由代数と微分を忘れた同型で比較する。
- `Operad.cellStageSchurDegreeIso`：同じcarrierの各次数を元のSchur自由代数の次数へ比較する。
- `BarrattEccles.cellStageWordBasis c hX j i`：始対象からの実際の相対セル複体の各段階j・各次数iについて、carrier上のModule.Basisを与える。

従って**各段階の各次数**には、同じ基底をModule.Free.of_basisへ渡し、Module.Flat.of_freeを使う筋が既にある。
ArityKFlat.leanの`complexArity_kFlat`が、この二つのMathlib APIを同じ順に使っていることも確認した。
従来の「cofibrantCarrierKFlatだけから項別平坦性は出ない」という注意は維持するが、
項別平坦性への入口が未構成の自由な台の推測だけ、という扱いにはしない。
同じ元のセル段階の**明示的な基底**が既に本体にある。

### 369.2 actualな完備化模型まで残る比較

各段階の基底があることと、欲しいnative頂点を表す最終cell模型が項別平坦であることは分ける。
`cofibrantCarrierKFlat_of_cellStages`では、小対象分解の最後のcarrierを
`isColimitOfPreserves U t'.isColimit`で台の複体の余極限へ比較し、最後にretractへ戻している。
項別平坦性には同じ最後の余極限の次数ごとの比較、または生成元の全体での基底の比較が要る。
各段階のModule.Basisだけを最終頂点のModule.Basisと読み替えない。
一般のcofibrant模型を使うなら、retractを各次数の平坦性へ移す義務も残る。

(a)では任意の模型の自由性を主張するより、同じraw対象へのセル置換を選び、
既存K平坦性とこの各次数の基底からの項別平坦性をそろえる経路が具体的な候補となる。
ただし、その置換が同じnativeなraw対象を表すこと、元のFrobeniusの辺と完備化単位を表すことは
別の比較である。これを既存のK平坦性だけで証明済みとはしない。
その後の同じBE作用の連続延長と、全鎖の有限primitiveの検収も§331のまま残る。

### 369.3 (b)(c)との比較

(b)では§357のとおりperfect性や半線形同型だけから単位の全射性・Tate項消滅を結論できない。
今回の入口は(a)の模型の選択を具体化するもので、この偽の消去を使わない。
一方、nativeな指定対象・辺と全鎖のprimitiveの比較はまだ供給していないため、
May案が完備化後にも通ったとの主張はしない。(a)(b)のactualな比較が両方不可能と
判明したわけでもないので、(c)への判定はまだ出さない。
新しい仮定・完備化のLean・界面・drafts・G10の部品は追加していない。


## 370. 退化・零出力・全arityの実際の合成則の基底値（検証済み、取り込み点）

一覧：済み 12／全体 48（うち追加 4）

§361〜368を検証した。元の退化raw語の全切断和の零性を、同じ係数合成と
実際の二段作用の等式へ接続し、正の出力arityの全分岐を合わせた。
零出力arityでは元の空のCutを指定して零単体の値を読み、残る正次数は同じsingle複体の
零対象または存在しない基底で処理した。

CochainCompositionBasisAllで、全arity・全内外係数次数・全入力単体に対する
元の二つの複体射の基底値が厳密に一致する。内側・出力の零arity、退化raw語の零項も含む。
全複体射への外延性と、一覧が要求する元の全有限添字の対合の包装はまだ残る。
そのためL12a・L12を完了扱いにはせず、一覧IDの済み数も増やさない。

|登録候補（すべてSerrePositivity.EInfinity.SimplexCuts）|行数|
|---|---:|
|DegenerateCutGeneratorFamilies|48|
|NullaryDegenerateCutSums|57|
|NullaryRawLengthValues|40|
|NullaryDegenerateComposition|115|
|NullaryPositiveOutputComposition|54|
|NullaryZeroOutputValue|102|
|NullaryZeroOutputComposition|55|
|CochainCompositionBasisAll|58|

今回529行、M14実測28,026行、L12a 12,819行、外枠31,000行まで2,974行。
対象ビルドm14-nullary-degenerate-cut-sums-01.log（3,058 jobs）、
m14-nullary-positive-output-composition-01.log（3,124 jobs）、
m14-cochain-composition-basis-all-03.log（3,278 jobs）まで成功、対象最終警告0。
小監査audit-m14-nullary-positive-output-composition.logは5本26宣言、
audit-m14-cochain-composition-basis-all.logは3本12宣言。
全て標準三公理のみ、sorry・独自公理0。各回で鍵を取り返却。
共有入口・共有監査・mainの作業木・既存の公開宣言は変更していない。

完備化後のP⁰の三案の並行する紙の確認は§369。既存cellStageWordBasisが
各セル段階・各次数の基底を与えることを確認し、(a)での項別平坦性への入口を具体化した。
最後の余極限・retract・nativeな対象と辺・全鎖のprimitiveの比較はまだ残る。
(b)の単位全射性・Tate消滅を追加仮定として使わず、(c)への判定もまだ出していない。
完成見込みの外枠超過の懸念と完備化の未評価分は維持する。

mainは391b2a0d2のまま。3b-4a完成の取り込み後は§33のTotの9欄を先にする。


## 371. 零項を固定点に残す同じ部分同値の交換（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

L12aの空語分岐では、零次出力の部分型だけを左側のCutと交換し、
元の右側の正次数の零項を固定点として保持する。指定された同値eと逆以外は選ばない。
一覧の有限対合を構成するための同じ交換とその法則であり、新しい数学・一覧IDではない。
各証明200行以内。有限点検を先に行い、右の添字数0〜6の全部分集合とその全順序づけ
2,372組・25,019要素について、二回で恒等・固定点の範囲・実整数項の相殺を確認した。

```lean
def matchedSubsetExchange (P : β → Prop) [DecidablePred P] (e : α ≃ {b // P b}) :
    α ⊕ β → α ⊕ β
  | Sum.inl a => Sum.inr (e a).val
  | Sum.inr b => if h : P b then Sum.inl (e.symm ⟨b, h⟩) else Sum.inr b
```

```lean
lemma matchedSubsetExchange_involutive (P : β → Prop) [DecidablePred P]
    (e : α ≃ {b // P b}) : Function.Involutive (matchedSubsetExchange P e)
```

```lean
def matchedSubsetPerm (P : β → Prop) [DecidablePred P] (e : α ≃ {b // P b}) :
    Equiv.Perm (α ⊕ β)
```

```lean
def matchedSubsetBalanceTerm {M : Type w} [AddCommGroup M] (F : α → M) (G : β → M) :
    α ⊕ β → M
  | Sum.inl a => F a
  | Sum.inr b => -G b
```

```lean
lemma matchedSubsetPerm_fixed_zero {M : Type w} [AddCommGroup M]
    (P : β → Prop) [DecidablePred P] (e : α ≃ {b // P b}) (F : α → M) (G : β → M)
    (hzero : ∀ b, ¬P b → G b = 0) (i : α ⊕ β) (hi : matchedSubsetPerm P e i = i) :
    matchedSubsetBalanceTerm F G i = 0
```

```lean
lemma matchedSubsetPerm_term_neg {M : Type w} [AddCommGroup M]
    (P : β → Prop) [DecidablePred P] (e : α ≃ {b // P b}) (F : α → M) (G : β → M)
    (hpair : ∀ a, F a = G (e a).val) (hzero : ∀ b, ¬P b → G b = 0) (i : α ⊕ β) :
    matchedSubsetBalanceTerm F G (matchedSubsetPerm P e i) =
      -matchedSubsetBalanceTerm F G i
```

hpair・hzeroはこの一般の包装の入力。実際の空語の対合へ適用するときは
既に証明した元のCut対応・指定面・実際の余単位の値で供給し、結論へ仮定として残さない。


## 372. 元の一点Cut対応と実際の空語作用による全添字の対合（実装前）

一覧：済み 12／全体 48（うち追加 4）

§371へ元のnullaryOutputCutEquivと実際のCut項を供給する。
小さい全Cutと、大きい全Cut（正次数の零項も含む）の直和を保つ。
対合は係数環・入力単体を選ぶ前に指定し、全係数環・全入力に共通に使う強い形。
各証明200行以内、同じL12aの有限対応と既存構成の評価の包装。
hpair・hzeroを最終の結論へ仮定として残さない。

```lean
def nullarySmallCutTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (w : Surjection.Word r (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) (t : Cut m q) : (power (chains A S) r).X z
```

```lean
def nullaryOuterCutTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (v : Surjection.Word (r + 1) (m + 2)) (ν : Surjection.BasisWord 0 0) (k : Fin (r + 1))
    (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z)
    (s : Cut (m + 1) q) : (power (chains A S) r).X z :=
  cutSign s v.val •
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) r 0 k
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (r + 1)) 0 z z (zero_add z)
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up ν)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (r + 1) (cutGeneratorFamily A S s v x) z
            (by rw [vectorDegree_cutGeneratorFamily]
                have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r
```

```lean
def nullaryCanonicalBalancePerm {m q r : ℕ} (v : Surjection.Word r (m + 2))
    (p : Fin (m + 2)) (k : Fin r) (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    Equiv.Perm (Cut m q ⊕ Cut (m + 1) q)
```

```lean
def nullaryCanonicalBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (ν : Surjection.BasisWord 0 0) (k : Fin (r + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) :
    Cut m q ⊕ Cut (m + 1) q → (power (chains A S) r).X z
```

```lean
lemma nullarySmallCutTerm_eq_insert (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (ν : Surjection.BasisWord 0 0) (p : Fin (m + 2)) (k : Fin (r + 1))
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i))
    (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) (t : Cut m q) :
    nullarySmallCutTerm A S w x z hz t =
      nullaryOuterCutTerm A S v ν k x z hz (nullaryPointInsertCut t p)
```

```lean
lemma nullaryOuterCutTerm_eq_zero_of_nonzero (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (v : Surjection.Word (r + 1) (m + 2)) (ν : Surjection.BasisWord 0 0)
    (k : Fin (r + 1)) (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z)
    (s : Cut (m + 1) q) (hs : outputDegree s v k ≠ 0) :
    nullaryOuterCutTerm A S v ν k x z hz s = 0
```

```lean
lemma nullaryCanonicalBalance_pairing {m q r : ℕ}
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (ν : Surjection.BasisWord 0 0) (p : Fin (m + 2)) (k : Fin (r + 1))
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) :
    ∃ τ : Equiv.Perm (Cut m q ⊕ Cut (m + 1) q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌) (z : ℤ)
        (hz : -((m + q + 1 - r : ℕ) : ℤ) = z),
        nullaryCanonicalBalanceTerm A S v w ν k x z hz i = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌) (z : ℤ)
        (hz : -((m + q + 1 - r : ℕ) : ℤ) = z),
        nullaryCanonicalBalanceTerm A S v w ν k x z hz (τ i) =
          -nullaryCanonicalBalanceTerm A S v w ν k x z hz i)
```

これは同じ語長の正規形での一出現・非退化raw語の包装。
元の全OverlapPartitionの因子と元の語長へ移す包装、退化・零出力を合わせる全体の型はまだ残る。
そのため、この節だけでL12a全体を完了扱いにしない。


## 373. 元の全OverlapPartition因子と退化・反復の固定零項（実装前）

一覧：済み 12／全体 48（うち追加 4）

左の全添字に元のOverlapPartition × Cutを保持し、合成符号と同じraw語の正規化を読む。
右は元の外側語を等しい語長へ移した全Cutで、区間数の等式は(m+1)+d=(m+d)+1。
これは元の右の全Cutの算術的な等式移送で、別のCutを選び直すものではない。
元の右の全和との比較には既存sum_cutGenerator_terms_eq_mpとword_eq_mp_transを使える。
反復出現では左の分割が存在せず、右の全項は正次数の空語作用で零となる。
退化raw語の右の各項の零性も既存の全和の証明から取り出す。各証明200行以内。

```lean
def nullaryNativeOuterWord {m d : ℕ} (u : Surjection.BasisWord (m + 2) d) :
    Surjection.Word (m + 2) ((m + d) + 2)
```

```lean
lemma nullaryNativeOuterWord_count {m d : ℕ} (u : Surjection.BasisWord (m + 2) d)
    (k : Fin (m + 2)) :
    Surjection.occurrenceCount (nullaryNativeOuterWord u).val k = Surjection.occurrenceCount u.val k
```

```lean
lemma overlap_eq_single_of_count_one {n l : ℕ} (hn : n = 1)
    (ρ : Surjection.OverlapPartition n l) :
    ρ = Eq.mp (congrArg (fun C => Surjection.OverlapPartition C l) hn.symm)
      (Surjection.OverlapPartition.single l)
```

```lean
abbrev NullaryNativeBalanceIndex {m d : ℕ} (u : Surjection.BasisWord (m + 2) d)
    (k : Fin (m + 2)) (q : ℕ)
```

```lean
def nullaryNativeCompositeTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m d : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (q : ℕ)
    (c : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × Cut (m + d) q)
    (x : S _⦋q⦌) : (power (chains A S) (m + 1)).X (-((d + q : ℕ) : ℤ))
```

```lean
def nullaryNativeOuterTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m d : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (q : ℕ) (s : Cut ((m + d) + 1) q) (x : S _⦋q⦌) :
    (power (chains A S) (m + 1)).X (-((d + q : ℕ) : ℤ))
```

```lean
def nullaryNativeBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m d : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (q : ℕ) (i : NullaryNativeBalanceIndex u k q) (x : S _⦋q⦌) :
    (power (chains A S) (m + 1)).X (-((d + q : ℕ) : ℤ))
```

```lean
lemma nullaryOuterCutTerm_eq_zero_of_raw_degenerate
    (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (v : Surjection.Word (r + 1) (m + 2)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hv : ∀ i, k.succAbove (w i) = v.val (p.succAbove i)) (hw : ¬Surjection.Nondegenerate w)
    (ν : Surjection.BasisWord 0 0) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) (s : Cut (m + 1) q) :
    nullaryOuterCutTerm A S v ν k x z hz s = 0
```

```lean
lemma nullaryNativeBalanceTerm_eq_zero_of_count_ne_one
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (q : ℕ) (hcount : Surjection.occurrenceCount u.val k ≠ 1)
    (i : NullaryNativeBalanceIndex u k q) (x : S _⦋q⦌) :
    nullaryNativeBalanceTerm A S u ν k q i x = 0
```

この節は元の全添字・項・固定零項の入力の包装で、これだけで全分岐の対合を完了扱いにしない。
新しい数学や一覧IDは追加しない。


## 374. 元の全分割を保持する一出現・非退化対合（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§373の全添字に戻す。空語分割ρの一意性だけで左の分割因子を同値移送し、
同じ一点Cut挿入同値へ合成する。元のcompositionSignは内側次数零の既存法則で1。
これは既存の対合・係数移送の法則と証明分割で、新しい数学・一覧IDは足さない。
各証明200行以内。正次数の右Cutも消去せず固定零項として残す。

```lean
def nullaryOverlapCutEquiv {c N q : ℕ} (ρ : Surjection.OverlapPartition c 0) :
    (Surjection.OverlapPartition c 0 × Cut N q) ≃ Cut N q

lemma nullaryNativeCompositeTerm_eq_small
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (w : Surjection.BasisWord (m + 1) d) (hw : w.val = IntervalCuts.nullaryRawWord u ν k ρ)
    (c : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × Cut (m + d) q)
    (x : S _⦋q⦌) :
    nullaryNativeCompositeTerm A S u ν k q c x =
      nullarySmallCutTerm A S (positiveWord w) x (-((d + q : ℕ) : ℤ)) (by omega) c.2

lemma nullaryNativeBalance_pairing_of_nondegenerate {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (w : Surjection.BasisWord (m + 1) d) (hw : w.val = IntervalCuts.nullaryRawWord u ν k ρ) :
    ∃ τ : Equiv.Perm (NullaryNativeBalanceIndex u k q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryNativeBalanceTerm A S u ν k q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryNativeBalanceTerm A S u ν k q (τ i) x =
          -nullaryNativeBalanceTerm A S u ν k q i x)
```

## 375. 元の全空語添字の退化枝と正出力の包装（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§374の非退化対合が対象ビルドで通った。次は元の全ρ因子を保つ退化零項と、
反復・退化・非退化の三分岐を同じ全添字へ包装する。
元の零項の法則と既存対合の証明分割で、新しい構成・数学・IDは足さない。
各証明200行以内。零出力と正の内側arityまで含むL12a全体の完成とはしない。

```lean
lemma nullaryNativeBalanceTerm_eq_zero_of_degenerate
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (hdeg : ¬Surjection.Nondegenerate (IntervalCuts.nullaryRawWord u ν k ρ))
    (i : NullaryNativeBalanceIndex u k q) (x : S _⦋q⦌) :
    nullaryNativeBalanceTerm A S u ν k q i x = 0

lemma nullaryNativeBalance_pairing {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2)) :
    ∃ τ : Equiv.Perm (NullaryNativeBalanceIndex u k q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryNativeBalanceTerm A S u ν k q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryNativeBalanceTerm A S u ν k q (τ i) x =
          -nullaryNativeBalanceTerm A S u ν k q i x)
```

## 376. 元の全空語添字の正出力対合（検証済み、取り込み点）

一覧：済み 12／全体 48（うち追加 4）

§371〜375の9本を検証した。全ρ×全小Cutと全大Cutを保持し、非退化では
元の一点Cut挿入で対応させ、反復・退化・正次数の選択因子の零項を固定点に残す。
対合は係数環・単体に依存せず、全係数環・全入力で元の実テンソルの項が相殺する。
元のcompositionSignは内側次数零の法則で計算し、退化raw語の項も消していない。
零出力と全arityの有限添字の包装はまだ残る。L12aの完了を宣言しない。

登録対象（全て SerrePositivity.EInfinity.SimplexCuts の下）：

- MatchedSubsetPairing（87行）
- NullaryCanonicalBalanceTerms（60行）
- NullaryCanonicalBalanceValues（75行）
- NullaryCanonicalBalancePairing（49行）
- NullaryNativeInputData（45行）
- NullaryNativeBalanceTerms（51行）
- NullaryNativeZeroValues（64行）
- NullaryNativeNondegeneratePairing（100行）
- NullaryNativeBalancePairing（86行）

今回617行、M14実測28,643行、L12a 13,436行、外枠31,000行まで2,357行。
各証明200行以内。対象ビルド3083 jobs成功、追加警告0。
小さい監査9モジュール84宣言・標準三公理のみ、sorry・追加公理0。
最初のNativeInputDataの100字警告は改行して再ビルドで消した。
共有鍵は各対象ビルド・監査の間だけ取得し、全て返却済み。

完成見込みの外枠超過の懸念（§314以降）と完備化後P⁰の未評価分は残す。
mainは391b2a0d2のままで、3b-4a完成の取り込みはまだない。
完備化の三案は§369の結論を維持する：(a)の項別平坦模型と全鎖primitiveの比較は未証明、
(b)はperfect性だけで単位の全射を結論できず、(c)が不可欠とはまだ判定しない。

## 377. 零出力の元の有限項を一項ずつ読む（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

零出力では外側の正次数基底は空。外側次数零では元の全空語分割と
空作用の余単位一項（PUnit）、右側の元の全Cut 0 qを保持する。
Cut 0 qは元のcard=0から唯一。和の等式だけで済ませず、この唯一Cutに対応させる。
比較は§370の元の射の厳密な等式を、既存の全Cut展開と唯一性で一項へ戻す法則。
新しい数学・IDは足さず、各証明200行以内。

```lean
abbrev NullaryZeroBalanceIndex (u : Surjection.BasisWord 1 0) (k : Fin 1) (q : ℕ) :=
  (Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × PUnit) ⊕ Cut 0 q

def nullaryZeroCompositeTerm (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord 1 0) (ν : Surjection.BasisWord 0 0) (k : Fin 1) {q : ℕ}
    (c : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × PUnit)
    (x : S _⦋q⦌) : (power (chains A S) 0).X (-(q : ℤ))

def nullaryZeroOuterTerm (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord 1 0) (ν : Surjection.BasisWord 0 0) (k : Fin 1) {q : ℕ}
    (s : Cut 0 q) (x : S _⦋q⦌) : (power (chains A S) 0).X (-(q : ℤ))

lemma nullaryZeroCompositeTerm_eq_outer (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord 1 0) (ν : Surjection.BasisWord 0 0) (k : Fin 1) {q : ℕ}
    (c : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × PUnit)
    (s : Cut 0 q) (x : S _⦋q⦌) :
    nullaryZeroCompositeTerm A S u ν k c x = nullaryZeroOuterTerm A S u ν k s x
```

## 378. 零出力の全添字の対合（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

元の空語分割の一意性とcard=0のCutの一意性だけを使う。
全ρ×PUnitと全Cut 0 qの同値で左右を交換する。係数環・単体に共通、
元の一項ごとの比較は§377を使う。既存対合の法則と証明分割、各証明200行以内。

```lean
def nullaryZeroCutEquiv (u : Surjection.BasisWord 1 0) (k : Fin 1) (q : ℕ) :
    (Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × PUnit) ≃ Cut 0 q

def nullaryZeroBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord 1 0) (ν : Surjection.BasisWord 0 0) (k : Fin 1) (q : ℕ)
    (i : NullaryZeroBalanceIndex u k q) (x : S _⦋q⦌) : (power (chains A S) 0).X (-(q : ℤ))

lemma nullaryZeroBalance_pairing (u : Surjection.BasisWord 1 0)
    (ν : Surjection.BasisWord 0 0) (k : Fin 1) (q : ℕ) :
    ∃ τ : Equiv.Perm (NullaryZeroBalanceIndex u k q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryZeroBalanceTerm A S u ν k q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryZeroBalanceTerm A S u ν k q (τ i) x =
          -nullaryZeroBalanceTerm A S u ν k q i x)
```

## 379. L12aの元の全arity有限添字と共通次数の包装（実装前の型）

一覧：済み 12／全体 48（うち追加 4）

§112のCompositeBalanceIndex・compositeBalanceTerm・compositeBalance_pairingを、
正の内側arity、空語の正出力、空語の零出力で包装する。
空語の正次数とarity 1の外側正次数は基底が空なのでPEmpty。
正の枝だけは元の計算済み整数次数から-(d+e+q)へeqToHomを使う。
項・面・符号を変えず、同じ複体の等しい次数の移送。ホモトピー圏を使わない。
新しい数学・IDは足さず、各証明200行以内。

```lean
def CompositeBalanceIndex {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (q : ℕ) : Type

instance compositeBalanceIndexFintype {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (q : ℕ) : Fintype (CompositeBalanceIndex u v k q)

def compositeBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (q : ℕ) (i : CompositeBalanceIndex u v k q) (x : S _⦋q⦌) :
    (power (chains A S) (m + n)).X (-((d + e + q : ℕ) : ℤ))

lemma compositeBalance_pairing {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (q : ℕ) :
    ∃ τ : Equiv.Perm (CompositeBalanceIndex u v k q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        compositeBalanceTerm A S u v k q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        compositeBalanceTerm A S u v k q (τ i) x = -compositeBalanceTerm A S u v k q i x)
```

## 380. 完備化後P⁰の(a)(b)(c)：任意頂点の厳密表示と、指定Frobeniusの比較を分ける（紙のみ）

一覧：済み 13／全体 48（うち追加 4）

(a)の「同じnative頂点を厳密BE代数で表す」部分を、既存APIまで具体化した。
BarrattEccles/CAlgVertexPresentation.leanの
`cAlgVertexRepresentative A x : (operad A).Algebra` と
`cAlgVertexRepresentativeIso A x : VertexIso (cAlgVertex A (cAlgVertexRepresentative A x)) x`
が任意のCAlg_R頂点xに使える。CAlg.leanの`cAlgVertexEquiv`も、coherent nerveの
零単体と元のcofibrant代数の対象の同値である。
従って**完備化後の頂点に何らかの厳密BE表示がないこと**は障害ではない。
mod pの後の指定頂点についても同じF_p上のAPIを使える。
この表示だけから、各項を完備化した二重模型や指定Frobeniusの辺まで表せるとは言わない。

§369の項別平坦なセル模型の最後のretractの義務には、既存の
`Module.Flat.of_retract i r (r.comp i = LinearMap.id)`が直接使える。
`cofibrantCarrierKFlat_of_cellStages`が使う同じ代数retractをcarrier、各次数へ写せば、
最後のretractの平坦性はこの法則へ帰着する。
なお各段階の平坦性から最終filtered余極限の各次数の平坦性への比較はまだ必要で、
K平坦性の既存定理を項別平坦性として読み替えない。

(a)で残る本質的な比較は、選んだ厳密表示に対してMayの値を定義できるかではなく、
**元のcosimplicial/二重模型の指定Frobeniusが、完備化後にも同じ値を誘導するか**。
ordinaryな項別完備化を使うなら、有限多重線形作用の連続延長と、
全鎖での有限primitiveの恒等式（非cycleにはdaを含む誤差項）を検収する必要がある。
完備化のcycleを単に未完備のcycleで近似できるとは仮定しない。
L43bのclosed-inputの比較からこの全鎖の式が出るかは未証明であり、
新しい数学の補題が必要と確定したら型つき一覧の規則で別途停止する。
今回そのような追加補題のLeanを実装したものではない。

(b)は§357のperfect環・半線形同型だけでは単位の全射性やTate項消滅を導けない、
という結論のまま。actualなprismatic対象に必要な有界性・消滅の証明はまだない。
(a)の指定辺との比較が不可能と示せたわけではないので、(c)が不可欠とは判定しない。
(c)に至れば§32どおり止める。新しい仮定、G10の部品、界面・draftsの変更は加えていない。


## 381. L12aの全arity対合が完了（検証済み、取り込み点）

一覧：済み 13／全体 48（うち追加 4）

`CompositeBalancePairing.compositeBalance_pairing`が§112の型を満たした。
正の内側arity、空語の全正出力枝、零出力を全係数次数・全入力次数で含む。
元の全分割・全Cutを保持し、退化零項も固定零項として含める。
零出力は元のcard=0の唯一Cutと空作用の余単位の一項を対応させる。
対合は全係数環・全単体に共通。共通整数次数へのeqToHomも負号・零を保つ。
ホモトピー圏の等式への弱めはしていない。
L12aだけを完了へ進め、L12・L14・L16などの別項目は未完了のまま。

登録対象（全て SerrePositivity.EInfinity.SimplexCuts の下）：

- NullaryZeroBalanceValues（78行）
- NullaryZeroBalancePairing（72行）
- CompositeBalanceTerms（69行）
- CompositeBalancePairing（66行）

今回285行、M14実測28,928行、L12a 13,721行、外枠31,000行まで2,072行。
対象ビルド3292 jobs成功、追加警告0。
小さい監査4モジュール78宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。鍵は各対象ビルド・監査の間だけ取り、返却済み。
§376の登録対象9本は3b57d07e8。今回の4本と合わせて取り込み対象は13本。
共有入口・共有監査の登録は触っていない。
mainは391b2a0d2のまま。3b-4a完成の取り込みが入れば§33のTotへ切り替える。

§314以降の完成見込みが外枠に収まらない懸念と、完備化後P⁰の未評価分を維持する。
現在の実測は外枠内であり、次はL12の同じ有限和の相殺の包装へ進む。

