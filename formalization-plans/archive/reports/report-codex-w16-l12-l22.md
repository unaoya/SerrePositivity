# BS-W16 の報告（report-codex-w16.md） — L12〜L22（§382〜§403、2026-11-15）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 382. L12：同じ全有限和の相殺（実装前の型）

一覧：済み 13／全体 48（うち追加 4）

L12aの全対合と固定零項をFinset.sum_ninvolutionへ渡す。
左右の和は元の直和添字の左・右で取り、反対側では零を補うだけ。
左は合成側の正の項、右は二段側の項（balanceTermの負号を戻す）。
新しい係数・面・添字や数学は作らない既存有限和の法則の包装。
各証明200行以内。

```lean
def compositeBalanceIsLeft {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (q : ℕ) (i : CompositeBalanceIndex u v k q) : Bool

lemma sum_compositeBalanceTerm_eq_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (q : ℕ) (x : S _⦋q⦌) :
    ∑ i : CompositeBalanceIndex u v k q, compositeBalanceTerm A S u v k q i x = 0

def compositeCutSum (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) {q : ℕ} (x : S _⦋q⦌) :
    (power (chains A S) (m + n)).X (-((d + e + q : ℕ) : ℤ))
def nestedCutSum (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) {q : ℕ} (x : S _⦋q⦌) :
    (power (chains A S) (m + n)).X (-((d + e + q : ℕ) : ℤ))

lemma cutSum_composite (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) :
    compositeCutSum A S u v k x = nestedCutSum A S u v k x
```

## 383. L12：全arityの同じ有限Cut和の一致（検証済み、取り込み点）

一覧：済み 14／全体 48（うち追加 4）

`CompositeCutSumCancellation.cutSum_composite`が通った。
L12aの全対合をそのまま使い、固定点は零、非固定点は反対符号として相殺する。
合成側の全分割・Cutの項と二段側の全Cutの項を、元の直和の左右で選び、
反対側へ零を補う表記で左右の有限和を定義した。既存の整数係数・指定面は変更していない。
零出力・空語・退化項も含む全arity、全係数環、全入力次数での主張。
全複体射への延長（L14/L16）やL13などは、この有限和の包装だけで完了扱いにしない。

登録対象：SerrePositivity.EInfinity.SimplexCuts.CompositeCutSumCancellation（84行）。
対象ビルド3293 jobs成功、追加警告0。
小さい監査1モジュール18宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。共有鍵は対象ビルド・監査の間だけ取り、返却済み。

M14実測29,012行、L12a実測13,721行（今回L12の84行はL12aに重複計上しない）。
外枠31,000行まで1,988行。直前の会話中で29,019行と述べたのは加算の誤りで、
今回のファイルのwc -lは84行、28,928+84=29,012行が正しい。
完備化後P⁰の三案の紙の確認は§380。新しい仮定を足して隠していない。
M14全体の完成見込みの外枠超過の懸念は残り、一覧の残項を完成扱いにしていない。

## 384. L13：一般次数の一文字単位切断（実装前の型）

一覧：済み 14／全体 48（うち追加 4）

区間だけのUnitValuesは適用せず、同じ右単位子の値の補題だけを再利用する。
任意のCut 0 qはcard=0で唯一、一色の非退化性は格子経路のvertex_injectiveから得る。
fullColorVertices_eq_idと同じ順序列挙で指定面を恒等へ同定する。
符号は位置が一つなので逆転・caesuraがなく1。各証明200行以内。
既存構成の単位・指定面・係数移送の法則と証明分割で、新しいIDは足さない。

```lean
lemma unaryCut_faceData {q : ℕ} (s : Cut 0 q) (u : Surjection.Word 1 1) :
    (⟨outputDegree s u 0, vertices s u 0⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) =
      ⟨q, OrderHom.id⟩
lemma unaryCut_sign {q : ℕ} (s : Cut 0 q) (u : Surjection.Word 1 1) : cutSign s u.val = 1
lemma unaryCut_generatorFamily (A : Type u) [CommRing A] (S : SSet.{0}) {q : ℕ}
    (s : Cut 0 q) (u : Surjection.Word 1 1) (x : S _⦋q⦌) :
    cutGeneratorFamily A S s u x = fun _ => ⟨q, gen A S q x⟩
lemma vectorTensorAt_one (A : Type u) [CommRing A] (K : Complex A)
    (a : Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ) (h : -(a.1 : ℤ) = t) :
    vectorTensorAt K 1 (fun _ => a) t (by simp [vectorDegree, degreeSum]; omega) =
      (oneIso K).inv.f t ((eqToHom (congrArg K.X h)).hom a.2)
lemma cutSum_unit (A : Type u) [CommRing A] (S : SSet.{0}) {q : ℕ} (x : S _⦋q⦌) :
    cutSum A S (Surjection.permutationWord (1 : Equiv.Perm (Fin 1))) x =
      (oneIso (chains A S)).inv.f (-((0 + q : ℕ) : ℤ))
        ((eqToHom (congrArg (chains A S).X
          (by omega : -(q : ℤ) = -((0 + q : ℕ) : ℤ)))).hom (gen A S q x))
```

## 385. L13の全入力次数の単位Cut和（検証済み、取り込み点）

一覧：済み 15／全体 48（うち追加 4）

元の唯一Cutの色別順序列挙を恒等面へ戻し、全単体の生成元を得た。
同じ符号は1。一因子の斉次テンソルを一般の複体の右単位子の逆へ比較して、
`UnaryCutUnit.cutSum_unit`を全qについて証明した。
元のcutSumの整数次数-(0+q)と生成元の次数-qの等式移送を型に明示している。
区間用の単位作用の完成定理は使わず、一般の複体の右単位子の値だけを再利用した。

登録対象：SerrePositivity.EInfinity.SimplexCuts の下

- UnaryCutFaces（80行）
- UnaryCutUnit（64行）

今回144行、M14実測29,156行、外枠31,000行まで1,844行。
対象ビルド2703 jobs成功、追加警告0。
小さい監査2モジュール14宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。鍵は対象ビルド・監査の間だけ取り、返却済み。
mainは391b2a0d2のまま。§33の3b-4a完成の取り込みはまだない。
完備化後P⁰の指定Frobeniusとの比較は§380のまま未解決で、新しい仮定を加えていない。
L14の空語の実複体射の包装へ進む。

## 386. L14の空語余作用の指定射との一致（実装前の型）

一覧：済み 15／全体 48（うち追加 4）

零arityのcomponentは既にnullaryActionから定義されている。
元のtensorLiftの斉次成分とTensorProductの外延性で同じ複体射へ戻し、
左単位子の自然性だけで係数augmentation⊗AW余単位の式に直す。
既存構成の法則の証明分割で新しいIDなし、各証明200行以内。
L14の合成則の全複体射への延長は別に残す。

```lean
lemma cochainAction_nullary_eq (A : Type u) [CommRing A] (S : SSet.{0}) :
    cochainAction A S 0 = nullaryAction A S
lemma coaction_nullary (A : Type u) [CommRing A] (S : SSet.{0}) :
    cochainAction A S 0 =
      (nullaryCoefficientAugmentation A ⊗ₘ AlexanderWhitney.cochainCounit A S) ≫
        (λ_ (𝟙_ (Complex A))).hom
```

## 387. L14/L16の全整数外延性（実装前の型）

一覧：済み 15／全体 48（うち追加 4）

既存triple_extを二つのχの元の語基底と、一般Sの正規化生成元へ特殊化する。
区間に限定した外延性は使わず、複体の正次数は元の零延長から除く。
同じ線形写像の基底外延性・貼り合わせの法則と証明分割で、新しい数学・IDは足さない。
各証明200行以内。wordPairSimplexInputは元の二つのιTensorObjの値の記法だけ。

```lean
lemma chains_generator_linear_ext (A : Type u) [CommRing A] (S : SSet.{0}) (q : ℕ)
    {M : Type u} [AddCommGroup M] [Module A M]
    {f g : (chains A S).X (-(q : ℤ)) →ₗ[A] M}
    (h : ∀ x : S _⦋q⦌, f (gen A S q x) = g (gen A S q x)) : f = g
lemma coefficient_simplex_linear_ext (A : Type u) [CommRing A] (S : SSet.{0}) (m n d e q : ℕ)
    {M : Type u} [AddCommGroup M] [Module A M]
    {f g : ((Surjection.complex A m).X (-(d : ℤ)) ⊗[A]
      (Surjection.complex A n).X (-(e : ℤ))) ⊗[A] (chains A S).X (-(q : ℤ)) →ₗ[A] M}
    (h : ∀ (u : Surjection.BasisWord m d) (v : Surjection.BasisWord n e) (x : S _⦋q⦌),
      f (((Surjection.complexXIso A m d).inv (Surjection.basis A m d (ULift.up u)) ⊗ₜ[A]
        (Surjection.complexXIso A n e).inv (Surjection.basis A n e (ULift.up v))) ⊗ₜ[A] gen A S q x) =
      g (((Surjection.complexXIso A m d).inv (Surjection.basis A m d (ULift.up u)) ⊗ₜ[A]
        (Surjection.complexXIso A n e).inv (Surjection.basis A n e (ULift.up v))) ⊗ₜ[A] gen A S q x)) : f = g

def wordPairSimplexInput (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord m d) (v : Surjection.BasisWord n e) (x : S _⦋q⦌) :
    ((Surjection.complex A m ⊗ Surjection.complex A n) ⊗ chains A S).X
      (-(d : ℤ) + -(e : ℤ) + -(q : ℤ))
lemma coefficient_simplex_hom_ext (A : Type u) [CommRing A] (S : SSet.{0}) (m n : ℕ)
    {K : Complex A} {f g : (Surjection.complex A m ⊗ Surjection.complex A n) ⊗ chains A S ⟶ K}
    (h : ∀ (d e q : ℕ) (u : Surjection.BasisWord m d) (v : Surjection.BasisWord n e) (x : S _⦋q⦌),
      f.f (-(d : ℤ) + -(e : ℤ) + -(q : ℤ)) (wordPairSimplexInput A S u v x) =
        g.f (-(d : ℤ) + -(e : ℤ) + -(q : ℤ)) (wordPairSimplexInput A S u v x)) : f = g
```

## 388. L14/L16の同じ元の複体射の部分合成則（実装前の型）

一覧：済み 15／全体 48（うち追加 4）

§370の全arity基底値を§387の全整数外延性で延長する。
左辺の同じ複体合成の値はwhiskerRight_applyとcomplexPartialComposition_neg_tmul、
partialComposition_basisだけで元のcompositionOnWordsへ戻す。
中間整数次数-(d+e)と-d-eの照合は同じιTensorObjの等式移送で、作用・係数を変えない。
既存構成の係数移送・合成則と証明分割で新しい数学・IDなし、各証明200行以内。

```lean
lemma cochainAction_composition_input (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) :
    ((Surjection.complexPartialComposition A m n k ▷ chains A S) ≫
      cochainAction A S (m + n)).f (-(d : ℤ) + -(e : ℤ) + -(q : ℤ))
        (wordPairSimplexInput A S u v x) =
    (cochainAction A S (m + n)).f (-(d : ℤ) + -(e : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A (m + n)) (chains A S)
        (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(e : ℤ) + -(q : ℤ)) (by omega)
        ((Surjection.complexXIso A (m + n) (d + e)).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x))
lemma coaction_comp_all (A : Type u) [CommRing A] (S : SSet.{0}) (m n : ℕ) (k : Fin (m + 1)) :
    (Surjection.complexPartialComposition A m n k ▷ chains A S) ≫ cochainAction A S (m + n) =
      iteratedCochainAction A S m n k
lemma coaction_comp_nullary (A : Type u) [CommRing A] (S : SSet.{0}) (m : ℕ) (k : Fin (m + 1)) :
    (Surjection.complexPartialComposition A m 0 k ▷ chains A S) ≫ cochainAction A S m =
      iteratedCochainAction A S m 0 k
```


§386の第1型は既存の`CochainNullaryAction.cochainAction_zero_eq_nullaryAction`と同じである。
最終実装ではその既存宣言を直接再利用し、重複する新しい別名は追加しない。
新規NullaryActionLawには指定されたaugmentation⊗余単位の式の包装だけを残した。

## 389. L14・L16：全arityの元の実複体射の合成則（検証済み、取り込み点）

一覧：済み 17／全体 48（うち追加 4）

`coaction_comp_all`で、空語を含む全arityの元の複体射の部分合成則を示した。
基底値の一致だけでなく、正の整数次数の元は元の零延長で零、
非正整数次数は二語基底と任意次元の正規化生成元で判定する全射の外延性を通している。
`coaction_comp_nullary`と指定augmentation⊗AW余単位の`coaction_nullary`も含む。
L14とL16を完了へ進める。L15は次に残る。L12aの行数には重複計上しない。

登録対象：SerrePositivity.EInfinity.SimplexCuts の下

- NullaryActionLaw（29行）
- SimplexGeneratorLinearExt（61行）
- SimplexTripleGeneratorExt（83行）
- CochainCompositionInput（61行）
- CochainCompositionLaws（36行）

今回270行、M14実測29,426行、外枠31,000行まで1,574行。
対象ビルド3287 jobs成功、追加警告0。
小さい監査5モジュール32宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。共有鍵は各対象ビルド・監査の間だけ取り、返却済み。
mainは391b2a0d2のまま。3b-4a完成の取り込みはまだない。
完備化後P⁰の指定Frobeniusとの比較は§380のまま未解決で、新しい仮定なし。

## 390. L15の全複体射の自然性（実装前の型）

一覧：済み 17／全体 48（うち追加 4）

同じ基底外延性の二入力版を作り、L05のcutTerm_mapを全Cut和へ、
その後実際のcochainActionへ延長する。零arityは同じ空語augmentationと
既存cochainCounit_natural、左単位子の自然性だけを使う。
既存の自然性・線形延長・貼り合わせの法則の証明分割で、新しい数学・IDは足さない。
各証明200行以内。

```lean
lemma coefficient_simplex_pair_hom_ext (A : Type u) [CommRing A] (S : SSet.{0}) (m : ℕ)
    {K : Complex A} {f g : Surjection.complex A m ⊗ chains A S ⟶ K}
    (h : ∀ (d q : ℕ) (u : Surjection.BasisWord m d) (x : S _⦋q⦌),
      f.f (-((d + q : ℕ) : ℤ))
        (ιTensorObj (Surjection.complex A m) (chains A S) (-(d : ℤ)) (-(q : ℤ))
          (-((d + q : ℕ) : ℤ)) (by omega)
          ((Surjection.complexXIso A m d).inv (Surjection.basis A m d (ULift.up u)) ⊗ₜ[A] gen A S q x)) =
      g.f (-((d + q : ℕ) : ℤ))
        (ιTensorObj (Surjection.complex A m) (chains A S) (-(d : ℤ)) (-(q : ℤ))
          (-((d + q : ℕ) : ℤ)) (by omega)
          ((Surjection.complexXIso A m d).inv (Surjection.basis A m d (ULift.up u)) ⊗ₜ[A] gen A S q x))) : f = g
lemma cutSum_map (A : Type u) [CommRing A] {S T : SSet.{0}} (f : S ⟶ T)
    {r d q : ℕ} (u : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    (TensorPowers.map ((BarrattEccles.normalizedFunctor A).map f) (r + 1)).f (-((d + q : ℕ) : ℤ))
      (cutSum A S u x) = cutSum A T u (f.app _ x)
lemma coaction_natural (A : Type u) [CommRing A] {S T : SSet.{0}} (f : S ⟶ T) (r : ℕ) :
    (Surjection.complex A r ◁ (BarrattEccles.normalizedFunctor A).map f) ≫ cochainAction A T r =
      cochainAction A S r ≫ TensorPowers.map ((BarrattEccles.normalizedFunctor A).map f) r
```

## 391. L15：全arityの元の複体射の自然性（検証済み、取り込み点）

一覧：済み 18／全体 48（うち追加 4）

`CochainNaturality.coaction_natural`を全arityについて証明した。
正arityは元の全Cut項の自然性を全Cut和へ戻し、元の語基底と任意次元の
正規化単体生成元の外延性で全係数・全複体射へ延長した。
零arityは構成済みの空語作用と既存のAW余単位の自然性を使い、
左右のテンソル作用の交換と左単位子の自然性だけで同じ指定射へ戻した。
正整数次数の元は元の零延長で零。有限次元性・有界性の仮定は追加していない。

登録対象：SerrePositivity.EInfinity.SimplexCuts の下

- SimplexPairGeneratorExt（75行）
- CochainNaturality（55行）

今回130行、M14実測29,556行、外枠31,000行まで1,444行。
対象ビルド3010 jobs成功、追加警告0。
小さい監査2モジュール11宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。鍵は対象ビルド・監査の間だけ取り、返却済み。
mainは391b2a0d2のまま。3b-4a完成の取り込みはまだない。
次はL17の同変性・単位を実複体射へ延長し、L18の同じTRによる制限へ進む。
M14全体や完備化後P⁰の比較を完成扱いにしていない。完備化三案は§380の状態を維持する。

## 392. L17の同変性と単位の実複体射への延長（実装前の型）

一覧：済み 18／全体 48（うち追加 4）

同変性はL11と二入力外延性を使い、零arityの置換は唯一性で恒等へ戻す。
係数の負次数のrenameは既存complexRename_neg_hom_applyをそのまま使う。
単位はL13の同じ唯一Cut・指定面・一因子テンソルの計算を、入力の元の次数-qで読み、
左単位子とcomplexUnitの既存の値の公式で実複体射へ延長する。
既存構成の係数移送・単位・等変性・線形延長の法則と証明分割で、新しい数学・IDなし。
各証明200行以内。

```lean
lemma complexRename_basis_inv (A : Type u) [CommRing A] {n d : ℕ}
    (σ : Equiv.Perm (Fin n)) (v : Surjection.BasisWord n d) :
    (Surjection.complexRename A n σ).f (-(d : ℤ))
      ((Surjection.complexXIso A n d).inv (Surjection.basis A n d (ULift.up v))) =
        (Surjection.complexXIso A n d).inv
          (Surjection.basis A n d (ULift.up (Surjection.Word.rename σ v)))
lemma cochainAction_permutation (A : Type u) [CommRing A] (S : SSet.{0})
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Surjection.complexRename A n σ ▷ chains A S) ≫ cochainAction A S n =
      cochainAction A S n ≫ (permutationAction (chains A S) n σ).asIso.hom
lemma cochainAction_equivariance (A : Type u) [CommRing A] (S : SSet.{0})
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((Surjection.sequence A).map (FiniteBijection.permutation n σ) ▷ chains A S) ≫ cochainAction A S n =
      cochainAction A S n ≫ (permutationAction (chains A S) n σ).asIso.hom

lemma cochainAction_unit_generator (A : Type u) [CommRing A] (S : SSet.{0}) {q : ℕ} (x : S _⦋q⦌) :
    (cochainAction A S 1).f (-(q : ℤ))
      (ιTensorObj (Surjection.complex A 1) (chains A S) 0 (-(q : ℤ)) (-(q : ℤ)) (zero_add _)
        ((Surjection.complexXIso A 1 0).inv (Surjection.unitElement A) ⊗ₜ[A] gen A S q x)) =
      (oneIso (chains A S)).inv.f (-(q : ℤ)) (gen A S q x)
lemma cochainAction_unit_inv (A : Type u) [CommRing A] (S : SSet.{0}) :
    (λ_ (chains A S)).inv ≫ (Surjection.complexUnit A ▷ chains A S) ≫ cochainAction A S 1 =
      (oneIso (chains A S)).inv
lemma cochainAction_unit (A : Type u) [CommRing A] (S : SSet.{0}) :
    (Surjection.complexUnit A ▷ chains A S) ≫ cochainAction A S 1 ≫ (oneIso (chains A S)).hom =
      (λ_ (chains A S)).hom
```

## 393. L18の同じTRによる全単体集合の余代数（実装前の型）

一覧：済み 18／全体 48（うち追加 4）

証明済みの全arityの単位・同変性・部分合成則を既存Coalgebraの欄へ束ねる。
底の複体と射は元のnormalizedFunctorのまま、L15から余代数射を作る。
Eへの制限は既存restrictCoalgebraObj/Map/Functorと元のTableReduction.operadMapを使う。
新しい作用・模型を選ばない同じ構成の貼り合わせの包装。各証明200行以内。

```lean
def surjectionCoalgebra (A : Type u) [CommRing A] (S : SSet.{0}) :
    (Surjection.operad A).Coalgebra
def surjectionCoalgebraMap (A : Type u) [CommRing A] {S T : SSet.{0}} (f : S ⟶ T) :
    surjectionCoalgebra A S ⟶ surjectionCoalgebra A T
def surjectionCoalgebraFunctor (A : Type u) [CommRing A] :
    SSet.{0} ⥤ (Surjection.operad A).Coalgebra

def barrattEcclesCoalgebra (A : Type u) [CommRing A] (S : SSet.{0}) :
    (BarrattEccles.operad A).Coalgebra
def barrattEcclesCoalgebraMap (A : Type u) [CommRing A] {S T : SSet.{0}} (f : S ⟶ T) :
    barrattEcclesCoalgebra A S ⟶ barrattEcclesCoalgebra A T
def barrattEcclesCoalgebraFunctor (A : Type u) [CommRing A] :
    SSet.{0} ⥤ (BarrattEccles.operad A).Coalgebra
lemma barrattEcclesCoalgebra_coaction (A : Type u) [CommRing A] (S : SSet.{0}) (n : ℕ) :
    (barrattEcclesCoalgebra A S).coaction n =
      ((TableReduction.operadMap A).map.app (FiniteBijection.of n) ▷ chains A S) ≫
        cochainAction A S n
lemma barrattEcclesCoalgebraMap_hom (A : Type u) [CommRing A] {S T : SSet.{0}} (f : S ⟶ T) :
    (barrattEcclesCoalgebraMap A f).hom = (BarrattEccles.normalizedFunctor A).map f
```

§393のL18の射の保存式は、同じ既存CoalgebraHom.commの指定欄として明示する。
新しい主張ではなく、構成した射の欄を取り出す法則。

```lean
lemma barrattEcclesCoalgebraMap_comm (A : Type u) [CommRing A] {S T : SSet.{0}}
    (f : S ⟶ T) (n : ℕ) :
    ((BarrattEccles.operad A).arity n ◁ (BarrattEccles.normalizedFunctor A).map f) ≫
        (barrattEcclesCoalgebra A T).coaction n =
      (barrattEcclesCoalgebra A S).coaction n ≫
        TensorPowers.map ((BarrattEccles.normalizedFunctor A).map f) n
```

## 394. L17・L18：元の全単体集合のBF余代数関手（検証済み、取り込み点）

一覧：済み 20／全体 48（うち追加 4）

L17の全整数複体射の単位と同変性、L18のχ余代数とTRによるE余代数の関手が通った。
入力の単体次元・語次数・arityの制限はない。零arityは唯一の置換を恒等へ戻す。
単位は元の一文字語の唯一Cutを全単体で評価し、正整数次数の元は元の零延長で零とした。
対称列の指定置換、指定のcomplexUnit、同じTableReduction.operadMapを使用している。
底の複体・写像はnormalizedFunctorのものをそのまま保持し、作用の式と射の保存式を明示した。

登録対象：SerrePositivity.EInfinity.SimplexCuts の下

- CochainPermutation（66行）
- CochainUnit（91行）
- Coalgebra（80行）

今回237行、M14実測29,793行、外枠31,000行まで1,207行。
対象ビルド3359 jobs成功、追加警告0。
小さい監査3モジュール22宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。共有鍵は各対象ビルド・監査の間だけ取り、返却済み。
mainは391b2a0d2のまま。§33の3b-4a完成の取り込みはまだない。
次はL19以降のcosimplicial正規化。一般次元のBF余代数ができたことを、
正規化cosimplicial代数の全関手やMayのtop計算の完成とは扱わない。
完備化後P⁰の指定Frobeniusとの比較は§380のまま未解決。

## 395. L19の一般余単体的加群への特殊化（実装前の型）

一覧：済み 20／全体 48（うち追加 4）

正規化cosimplicial代数の加群忘却に使える一般性で置く。
SimplexCuts.normalizedComponent（χ係数の作用成分）とは別の名前空間
EInfinity.CosimplicialNormalizationを使う。
次数0は全体、次数q+1は全σ_iの核の共通部分。
微分は元の交代余面和そのもの。σ_iδ_jは二つの隣接項だけが恒等で、
残りは入力のσの零へ戻す。二項の整数符号は反対。
L19の既存cosimplicial恒等式・有限和・核の法則の証明分割で新しいIDなし。
各証明200行以内。

```lean
def normalizedSubmodule (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    (q : ℕ) → Submodule A (X.obj ⦋q⦌)
def alternatingCofaces (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) (q : ℕ) :
    X.obj ⦋q⦌ →ₗ[A] X.obj ⦋q + 1⦌
lemma mem_normalized_succ (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A))
    (q : ℕ) (a : X.obj ⦋q + 1⦌) :
    a ∈ normalizedSubmodule A X (q + 1) ↔ ∀ i : Fin (q + 1), (X.σ i) a = 0
lemma coface_codegeneracy_zero_of_not_neighbors
    (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) {q : ℕ}
    (a : X.obj ⦋q⦌) (ha : a ∈ normalizedSubmodule A X q) (i : Fin (q + 1)) (j : Fin (q + 2))
    (h₀ : j ≠ i.castSucc) (h₁ : j ≠ i.succ) : (X.σ i) ((X.δ j) a) = 0
lemma normalized_d_mem_exact (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A))
    (q : ℕ) (a : normalizedSubmodule A X q) :
    ∀ i : Fin (q + 1), (X.σ i) (alternatingCofaces A X q a.val) = 0
lemma alternatingCofaces_mem (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A))
    (q : ℕ) (a : normalizedSubmodule A X q) :
    alternatingCofaces A X q a.val ∈ normalizedSubmodule A X (q + 1)
```

## 396. L19の全codegeneracy核の微分保存（検証済み、取り込み点）

一覧：済み 21／全体 48（うち追加 4）

一般の余単体的A加群について、元の全σの核の共通部分を
元の交代余面微分が保つことを証明した。
次数零も含む。σ_iδ_jの隣接二項以外を同じ入力のσの零へ戻し、
残る二つの恒等項を元の整数符号で相殺する。
cosimplicial代数の加群忘却へ適用できる一般性で、有限次元性等の追加仮定なし。
正規化の作用成分名と衝突しない別の名前空間CosimplicialNormalizationに置いた。

登録対象：SerrePositivity.EInfinity.CosimplicialNormalization の下

- Components（34行）
- Differential（90行）

今回124行、M14実測29,917行、外枠31,000行まで1,083行。
対象ビルド1369 jobs成功、追加警告0。
小さい監査2モジュール21宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。共有鍵は対象ビルド・監査の間だけ取り、返却済み。
L20の同じ制限微分・包含・写像へ進む。

## 397. L20の同じ制限微分・包含・自然性（実装前の型）

一覧：済み 21／全体 48（うち追加 4）

元の交代余面複体の二乗零を使い、L19の核への制限を自然数コチェイン複体へ束ねる。
射は同じf.appの制限、包含は元の部分加群のsubtype。最後はembeddingUpNatによる
既存の零延長関手へ送る。G10・実現・native Totの部品は作らない。
既存構成の制限・微分・自然性・貼り合わせの法則と証明分割で新しいIDなし。
各証明200行以内。

```lean
lemma alternatingCofaces_eq_objD_hom (A : Type u) [CommRing A]
    (X : CosimplicialObject (ModuleCat A)) (q : ℕ) :
    alternatingCofaces A X q = (AlgebraicTopology.AlternatingCofaceMapComplex.objD X q).hom
def normalizedDifferential (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) (q : ℕ) :
    ModuleCat.of A (normalizedSubmodule A X q) ⟶ ModuleCat.of A (normalizedSubmodule A X (q + 1))
lemma normalizedDifferential_squared (A : Type u) [CommRing A]
    (X : CosimplicialObject (ModuleCat A)) (q : ℕ) :
    normalizedDifferential A X q ≫ normalizedDifferential A X (q + 1) = 0

def normalizedCochainNat (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    CochainComplex (ModuleCat A) ℕ
def normInclusionNat (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    normalizedCochainNat A X ⟶ (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).obj X
lemma normalized_map_mem (A : Type u) [CommRing A] {X Y : CosimplicialObject (ModuleCat A)}
    (f : X ⟶ Y) (q : ℕ) (a : normalizedSubmodule A X q) :
    (f.app ⦋q⦌) a.val ∈ normalizedSubmodule A Y q

def normalizedMapNat (A : Type u) [CommRing A] {X Y : CosimplicialObject (ModuleCat A)} (f : X ⟶ Y) :
    normalizedCochainNat A X ⟶ normalizedCochainNat A Y
def normalizedCochainNatFunctor (A : Type u) [CommRing A] :
    CosimplicialObject (ModuleCat A) ⥤ CochainComplex (ModuleCat A) ℕ
def normalizationInclusionNat (A : Type u) [CommRing A] :
    normalizedCochainNatFunctor A ⟶ AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)

def normalizedCochainFunctor (A : Type u) [CommRing A] :
    CosimplicialObject (ModuleCat A) ⥤ Complex A
def unnormalizedCochainFunctor (A : Type u) [CommRing A] :
    CosimplicialObject (ModuleCat A) ⥤ Complex A
def normalizationInclusion (A : Type u) [CommRing A] :
    normalizedCochainFunctor A ⟶ unnormalizedCochainFunctor A
def normInclusion (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    (normalizedCochainFunctor A).obj X ⟶ (unnormalizedCochainFunctor A).obj X
lemma normInclusion_d (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) (i j : ℤ) :
    ((normalizedCochainFunctor A).obj X).d i j ≫ (normInclusion A X).f j =
      (normInclusion A X).f i ≫ ((unnormalizedCochainFunctor A).obj X).d i j
lemma normInclusion_naturality (A : Type u) [CommRing A]
    {X Y : CosimplicialObject (ModuleCat A)} (f : X ⟶ Y) :
    (normalizedCochainFunctor A).map f ≫ normInclusion A Y =
      normInclusion A X ≫ (unnormalizedCochainFunctor A).map f
```

§397の整数零延長の次数比較も、既存extendXIsoの指定同型として取り出す。

```lean
def normalizedCochainXIso (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) (q : ℕ) :
    ((normalizedCochainFunctor A).obj X).X (q : ℤ) ≅ ModuleCat.of A (normalizedSubmodule A X q)
```

## 398. L20の全整数正規化複体と指定包含（検証済み、取り込み点）

一覧：済み 22／全体 48（うち追加 4）

L19の元の核への制限微分を自然数コチェイン複体に束ね、
二乗零は元の交代余面複体のd_squaredから判定した。
全余単体的写像の各項を同じ核へ制限して関手にし、元のsubtypeの包含を自然変換にした。
これらを既存embeddingUpNatの零延長関手へ送り、全整数での微分との可換性と自然性を得た。
整数非負次数と元の全codegeneracy核の指定比較も既存extendXIsoで明示した。
一般余単体的A加群の構成なので、cosimplicial代数の加群忘却へ適用できる。
指定包含のホモトピー逆（L21）、代数作用やnative Totは完成扱いにしない。

登録対象：SerrePositivity.EInfinity.CosimplicialNormalization の下

- NatComplex（63行）
- NatFunctor（91行）
- IntegerComplex（57行）

今回211行、M14実測30,128行、外枠31,000行まで872行。
対象ビルド1920 jobs成功、追加警告0。
小さい監査3モジュール31宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。共有鍵は各対象ビルド・監査の間だけ取り、返却済み。
mainは391b2a0d2のまま。§33の3b-4a完成の取り込みはまだない。

### 398.1 L21への既存APIの入口と残りの外枠

MathlibのDoldKan.Degeneracies.leanにはσ_comp_PInftyと
`degeneraciesVanish_iff_QInfty_f_comp`、PInfty.leanにはPInfty_f_add_QInfty_fがある。
HomotopyEquivalence.leanの`homotopyPInftyToId`を、同じcosimplicial対象を
反対圏で見たsimplicial対象へ適用できる。
Homotopy.unopとEmbedding/ExtendHomotopy.leanのHomotopy.extendも既存。
従ってL21では新しい収縮を作らず、同じPInftyの反対圏による移送を試す。
移した射影が全σの核に入ること、核で恒等であること、
同じ指定包含との合成が元の射影であることの接続はまだ未実装。

この接続と指定ホモトピー逆の包装を新規300〜550行程度と暫定見積もりする。
L21をこの範囲で閉じても残り外枠は322〜572行。
§314のL22〜26の未供給の評価・復元の下端900行だけでもそこに収まらない。
外枠は自分では上げず、次の接続が超えそうな所で検証済みをコミットして停止する。
L22以降やMayのtop計算、完備化後P⁰の未評価分を消した見積もりにはしない。
完備化の三案の比較は§380のまま。指定Frobeniusとの比較は未解決で、仮定を追加していない。

## 399. L21の同じDold–Kan射影の反対圏移送（実装前の型）

一覧：済み 22／全体 48（うち追加 4）

§398.1の経路を型に落とす。同じ余単体的対象を反対圏のsimplicial対象で読み、
既存PInftyとhomotopyPInftyToIdを運ぶ。指定した全σ核と包含は変更しない。
σ_comp_PInftyで像が核に入ること、degeneraciesVanish_iff_QInfty_f_compと
PInfty_f_add_QInfty_fで核上の恒等性を判定する。
全てL21の既存射影の係数移送・法則・貼り合わせの証明分割。新しいIDは足さない。
各証明200行以内。残り外枠872行、L21の見込み300〜550行。

```lean
def dualSimplicial (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    SimplicialObject ((ModuleCat A)ᵒᵖ)
def dualAlternatingIso (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    ((AlgebraicTopology.alternatingFaceMapComplex ((ModuleCat A)ᵒᵖ)).obj (dualSimplicial A X)).unop ≅
      (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).obj X

def cofaceProjectorNat (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).obj X ⟶
      (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).obj X
lemma cofaceProjectorNat_f (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) (q : ℕ) :
    (cofaceProjectorNat A X).f q =
      ((AlgebraicTopology.DoldKan.PInfty (X := dualSimplicial A X)).f q).unop
def cofaceProjectorNat_homotopy (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    Homotopy (cofaceProjectorNat A X) (𝟙 _)

lemma cofaceProjectorNat_mem (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A))
    (q : ℕ) (a : X.obj ⦋q⦌) : (cofaceProjectorNat A X).f q a ∈ normalizedSubmodule A X q
lemma cofaceProjectorNat_normalized (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A))
    (q : ℕ) (a : normalizedSubmodule A X q) : (cofaceProjectorNat A X).f q a.val = a.val

def normalizationRetractionNat (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).obj X ⟶ normalizedCochainNat A X
lemma normInclusionNat_retraction (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    normInclusionNat A X ≫ normalizationRetractionNat A X = 𝟙 _
lemma normalizationRetractionNat_inclusion (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    normalizationRetractionNat A X ≫ normInclusionNat A X = cofaceProjectorNat A X

def normalizationHomotopyEquivNat (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    HomotopyEquiv (normalizedCochainNat A X)
      ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).obj X)
def normalizationHomotopyEquiv (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    HomotopyEquiv ((normalizedCochainFunctor A).obj X) ((unnormalizedCochainFunctor A).obj X)
lemma normalizationHomotopyEquiv_hom (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat A)) :
    (normalizationHomotopyEquiv A X).hom = normInclusion A X
```

## 400. L21の指定正規化包含のホモトピー逆（検証済み、取り込み点）

一覧：済み 23／全体 48（うち追加 4）

`normalizationHomotopyEquiv`を全整数の同じ複体について構成した。
`normalizationHomotopyEquiv_hom`はrflで、homはL20の元のnormInclusionそのもの。
別の比較射への変更や、擬同型の存在だけへの弱めはしていない。

同じ対象を反対圏のsimplicial対象で読み、既存PInftyとhomotopyPInftyToIdを移した。
σ_comp_PInftyから像が全σの核に入ることを示し、
degeneraciesVanish_iff_QInfty_f_compとPInfty+QInfty=1から同じ核上の恒等性を得た。
その射影を元の核へ制限して逆射を作り、包含との一方の合成は厳密な恒等、
もう一方は元の同じ射影と厳密に一致。既存ホモトピーを後者へ接続した。
自然数複体から既存Homotopy.extendで同じembeddingUpNatの零延長へ送っている。
一般余単体的A加群の全次数の主張で、有界性・有限次元性などの追加仮定なし。
新しい収縮やG10・native Totの部品は作っていない。

登録対象：SerrePositivity.EInfinity.CosimplicialNormalization の下

- DualProjector（75行）
- ProjectorKernels（64行）
- NatHomotopyEquiv（74行）
- IntegerHomotopyEquiv（43行）

今回256行、M14実測30,384行、外枠31,000行まで616行。
見込み300〜550行との差は44〜294行減。既存の退化消滅の同値とP+Qの恒等式を直接使い、
新しい射影・ホモトピーの再構成を省けた分。
対象ビルド1936 jobs成功、追加警告0。
小さい監査4モジュール30宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。共有鍵は各対象ビルド・監査の間だけ取り、返却済み。
mainは391b2a0d2のまま。§33の3b-4a完成の取り込みはまだない。

### 400.1 L22の入力の確認と次の外枠

次はL22のconvolutionの等化子の関手性。元の
SerrePositivity.Cosimplicial.CosimplicialAlgebra Aは
`CosimplicialObject (Under (CommRingCat.of A))`であることを確認した。
CommAlgCat値だけへ範囲を変更しない。各項の離散BE代数には、既存の
`(commAlgCatEquivUnder (CommRingCat.of A)).inverse`の後に
BarrattEccles.discreteAlgebraFunctor Aを用いる経路が既に本体にある。

P・Qの元の全次数の積には、Functor.pi'とLimits.Pi.functorを組み合わせれば
対象ごとの積と同じ射を保った関手を作れる。
後合成には既存convolutionFunctor、前合成の自然性にはconvolutionPreNatが使える。
L22の新規は従来の140〜260行程度を入口とするが、未検証の見込みであり、
全等化子や評価・復元ができたとはしていない。
これを閉じても残りは356〜476行で、L23の従来見込み450〜850行は上端が収まらない。
外枠は上げず、超えそうな所で検証済みをコミットして報告して止める。
完備化後P⁰の三案と指定Frobeniusの未解決の比較は§380のまま維持する。

## 401. L22の元の全積・二射・等化子（実装前の型）

一覧：済み 23／全体 48（うち追加 4）

元のCosimplicialAlgebra A（Under値）を保つ。各項の離散代数は既存のUnderの同値と
既存discreteAlgebraFunctorを合成し、単体余代数はL18の同じ全BF作用を使う。
P・Qは全次数と全単体射にわたる元の積。積の射影・等化子の包含を保持する。
前後合成の自然性はconvolutionFunctorとconvolutionPreNatの既存の法則。
等化子の射は同じ積の射をequalizer.liftする。恒等・合成は包含で判定する。
既存構成の自然性・単位・合成・貼り合わせの法則の証明分割で新しい数学・IDなし。
各証明200行以内。残り外枠616行。L23の評価・復元や台の同型はまだ含めない。

以下はEInfinity.BergerFresse名前空間。CosimplicialAlgebraは元の同じ別名。

```lean
abbrev SimplexMorphismIndex := Σ q r : ℕ, (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌
def discreteUnderFunctor (A : Type u) [CommRing A] :
    Under (CommRingCat.of A) ⥤ (BarrattEccles.operad A).Algebra
def simplexCoalgebraFunctor (A : Type u) [CommRing A] :
    SimplexCategory ⥤ (BarrattEccles.operad A).Coalgebra

def convolutionOnUnder (A : Type u) [CommRing A] (q : ℕ) :
    Under (CommRingCat.of A) ⥤ (BarrattEccles.operad A).Algebra
def convolutionAt (A : Type u) [CommRing A] (q r : ℕ) :
    CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra

def postAt (A : Type u) [CommRing A] {q r : ℕ} (α : (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌) :
    convolutionAt A q q ⟶ convolutionAt A q r
def preAt (A : Type u) [CommRing A] {q r : ℕ} (α : (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌) :
    convolutionAt A r r ⟶ convolutionAt A q r

def convolutionProductFunctor (A : Type u) [CommRing A] :
    CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra
def convolutionArrowProductFunctor (A : Type u) [CommRing A] :
    CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra
def convolutionProductProjection (A : Type u) [CommRing A] (q : ℕ) :
    convolutionProductFunctor A ⟶ convolutionAt A q q

def convolutionProductLift (A : Type u) [CommRing A] {ι : Type}
    (F : CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra)
    (G : ι → CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra) (φ : ∀ i, F ⟶ G i) :
    F ⟶ Functor.pi' G ⋙ Limits.Pi.functor ι

def post (A : Type u) [CommRing A] : convolutionProductFunctor A ⟶ convolutionArrowProductFunctor A
def pre (A : Type u) [CommRing A] : convolutionProductFunctor A ⟶ convolutionArrowProductFunctor A
lemma post_naturality (A : Type u) [CommRing A] {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    (convolutionProductFunctor A).map f ≫ (post A).app Y =
      (post A).app X ≫ (convolutionArrowProductFunctor A).map f
lemma pre_naturality (A : Type u) [CommRing A] {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    (convolutionProductFunctor A).map f ≫ (pre A).app Y =
      (pre A).app X ≫ (convolutionArrowProductFunctor A).map f

def bfNormalizedObj (A : Type u) [CommRing A] (X : CosimplicialAlgebra A) :
    (BarrattEccles.operad A).Algebra
def bfNormalizedMap (A : Type u) [CommRing A] {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    bfNormalizedObj A X ⟶ bfNormalizedObj A Y

def bfNormalizedAlgebra (A : Type u) [CommRing A] :
    CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra
lemma bfNormalizedAlgebra_map_id (A : Type u) [CommRing A] (X : CosimplicialAlgebra A) :
    bfNormalizedMap A (𝟙 X) = 𝟙 (bfNormalizedObj A X)
lemma bfNormalizedAlgebra_map_comp (A : Type u) [CommRing A]
    {X Y Z : CosimplicialAlgebra A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    bfNormalizedMap A (f ≫ g) = bfNormalizedMap A f ≫ bfNormalizedMap A g
```

## 402. L22の半分の区切りと内部補助の型の整理（実装前）

一覧：済み 23／全体 48（うち追加 4）

下書き198行、ConvolutionDiagramの71行は対象ビルド成功。
残る全積と等化子の包装は未検証で、L22は未完了。
内部補助convolutionProductLiftの不要な一般添字ι・任意の積族Gで
型クラス探索が時間切れになった。heartbeatsは上げず、元の全単体射の積専用の補助とする。
L22の全入力X・全次数・全単体射の範囲、元の積・等化子は変更しない。
この補助は新規・未コミットで、既存の公開宣言の型は変えない。

```lean
def convolutionProductLift (A : Type u) [CommRing A]
    (F : CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra)
    (φ : ∀ α : SimplexMorphismIndex, F ⟶ convolutionAt A α.1 α.2.1) :
    F ⟶ convolutionArrowProductFunctor A
```

半分の見込みを再確認すると、図式71行と残る包装120〜160行程度で191〜231行。
現在のM14の検証済み30,384行に足しても外枠31,000行の中。
等化子の台の評価・復元は別のL23であり、この見込みに完成分として含めない。


## 403. L22の元の全convolution等化子の全関手が完了（検証済み、取り込み点）

一覧：済み 24／全体 48（うち追加 4）

元のUnder値CosimplicialAlgebra Aを入力とし、全次数・全単体射の積の
post/preを同じ射で等化するbfNormalizedAlgebraを作った。
射は元の積の射を持ち上げ、恒等・合成は元の等化子の包含で判定した。
対象ごとの等化子だけでなく全関手。ホモトピー圏への弱めはない。
L23の評価・復元、L26の正規化複体との指定同型はまだ含まない。

登録対象（全てSerrePositivity.EInfinity.BergerFresseの下）：

- ConvolutionDiagram（71行）：Underの同じ離散代数、全単体の同じBE余代数、前後合成。
- ProductDiagram（71行）：元の全積の関手、射影、前後合成の自然変換。
- EqualizerFunctor（60行）：同じ等化子、同じ射、恒等・合成と全関手。

追加202行。L22の見込み140〜260行の範囲内。
M14実測30,586行、外枠31,000行まで414行。
対象ビルド3746 jobs成功、追加警告0。
小監査3モジュール31宣言・標準三公理のみ、sorry・追加公理0。
各証明200行以内。対象ビルドと小監査の終了を確認し、鍵は返却済み。
監査開始時に別の既存lake buildの通知はあったが、当レーンの常駐セッションではない。
共有の入口・監査・他レーン・draftsは変更していない。

検証ログ：
`/tmp/bsw16/m14-bf-equalizer-functor-04.log`、
`/tmp/bsw16/audit-m14-bf-equalizer-functor.log`。

