# BS-W16 の報告（report-codex-w16.md） — L10（§138〜§146、2026-11-14）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 138. L10への接続：既存の基底と正規化生成元の外延性（実装前の型）

一覧：済み 10／全体 48（うち追加 4）

L09の検証済み7本はd5a28b42fへ保存した。次は固定したL10の全整数Leibnizへ進む。
まずC303は既存のSurjection.basis.extとAlexanderWhitney.generator_hom_extを
同じ双線形族へ適用する構成の法則。新しい生成性の定理は作らない。
arityはnで零も許すが、χ・入力複体・微分の組み立ては固定した§108のとおりにする。
この法則だけでL10完了とは数えない。局所heは元の二つのLinearMapをModuleCat.ofHomで
見た射の等式で、最後に元の線形写像へ戻す。個々の補題200行以内。型を記録して実装する。

```lean
lemma normalized_bilinear_ext (S : SSet.{0}) {n d q : ℕ} {M : ModuleCat A}
    (f g : Surjection.degreeModule A n d →ₗ[A] (AlexanderWhitney.chains A S).X q →ₗ[A] M)
    (h : ∀ (w : Surjection.BasisWord n d) (x : S _⦋q⦌),
      f (Surjection.basis A n d (ULift.up w)) (AlexanderWhitney.generator A S q x) =
        g (Surjection.basis A n d (ULift.up w)) (AlexanderWhitney.generator A S q x)) :
    f = g
```

C303の実装では出力Mの宇宙を `{M : ModuleCat.{u} A}` と明示する。
既存generator_hom_extとL10の実際の終域のテンソル冪は、どちらもAと同じ宇宙uの
ModuleCatを使う。省略した宇宙が新しい変数として推論されるのを防ぐためで、
L10の固定した型・係数環・入力・終域を変更するものではない。

### 138.1 C303の検証・保存

一覧：済み 10／全体 48（うち追加 4）

C303の対象ビルド **成功、2,320 jobs**。専用の小さい監査は
**1モジュール・1宣言・標準三公理のみ**。sorry・追加公理0、Lean警告0。
`NormalizedBilinearExt.lean` は36行。未登録の新規モジュール候補として追加する
（`SerrePositivity.EInfinity.SimplexCuts.NormalizedBilinearExt`）。
L09の7本とは別のL10の補助であり、L10完了とは数えない。

ログ：`/tmp/bsw16/m14-normalized-bilinear-ext-02.log`、
監査：`/tmp/bsw16/audit-m14-normalized-bilinear-ext.lean`、
結果：`/tmp/bsw16/m14-normalized-bilinear-ext-audit.log`。
鍵はビルド・監査ごとに取り、終了を確認して返却した。

M14の実測は14,057+36=**14,093行**、L09a・L09の最終実測8,991行は不変。
L10の実装済み補助は36行。外枠25,000行は変更せず、残り枠は **10,907行**。
次のL10の束の見込みを出す際、この36行を未実装部分へ重ねて加算しない。

### 138.2 L10の残る成分と法則の型（紙のみ）

一覧：済み 10／全体 48（うち追加 4）

既存normalizedComponentと元の二つの微分の合成を、同じ双線形族の値として読む。
以下二つはその線形像の記法であり、係数微分・入力微分を別のものへ変更しない。
C304はC303で元の基底・正規化生成元へ帰着し、L09を適用する。

```lean
def normalizedCoefficientBoundary (A : Type u) [CommRing A] (S : SSet.{0}) (r : ℕ) :
    (d q : ℕ) → Surjection.degreeModule A (r + 1) d →ₗ[A]
      (AlexanderWhitney.chains A S).X q →ₗ[A]
        (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)

def normalizedSimplexBoundary (A : Type u) [CommRing A] (S : SSet.{0}) (r : ℕ) :
    (d q : ℕ) → Surjection.degreeModule A (r + 1) d →ₗ[A]
      (AlexanderWhitney.chains A S).X q →ₗ[A]
        (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)

-- C304：同じ非負次数の双線形族の微分の法則。
lemma normalizedComponent_d (A : Type u) [CommRing A] (S : SSet.{0}) (r d q : ℕ) :
    (normalizedComponent A S r d q).compr₂
        ((power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
          (-((d + q : ℕ) : ℤ) + 1)).hom =
      normalizedCoefficientBoundary A S r d q +
        (-1 : ℤ) ^ d • normalizedSimplexBoundary A S r d q
```

前者はd=0で零、d+1で元のSurjection.differentialをnormalizedComponentの係数側へ前置し、
共通次数へ移す。後者はq=0で零、q+1で元の正規化鎖のdを入力側へ前置して共通次数へ移す。
これらの生成元の値は、検証済みL09の右辺の二つの線形像そのもの。

次に、既存positiveComponentを両入力の非正整数次数へ等式移送で延長し、正次数は零とする。
これは§108.2で固定した整数次数のcomponentを組み立てる補助で、新しい作用の選択ではない。
正arityの補助の型は次。arity零の扱いは固定した§108.3・L14の規約を維持する。

```lean
def positiveIntegerBilinear (A : Type u) [CommRing A] (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) :
    (Surjection.complex A (r + 1)).X i →ₗ[A] (chains A S).X j →ₗ[A]
      (power (chains A S) (r + 1)).X t

-- C305：元の負自然数次数では、同じ既存positiveComponentを復元。
lemma positiveIntegerBilinear_neg (A : Type u) [CommRing A] (S : SSet.{0}) (r d q : ℕ) :
    positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ)) (-((d + q : ℕ) : ℤ)) (by omega) =
      positiveComponent A S r d q

-- C306：同じ正arityの全整数双線形成分のLeibniz則。
lemma positiveIntegerBilinear_d (A : Type u) [CommRing A] (S : SSet.{0})
    (r : ℕ) (i j : ℤ) (a : (Surjection.complex A (r + 1)).X i) (b : (chains A S).X j) :
    (power (chains A S) (r + 1)).d (i + j) (i + j + 1)
        (positiveIntegerBilinear A S r i j (i + j) rfl a b) =
      positiveIntegerBilinear A S r (i + 1) j (i + j + 1) (by omega)
        ((Surjection.complex A (r + 1)).d i (i + 1) a) b +
      i.negOnePow • positiveIntegerBilinear A S r i (j + 1) (i + j + 1) (by omega) a
        ((chains A S).d j (j + 1) b)
```

整数の非正分岐ではd=(-i).toNat・q=(-j).toNatとし、既存positiveComponentの前後を
同じ次数のeqToHomで移す。C306は§136.4の次元によらないχの微分比較、chains_d_neg、
正次数の零性、C304・C305を使う。区間の零・−1以外の零性は一般Sへ適用しない。
その後TensorProduct.ext・tensorLiftへ渡す。L10の固定した全体の型は§108のまま維持する。
上の型はC303以外まだ紙のみで、完了数・検証済み行数へ含めない。

## 139. 同じ正規化双線形族の微分の接続（L10、実装前の型）

一覧：済み 10／全体 48（うち追加 4）

§138.2の二つの既存線形像の記法とC304を実装する。C307・C308は、その同じ基底・
正規化生成元での評価の法則。C307は既存normalizedComponent_gen、C308は同じ入力の
線形合成の評価で、次数零も含む。C304はC303と検証済みL09だけで証明する。
新しい生成性の数学や比較射を作らない。個々の補題200行以内。追加する評価の型は次。

```lean
lemma normalizedCoefficientBoundary_generator (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    normalizedCoefficientBoundary A S r d q (Surjection.basis A (r + 1) d (ULift.up w))
        (AlexanderWhitney.generator A S q x) = cutSumCoefficientBoundary A S r d q w x

lemma normalizedSimplexBoundary_generator (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    normalizedSimplexBoundary A S r d q (Surjection.basis A (r + 1) d (ULift.up w))
        (AlexanderWhitney.generator A S q x) = cutSumSimplexBoundary A S w q x
```

二つの定義とC304の型は§138.2のまま。L10の全整数の組み立ては未完で、完了数へ足さない。

### 139.1 C304・C307・C308 の検証・保存

一覧：済み 10／全体 48（うち追加 4）

対象ビルド成功（2,527 jobs）、小さい監査成功（1モジュール・40宣言、標準三公理のみ）。
sorry・追加公理0、Lean警告0。NormalizedComponentDifferential.lean は77行。
登録候補：`SerrePositivity.EInfinity.SimplexCuts.NormalizedComponentDifferential`。
ビルドログ：`/tmp/bsw16/m14-normalized-component-differential-01.log`。
監査入力：`/tmp/bsw16/audit-m14-normalized-component-differential.lean`、
監査結果：`/tmp/bsw16/m14-normalized-component-differential-audit.log`。
各鍵は終了・返却を確認。全整数のLeibniz則はまだ未完なのでL10を完了へ足さない。

M14実測14,093+77=**14,170行**、L09a・L09の8,991行は不変。
L10の実装済み補助は113行。外枠25,000行、残り10,830行。

## 140. 同じ成分の整数次数への延長（L10、実装前の型）

一覧：済み 10／全体 48（うち追加 4）

§138.2 の positiveIntegerBilinear・C305 を実装する。係数・入力の双方を元の
負自然数次数へ同じ等式で移送し、正次数の分岐を零とする。C309・C310 は
その定義の分岐の法則で、既存の零延長以外の数学を追加しない。型は次。

```lean
lemma positiveIntegerBilinear_eq_zero_left (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) (hi : 0 < i) :
    positiveIntegerBilinear A S r i j t h = 0

lemma positiveIntegerBilinear_eq_zero_right (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) (hj : 0 < j) :
    positiveIntegerBilinear A S r i j t h = 0
```

C305・整数成分の型は§138.2のまま。C306とテンソル複体の射への接続は次。
個々の法則は200行以内。L10未完、一覧の数は変えない。

### 140.1 出力次数の移送の法則（C311、実装前）

一覧：済み 10／全体 48（うち追加 4）

C305・C309・C310 の対象ビルドは2,528 jobsで成功、Lean警告0。
依存型の次数移送は自然数の零・後続へ分ければ元の成分と定義的に同じになる。
全整数微分への接続に、同じ出力次数を変数tで読む法則だけを足す。

```lean
lemma positiveIntegerBilinear_neg_target (S : SSet.{0}) (r d q : ℕ) (t : ℤ)
    (h : -(d : ℤ) + -(q : ℤ) = t) :
    positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ)) t h =
      (positiveComponent A S r d q).compr₂
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z)
          (by omega : -((d + q : ℕ) : ℤ) = t))).hom
```

出力の和を代入してC305を使う証明の分割で、新しい比較射ではない。

## 141. 元の整数複体の二つの微分への接続（L10、実装前）

一覧：済み 10／全体 48（うち追加 4）

C312はC304へ同じ次数同型を前置した評価。C313は元のχの延長微分の
`IntervalCuts.surjection_d_neg_apply`、C314は元の鎖の`chains_d_neg`を使う。
入力を区間へ制限せず、同じ一般Sの全非負鎖次数を扱う。いずれも既存構成の
係数移送・微分との両立の法則で、新しい作用や擬同型の構成ではない。

```lean
lemma positiveComponent_d (S : SSet.{0}) (r d q : ℕ)
    (a : (Surjection.complex A (r + 1)).X (-(d : ℤ)))
    (b : (chains A S).X (-(q : ℤ))) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ)) (-((d + q : ℕ) : ℤ) + 1)
      (positiveComponent A S r d q a b) =
    normalizedCoefficientBoundary A S r d q
      ((Surjection.complexXIso A (r + 1) d).hom a) ((chainsXIso A S q).hom b) +
    (-1 : ℤ)^d • normalizedSimplexBoundary A S r d q
      ((Surjection.complexXIso A (r + 1) d).hom a) ((chainsXIso A S q).hom b)

lemma positiveCoefficientBoundary_succ (S : SSet.{0}) (r d q : ℕ)
    (a : (Surjection.complex A (r + 1)).X (-((d + 1 : ℕ) : ℤ)))
    (b : (chains A S).X (-(q : ℤ))) :
    normalizedCoefficientBoundary A S r (d + 1) q
      ((Surjection.complexXIso A (r + 1) (d + 1)).hom a) ((chainsXIso A S q).hom b) =
    positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ))
      (-(((d + 1) + q : ℕ) : ℤ) + 1) (by omega)
      ((Surjection.complex A (r + 1)).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ)) a) b

lemma positiveSimplexBoundary_succ (S : SSet.{0}) (r d q : ℕ)
    (a : (Surjection.complex A (r + 1)).X (-(d : ℤ)))
    (b : (chains A S).X (-((q + 1 : ℕ) : ℤ))) :
    normalizedSimplexBoundary A S r d (q + 1)
      ((Surjection.complexXIso A (r + 1) d).hom a) ((chainsXIso A S (q + 1)).hom b) =
    positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ))
      (-((d + (q + 1) : ℕ) : ℤ) + 1) (by omega) a
      ((chains A S).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) b)
```

C313・C314の次数零の分岐は、C309・C310と正規化境界の零分岐を使う。
最後の全整数LeibnizはC306（§138.2）のまま。個々の証明200行以内。

## 142. 全整数の Leibniz の次数の指定（L10、実装前）

一覧：済み 10／全体 48（うち追加 4）

C311とC312・C313は型検査済み。C314の次数移送の終域を明示して検証を続ける。
C306の型は§138.2のまま。前提計算として、同じ等式の各次数を別名で指定する
C315を置く。証明は指定した四つの次数の等式による置換のみ。

```lean
lemma positiveIntegerBilinear_d_reindex (S : SSet.{0}) (n : ℕ)
    (i j i' j' t t' : ℤ) (hi : i' = i + 1) (hj : j' = j + 1)
    (ht : t = i + j) (ht' : t' = i + j + 1)
    (a : (Surjection.complex A (n + 1)).X i) (b : (chains A S).X j)
    (H : (power (chains A S) (n + 1)).d t t'
        (positiveIntegerBilinear A S n i j t (by omega) a b) =
      positiveIntegerBilinear A S n i' j t' (by omega)
        ((Surjection.complex A (n + 1)).d i i' a) b +
      i.negOnePow • positiveIntegerBilinear A S n i j' t' (by omega) a
        ((chains A S).d j j' b)) :
    (power (chains A S) (n + 1)).d (i + j) (i + j + 1)
        (positiveIntegerBilinear A S n i j (i + j) rfl a b) =
      positiveIntegerBilinear A S n (i + 1) j (i + j + 1) (by omega)
        ((Surjection.complex A (n + 1)).d i (i + 1) a) b +
      i.negOnePow • positiveIntegerBilinear A S n i (j + 1) (i + j + 1) (by omega) a
        ((chains A S).d j (j + 1) b)
```

C306は、正の入力次数を元の零延長の零性で消した後、dとqの零・後続を分ける。
同じ元の微分の像をC313・C314で戻し、残る符号はInt.negOnePow_neg・
Int.coe_negOnePow_natCastで同じ整数の符号へ直す。区間固有の零性は使わない。
C315もC306も個々の証明200行以内。正arityの検証後も、L10の全arityの固定型の
完了にはarity零（§108.3のL14の規約）の接続が必要であり、先に完了へ数えない。

## 143. arity 零を含む同じ成分への接続（L10、実装前の型）

一覧：済み 10／全体 48（うち追加 4）

§108.3の固定したarity零の規約（L14）に従って空語augmentationと元のAW余単位を束ね、
L10の全arityのcomponentに含める。零arityを零作用とする置き換えは行わない。
χの元のdegreeModule A 0 1は基底が空なので零対象であり、
normalizedChainsのd 1 0を前置したzeroAugmentationは零。その既存の法則により
ChainComplex.toSingle₀Equivで鎖写像を作り、元の次数延長とextendSingleIsoを使う。
型は次。新しい構成の追加ではなく、固定したL14の構成のうちL10に要る接続である。

```lean
def nullaryCoefficientChainAugmentation :
    Surjection.normalizedChains A 0 ⟶ tensorUnit (ModuleCat A) (.down ℕ)

def nullaryCoefficientAugmentation : Surjection.complex A 0 ⟶ 𝟙_ (Complex A)

def nullaryAction (S : SSet.{0}) :
    Surjection.complex A 0 ⊗ chains A S ⟶ power (chains A S) 0

def component (S : SSet.{0}) : (r : ℕ) → (i j t : ℤ) → (h : i + j = t) →
    (Surjection.complex A r).X i →ₗ[A] (chains A S).X j →ₗ[A]
      (power (chains A S) r).X t

lemma component_d (S : SSet.{0}) (r : ℕ) (i j : ℤ)
    (a : (Surjection.complex A r).X i) (b : (chains A S).X j) :
    (power (chains A S) r).d (i + j) (i + j + 1)
        (component A S r i j (i + j) rfl a b) =
      component A S r (i + 1) j (i + j + 1) (by omega)
        ((Surjection.complex A r).d i (i + 1) a) b +
      i.negOnePow • component A S r i (j + 1) (i + j + 1) (by omega) a
        ((chains A S).d j (j + 1) b)
```

nullaryActionはχの空語augmentation、左単位同型、AlexanderWhitney.cochainCounitの合成。
componentの零arityは同じ射をιTensorObjで評価したもの、正arityは既存positiveIntegerBilinear。
component_dの零arityの証明は既存tensorComponent_dを純粋テンソルで評価するだけ。
空語での具体的な生成元の評価や他のL14の包装は、これだけで完了扱いにしない。
個々の証明200行以内。界面・G10・ほかのレーンのファイルには触れない。

## 144. 同じテンソル成分から実複体射への包装（L10、実装前の型）

一覧：済み 10／全体 48（うち追加 4）

L10の微分公式を既存TensorProduct.lift・tensorLiftへ渡す。C316は元の
テンソル成分の微分の法則、C317は元の斉次成分の復元で、構成し直した作用は使わない。
IntervalCuts.CochainActionと同じ次元によらない包装を、今回の一般Sのcomponent_dに適用する。

```lean
def cochainActionComponent (S : SSet.{0}) (r : ℕ) (i j t : ℤ) (h : i + j = t) :
    (Surjection.complex A r).X i ⊗ (chains A S).X j ⟶ (power (chains A S) r).X t

lemma cochainActionComponent_d (S : SSet.{0}) (r : ℕ) (i j : ℤ) :
    cochainActionComponent A S r i j (i + j) rfl ≫
        (power (chains A S) r).d (i + j) (i + j + 1) =
      ((Surjection.complex A r).d i (i + 1) ▷ (chains A S).X j) ≫
        cochainActionComponent A S r (i + 1) j (i + j + 1) (by omega) +
      i.negOnePow • (((Surjection.complex A r).X i ◁ (chains A S).d j (j + 1)) ≫
        cochainActionComponent A S r i (j + 1) (i + j + 1) (by omega))

def cochainAction (S : SSet.{0}) (r : ℕ) :
    Surjection.complex A r ⊗ chains A S ⟶ power (chains A S) r

lemma ι_cochainAction (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) :
    ιTensorObj (Surjection.complex A r) (chains A S) i j t h ≫
      (cochainAction A S r).f t = cochainActionComponent A S r i j t h
```

対称性・単位・部分合成の公理はこれだけで供給されたと扱わない。
個々の証明200行以内。新しい数学を一覧へ足さず、固定したL10の証明の分割として数える。

## 145. L11の次元によらない符号APIの下調べ（紙のみ）

一覧：済み 10／全体 48（うち追加 4）

L10の検証待ちに、後続L11の既存APIを点検した。
IntervalCuts.positionInversions_symmDiff_adjacentは色の単射性を要求せず、一般の色列へ使える。
同じneg_one_pow_card_symmDiffも使える。一方、positionInversionSign_adjacentと
card_colorCrossPairsは集合上の色の単射性を要求するため、そのまま適用しない。
SimplexCuts.active_color_cardは活動頂点の各色のfiberの濃度を一般qのoutputDegreeへ戻せる。

有限点検では、色数2〜4・位置数0〜5・全位置部分集合・全隣接交換について、
二色の非順序位置対の濃度=両fiberの濃度の積、および逆転符号の変化を確認した。
**132,374例成功**。スクリプト：`/tmp/bsw16/check-weighted-adjacent-color-pairs.py`、
結果：`/tmp/bsw16/check-weighted-adjacent-color-pairs.log`。
これはLeanの全称証明の代わりには数えず、L11の完了数・実測にも足さない。

次に必要な同じ有限集合の数え上げ・符号の法則の型は次。まだ紙のみ。
既存colorCrossPairsを作り直さず、二色のfiberの積を位置順に並べた同じ対として数える。

```lean
-- C318（予定）：既存の二色位置対の濃度。色の単射性を要求しない。
lemma card_colorCrossPairs_weighted {n l : ℕ} (v : Fin l → Fin n)
    (s : Finset (Fin l)) (a b : Fin n) (hab : a ≠ b) :
    (IntervalCuts.colorCrossPairs v s a b).card =
      (s.filter (fun i => v i = a)).card * (s.filter (fun i => v i = b)).card

-- C319（予定）：同じ逆転符号の隣接交換。二色の各出現数を保持する。
lemma positionInversionSign_adjacent_weighted {n l : ℕ} (a : Fin n)
    (v : Fin l → Fin (n + 1)) (s : Finset (Fin l)) :
    (-1 : ℤ) ^ IntervalCuts.positionInversionCount (Coxeter.adjacentTransposition a ∘ v) s =
      (-1 : ℤ) ^ IntervalCuts.positionInversionCount v s *
        (-1 : ℤ) ^ ((s.filter (fun i => v i = a.castSucc)).card *
          (s.filter (fun i => v i = a.succ)).card)
```

この二本は固定したL11の符号の証明の分割で、別の数学の主張を追加するものではない。
L10の検証・監査・保存後に実装する。個々の有限数え上げの証明が200行を超えれば実測を記す。

## 146. L10 完了：全 arity・全整数の厳密な微分則と実複体射

一覧：済み 11／全体 48（うち追加 4）

L10 `component_d` を、任意の可換環A、一般の単体集合S、全arity r、全整数i・j、
元のχ(r)と鎖の任意の元について証明した。非正性や特定の単体次元を仮定していない。
正arityは既存の正規化切断和そのもの。零arityは元の空語augmentationとAW余単位であり、
零作用への変更ではない。同じ成分をTensorProduct.lift・tensorLiftで実複体射
`cochainAction`にまとめ、`ι_cochainAction`で指定した成分を復元した。
元の加群・複体の射の等式で証明しており、ホモトピー圏へ弱めていない。

対象ビルド成功（2611 jobs）、
専用の小さい監査成功（6モジュール・143宣言、標準三公理のみ）。
sorry・追加公理0、Lean警告0。ビルドと監査は一回ずつ別の鍵を取り、終了・返却を確認。
鍵待ちの間に常駐ビルドセッションを使っていない。
監査末尾の `#check @component_d` で、全arity・全整数の型と仮定も確認した。

登録候補（今回の6本、接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 実測行数 |
| --- | ---: |
| PositiveIntegerComponent | 70 |
| PositiveComponentDifferential | 69 |
| PositiveIntegerLeibniz | 105 |
| NullaryAction | 46 |
| ComponentLeibniz | 46 |
| CochainAction | 54 |

前の保存済み補助 `NormalizedBilinearExt`（36行）、`NormalizedComponentDifferential`
（77行、fed42a19e）もL10の登録候補。共通入口・共通監査の登録は調整役の持ち分。
L14の残る零arityの生成元の具体式や合成との接続は、今回だけで完了へ数えない。

ログ：`/tmp/bsw16/m14-cochain-action-final.log`、
監査入力：`/tmp/bsw16/audit-m14-cochain-action.lean`、
監査結果：`/tmp/bsw16/m14-cochain-action-audit.log`。

### 146.1 実測・見込みと外枠

一覧：済み 11／全体 48（うち追加 4）

L09a・L09の実測8,991行は不変。M14は14,170+390=**14,560行**。
今回までのL10は**457行**（零arityの共通構成46行はL14の前段として別計上）。
§121.4のL10の130〜230行に対し、上端との差は+227行。
基底/正規化生成元の外延性36行、正規化微分77行に加え、全整数への次数移送、
元の二つの微分との照合、全arityの包装、テンソル複体射の構成が必要だった。
これらは既存の微分の法則・証明の分割で、一覧に新しい数学は足していない。

L10を未実装の見込みから除き、L14前段46行も重複計上せず、残りを次のように更新する。

| 部分 | 残りの下端 | 残りの上端 |
| --- | ---: | ---: |
| L11〜L28（L12a込み、L14前段は控除） | 4,154 | 7,514 |
| L29〜L37 | 1,200 | 2,000 |
| G10後の指定比較への適用 | 500 | 900 |
| filtered塔 | 300 | 550 |
| 二重模型の実現の比較 | 1,500 | 2,800 |
| **M14完成時（実測込み）** | **22,214** | **28,324** |

外枠25,000行、現在の残り枠は10,440行。上端は外枠を3,324行超えるリスクを保持する。
完成済みの分を控除した見積もりであり、残る数学を完成扱いしていない。
次は固定したL11。G10の部品、M15・G12は作らない。B4は595254e10で完了済み。

