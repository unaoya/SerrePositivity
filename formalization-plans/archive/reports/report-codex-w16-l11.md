# BS-W16 の報告（report-codex-w16.md） — L11（§147〜§156、2026-11-14）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 147. L11 の重複色の符号の接続（実装前）

一覧：済み 11／全体 48（うち追加 4）

§145 に型を記した C318・C319 を順に実装する。有限点検132,374例の結果は同節のまま。
既存 colorCrossPairs を二つの色の fiber の積から位置順に並べて数える。
C318 の局所 recover は同じ並べ替えから色a側を復元する法則であり、独立の構成ではない。
型は `p ∈ fiber a ×ˢ fiber b → (if v (F p).1 = a then F p else (F p).swap) = p`、
`F p := if p.1 < p.2 then p else p.swap`。その復元・単射・全射は C318 の証明の分割。
C319 は既存の逆転対の対称差の公式と C318 だけを使う。各証明200行以内。
χ の renameLinear_basis も実際の基底語の色置換の式であることを確認した。
ほかの係数作用へ変更せず、次に出力の実テンソルの置換との照合へ接続する。

## 148. L11 の同じ切断符号への接続（実装前の型）

一覧：済み 11／全体 48（うち追加 4）

C318・C319は2,201 jobsの対象ビルドに成功、Lean警告0。
次に、色置換で元の活動位置と位置指数が変わらない法則C321〜C323を使い、
C320で隣接交換の切断符号を同じ二出力次数の符号へ戻す。
C320はC319・既存active_color_card・permutationExponent_eq_active_inversionsの接続だけ。
全一般qの実際の整数の等式を保ち、出力が零・一次元であることは仮定しない。
型は次。固定したL11の既存構成の法則・証明分割として数える。

```lean
lemma label_rename {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (σ : Equiv.Perm (Fin r)) : label s (σ ∘ v) = σ ∘ label s v

lemma activeVertexPositions_rename {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (σ : Equiv.Perm (Fin r)) :
    activeVertexPositions s (σ ∘ v) = activeVertexPositions s v

lemma positionExponent_rename {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (σ : Equiv.Perm (Fin r)) :
    positionExponent s (σ ∘ v) = positionExponent s v

lemma cutSign_adjacent {m q n : ℕ} (s : Cut m q)
    (v : Surjection.Word (n + 1) (m + 1)) (a : Fin n) :
    cutSign s (Coxeter.adjacentTransposition a ∘ v.val) =
      cutSign s v.val * (-1 : ℤ) ^ (outputDegree s v a.castSucc * outputDegree s v a.succ)
```

各証明200行以内。L11の実テンソルの置換と切断和の包装はまだ未完。

## 149. L11 の元の純粋テンソルの交換の法則（実装前の型）

一覧：済み 11／全体 48（うち追加 4）

切断符号のC320〜C323は2,222 jobsの対象ビルドに成功、Lean警告0。
次に任意の複体Kで、元の結合子・Koszul交換・結合子を同じ斉次元で評価するC324を置く。
区間のswapFirstIso_applyの証明はこの部分に区間の性質を使っていないため、
同じ証明を一般Kで述べる。元の定義・公開宣言は変えない。

vectorDegree・vectorTensorは既存degreeSum・tensorValueへ同じ次数と元を渡すabbrev、
vectorTensorAtは終域の等式移送だけ。次数と元をSigmaに一緒に保持するのは、
色を替えた同じ因子を移す記法であり、新しい作用・比較・模型の構成ではない。
C325〜C330・C333はその同じテンソル・包含・次数移送の法則。型は次。

```lean
lemma swapFirstIso_apply (n : ℕ) (i j k t : ℤ) (ht : i + (j + k) = t)
    (x : K.X i) (y : K.X j) (z : (power K n).X k) :
    (swapFirstIso K n).hom.f t
      (ιTensorObj K (K ⊗ power K n) i (j + k) t ht
        (x ⊗ₜ[A] ιTensorObj K (power K n) j k (j + k) rfl
          (y ⊗ₜ[A] z))) =
      (i * j).negOnePow •
        ιTensorObj K (K ⊗ power K n) j (i + k) t
          (by omega) (y ⊗ₜ[A]
            ιTensorObj K (power K n) i k (i + k) rfl (x ⊗ₜ[A] z))

abbrev vectorDegree (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) : ℕ

abbrev vectorTensor (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) :
    (power K n).X (-(vectorDegree K n f : ℤ))

def vectorTensorAt (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (h : -(vectorDegree K n f : ℤ) = t) : (power K n).X t

lemma vectorDegree_permutation (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (σ : Equiv.Perm (Fin n)) : vectorDegree K n (f ∘ σ) = vectorDegree K n f

lemma vectorDegree_cons (n : ℕ) (a : Σ d : ℕ, K.X (-(d : ℤ)))
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) :
    vectorDegree K (n + 1) (Fin.cons a f) = a.1 + vectorDegree K n f

@[simp] lemma vectorTensorAt_refl (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) :
    vectorTensorAt K n f (-(vectorDegree K n f : ℤ)) rfl = vectorTensor K n f

lemma vectorTensorAt_succ (n : ℕ) (f : Fin (n + 1) → Σ d : ℕ, K.X (-(d : ℤ)))
    (i j t : ℤ) (hi : -((f 0).1 : ℤ) = i)
    (hj : -(vectorDegree K n (fun k => f k.succ) : ℤ) = j) (ht : i + j = t) :
    vectorTensorAt K (n + 1) f t (by
      simp only [vectorDegree, degreeSum, Nat.cast_add]; omega) =
      ιTensorObj K (power K n) i j t ht
        ((eqToHom (congrArg K.X hi)).hom (f 0).2 ⊗ₜ[A]
          vectorTensorAt K n (fun k => f k.succ) j hj)

lemma vectorTensorAt_cons (n : ℕ) (a : Σ d : ℕ, K.X (-(d : ℤ)))
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (h : -(a.1 : ℤ) + -(vectorDegree K n f : ℤ) = t) :
    vectorTensorAt K (n + 1) (Fin.cons a f) t
      (by simp only [vectorDegree_cons, Nat.cast_add]; omega) =
      ιTensorObj K (power K n) (-(a.1 : ℤ)) (-(vectorDegree K n f : ℤ)) t h
        (a.2 ⊗ₜ[A] vectorTensor K n f)

lemma vectorTensorAt_cons_cons (n : ℕ) (a b : Σ d : ℕ, K.X (-(d : ℤ)))
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (h : -(a.1 : ℤ) + (-(b.1 : ℤ) + -(vectorDegree K n f : ℤ)) = t) :
    vectorTensorAt K (n + 2) (Fin.cons a (Fin.cons b f)) t
      (by simp only [vectorDegree_cons, Nat.cast_add]; omega) =
      ιTensorObj K (K ⊗ power K n) (-(a.1 : ℤ))
        (-(b.1 : ℤ) + -(vectorDegree K n f : ℤ)) t h
        (a.2 ⊗ₜ[A] ιTensorObj K (power K n) (-(b.1 : ℤ)) (-(vectorDegree K n f : ℤ))
          (-(b.1 : ℤ) + -(vectorDegree K n f : ℤ)) rfl (b.2 ⊗ₜ[A] vectorTensor K n f))

lemma swapFirstIso_vectorTensorAt (n : ℕ) (a b : Σ d : ℕ, K.X (-(d : ℤ)))
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (h : -(a.1 : ℤ) + (-(b.1 : ℤ) + -(vectorDegree K n f : ℤ)) = t) :
    (swapFirstIso K n).hom.f t
      (vectorTensorAt K (n + 2) (Fin.cons a (Fin.cons b f)) t
        (by simp only [vectorDegree_cons, Nat.cast_add]; omega)) =
      ((-(a.1 : ℤ)) * (-(b.1 : ℤ))).negOnePow •
        vectorTensorAt K (n + 2) (Fin.cons b (Fin.cons a f)) t
          (by simp only [vectorDegree_cons, Nat.cast_add]; omega)
```

同じ三つの次数の移送は、既存IntervalCuts.tensorInclusion_transport（P・Qが任意）を使う。
各証明200行以内。この段階で区間に固有の零性・頂点や辺の分類は使わない。

## 150. L11 の一般位置の隣接交換の法則（実装前の型）

一覧：済み 11／全体 48（うち追加 4）

C324が使う既存の結合子の評価の供給元はMaurerCartanCurryingだったので、
区間の単位則を経由せず、その一般複体のモジュールを直接importする。
次のC331・C332も、元のadjacentIsoの先頭/尾の再帰の法則を同じ斉次元で評価する。
先頭はC330、尾は既存whiskerLeft_applyと帰納仮定。新しいテンソル置換は作らない。

```lean
lemma cons_comp_shiftPerm {α : Type*} (n : ℕ) (a : α) (f : Fin n → α)
    (σ : Equiv.Perm (Fin n)) :
    Fin.cons a f ∘ shiftPerm σ = Fin.cons a (f ∘ σ)

lemma adjacentIso_vectorTensorAt (n : ℕ) (i : Fin n) (f : Fin (n + 1) → Σ d : ℕ, K.X (-(d : ℤ)))
    (r : ℤ) (hf : -(vectorDegree K (n + 1) f : ℤ) = r) :
    (adjacentIso K n i).hom.f r (vectorTensorAt K (n + 1) f r hf) =
      ((-((f i.castSucc).1 : ℤ)) *
        (-((f i.succ).1 : ℤ))).negOnePow •
          vectorTensorAt K (n + 1) (f ∘ adjacentTransposition i) r
            (by rw [vectorDegree_permutation]; exact hf)
```

各証明200行以内。一般の次数と元をそのまま保持しており、単体の次元の制限はない。
切断の面の族との一致は、後で既存の指定面・次数移送の法則で接続する。

## 151. L11 の同じ指定面の因子への接続（実装前の型）

一覧：済み 11／全体 48（うち追加 4）

C324とvectorTensorAtの次数移送・先頭交換の法則は型検査に成功した。
一般位置の再帰に使うshiftPermの供給元GroupTheory.Coxeter.FirstToLastを直接importする。
次にC334〜C338で、元の色別位置集合、元の次数、同じ順序の指定面の生成元を照合する。
cutVectorは既存cutTensorの一因子を同じ次数と元のSigmaに入れる記法のみ。
C336はその対の等式なので、次数の一致だけでなく同じ指定面の生成元そのものを保持する。
新しい面や比較射の選択はしない。型は次。

```lean
lemma colorPositions_rename {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (σ : Equiv.Perm (Fin r)) (a : Fin r) :
    colorPositions s (σ ∘ v) (σ a) = colorPositions s v a

lemma outputDegree_rename {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (σ : Equiv.Perm (Fin r)) (a : Fin r) :
    outputDegree s (Surjection.Word.rename σ v) (σ a) = outputDegree s v a

def cutVector {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (x : S _⦋q⦌) :
    Σ d : ℕ, (chains A S).X (-(d : ℤ))

lemma cutVector_rename_image {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (σ : Equiv.Perm (Fin r)) (a : Fin r) (x : S _⦋q⦌) :
    cutVector A S s (Surjection.Word.rename σ v) (σ a) x = cutVector A S s v a x

lemma cutVector_rename {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (σ : Equiv.Perm (Fin r)) (x : S _⦋q⦌) :
    (fun a => cutVector A S s (Surjection.Word.rename σ v) a x) =
      (fun a => cutVector A S s v a x) ∘ σ.symm

lemma cutTensor_vectorTensorAt {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌) (t : ℤ)
    (h : -(degreeSum r (outputDegree s v) : ℤ) = t) :
    vectorTensorAt (chains A S) r (fun a => cutVector A S s v a x) t h =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensor A S s v x)
```

C334は色置換の単射性、C335はその濃度、C336は同じ位置集合の順序列挙の等式。
C337は逆置換による添字の読み替え、C338は既存cutTensorの定義そのもの。
各証明200行以内。法則と証明の分割なので一覧の総数は変えない。

## 152. L11 の半分での途中報告（止まらず続行）

一覧：済み 11／全体 48（うち追加 4）

L11の§121.4の見込み250〜450行の半分225行を超えた。
現在、対象ビルドに通った5本は92+45+60+111+90=**398行**。
内訳は二色対の濃度・符号92、切断符号45、一般の先頭交換60、同じ次数移送111、
一般位置の隣接交換90。個々の証明200行以内。Lean警告0。
5本の小さい監査は、残る接続とまとめて行う前で、監査済みとは数えない。

M14のコミット・監査済み実測14,560行に対し、型検査済みの追加は398行、合計14,958行。
CutVectorsRenamingの70行はまだ照合の一箇所を修正中で、この合計へ含めていない。
残りは次の同じ構成の接続であり、新しい数学を増やす段ではない。

| 残り | 追加見込み |
| --- | ---: |
| 同じ色別位置集合と指定面生成元の照合を仕上げる | 70〜110 |
| 同じ実テンソルの交換・切断符号の交換を合わせ、切断項の全置換へ | 95〜150 |
| 元の語長・全次数の移送を保って有限和へ戻す | 55〜80 |
| **L11の残り** | **220〜340** |
| **L11完成時（398行込み）** | **618〜738** |

§121.4のL11の250〜450行に対して、完成時の上端は+288行となる見込み。
同じ元の次数・値の依存した族を保持するため、一般Kの斉次テンソルの交換・
等式移送の接続を独立に明示する必要があった。
§146.1の全体見込みでL11の行だけを置き換えると、M14完成時は**22,582〜28,612行**。
外枠25,000行に対する上端超過のリスクを保持する。型検査済みの実測はまだ外枠に届いて
いないので、指示どおり止まらずL11を閉じる接続へ進む。G10の部品は作らない。

## 153. L11 の切断項と同じ有限和への包装（実装前の型）

一覧：済み 11／全体 48（うち追加 4）

C339はC332を元のcutVectorの族へ適用し、C337・C338で同じcutTensorAtへ戻す。
C340は同じcutSignのC320を合わせ、C341は既存permutation_induction_rightで
任意の置換へ延長する。C342・C343は元の語長の等式移送との可換性。
L11は既存component_index_naturalityと元の有限和の線形性で閉じる。型は次。

```lean
lemma cutTensorAt_adjacent {m q n : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word (n + 1) (m + 1)) (a : Fin n) (x : S _⦋q⦌) :
    (adjacentIso (chains A S) n a).hom.f (-((m + q + 1 - (n + 1) : ℕ) : ℤ))
        (cutTensorAt A S s v x) =
      (-1 : ℤ) ^ (outputDegree s v a.castSucc * outputDegree s v a.succ) •
        cutTensorAt A S s (Surjection.Word.rename (adjacentTransposition a) v) x

lemma cutTerm_adjacent {m q n : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word (n + 1) (m + 1)) (a : Fin n) (x : S _⦋q⦌) :
    (permutationAction (chains A S) (n + 1) (adjacentTransposition a)).asIso.hom.f
        (-((m + q + 1 - (n + 1) : ℕ) : ℤ)) (cutTerm A S s v x) =
      cutTerm A S s (Surjection.Word.rename (adjacentTransposition a) v) x

lemma cutTerm_permutation {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (σ : Equiv.Perm (Fin r)) (x : S _⦋q⦌) :
    (permutationAction (chains A S) r σ).asIso.hom.f
        (-((m + q + 1 - r : ℕ) : ℤ)) (cutTerm A S s v x) =
      cutTerm A S s (Surjection.Word.rename σ v) x

lemma rename_eq_mp {n l l' : ℕ} (h : l = l') (σ : Equiv.Perm (Fin n))
    (v : Surjection.Word n l) :
    Eq.mp (congrArg (fun k => Surjection.Word n k) h) (Surjection.Word.rename σ v) =
      Surjection.Word.rename σ (Eq.mp (congrArg (fun k => Surjection.Word n k) h) v)

lemma positiveWord_rename {r d : ℕ} (v : Surjection.BasisWord (r + 1) d)
    (σ : Equiv.Perm (Fin (r + 1))) :
    positiveWord (Surjection.Word.rename σ v) = Surjection.Word.rename σ (positiveWord v)

lemma cutSum_permutation (S : SSet.{0}) {r d q : ℕ}
    (v : Surjection.BasisWord (r + 1) d) (σ : Equiv.Perm (Fin (r + 1))) (x : S _⦋q⦌) :
    cutSum A S (Surjection.Word.rename σ v) x =
      (permutationAction (chains A S) (r + 1) σ).asIso.hom.f (-((d + q : ℕ) : ℤ))
        (cutSum A S v x)
```

切断項のC341は全arity。cutSumは本体の既存定義が正arityの語であり、その同じ型を保つ。
§108.3で別扱いとした空語・零arityの本体への接続はL14のまま変更しない。
すべて元の加群の値の等式を主張し、ホモトピー圏への等式へ弱めない。
各証明200行以内。法則と証明の分割なので一覧の総数を増やさない。

## 154. C336 の同じ位置集合を通す証明分割

一覧：済み 11／全体 48（うち追加 4）

C336で構造を順にsimpした後、残る外側の次数を直接rwしようとすると、
順序列挙の始域Fin(card-1+1)も依存しているため、motiveが型を持たなかった。
主張の型・指定面・次数は変えない。同じ元の式を、非空位置集合の部分型を
引数にする局所Fとして書き、Subtype.extとcongrArgで同じ集合の等式を渡す。
局所Fは元のcutVectorの既存の式を展開したもので、新しい面・作用・比較の構成ではない。

```lean
F : {t : Finset (Fin (m + q + 1)) // t.Nonempty} →
  Σ d : ℕ, (chains A S).X (-(d : ℤ))
-- tの順序列挙と元のs.verticalで面を読み、次数t.card-1の同じgenを返す。
-- 必要な引数の等式：
(⟨colorPositions s (Surjection.Word.rename σ v).val (σ a),
    colorPositions_nonempty s (Surjection.Word.rename σ v) (σ a)⟩ :
  {t : Finset (Fin (m + q + 1)) // t.Nonempty}) =
  ⟨colorPositions s v.val a, colorPositions_nonempty s v a⟩
```

この引数の等式は既存C334をSubtype.extへ渡すだけ。C336全体の証明は200行以内。

## 155. 同じ因子の族を指定次数で読む法則（C344、実装前）

一覧：済み 11／全体 48（うち追加 4）

C336は局所Fを通す証明で通った。C339で因子の族の等式だけをrwすると、
vectorTensorAtの次数の証明もその族に依存するためmotiveが型を持たない。
次の同じ構成の法則で、両側の次数証明を一緒に受け取って等しい値へ移す。
これは等しい因子の族と等式移送の法則だけで、指定面や作用を変えない。

```lean
lemma vectorTensorAt_congr (n : ℕ) (f g : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (hf : -(vectorDegree K n f : ℤ) = t) (hg : -(vectorDegree K n g : ℤ) = t)
    (hfg : f = g) : vectorTensorAt K n f t hf = vectorTensorAt K n g t hg
```

証明は因子の族の等式で置換してrfl。C339の中では、この値の等式を使ってから
元のcutTensorAtへ戻す。C340では既存adjacentAutの同型のhomを元のadjacentIsoとして
明示する。C341の帰納法は既存GroupTheory.Coxeter.PermutationInductionを直接importする。
いずれも既存構成の法則・証明分割で、一覧の総数は変えない。

## 156. L11 完了：同じ一般切断和と元の Koszul 置換

一覧：済み 12／全体 48（うち追加 4）

L11 `cutSum_permutation` を、既存cutSumの全ての入力（任意の可換環A・
一般S・全正arity・語次数d・単体次数q・任意の色置換・実際の生成元）で証明した。
切断項のC341 `cutTerm_permutation` は全arityで述べている。
§108.3で別にした零arityの空語と部分合成の接続はL14のまま保持し、完了へ数えない。
同じ位置集合・同じ順序の指定面・同じ正規化生成元・元のcutSignを保ち、
実際の整数複体のテンソル置換と一致させた。ホモトピー圏の等式への変更はない。
非退化な切断だけへ制限せず、退化した面の因子も元の正規化生成元のまま含む。

対象ビルド成功（2,265 jobs）、小さい監査成功（8モジュール・82宣言、標準三公理のみ）。
sorry・追加公理0、Lean警告0。ビルド・監査ごとに独立の鍵を取り、終了・返却を確認。
監査末尾の#checkでL11・C341・C332の実際の全称型も確認した。
元の公開宣言・界面・共通入口・共通監査は変更していない。

登録候補（接頭部 `SerrePositivity.EInfinity.SimplexCuts.`）：

| モジュール | 実測行数 |
| --- | ---: |
| WeightedColorPairs | 92 |
| CutRenamingSigns | 45 |
| TensorFirstSwap | 60 |
| VectorTensorTransport | 118 |
| TensorAdjacentSwap | 90 |
| CutVectorsRenaming | 82 |
| CutTermPermutation | 107 |
| CutSumPermutation | 53 |

八本は入口の `CutSumPermutation` からすべてimportされる。
宣言元を選ぶ共通監査では、この八本をそれぞれ登録できる。
一般Kのモノイダル評価の法則も、この段ではSimplexCutsの共通補助として置いた。

ログ：`/tmp/bsw16/m14-cut-sum-permutation-05.log`。
監査入力：`/tmp/bsw16/audit-m14-cut-sum-permutation.lean`、
結果：`/tmp/bsw16/m14-cut-sum-permutation-audit.log`。
有限点検132,374例は§145のとおりで、Leanの全称証明とは別の点検。

### 156.1 見込みと実測の差、M14全体の残り

一覧：済み 12／全体 48（うち追加 4）

L11実測は**647行**。§121.4の250〜450行に対し、上端との差は**+197行**。
§152の途中の398行からは+249行で、そこで出した残り220〜340行の見込み内。
増分は次の同じ構成の接続だった。

| §152の残りの行 | 見込み | 実測 |
| --- | ---: | ---: |
| 色別位置集合と指定面生成元 | 70〜110 | 82 |
| 実テンソル・符号を合わせた切断項の置換 | 95〜150 | 107 |
| 元の語長と全次数を保った有限和 | 55〜80 | 53 |
| 同じ因子の族の次数移送の法則C344 | 上の接続に含む | 7 |
| **合計** | **220〜340** | **249** |

C344の7行は「実テンソル・符号を合わせた接続」の同じ次数移送の法則として増えた。
§152の表の独立の数学の不足を新設したものではない。個々の証明200行以内。
型は§155へ記録した。§152の398行と合わせた647行を一度だけ数える。

M14実測は14,560+647=**15,207行**、L09a・L09の8,991行は不変。
L11を残りの見込みから除いて更新する。

| 部分 | 残りの下端 | 残りの上端 |
| --- | ---: | ---: |
| L12a・L12〜L28（L14前段46行は既に控除） | 3,904 | 7,064 |
| L29〜L37 | 1,200 | 2,000 |
| G10後の指定比較への適用 | 500 | 900 |
| filtered塔 | 300 | 550 |
| 二重模型の実現の比較 | 1,500 | 2,800 |
| **M14完成時（実測込み）** | **22,611** | **28,521** |

外枠25,000行、現在の残り枠は**9,793行**。上端には3,521行の超過リスクが残る。
残るL12aなどの数学を完成済みとして控除していない。
次は固定したL12aの二段切断と一段切断の有限項の対応。
G10の部品、M15・G12には触れない。B4は595254e10で完了済みのまま。

