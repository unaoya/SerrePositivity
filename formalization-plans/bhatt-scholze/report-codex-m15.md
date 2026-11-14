# BS-M15（⑤d）作業報告

## 1. 着手・M15 段0（2026-11-14、紙）

指定 worktree `SerrePositivity-bs-m15`、枝 `math/bs-m15` で実施。
`git merge main` は `602fe450f → ac3544c4a` の fast-forward で完了した。
main には書き込んでいない。作業前の枝は clean。
指示書 `bhatt-scholze-codex-m15.md` §1–4 を読んだ。
⑤a の `../SerrePositivity-bs-impl/formalization-plans/bhatt-scholze/report-codex-w16.md`
§60–61・§66・§95・§97・§107・§111 を読み取り専用で引き継いだ
（同 worktree の HEAD は `e95184dc1`）。⑤a の未コミット分も含む作業木を変更していない。

**段0判定：追加 Lean の見込みは 7,000〜11,700 行。上端が事前承認の
8,500 行を超えるため、指示書 §3.1 に従って実装前に停止する。**
以下は残る数学的出力の型案で、Lean に追加した宣言でも型検査済みコードでもない。
未供給の構成を仮定の束へ移して完成とする案は採用しない。

### 1.1 再利用の確定範囲と見積もりの変更理由

既存ソースで次を照合した。

- `DGAlgebraDerivedInfinity.lean` の `dgAlgebraDerivedInfinityCategory` と安定性は
  `Mon (Complex A)` 上の**右**加群を扱う。一般 R を H⁰(R) に置き換える必要はない。
- `DGAlgebraMoritaInfinity.lean` の
  `dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso` は同じ dg 代数射の
  準同型から拡大の同値を供給する。この証明を作り直す費用は除いた。
- `DGModuleDerivedFunctor.lean` の `dgModuleDerivedFunctor` は射影的対象の保存を要求する。
  任意の係数射の restriction はその仮定を満たすとは限らない。
  restriction 後の解像度を含む全関手と、native な随伴の単位・余単位は依然必要。
- `HomologyComposition.lean` の `coefficientOperation_comp` は再利用できる。
  `HomologyAssociativity.lean` のホモトピー結合則から、同じ複体上の厳密な
  `Mon` の結合則は得たと数えない。標準零単体の全挿入（零 arity 込み）が最初の出力。
- `research/ha-coverage/review/ch4.csv` は HA 4.2.1.15・4.2.3.5・4.5.2.1 を
  通常圏に限る部分一致、4.5.3.1 を未供給と記録する。
  通常の balanced tensor は native な対称相対テンソルの構成済み API ではない。
- `drafts/DerivedGeneral/CompletionFunctor.lean` の `completionReflection` と
  `cAlgCompletionReflection` は `sorry` のまま。これらを証明済みの反射として
  無償に取り込まず、M15 に必要な module 完備反射と比較を費用へ入れる。
  A5 の Koszul・Nakayama の個別証明まで M15 に移す見積もりではない。

§95・§107 の 2,500〜4,500 行は暫定値だった。今回は次の全出力を一覧に含めた上で
束を再評価した。既存 dg nerve・安定性・拡大の弱同値不変性は再実装しない。

| 束 | 下端 | 上端 | 型一覧 |
| --- | ---: | ---: | --- |
| 同じ台の厳密忘却、固定模型の台・単位・指定辺 | 900 | 1,600 | M01–M05 |
| native restriction・随伴、恒等・合成と全族の降下 | 1,000 | 1,800 | M06–M10 |
| E∞ 相対テンソルの全構造・底変換 | 1,800 | 2,800 | M11–M15 |
| fiber・指数射、単位底比較と thick の共通化 | 600 | 1,000 | M16–M20 |
| 指数判定・底変換・合成・テンソル | 900 | 1,500 | M21–M27 |
| Amitsur 塔と指定増大の降下 | 600 | 1,000 | M28–M30 |
| RHom の係数付き全関手・評価と指数二の判定 | 500 | 800 | M31–M35 |
| 完備加群・完備テンソル・余極限評価・利用側接続 | 700 | 1,200 | M36–M42、離散特殊化 |
| **計** | **7,000** | **11,700** | |

前の三分割では「一般 R 加群」2,500〜4,500 が **4,300〜7,200**、
「指数」900〜1,500 は不変、「降下・評価・完備」1,400〜2,500 が **1,800〜3,000**。
差分は計 **+2,200〜+3,200**。全族の降下・随伴・対称テンソルと、
未証明の完備反射を独立に検収できる出力として積んだことによる。
これは実装前の工数見積もりで、必要行数の数学的下界ではない。
外枠二倍を使って事前承認の判定を回避しない。

### 1.2 型一覧の読み方・一般 E の境界

以下の記号は紙上の略記。未定義の名前の実在や型検査の成功を主張しない。

```lean
universe u
-- E : EInfinityTheory.{u}; A : Type u; [CommRing A]
-- Alg := E.CAlg A
-- V (C : SSet.{u+1}) := C _⦋0⦌
-- D := derivedInfinityCategory A
-- R B C : V Alg; f : SSet.Edge R B
-- C_R := modulesOver E A R; U_R := modulesOverForget E A R
-- one_R := moduleUnit E A R; B_f := algebraAsModule E A f
-- eta_f := algebraModuleUnit E A f : SSet.Edge one_R B_f
-- T_R M := moduleTensorWith E A R M : C_R ⟶ C_R
-- Ext f := moduleExtend E A f; Res f := moduleRestrict E A f
-- hC := C.HomotopyCategory; [e] := homMk e.toTruncated
-- DLE k X := ∀ i : ℤ, k < i → Subsingleton (derivedInfinityHomology A i X)
```

全族とは、実 cocartesian fibration `p : TotalModules ⟶ Alg` と、その R 上の fiber、
cocartesian transport としての `Ext f` をいう。M10 はこの実対象を構成する出力。
対称テンソルの全構造は有限基点集合上の実 operadic fibration として構成し、
単に hC_R の対称モノイダル圏だけを作って済ませない。
以下の `ModuleFamily`・`SymmetricModuleTensor` はその**数学的対象の型の仮名**であり、
未証明命題だけを欄にする Setup 型を追加する承認ではない。

注意：`EInfinityTheory` の任意の E には、BE 模型への比較や module の族の欄がない。
BE の `assocForget` だけを構成しても、任意の E に対する `modulesOver E A R` は得られない。
M10 はまず BE 模型で構成し、任意 E の入口を保つ場合は同じ CAlg・忘却との比較から
輸送できることを別途示す必要がある。現界面からその比較が導けるとは未確認。
ここは**未解決の型の境界**として明記し、E を無断で BE に特殊化しない。
上表は BE での構成と、利用側が同じ模型を参照する接続の見込み。
任意 E の表現定理を新たに証明する費用まで有限上端で保証するものではない。
この不確定性も、旧上端 8,500 を据え置いて実装開始できない理由である。

### 1.3 最初の受け渡し：M01–M20

原典番号の対応は⑤a §61.4・§95.3 のものを引き継ぐ。
HA 4.2.1.15、4.2.3.5・4.2.3.7、4.5.1.1・4.5.2.1・4.5.3.1。
番号の対応は、その一般定理が本リポジトリに実装済みであることを意味しない。
M01–M05 は BE 側の新設 `EInfinity/BarrattEccles/Modules/`、
一般の構成は `EInfinity/Modules/` に置く。既存のファイルは編集しない。

```lean
-- M01 標準零単体の係数（A・operad の引数は明示）
standardCoefficient (A : Type u) [CommRing A] (n : ℕ) :
  𝟙_ (Complex A) ⟶ (operad A).arity n
-- M02 単位（operad の単位）
standardCoefficient A 1 = (operad A).unit
-- M03 全挿入。n = 0 を除外しない
∀ (m n : ℕ) (i : Fin (m + 1)),
  coefficientComposite m n i (standardCoefficient A (m+1))
    (standardCoefficient A n) = standardCoefficient A (m+n)
-- M04 同じ carrier・元の複体の単位と積・全代数射を持つ忘却
assocForget (A : Type u) [CommRing A] :
  (operad A).Algebra ⥤ Mon (Complex A)
-- M05 固定模型の右加群、台の忘却と正則加群
strictModuleInfinity (X : (operad A).Algebra) : SSet.{u+1}
strictModuleUnderlying (X : (operad A).Algebra) :
  strictModuleInfinity A X ⟶ derivedInfinityCategory A
strictModuleUnit (X : (operad A).Algebra) : V (strictModuleInfinity A X)
-- C01（照合一）M04–M05 の台・正則加群・指定単位射と BE carrier の比較。
-- carrier は M04 で変えない。U(strictModuleUnit X) は同じ X.carrier の像。

-- M06 全厳密射の native 拡大・制限（g : X ⟶ Y）
strictExtend g : strictModuleInfinity A X ⟶ strictModuleInfinity A Y
strictRestrict g : strictModuleInfinity A Y ⟶ strictModuleInfinity A X
-- M07 通常圏の随伴の写しと同じ全単位・余単位を持つ native 随伴
QCatAdjunction (strictExtend g) (strictRestrict g)
-- M08 恒等・合成（拡大。restriction は逆順）
FunctorIso (strictExtend (𝟙 X)) (𝟙 _)
FunctorIso (strictExtend (g ≫ h)) (strictExtend g ≫ strictExtend h)
-- M09 同じ拡大の弱同値不変性
QuasiIso g.hom → IsQCatEquivalence (strictExtend g)
-- M10 全族・native な辺と合成への降下。上の transport を含む実構成
moduleFamily A : ModuleFamily (barrattEcclesCore.CAlg A)
-- fiber が C_R、transport が Ext f。高次単体も含む射影を構成する。
-- C02（照合二）厳密族の局所化との全関手比較、同じ U・単位・随伴。

-- M11 同じ C_R に対する相対テンソルの operadic 構造
moduleTensorStructure A R : SymmetricModuleTensor C_R
-- M12 同じ単位と左右単位子（全関手同型）
FunctorIso (T_R one_R) (𝟙 C_R)
-- M13 結合子・対称性は M11 の実 operadic 構造からの指定比較。
-- 頂点 M,N,P での表示：
VertexIso (tensor R (tensor R M N) P) (tensor R M (tensor R N P))
VertexIso (tensor R M N) (tensor R N M)
-- M14 両変数での完全性（M11 の対称性で第二変数へ）
∀ M : V C_R, IsExactFunctor (T_R M)
-- M15 拡大は対称モノイダル、同じ pushout に対する底変換
-- Q は CAlg の同じ正方形、f : R→B、g : R→R'、g' : B→B'、f' : R'→B'
IsColimitCone (pushoutCocone Q) →
  FunctorIso (Res f ≫ Ext g) (Ext g' ≫ Res f')
-- Ext f(one_R) ≃ one_B、Ext f(M⊗_R N) ≃ Ext f M⊗_B Ext f N は
-- 対称モノイダル関手という実構造に含める。合成・単位との coherence も要る。

-- M16 指定単位辺・fiber。fiberArrow f : F_f → one_R は実 fiber 錐の脚
algebraModuleUnit f : SSet.Edge one_R B_f
moduleFiber f : V C_R
moduleFiberArrow f : SSet.Edge (moduleFiber f) one_R
-- M17 反復相対テンソルと、同じ脚からの指定指数射
fiberPower f (n : ℕ) : V C_R
fiberPowerArrow f (n : ℕ) : SSet.Edge (fiberPower f n) one_R
-- n=0 は one_R の恒等射。全 n で F_f の脚のテンソルと単位子から作る。
-- M18 単位底での全関手比較（tensor・指定辺も含める）
moduleAtUnitEquivalence A : QCatEquivalence (modulesOver E A (unitAlgebra E A)) D
-- M19 thick の共通定義と tensor による閉性（1.6 を参照）
IsThickTensorIdeal (R : V Alg) (P : V C_R → Prop) : Prop
thickTensorIdealGenerated (R : V Alg) (M : V C_R) : V C_R → Prop
-- M20 定義二つ。相互同値を定義に埋め込まない
IsDescendableOver A R B f := thickTensorIdealGenerated R B_f one_R
HasDescentIndexLEOver A R B f n := ([fiberPowerArrow f n] = 0)
-- C03（照合三）同じ E.forget が送る f と M16–M18 の台・fiber・指数射の比較。
```

M01–M20 が⑤a §107.3 の五点を全て満たして初めて最初の受け渡しとなる。
M08 の二つの同型を孤立して作るだけでは M10 の高次の降下を満たさない。
M13 の頂点同型だけでも M11 を満たさない。C01–C03 は補助照合の予定上限三本。
本一覧の主出力を細分して本数を増やす数え方はしない。

### 1.4 指数・降下：M21–M30

略記 `Desc f`・`Idx f n` は M20 の二つの Prop。
`bottom Q` 等は drafts と同じ `squareBottomArrow` 等から `.ofTruncated` で戻した辺。
`Arrow := (ihom Δ[1]).obj Alg`、`edge v` は drafts の `algebraArrowEdge`。

```lean
-- M21 Mathew Definition 3.18 の定義からの有限指数判定
Desc f ↔ ∃ n : ℕ, Idx f n
-- M22 単位底特殊化（Shared の離散定義との一致）
Desc (f : SSet.Edge (unitAlgebra E A) B) ↔ IsDescendable E A B
-- M23 底変換
IsColimitCone (pushoutCocone Q) → Desc (bottom Q) → Desc (top Q)
-- M24 同じ正方形での指数保存
IsColimitCone (pushoutCocone Q) → Idx (bottom Q) n → Idx (top Q) n
-- M25 指定合成の証人を保持
SSet.Edge.CompStruct f g h → Desc f → Desc g → Desc h
-- M26 相対テンソル（同じ pushout の対角辺）
IsColimitCone (pushoutCocone Q) →
  Desc (bottom Q) → Desc (left Q) → Desc (diagonal Q)
-- M27 始域も異なる二辺のテンソル。D₂ は Fin 2 の離散図式
(c : JoinCocone D₂) → IsColimitCone c →
  (∀ j : Fin 2, Desc (edge (D₂.app _ (ULift.up (nerveVertex (Discrete.mk j)))))) →
  Desc (edge c.vertex)
-- M28 任意の R 加群への Amitsur 図式（実際の増大・全脚を保持）
moduleAmitsur (d : AmitsurData E A f) (M : V C_R) :
  augmentedShape ⟶ C_R
-- M29 指数の零性から同じ module 増大錐の極限性
Idx f n → IsLimitCone (moduleAmitsurAug d M)
-- M30 Shared の要求する CAlg の同じ増大錐（M=one_R）
Desc f → (d : AmitsurData E A f) → IsLimitCone d.aug
```

M29 では Amitsur の部分 Tot の塔と fiber のテンソル冪の関係から収束を証明する。
有限段の retract が得られたことだけを無限 Tot の極限性と読み替えない。
M30 の `AmitsurData` の base・zero・leg・term は既存 drafts のものを使い、
都合のよい別の増大へ差し替えない。Mathew Proposition 3.22 の利用箇所。

### 1.5 RHom・完備版・A5 の入力：M31–M42

```lean
-- M31 R 加群の内部 Hom と、その台を取る全関手
moduleRHom R : C_Rᵒᵖ ⊗ C_R ⟶ C_R
-- ここで C_Rᵒᵖ は simplicial opposite。⊗ は SSet の積。
-- M32 同じ tensor と内部 Hom の随伴（任意の M）
QCatAdjunction (T_R M) (moduleRHomWith R M)
-- M33 評価の h 上の零次比較（相手 N を動かす自然な加法同型）
((hC_R).Hom M N) ≃+
  derivedInfinityHomology A 0 (U_R (moduleRHomObj R M N))
-- M34 A 係数付き Hom。L は任意の D(A) 頂点、平坦性を要求しない
fiberSquareRHom (f : SSet.Edge R B) (L : V D) : V D :=
  U_R (moduleRHomObj R (fiberPower f 2) (moduleFromBase R L))
-- moduleFromBase R は R⊗_A(-) の実 ∞ 関手。tensorWith の向きを固定する。
-- M35 Shared の True を置き換える実質的主張
DLE (-1) (fiberSquareRHom f (unitComplex A)) → Idx f 2

-- M36 台が s 完備な R 加群の充満部分準圏と反射
completeModules R (s : Finset A) : SSet.{u+1}
moduleCompletion R s : C_R ⟶ completeModules R s
QCatAdjunction (moduleCompletion R s) (completeModulesInclusion R s)
-- M37 完備テンソルと単位。通常の tensor の後の完備化
completeTensor R s M N := moduleCompletion R s (tensor R M.val N.val)
-- 完備 R のとき単位は one_R、M11 と同じ向きの対称 operadic 構造を構成。
-- M38 完備圏での定義と指数判定（通常版との同値を定義にしない）
IsDescendableCompleteOver A s R B f : Prop
HasDescentIndexLECompleteOver A s R B f n : Prop
IsDescendableCompleteOver A s R B f ↔
  ∃ n, HasDescentIndexLECompleteOver A s R B f n
-- M39 Shared の完備版 True の代わり。cR,cB は忘却した台の完備性
(cR : IsDerivedComplete A s ((E.forget A).app _ R)) →
(cB : IsDerivedComplete A s ((E.forget A).app _ B)) →
  Desc f → IsDescendableCompleteOver A s R B f
-- 指数 n も同じ仮定で保つ。逆向きは要求しない。
-- M40 BS17 Lemma 11.22 の Shared での入口（Dseq は Arrow の ℕ 図式）
(c : JoinCocone Dseq) → IsColimitCone c →
  (∀ j : ℕ, Idx (edge (Dseq.app _ (ULift.up (nerveVertex j)))) n) →
  Idx (edge c.vertex) (2*n)
-- M41 完備圏での同じ余極限評価（complete Arrow の中で hc を要求）
(c : JoinCocone DseqComp) → IsColimitCone c →
  (∀ j : ℕ, HasDescentIndexLECompleteOver A s _ _ (edgeComp (DseqComp.app _
    (ULift.up (nerveVertex j)))) n) →
  HasDescentIndexLECompleteOver A s _ _ (edgeComp c.vertex) (2*n)
-- M42 完備版 Amitsur の同じ増大錐についての降下
IsDescendableCompleteOver A s R B f →
  (d : CompleteAmitsurData A s f) → IsLimitCone d.aug
```

`U_R (...)` 等の頂点適用は `app (op ⦋0⦌)` の略記。
M33 の `M N` は hC_R の対応頂点、左辺は加法的 Hom 群とする。
M35 の `unitComplex A` は D(A) の A。DLE は drafts の
`Derived.IsConnectiveAt A (-1)` と同じ条件（H^i=0、i>−1）であり、符号を反転しない。
M31 は既存の空間値 Hom から内部 Hom の表現対象を供給する工程を含む。

A5/StrongDescent の `fiberSquareRHom`（97 行）の入力型と M34 を一致させる。
特に **RHom_R(F⊗_R F, R⊗_A L)** を使い、
`RHom_R(F⊗_R F,R) ⊗_A L` を任意の L に対して同一視しない。
A5 の Koszul 接続に要るのは M32 の底変換随伴と、**双対可能な K に限る**
次の射の同値性：

```lean
IsDualizable K → Nonempty (VertexIso
  (fiberSquareRHom f K)
  ((tensorWith K).app _ (fiberSquareRHom f (unitComplex A))))
```

これは M32・M34 の係数作用の投影公式として証明する主出力の一部。
A5 の任意離散係数での負次数評価、Koszul 塔の最高次全射、Nakayama は A5 のまま。
RHom の負次数性を M15 の仮定として束ねて A5 の証明済み結果にはしない。

完備 R,B のもとで A5 が必要とする結論は完備圏の descendability。
現 `StrongDescent.lean` は完備版の説明で非完備版 `IsDescendableOver` を表示しているため、
M39 だけではその表示どおりの通常版を逆に導けない。完備版 Prop を A5 が使うのか、
通常版まで別途証明するのかは型の受け渡し時の確認点とする。drafts は無断修正しない。
完備版だけを証明して通常版の完成とは報告しない。

Shared の離散版 `HasDescentIndexLE`、指数判定、baseChange・comp・tensor・Tot、
Frobenius の `DiscreteSource` 付き版、`IsDescendableComplete` への特殊化は
M18・M22・M24–M30・M39–M40 から元の全引数のまま供給する互換出力。
型は `drafts/Shared/Descendable.lean` の同名宣言と同一に保つ。
同ファイル末尾の `isDescendable_of_faithfullyFlat`（Mathew Prop 3.31）は A5 が使わない
別の数学的結果で、上記 M15 引き継ぎの指数・降下・完備版の実装済み数には含めない。

### 1.6 K の R53 との共通化

`refactor-ledger.md` の R53 の行は現版では **55 行（§8 より前）**にある。
「K の再開の①の段0で扱う」という計画状態。
本体全体を `rg` で検索したところ、単語としての `IsThick`・`thickClosure` は未発見。
`StableHoGeneration.lean` は docstring でも明示的に retract 閉包を含めない。
これをそのまま thick と呼ぶことはできない。

一本化案：安定準圏 C 上の頂点述語 P に対する `IsThick C P` を共通の芯とし、
同型・零対象・実 cofiber/fiber・retract で閉じる条件を置く。
`IsThickTensorIdeal` はそれに `∀ x M, P x → P (T M x)` を加えるだけとする。
shift と有限余極限の条件との同値を証明し、drafts の定義へ接続する。

```lean
-- 芯と tensor の閉性の分離（紙上の型）
IsThickTensorIdeal R P ↔
  IsThick C_R P ∧ (∀ x M : V C_R, P x → P ((T_R M).app _ x))
-- 定義の交わりによる生成の普遍性
thickTensorIdealGenerated R M N ↔
  ∀ P : V C_R → Prop, IsThickTensorIdeal R P → P M → P N
```

数学的な共通化は可能だが、既存の K の完成 API に import を差すだけでは済まない。
新しい汎用 `IsThick` を `EInfinity/Modules/` に置いて K から EInfinity へ依存させるのも
不適切なので、K の①での共通配置と公開名を調整すべき境界として記録する。
今回は R53 の実装や台帳の状態を先取りせず、M19 の費用内に比較を確保した。

### 1.7 実測・検証・停止

- 追加はこの報告書一本。Lean ファイル **0 本・0 行・0 宣言**、証明完了 **0 本**。
- M01–M42 は紙の主出力の識別子。恒等・合成や operadic 構造内の法則を含むため、
  「42 個の Lean 定理を証明した」という実測ではない。
- 各主出力に対する前提計算は三本まで、補助照合は C01–C03 の三本までという規則を
  維持する。一覧外の新しい数学が判明した場合は追加枠として進まず報告する。
- 対象ビルド・公理監査は未実施。Lean の変更がなく、段0の上端超過で実装前に
  停止したため。共有ビルド鍵・整理券は取得していない。大きい監査も行っていない。
- 小さい監査は `git diff --check` と変更パスの確認。⑤a 所有の既存ファイル、
  `EInfinity/Interface/`、drafts、main は変更しない。
- M15・G12 の停止点1・2には未到達。上限超過による段0停止を G12 着手で迂回しない。

再開時の判断材料は (i) 上端 11,700 の扱い、(ii) 一般 E の入口と BE への輸送の型、
(iii) A5 の完備版 Prop の受け渡し。これらを未証明の新 interface 欄や仮定にして
隠さず、段0の報告として自分の枝に保存する。


## 2. D80 承認後：標準係数・結合的忘却・厳密底の加群関手（11-14）

ユーザーの段0承認と指示書 §5 を受領。外枠は **17,000 行**、約8,500行での
途中報告を維持する。任意 E への輸送は作らず、BE 模型と A5 の特殊化で進める。
main の承認文書（`41101afb1` を含む）を自分の枝へマージした。
main 自身・⑤a の所有する既存ファイル・界面には書き込んでいない。

### 2.1 検証済みの新設三本

全て `SerrePositivity/EInfinity/BarrattEccles/Modules/` 配下。

| ファイル | 行数（空行・docstring 込み） | 明示宣言数 | 出力 |
| --- | ---: | ---: | --- |
| `StandardCoefficient.lean` | 129 | 9 | M01–M03：全 arity の標準零単体、単位との一致、厳密な全挿入 |
| `AssociativeForget.lean` | 183 | 12 | M04：同じ carrier の結合的 dg 代数と全代数射の忘却関手 |
| `StrictModules.lean` | 108 | 9 | M05 の実構成、M06 の二関手、M09 の拡大の弱同値不変性 |
| **合計** | **420** | **30** | |

生成された補助宣言を含まない明示 `def/abbrev/lemma/theorem` の実測。
M01–M04 は検証済み。M05 は台・正則加群の実頂点を構成したが、
解像度後の台と元の正則加群の指定比較（C01 の残り）は未完。
M06 は全厳密射の拡大・制限の実 ∞ 関手を構成済みで、M07 の随伴はまだ別工程。
M09 は同じ拡大の弱同値不変性が検証済み。
M08・M10 以降の全族・相対テンソル・指数・降下・RHom・完備版は未完。
**固定した厳密底の段階を、native CAlg の全辺への降下の完成とは数えない。**

### 2.2 実装の内容と残る受け渡し

M03 は収縮の切断を使わず、各 arity の恒等置換の零単体から作った。
shuffle 次数 `(0,0)` の経路は一意で符号は一、内側・外側の恒等置換の合成も恒等。
これを元の複体の零次の一の像で検査し、`n=0` 込みで厳密な合成則を証明した。
M04 の左右単位則・結合則はこの等式と代数の作用公理から得た。
右単位則に可換性やホモロジー上の一致は使っていない。
原典対応は Berger–Fresse §1.1.1–1.1.3。

主出力の型は段0どおり。実名は以下。

```lean
standardCoefficient_composite (A : Type u) [CommRing A]
    (m n : ℕ) (i : Fin (m+1)) :
  coefficientComposite m n i (standardCoefficient A (m+1))
    (standardCoefficient A n) = standardCoefficient A (m+n)
assocForget (A : Type u) [CommRing A] :
  (operad A).Algebra ⥤ Mon (Complex A)
assocForget_forget (A : Type u) [CommRing A] :
  assocForget A ⋙ Mon.forget (Complex A) = Operad.Algebra.forget (operad A)
strictModuleUnderlying A X : strictModuleInfinity A X ⟶ derivedInfinityCategory A
strictModuleUnit A X : (strictModuleInfinity A X) _⦋0⦌
strictModuleExtend (f : X ⟶ Y) : strictModuleInfinity A X ⟶ strictModuleInfinity A Y
strictModuleRestrict (f : X ⟶ Y) : strictModuleInfinity A Y ⟶ strictModuleInfinity A X
strictModuleExtend_weak (f : X ⟶ Y) (hf : QuasiIso f.hom) :
  IsQCatEquivalence (strictModuleExtend f)
```

§1 の restriction の射影性保存の問題に対して、
`dgModuleDerivedFunctor` に仮定を足す経路は採用しなかった。
既存 `dgModuleResolvedInfinity` は任意の dg 加群値関手の出力を全関手的に解像する。
これを半自由加群の全包含の後の `dgModuleRestriction` に適用して、実 restriction を構成。
台の忘却にも `moduleEvaluationDG` と `ringConstantDG` の後に同じ構成を使い、
`semifreePointEquivalence` で既存 D(A) に戻す。
正則加群は同じ一対象 dg 圏の representable を解像して指定した。

この出力解像度の存在は M07 の同じ単位・余単位の検証を自動では供給しない。
一般 kernel の `dgKernelAdjunction` と graph 比較は再利用候補として確認済み。
これと今構成した restriction の全関手比較が次の検査対象。

数え方：M03 の shuffle 二補題は前提計算二本。
M04 の全 arity における一入力単位則・部分合成則・射保存則は前提計算三本。
三つのモノイド公理は M04 の構造構成の証明分割として数える。
`assocForget_forget` は C01 の厳密な台の部分。C02・C03 は未使用。
新しい一覧外の数学の補題を追加したとは数えていない。

### 2.3 対象ビルドと小さい監査

全呼び出しを `scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- ...` で実行。
新設三本だけを `lake env lean -o <自分の .lake の出力> <対象>` で検証した。
既存 main の olean は自分の .lake 配下の参照リンクから読み、新規三本の出力だけを
自分の worktree に作った。main と⑤a の build 成果物は書き換えていない。

三本の対象ビルド成功。新規30宣言の `#print axioms` の小監査も成功し、
全て **`propext`・`Classical.choice`・`Quot.sound` のみ**。
`sorryAx`・追加公理なし。監査入力は `/tmp/m15-small-audit.lean`、
ログは `/tmp/m15-small-audit.log`。全体ビルド・大きい監査は回していない。
`git diff --check` と新設三本の禁止語（`sorry`・`axiom`・`admit`）検査も実施する。

これは 420 / 17,000 行時点の区切り記録で、規模による停止ではない。
M15 の停止点1には未到達。引き続き M05 の指定比較・M07 の随伴・M08 の合成へ進む。


## 3. 共通の厚い閉包と native な graph 随伴（11-14、区切り）

追加の三本も対象ビルドを完了した。

| ファイル（SerrePositivity/ 以下） | 行数 | 明示宣言数 |
| --- | ---: | ---: |
| `InfinityCategories/HA/StableInfinityCategories/Thick.lean` | 80 | 5 |
| `EInfinity/Modules/ThickTensorIdeal.lean` | 57 | 4 |
| `EInfinity/BarrattEccles/Modules/StrictAdjunction.lean` | 48 | 2 |
| **今回** | **185** | **11** |
| **累計（六本）** | **605** | **41** |

### 3.1 共通の芯（M19 の一般部分）

`IsThick` は stable な準圏の頂点述語に対し、零・同型・実 cofiber・実 fiber・
ホモトピー圏の retract に関する閉性を持つ。
`thickClosure` を全ての厚い上界の交わりで構成し、生成元の包含・閉性・最小性を証明。
安定圏一般のファイルは EInfinity に依存しない。
原典の対応節は HA §1.1.3、HTT §4.4.5。

`EInfinity/Modules/ThickTensorIdeal.lean` の `IsThickTensorIdeal` は共通の
`IsThick` を継承して、指定した tensorWith の閉性だけを加える。
`thickTensorIdealGenerated` の閉性と生成元の所属も証明した。
原典対応は Mathew Definition 3.18。
これらは M19 の閉包構成の部分証明であり、別の数学的前提を束ねたものではない。

この段階の tensorWith は明示引数であり、BE 相対テンソルの実装済み性は意味しない。
BE の全族への代入、drafts の有限余極限・shift 表示との比較は未完なので、
**M19 全体を完了にはしない**。K 側の既存ファイルは編集していない。

### 3.2 M07 の native な随伴と残る型

同じ厳密 BE 射の `dgAlgebraMap` の graph に、既存の `dgKernelAdjunction` を適用し、
`dgKernelDerivedInfinity_graphIso` と `qcatAdjunctionChangeLeft` で
**既に指定した strictModuleExtend** を左随伴とする実随伴を構成した。
実右随伴の名前は `strictModuleAdjointRestrict`。

この随伴は全関手圏での単位・余単位と両三角式を持つ。
一方、§2 の `strictModuleRestrict` は生の dg 制限を全関手的に解像したもの。
現時点で両者は別の実関手であり、以下の型の比較が未完：

```lean
FunctorIso (strictModuleAdjointRestrict f) (strictModuleRestrict f)
```

この比較と指定された通常の拡大・制限の単位・余単位の接続を証明してから、
M07 完了と数える。h 上の `dgKernelRightAdjoint_classicalIso` だけを、
この全関手同型として使用しない。これは M07／C02 の受け渡しの残りで、
新たな任意 E への輸送や界面欄の追加には進まない。

### 3.3 検証・キャッシュ・現在地

新規三本の対象ビルド成功、累計六本の全41明示宣言の `#print axioms` 小監査成功。
全て標準三公理のみ、`sorryAx` なし。Lean ソースにも `sorry`・`axiom`・`admit` なし。
全体ビルド・大きい監査は実施していない。

一般の安定圏の出力先を追加した際、キャッシュ参照ディレクトリの symlink を
辿って **今回新設した Thick の olean 三ファイルだけ**が main 側のキャッシュへ
出たことを確認した。自分が作った三ファイルを内容照合後に自分の worktree へ移し、
共有側の当該三ファイルを除いた。本体ソース・既存成果物は変更していない。
ビルド補助 `/tmp/m15-target-build.py` を修正し、出力先の各親ディレクトリを
自分の実ディレクトリへ分離した上で、出力先が自分の worktree 内に解決されることを
assert するようにした。累計六本の olean の実パスも自分の worktree 内と確認済み。

現在の一覧：M01–M04 完了、M05（台・単位の比較）途中、M06（二関手）構成済み、
M07（native な graph 随伴は構成済み、同じ restriction への比較）途中、
M08 未完、M09（拡大の弱同値不変性）検証済み、M19（共通の芯）先行分。
M10 以降の残り、RHom・完備反射・完備テンソル、A5 の BE 特殊化は未完。
外枠 17,000 行に対し 605 行。M15 の完成や規模の停止を宣言する区切りではない。

### 3.4 部分補題・構成の型の記録

IS-W2 §14 の証明分割の記録として、ここまでの新設六本の明示宣言の型を列挙する。
名前空間・open・宇宙・型クラスの文脈は各ソースと同じ。証明本体は含めない。
構造の欄は各ソースに記載し、ここでは構造の入口を示す。

`EInfinity/BarrattEccles/Modules/AssociativeForget.lean`：

```lean
def standardOperation (X : (operad A).Algebra) (n : ℕ) :
    power X.carrier n ⟶ X.carrier

def standardBinary (X : (operad A).Algebra) : X.carrier ⊗ X.carrier ⟶ X.carrier

lemma standardOperation_one (X : (operad A).Algebra) :
    standardOperation X 1 = (oneIso X.carrier).hom

lemma standardOperation_composite (X : (operad A).Algebra)
    (m n : ℕ) (i : Fin (m+1)) :
    standardOperation X (m+n) =
      (λ_ (power X.carrier (m+n))).inv ≫
      tensorInsertionAction X.carrier (𝟙_ (Complex A)) m n i
        ((λ_ (power X.carrier n)).hom ≫ standardOperation X n) ≫
      standardOperation X (m+1)

lemma standardBinary_assoc (X : (operad A).Algebra) :
    (standardBinary X ▷ X.carrier) ≫ standardBinary X =
      (α_ X.carrier X.carrier X.carrier).hom ≫
        (X.carrier ◁ standardBinary X) ≫ standardBinary X

lemma standardBinary_one_mul (X : (operad A).Algebra) :
    (standardOperation X 0 ▷ X.carrier) ≫ standardBinary X =
      (λ_ X.carrier).hom

lemma standardBinary_mul_one (X : (operad A).Algebra) :
    (X.carrier ◁ standardOperation X 0) ≫ standardBinary X =
      (ρ_ X.carrier).hom

lemma standardOperation_map {X Y : (operad A).Algebra} (f : X ⟶ Y) (n : ℕ) :
    standardOperation X n ≫ f.hom =
      TensorPowers.map f.hom n ≫ standardOperation Y n

def associativeAlgebra (X : (operad A).Algebra) : Mon (Complex A)

def associativeAlgebraMap {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    associativeAlgebra X ⟶ associativeAlgebra Y

def assocForget : (operad A).Algebra ⥤ Mon (Complex A)

lemma assocForget_forget : assocForget A ⋙ Mon.forget (Complex A) =
    Operad.Algebra.forget (operad A)

```

`EInfinity/BarrattEccles/Modules/StandardCoefficient.lean`：

```lean
def standardSimplex (n : ℕ) : (simplicial n) _⦋0⦌

lemma simplexEquiv_standardSimplex (n : ℕ) (k : Fin 1) :
    simplexEquiv n 0 (standardSimplex n) k = 1

def standardCoefficientCycle (n : ℕ) : complexCycles A (complex A n) 0

def standardCoefficient (n : ℕ) : 𝟙_ (Complex A) ⟶ (operad A).arity n

lemma standardCoefficient_unit : standardCoefficient A 1 = (operad A).unit

lemma standardCoefficient_zero_apply (n : ℕ) (a : A) :
    (standardCoefficient A n).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv a) =
    a • (complexXIso A n 0).inv (normalizedGenerator A n 0 (standardSimplex n))

lemma shuffleSimplex_standard (m n : ℕ) (i : Fin (m + 1)) (s : ShufflePath 0 0) :
    shuffleSimplex m n i s (standardSimplex (m+1)) (standardSimplex n) =
      standardSimplex (m+n)

lemma shuffleBilinear_standard (m n : ℕ) (i : Fin (m + 1)) :
    shuffleBilinear A m n i 0 0
      (normalizedGenerator A (m+1) 0 (standardSimplex (m+1)))
      (normalizedGenerator A n 0 (standardSimplex n)) =
      normalizedGenerator A (m+n) 0 (standardSimplex (m+n))

lemma standardCoefficient_composite (m n : ℕ) (i : Fin (m + 1)) :
    coefficientComposite m n i (standardCoefficient A (m+1))
      (standardCoefficient A n) = standardCoefficient A (m+n)

```

`EInfinity/BarrattEccles/Modules/StrictAdjunction.lean`：

```lean
def strictModuleAdjointRestrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictModuleInfinity A Y ⟶ strictModuleInfinity A X

def strictModuleGraphAdjunction {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    QCatAdjunction (strictModuleExtend f) (strictModuleAdjointRestrict f)

```

`EInfinity/BarrattEccles/Modules/StrictModules.lean`：

```lean
abbrev strictModuleInfinity (X : (operad A).Algebra) : SSet.{u+1}

theorem strictModuleInfinity_isStable (X : (operad A).Algebra) :
    SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (strictModuleInfinity A X)

def strictModuleUnderlyingDG (X : (operad A).Algebra) :
    DGFunctor A (SemifreeDGAlgebraModules A ((assocForget A).obj X))
      (RightModule A PUnit.{1})

def strictModuleUnderlying (X : (operad A).Algebra) :
    strictModuleInfinity A X ⟶ derivedInfinityCategory A

def strictModuleUnit (X : (operad A).Algebra) : (strictModuleInfinity A X) _⦋0⦌

def strictModuleExtend {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictModuleInfinity A X ⟶ strictModuleInfinity A Y

def strictModuleRestrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictModuleInfinity A Y ⟶ strictModuleInfinity A X

theorem strictModuleExtend_isExactFunctor {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor
      (strictModuleExtend f)

theorem strictModuleExtend_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : IsQCatEquivalence (strictModuleExtend f)

```

`InfinityCategories/HA/StableInfinityCategories/Thick.lean`：

```lean
structure IsThick (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (P : C _⦋0⦌ → Prop) : Prop

def thickClosure (P : C _⦋0⦌ → Prop) : C _⦋0⦌ → Prop

lemma subset_thickClosure (P : C _⦋0⦌ → Prop) {x} (hx : P x) : thickClosure C P x

lemma thickClosure_isThick (P : C _⦋0⦌ → Prop) : IsThick C (thickClosure C P)

lemma thickClosure_le_iff (P Q : C _⦋0⦌ → Prop) (hQ : IsThick C Q) :
    (∀ x, thickClosure C P x → Q x) ↔ ∀ x, P x → Q x

```

`EInfinity/Modules/ThickTensorIdeal.lean`：

```lean
structure IsThickTensorIdeal (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (tensorWith : C _⦋0⦌ → (C ⟶ C)) (P : C _⦋0⦌ → Prop) extends IsThick C P

def thickTensorIdealGenerated (M : C _⦋0⦌) : C _⦋0⦌ → Prop

lemma generated_isThickTensorIdeal (M : C _⦋0⦌) :
    IsThickTensorIdeal C tensorWith (thickTensorIdealGenerated C tensorWith M)

lemma mem_generated (M : C _⦋0⦌) : thickTensorIdealGenerated C tensorWith M M

```


## 4. 実 restriction の native 随伴、恒等・合成、正則加群の台（11-14）

### 4.1 運用の更新と実測

main の文書更新 `f0fac44da` を merge `fca3b6dff` で取り込んだ。
ユーザーの 11-14 の続行指示と coordination.md §2 に従い、既存の構成の
単位・余単位・自然性・係数移送・合成・貼り合わせの法則と証明の分割には
本数の上限を設けない。§1〜§3 に残る旧「3 本まで」の記述はこの規則に置換する。
型は以下に記録する。今回、200 行を超える補題はない。
外枠は引き続き M01〜M42・17,000 新設 Lean 行。8,500 行の途中報告点には未到達。

| 新設ファイル | 行 | 宣言（private を含む） | 一覧への対応 |
| --- | ---: | ---: | --- |
| `DGRestrictionLaws.lean` | 103 | 5 | M08 の制限の法則 |
| `DGGraphCounit.lean` | 119 | 6 | M07 の同じ二関手の随伴・余単位の法則 |
| `DGGraphNerveAdjunction.lean` | 77 | 3 | M07 の同じ二関手の随伴・余単位の法則 |
| `DGResolutionAdjunction.lean` | 110 | 6 | M07 の同じ二関手の随伴・余単位の法則 |
| `StrictRestrictionComparison.lean` | 85 | 3 | M07 の同じ二関手の随伴・余単位の法則 |
| `StrictFunctoriality.lean` | 83 | 6 | M08 の四つの比較 |
| `StrictUnderlyingComparison.lean` | 119 | 3 | M05 の台・正則加群の比較 |

今回は 7 本・696 行・32 宣言（公開 29、private 3）。
§3 までとの累積は **13 本・1301 行・73 宣言**。
全てこのレーンの新設ファイル。⑤a の所有する既存ファイル・界面は変更していない。

### 4.2 数学の接続と現在地

生の graph 拡大の余単位を選び直さず、既存の通常の H⁰ 随伴対応を
実加群シフトで全整数次数へ移し、全 Hom 複体の準同型性を証明した。
同じ全 Hom 自然な厳密 dg 余単位を nerve へ送り、全区間写像空間条件から
生の dg nerve 上の随伴 `graphRawAdjunction` を得た（HA §4.2.3）。

半自由包含 `j` と指定解像度 `q` は **j ⊣ q**。
各半自由加群のホモトピー射影性により、同じ augmentation が普遍余単位となる。
ここでも H⁰ の随伴だけを native な随伴とせず、全区間条件から両三角式を得た。
この随伴と生の graph 随伴を合成し、同じ実拡大の包含との比較を使って、
graph 右随伴と当初から定義した `strictModuleRestrict` を全関手同型で接続した。
これで M07 の主型 `QCatAdjunction (strictModuleExtend f) (strictModuleRestrict f)`
を実装した。指定比較に沿う全関手圏の単位の式も `strictModuleAdjunction_unitHom`
に明記した。C02 の全族・局所化・native な辺との照合は M10 とともに残る。

M08 の恒等・合成は拡大・制限の両側で全関手同型を構成した。
制限は既存の厳密な全 Hom 自然性を実出力解像度へ送り、拡大は
同じ制限との随伴の一意性で比較する。制限に射影性保存を仮定しない。
この四つの比較だけでは M10 の高次 coherence・局所化への降下は満たさない。

M05 については、台の評価が準同型を保つことを使い、二段の指定解像度を
同じ唯一点評価と一段の解像度へ全関手同型で比較した。
これを元の表現可能加群で評価し、`strictModuleUnit` の台と同じ BE carrier の
既存 D(A) 内の像との頂点同型 `strictModuleUnitUnderlyingIso` を得た。
元の複体上の平坦性は仮定しない。指定代数単位辺・fiber・指数辺との C01/C03 の
残りは M16 以降と合わせて実装する。

現在地：M01〜M04 完了、M05 の台・正則加群比較を追加、M06 の二関手構成済み、
M07 の実制限との native 随伴・単位移送式を検証、M08 の恒等・合成比較を検証、
M09 の拡大の弱同値不変性を検証、M19 の共通の芯を先行実装。
M10 の全族、M11 以降の相対テンソル、指数・降下、RHom、完備反射・完備テンソル、
A5 の BE 特殊化は未完。M15 の停止点1・G12 の停止点2には未到達。

### 4.3 検証

新設 7 モジュールの対象ビルドは PASS。最後に M05・M07・M08 の三つを再検証し、
公開宣言 29 件の `#print axioms` も PASS。全て
`[propext, Classical.choice, Quot.sound]` のみ（private の依存も推移的に含む）。
指定の `scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- ...` の内側で実行した。
ログは `/tmp/m15-laws-audit.log`。大きい監査・全体ビルドは行っていない。
既存 KST の dg 制限・余単位の法則を import して再利用した。
改名前のキャッシュが残っていた四つの既存依存モジュールは、この worktree の
ローカルキャッシュへ対象再ビルドし、元のソースは変更していない。
計算上限の引き上げ、`sorry`、新しい公理の宣言はない。

### 4.4 追加した法則・証明分割・主出力の型

以下の `N` は dg nerve 関手。各ブロックに実装の変数・namespace を保持する。
非可換の一般 dg 部分も M07/M08 の構成・法則のための共通部分で、任意 E への輸送ではない。

`SerrePositivity/EInfinity/Modules/DGRestrictionLaws.lean`：

```lean
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.KST.LocalizingInvariants
variable (A : Type u) [CommRing A]
variable (D E K : Type v) [DGCategory A D] [Small.{u} D]
  [DGCategory A E] [Small.{u} E] [DGCategory A K] [Small.{u} K]

def restrictionCompRawIso (F : DGFunctor A D E) (G : DGFunctor A E K) :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleRestriction A E K G.op) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleRestriction A D E F.op))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleRestriction A D K (F.comp G).op))

def restrictionIdRawIso :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleRestriction A D D (DGFunctor.id D).op))
      (𝟙 (dgModuleNerve A D))

def resolvedRestriction (F : DGFunctor A D E) :
    dgModuleDerivedInfinityCategory A E ⟶ dgModuleDerivedInfinityCategory A D

def resolvedRestriction_compIso (F : DGFunctor A D E) (G : DGFunctor A E K) :
    FunctorIso (resolvedRestriction A E K G ≫ resolvedRestriction A D E F)
      (resolvedRestriction A D K (F.comp G))

def resolvedRestriction_idIso :
    FunctorIso (resolvedRestriction A D D (DGFunctor.id D))
      (𝟙 (dgModuleDerivedInfinityCategory A D))
```

`SerrePositivity/EInfinity/Modules/DGGraphCounit.lean`：

```lean
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories

private lemma counitBijection {C T : Type*} [Category C] [Category T]
    {L : C ⥤ T} {R : T ⥤ C} (adj : L ⊣ R) (x : C) (y : T) :
    Function.Bijective (fun f : x ⟶ R.obj y => L.map f ≫ adj.counit.app y)

private lemma transportedCounit {C T : Type*} [Category C] [Category T]
    {L : C ⥤ T} {R R' : T ⥤ C} (adj : L ⊣ R) (e : R ≅ R') (y : T) :
    (adj.ofNatIsoRight e).counit.app y = L.map (e.inv.app y) ≫ adj.counit.app y

private lemma functorEqIso_hom_app {C T : Type*} [Category C] [Category T]
    {F G : C ⥤ T} (h : F = G) (x : C) :
    (eqToIso h).hom.app x = eqToHom (congrArg (fun H => H.obj x) h)

variable (A : Type u) [CommRing A]
variable (D E : Type v) [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

lemma moduleGradedShiftWitness (M : RightModule A D) (s : ℤ) :
    ∃ (N : RightModule A D) (f : GradedHom A M N (-s)) (g : GradedHom A N M s),
      differential A f = 0 ∧ differential A g = 0 ∧
      ∃ h : GradedHom A M M (-1),
        (homObject A (RightModule A D) M M).d (-1) 0 h =
          compose A g f (neg_add_cancel s) - (unitElement A M).val

lemma graphCounit_homotopy_bijective (F : DGFunctor A D E) (M : RightModule A E)
    (P : RightModule A D) :
    Function.Bijective (fun f :
      (toHomotopy A (RightModule A D)).obj (ForgetEnrichment.of (Complex A) P) ⟶
        (toHomotopy A (RightModule A D)).obj
          (ForgetEnrichment.of (Complex A) (restrictModule A D E F.op M)) =>
      (dgModuleExtension A D E F).onHomotopy.map f ≫
        (toHomotopy A (RightModule A E)).map (functorExtensionCounit A D E F M))

def graphUniversalCounit (F : DGFunctor A D E) (M : RightModule A E) :
    DGUniversalCounit A (RightModule A D) (RightModule A E) (dgModuleExtension A D E F) M
```

`SerrePositivity/EInfinity/Modules/DGGraphNerveAdjunction.lean`：

```lean
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open scoped Simplicial
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

def graphCounitHomotopy (F : DGFunctor A D E) :
    SSet.Homotopy (N (dgModuleRestriction A D E F.op) ≫ N (dgModuleExtension A D E F))
      (𝟙 (dgModuleNerve A E))

lemma graphCounitHomotopy_vertex_edge (F : DGFunctor A D E) (M : RightModule A E) :
    (simplicialHomotopyVertexEdge (graphCounitHomotopy A D E F) (Simplex.vertex M)).edge =
      (dgClosedEdge A (RightModule A E) (functorExtensionCounit A D E F M)).edge

def graphRawAdjunction (F : DGFunctor A D E) :
    QCatAdjunction (N (dgModuleExtension A D E F)) (N (dgModuleRestriction A D E F.op))
```

`SerrePositivity/EInfinity/Modules/DGResolutionAdjunction.lean`：

```lean
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open scoped Simplicial
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

abbrev semifreeInclusion

abbrev moduleResolution

lemma semifreeCounitColumn_eq (P T : SemifreeDGModules A D) (M : RightModule A D)
    (ε : ForgetEnrichment.of (Complex A) P.val ⟶ ForgetEnrichment.of (Complex A) M) :
    dgCounitColumn A (SemifreeDGModules A D) (RightModule A D) (semifreeInclusion A D)
      (closedHomEquiv A (RightModule A D)
        (ForgetEnrichment.of (Complex A) ((semifreeInclusion A D).obj P))
        (ForgetEnrichment.of (Complex A) M) ε) T =
    moduleHomPostcompose A D T.val P.val M ε

def semifreeUniversalCounit (P : SemifreeDGModules A D) (M : RightModule A D)
    (ε : ForgetEnrichment.of (Complex A) P.val ⟶ ForgetEnrichment.of (Complex A) M)
    (hε : moduleQuasiIso A D ε) :
    DGUniversalCounit A (SemifreeDGModules A D) (RightModule A D) (semifreeInclusion A D) M

lemma moduleResolution_vertex (M : RightModule A D) :
    (moduleResolution A D).app (Opposite.op ⦋0⦌) (Simplex.vertex (A

def moduleResolutionAdjunction :
    QCatAdjunction (N (semifreeInclusion A D)) (moduleResolution A D)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRestrictionComparison.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable {A : Type u} [CommRing A]

def strictModuleRestrictionComparison {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso (strictModuleAdjointRestrict f) (strictModuleRestrict f)

def strictModuleAdjunction {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    QCatAdjunction (strictModuleExtend f) (strictModuleRestrict f)

lemma strictModuleAdjunction_unitHom {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    (strictModuleAdjunction f).unitHom = (strictModuleGraphAdjunction f).unitHom ≫
      (hoFunctor.map ((pre (strictModuleExtend f)).app (strictModuleInfinity A X))).toFunctor.map
        (strictModuleRestrictionComparison f).hom
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictFunctoriality.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (A : Type u) [CommRing A]

lemma algebraMap_id (B : Mon (Complex A)) :
    dgAlgebraMap A (𝟙 B) = DGFunctor.id (dgAlgebraCategory A B)

lemma algebraMap_comp {B C T : Mon (Complex A)} (f : B ⟶ C) (g : C ⟶ T) :
    dgAlgebraMap A (f ≫ g) = (dgAlgebraMap A f).comp (dgAlgebraMap A g)

def strictModuleRestrict_idIso (X : (operad A).Algebra) :
    FunctorIso (strictModuleRestrict (𝟙 X)) (𝟙 (strictModuleInfinity A X))

def strictModuleRestrict_compIso {X Y Z : (operad A).Algebra} (f : X ⟶ Y) (g : Y ⟶ Z) :
    FunctorIso (strictModuleRestrict g ≫ strictModuleRestrict f)
      (strictModuleRestrict (f ≫ g))

def strictModuleExtend_idIso (X : (operad A).Algebra) :
    FunctorIso (strictModuleExtend (𝟙 X)) (𝟙 (strictModuleInfinity A X))

def strictModuleExtend_compIso {X Y Z : (operad A).Algebra} (f : X ⟶ Y) (g : Y ⟶ Z) :
    FunctorIso (strictModuleExtend (f ≫ g))
      (strictModuleExtend f ≫ strictModuleExtend g)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictUnderlyingComparison.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable (A : Type u) [CommRing A]

lemma constant_evaluation_closed {P Q : Complex A}
    (f : ForgetEnrichment.of (Complex A) P ⟶ ForgetEnrichment.of (Complex A) Q) :
    (moduleEvaluation A PUnit.{1} PUnit.unit).map ((ringConstantDG A).onClosed.map f) =
      (closedToComplex A).map f

def strictModuleResolvedUnderlyingIso (X : (operad A).Algebra) :
    FunctorIso
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) ≫ strictModuleUnderlying A X)
      (N (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
        (Opposite.op DGAlgebraPoint.star)) ≫
        dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
          (semifreePointEquivalence A).hom)

def strictModuleUnitUnderlyingIso (X : (operad A).Algebra) :
    VertexIso ((strictModuleUnderlying A X).app (Opposite.op ⦋0⦌) (strictModuleUnit A X))
      ((complexDerivedEvaluation A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ X.carrier))
```

## 5. 同じ忘却・弱同値の逆・厚さの照合・指定余単位（11-14）

§4 の実装と報告を `fce55c7b8` に保存した後、既存構成の法則を続行した。
coordination.md §2 の新しい数え方を適用する。新しい数学的な主出力を
M01〜M42 の外に増やしていない。200 行を超える補題はない。

### 5.1 検証した追加分と実測

| 新設ファイル | 行 | 宣言 | 対応 |
| --- | ---: | ---: | --- |
| `StrictWeakRestriction.lean` | 45 | 2 | M09：同じ拡大・制限を両向きとする弱同値の比較 |
| `StrictUnderlyingRestriction.lean` | 83 | 2 | M05/M06：指定制限と同じ台の忘却の全関手比較 |
| `ThickClosureLaws.lean` | 73 | 4 | M19：既存の安定閉包＋retract と共通の厚さの照合 |
| `DGCounitRecovery.lean` | 47 | 2 | M07：元の全余単位ホモトピーの回収 |

追加 4 本・248 行・10 宣言。累積は **17 本・1,549 行・83 宣言**
（private 3 を含む）。M15 の外枠 17,000 行、途中報告点 8,500 行には未到達。

`strictModuleWeakEquivalence` は既に証明した拡大の弱同値不変性を、
同じ native な右随伴の一意性で元の `strictModuleRestrict` へ移したもの。
これで同じ二関手を両向きに持つ準圏同値を得た。
`strictModuleRestrict_underlyingIso` は対象ごとの比較ではなく、指定制限の後の
忘却と元の忘却の **全関手同型**。一対象の全 Hom 上での評価の等式と、§4 の
指定解像度・台の全関手比較から構成する。M05/M06 の同じ台の接続を進めた。

厚さについては、共通の `IsThick` が既存の `StableVertexClosure` での閉性と
ホモトピー圏の retract 閉性に同値であることを示した（HA §1.1.3、HTT §4.4.5）。
既存の安定閉包から同じ厚い閉包への包含と、厚い条件に対する閉包の恒等則も証明した。
K の R53 側のファイル自体は変更していない。

二つの native 随伴の余単位について、頂点成分だけでなく、元の graph 余単位・
指定解像度の augmentation の **全ホモトピーの類との等式**を追加した。
これで随伴構成で指定した余単位の回収を明示した。

M10 の高次単体を含む全族と C02、M11 以降の相対テンソル、指定単位辺・fiber・指数、
降下・RHom・完備反射・完備テンソルと A5 の BE 特殊化は引き続き未完。
M08 の孤立した比較や今回の弱同値の逆だけで、M10 完了とは数えていない。

### 5.2 対象検証

追加 4 モジュールの対象ビルドと公開 10 宣言の小監査を、全て指定の
`scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- ...` の内側で行った。
最初の 8 宣言は `/tmp/m15-restriction-thick-audit.log`、余単位の 2 宣言は
`/tmp/m15-counit-audit.log`。全て PASS。公理依存は全 10 宣言とも
`[propext, Classical.choice, Quot.sound]` のみ。
大きい監査・全体ビルド・計算上限の引き上げは行っていない。
⑤a の既存ファイルと界面を変更せず、このレーンの新設ファイルに限った。

### 5.3 追加した型

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictWeakRestriction.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
variable {A : Type u} [CommRing A]

def strictModuleWeakEquivalence {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : QCatEquivalence (strictModuleInfinity A X) (strictModuleInfinity A Y)

theorem strictModuleRestrict_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : IsQCatEquivalence (strictModuleRestrict f)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictUnderlyingRestriction.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable {A : Type u} [CommRing A]

lemma strictRestriction_evaluation {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    (dgModuleRestriction A _ _ (dgAlgebraMap A ((assocForget A).map f)).op).comp
      (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
        (Opposite.op DGAlgebraPoint.star)) =
      moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj Y))
        (Opposite.op DGAlgebraPoint.star)

def strictModuleRestrict_underlyingIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso (strictModuleRestrict f ≫ strictModuleUnderlying A X)
      (strictModuleUnderlying A Y)
```

`SerrePositivity/InfinityCategories/HA/StableInfinityCategories/ThickClosureLaws.lean`：

```lean
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (C : SSet.{u}) [Quasicategory C] [IsStable C]

lemma IsThick.stableClosure {P : C _⦋0⦌ → Prop} (hP : IsThick C P)
    {x : C _⦋0⦌} (hx : StableVertexClosure {y | P y} x) : P x

lemma isThick_iff_stableClosure_retract (P : C _⦋0⦌ → Prop) :
    IsThick C P ↔
      (∀ x, StableVertexClosure {y | P y} x → P x) ∧
      (∀ x y, Nonempty (Retract (HomotopyCategory.mk x) (HomotopyCategory.mk y)) → P y → P x)

lemma stableVertexClosure_le_thickClosure (P : C _⦋0⦌ → Prop) {x}
    (hx : StableVertexClosure {y | P y} x) : thickClosure C P x

lemma thickClosure_eq_self (P : C _⦋0⦌ → Prop) (hP : IsThick C P) :
    thickClosure C P = P
```

`SerrePositivity/EInfinity/Modules/DGCounitRecovery.lean`：

```lean
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

lemma graphRawAdjunction_counitHom (F : DGFunctor A D E) :
    (graphRawAdjunction A D E F).counitHom =
      Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (graphCounitHomotopy A D E F))

omit [DGCategory A E] [Small.{u} E] in

lemma moduleResolutionAdjunction_counitHom :
    (moduleResolutionAdjunction A D).counitHom =
      Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgModuleResolutionAugmentationHomotopy A D))
```

## 6. M10 の厳密な相対圏の族への接続（11-14、着手前）

main の `fb3dfd20e` までの文書（共通の /goal・一覧の進捗規則）を取り込んだ。
B4 の実行指示はまだない。⑤d の M15→G12 の範囲で続行する。

**一覧：済み 9／全体 42（うち追加 0）**。
M01〜M09 の厳密底上の主出力は検証済み。M19 は一般の芯のみで未完。
C01〜C03 に記載した既存構成の照合は法則の記録であり、一覧の全体には加算しない。
全族や相対テンソルの主型は、孤立した比較や条件付き Setup で置き換えない。

### 6.1 次の束の型（M10 の構成の分割）

まず同じ dg 加群・同じ準同型を持つ通常の相対圏の fiber と実 restriction を作る。
その恒等・合成の比較は、既存の加群制限の元の成分を保持する。
これは M10 の局所化前の材料であり、native CAlg 上の cocartesian fibration が
既に出来たとは数えない。高次の族と局所化・fiber 比較はこの後に接続する。
新しい ID は追加しない。

```lean
-- A : Type u; [CommRing A]; X Y Z : (operad A).Algebra
-- D_X := dgAlgebraCategory A ((assocForget A).obj X)
abbrev strictRawModuleCategory (X : (operad A).Algebra) := ModuleCategory A D_X

def strictRawModuleRelativeCategory (X : (operad A).Algebra) : RelativeCategory.{u+1}

def strictRawModuleRestrict (f : X ⟶ Y) :
  strictRawModuleCategory A Y ⥤ strictRawModuleCategory A X

def strictRawModuleRestrictRelative (f : X ⟶ Y) :
  strictRawModuleRelativeCategory A Y ⟶ strictRawModuleRelativeCategory A X

def strictRawModuleRestrict_idIso (X : (operad A).Algebra) :
  strictRawModuleRestrict (𝟙 X) ≅ 𝟭 (strictRawModuleCategory A X)

def strictRawModuleRestrict_compIso (f : X ⟶ Y) (g : Y ⟶ Z) :
  strictRawModuleRestrict g ⋙ strictRawModuleRestrict f ≅ strictRawModuleRestrict (f ≫ g)
```

単位・合成比較の成分の評価、自然性・結合・貼り合わせの法則は同じ束の法則として
型を追記する。200 行を超える証明があれば行数も記録する。

### 6.2 M10 の次の分割の型（着手前）

前節の同じ単位・合成比較の貼り合わせを使って、通常の相対族の全圏と射影を作る。
この型を含む擬関手の結合・左右単位の法則は、元の成分の評価によって照合する。

```lean
open scoped CategoryTheory.Bicategory
-- A : Type u; [CommRing A]
def strictRawModuleRestrictionPseudofunctor :
  LocallyDiscrete ((operad A).Algebraᵒᵖ) ⥤ᵖ Cat.{u, u+1}
abbrev strictRawModuleTotal :=
  Pseudofunctor.CoGrothendieck (strictRawModuleRestrictionPseudofunctor A)
def strictRawModuleProjection : strictRawModuleTotal A ⥤ (operad A).Algebra
```

この通常の Grothendieck 圏だけでは M10 の完成ではない。同じ相対圏の局所化と
元の dg nerve fiber の全比較、native CAlg 上の高次 transport は依然必要。
**一覧：済み 9／全体 42（うち追加 0）**。

### 6.3 同じ全圏の忘却・相対局所化の射影（着手前）

```lean
-- A : Type u; [CommRing A]
def strictRawModuleTotalForget : strictRawModuleTotal A ⥤ Complex A
-- 準同型は「底の BE 射が準同型、かつ同じ台の加群射が準同型」の同時条件。
def strictRawModuleTotalRelative : RelativeCategory.{u+1}
def strictRawModuleTotalProjectionRelative :
  strictRawModuleTotalRelative A ⟶ algebraRelativeCategory A
abbrev moduleTotalInfinity : SSet.{u+1}
def moduleTotalProjection : moduleTotalInfinity A ⟶ CAlg_R A
```

相対局所化の射影は元の全単体を持つ実写像として作り、頂点の写像だけでは済ませない。
ただし射影の cocartesian 性と fiber の同じ半自由 dg nerve との比較が残る限り、
この写像だけを `ModuleFamily` の完成として数えない。

### 6.4 実装の実測と追加法則の型

| 新設ファイル | 行 | 宣言 |
| --- | ---: | ---: |
| `StrictRawModules.lean` | 118 | 10 |
| `StrictRawCoherence.lean` | 125 | 6 |
| `StrictRawFamily.lean` | 102 | 3 |
| `TotalLocalization.lean` | 94 | 6 |

新設 4 本・439 行・25 宣言。累積 **21 本・1,988 行・108 宣言**
（private 3 を含む）。200 行を超える補題はない。型付き一覧に新しい ID を追加していない。

**一覧：済み 9／全体 42（うち追加 0）**。

準同型を保つ元の制限、単位・合成比較の恒等成分、その逆成分と左右単位・結合の
貼り合わせを検証した。この同じデータから擬関手と通常の全圏を構成した。
全圏の台は元の複体で、準同型条件は底と台の二つの準同型類の逆像の交わり。
局所化の射影の底は新しい代数模型ではなく、既存の cofibrant 置換を通した同じ CAlg_R。
新設 4 モジュールの対象ビルドは PASS。公開 25 宣言の小監査も PASS、
公理依存は全て `[propext, Classical.choice, Quot.sound]` のみ。
指定の `scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- ...` の内側で実行した。
最終対象ログは `/tmp/m15-total-localization3.log`（比較・全圏）と
`/tmp/m15-total-localization4.log`（射影）、監査は `/tmp/m15-audit6-verified.log`。
大きい監査・全体ビルドは行っていない。計算上限も引き上げていない。

M10 の未完の部分は、局所化の射影の cocartesian 性（必要なら同じ底上の
fibration 模型との比較も含む）、fiber の元の半自由 dg nerve との全比較、
その比較の厳密な単位・忘却・拡大との整合性。ここを仮定の欄に置かない。
M11〜M42 の残りと G12 はまだ完成していない。

以下は今回の構成と法則の実装の型。`strictRawModuleRelativeCategory` は対象を変えず
Hom だけを ULift し、元の準同型を down で引き戻す。

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawModules.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (A : Type u) [CommRing A]

abbrev strictRawModuleCategory (X : (operad A).Algebra) :=
  ModuleCategory A (dgAlgebraCategory A ((assocForget A).obj X))

def strictRawModuleRelativeCategory (X : (operad A).Algebra) : RelativeCategory.{u+1}

variable {A}

def strictRawModuleRestrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleCategory A Y ⥤ strictRawModuleCategory A X

def strictRawModuleRestrictRelative {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleRelativeCategory A Y ⟶ strictRawModuleRelativeCategory A X

def strictRawModuleRestrict_idIso (X : (operad A).Algebra) :
    strictRawModuleRestrict (𝟙 X) ≅ 𝟭 (strictRawModuleCategory A X)

def strictRawModuleRestrict_compIso {X Y Z : (operad A).Algebra} (f : X ⟶ Y) (g : Y ⟶ Z) :
    strictRawModuleRestrict g ⋙ strictRawModuleRestrict f ≅ strictRawModuleRestrict (f ≫ g)

def strictRawModuleUnderlying (X : (operad A).Algebra) : strictRawModuleCategory A X ⥤ Complex A

lemma strictRawModuleHom_ext {X : (operad A).Algebra} {M T : strictRawModuleCategory A X}
    {f g : M ⟶ T} (h : (strictRawModuleUnderlying X).map f = (strictRawModuleUnderlying X).map g) :
    f = g

lemma strictRawModuleRestrict_idIso_eval (X : (operad A).Algebra) (M : strictRawModuleCategory A X) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_idIso X).hom.app M) =
      𝟙 ((strictRawModuleUnderlying X).obj M)

lemma strictRawModuleRestrict_compIso_eval {X Y Z : (operad A).Algebra}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : strictRawModuleCategory A Z) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_compIso f g).hom.app M) =
      𝟙 ((strictRawModuleUnderlying Z).obj M)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawCoherence.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {A : Type u} [CommRing A]

lemma strictRawModuleRestrict_eval {X Y : (operad A).Algebra} (f : X ⟶ Y)
    {M T : strictRawModuleCategory A Y} (g : M ⟶ T) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict f).map g) =
      (strictRawModuleUnderlying Y).map g

lemma strictRawModuleRestrict_idIso_inv_eval (X : (operad A).Algebra)
    (M : strictRawModuleCategory A X) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_idIso X).inv.app M) =
      𝟙 ((strictRawModuleUnderlying X).obj M)

lemma strictRawModuleRestrict_compIso_inv_eval {X Y Z : (operad A).Algebra}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : strictRawModuleCategory A Z) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_compIso f g).inv.app M) =
      𝟙 ((strictRawModuleUnderlying Z).obj M)

lemma strictRawModuleRestrict_comp_assoc {W X Y Z : (operad A).Algebra}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    isoWhiskerRight (strictRawModuleRestrict_compIso g h) (strictRawModuleRestrict f) ≪≫
        strictRawModuleRestrict_compIso f (g ≫ h) =
      Functor.associator (strictRawModuleRestrict h) (strictRawModuleRestrict g)
          (strictRawModuleRestrict f) ≪≫
        isoWhiskerLeft (strictRawModuleRestrict h) (strictRawModuleRestrict_compIso f g) ≪≫
        strictRawModuleRestrict_compIso (f ≫ g) h ≪≫
        eqToIso (congrArg (fun k => strictRawModuleRestrict k) (Category.assoc f g h))

lemma strictRawModuleRestrict_comp_id {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleRestrict_compIso f (𝟙 Y) ≪≫
        eqToIso (congrArg (fun k => strictRawModuleRestrict k) (Category.comp_id f)) =
      isoWhiskerRight (strictRawModuleRestrict_idIso Y) (strictRawModuleRestrict f) ≪≫
        Functor.leftUnitor (strictRawModuleRestrict f)

lemma strictRawModuleRestrict_id_comp {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleRestrict_compIso (𝟙 X) f ≪≫
        eqToIso (congrArg (fun k => strictRawModuleRestrict k) (Category.id_comp f)) =
      isoWhiskerLeft (strictRawModuleRestrict f) (strictRawModuleRestrict_idIso X) ≪≫
        Functor.rightUnitor (strictRawModuleRestrict f)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawFamily.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
variable (A : Type u) [CommRing A]

def strictRawModuleRestrictionPseudofunctor :
    LocallyDiscrete ((operad A).Algebraᵒᵖ) ⥤ᵖ Cat.{u, u+1}

abbrev strictRawModuleTotal := Pseudofunctor.CoGrothendieck
  (strictRawModuleRestrictionPseudofunctor A)

def strictRawModuleProjection : strictRawModuleTotal A ⥤ (operad A).Algebra
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/TotalLocalization.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
attribute [local implicit_reducible] strictRawModuleRestrictionPseudofunctor
variable (A : Type u) [CommRing A]

def strictRawModuleTotalForget : strictRawModuleTotal A ⥤ Complex A

def strictRawModuleTotalRelative : RelativeCategory.{u+1}

def strictRawModuleTotalProjectionRelative :
    strictRawModuleTotalRelative A ⟶ algebraRelativeCategory A

abbrev moduleTotalInfinity : SSet.{u+1}

instance moduleTotalInfinity_quasicategory : Quasicategory (moduleTotalInfinity A)

def moduleTotalProjection : moduleTotalInfinity A ⟶ CAlg_R A
```

## 7. M10 の固定底の fiber と全圏への包含（11-14、着手前）

main の `b2d198488` までの文書を取り込んだ。B4 の実行指示はまだない。
M10 の既存構成の分割として、同じ固定底の加群圏の包含と、通常の fiber の比較を作る。
Mathlib の同じ擬関手の Grothendieck 構成が持つ包含・Cartesian lift・fiber 同値を再利用する。
native な局所化後の fiber 同値や cocartesian 性を、この通常圏の結果で代用しない。

**一覧：済み 9／全体 42（うち追加 0）**。

```lean
-- A : Type u; [CommRing A]; X Y : (operad A).Algebra; f : X ⟶ Y
def strictRawModuleFiberInclusion (X : (operad A).Algebra) :
  strictRawModuleCategory A X ⥤ strictRawModuleTotal A

lemma strictRawModuleFiberInclusion_projection (X : (operad A).Algebra) :
  strictRawModuleFiberInclusion A X ⋙ strictRawModuleProjection A =
    (Functor.const (strictRawModuleCategory A X)).obj X

lemma strictRawModuleFiberInclusion_forget (X : (operad A).Algebra) :
  strictRawModuleFiberInclusion A X ⋙ strictRawModuleTotalForget A = strictRawModuleUnderlying X

def strictRawModuleFiberEquivalence (X : (operad A).Algebra) :
  strictRawModuleCategory A X ≌ Functor.Fiber (strictRawModuleProjection A) X

def strictRawModuleFiberInclusionRelative (X : (operad A).Algebra) :
  strictRawModuleRelativeCategory A X ⟶ strictRawModuleTotalRelative A

def strictRawModuleFiberBaseRelative (X : (operad A).Algebra) :
  strictRawModuleRelativeCategory A X ⟶ algebraRelativeCategory A

lemma strictRawModuleFiberInclusionRelative_projection (X : (operad A).Algebra) :
  strictRawModuleFiberInclusionRelative A X ≫ strictRawModuleTotalProjectionRelative A =
    strictRawModuleFiberBaseRelative A X

def moduleRawFiberInclusion (X : (operad A).Algebra) :
  localizationNerve (strictRawModuleRelativeCategory A X) ⟶ moduleTotalInfinity A
-- 同じ相対関手の全単体での射影可換式も構成する。
```

単位比較の逆成分が同じ台で恒等になる §6 の法則を使い、包含と台の忘却を
厳密な関手等式で接続する。相対包含の準同型保存はこの等式から供給する。

### 7.1 同じ通常の Cartesian lift の相対性（着手前）

続いて M10 の既存の Grothendieck 構成の Cartesian lift の法則を使う。
元の制限が同じ台を保つため、その標準 lift の台は恒等射であり、底の射が弱同値なら
標準 lift は全圏の指定準同型となる。これは局所化後の底の弱同値の反転に使う法則。

```lean
instance strictRawModuleProjection_isFibered : IsFibered (strictRawModuleProjection A)

def strictRawModuleCartesianLift (f : X ⟶ Y) (M : strictRawModuleCategory A Y) :
  (strictRawModuleFiberInclusion A X).obj ((strictRawModuleRestrict f).obj M) ⟶
    (strictRawModuleFiberInclusion A Y).obj M

lemma strictRawModuleCartesianLift_isStronglyCartesian (f : X ⟶ Y)
  (M : strictRawModuleCategory A Y) :
  IsStronglyCartesian (strictRawModuleProjection A) f (strictRawModuleCartesianLift A f M)

lemma strictRawModuleCartesianLift_underlying (f : X ⟶ Y)
  (M : strictRawModuleCategory A Y) :
  (strictRawModuleTotalForget A).map (strictRawModuleCartesianLift A f M) =
    𝟙 ((strictRawModuleUnderlying Y).obj M)

lemma strictRawModuleCartesianLift_weak (f : X ⟶ Y) (hf : QuasiIso f.hom)
  (M : strictRawModuleCategory A Y) :
  (strictRawModuleTotalRelative A).weakEquivalences
    (ULiftHom.up.map (strictRawModuleCartesianLift A f M))
```

これは通常の Cartesian 性の法則で、native な cocartesian 性は依然別に証明する。
**一覧：済み 9／全体 42（うち追加 0）**。

### 7.2 同じ正則加群の section（着手前）

M05・M10 の同じ正則加群を全圏へ載せる分割として、既存の
`representableRestrictionMap` により通常の section を構成する。
この射の同じ台は元の BE 代数射そのものなので、section は準同型を保つ。

```lean
-- A : Type u; [CommRing A]
def strictRawRegularObject (X : (operad A).Algebra) : strictRawModuleTotal A

def strictRawRegularMap (f : X ⟶ Y) : strictRawRegularObject A X ⟶ strictRawRegularObject A Y

lemma strictRawRegularMap_underlying (f : X ⟶ Y) :
  (strictRawModuleTotalForget A).map (strictRawRegularMap A f) = f.hom

def strictRawModuleUnitSection : (operad A).Algebra ⥤ strictRawModuleTotal A

lemma strictRawModuleUnitSection_projection :
  strictRawModuleUnitSection A ⋙ strictRawModuleProjection A = 𝟭 (operad A).Algebra

def strictRawModuleUnitSectionRelative : algebraRelativeCategory A ⟶ strictRawModuleTotalRelative A

lemma strictRawModuleUnitSectionRelative_projection :
  strictRawModuleUnitSectionRelative A ≫ strictRawModuleTotalProjectionRelative A = 𝟙 (algebraRelativeCategory A)

def moduleUnitSection : CAlg_R A ⟶ moduleTotalInfinity A
-- 同じ section の局所化射影との全単体での合成式も検証する。
```

正則加群の台・恒等・合成の法則と全圏の射の外延性を、この同じ構成の法則として
記録する。局所化後の fiber 同値が完成するまで、既存の半自由模型の単位との
全比較が終わったとは数えない。
**一覧：済み 9／全体 42（うち追加 0）**。

### 7.3 同じ相対局所化の係数移送の法則（着手前）

M10 で同じ全代数模型と cofibrant 模型を移すため、既存の自由 hammock の
augmentation・比較の係数自然性から、同じ局所化 Hom 射の弱同値性へ移す法則を使う。
これは既存の相対局所化関手の係数移送であり、新しいモデル構造は構成しない。

```lean
-- C D : RelativeCategory.{u}; F : C ⟶ D
lemma localizationHomMap_weak_of_hammock (X Y : C.category)
  (h : IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
  IsWeakHomotopyEquivalence (localizationHomMap F X Y)

lemma localizationNerveMap_fullyFaithful_of_hammock
  (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
  IsFullyFaithful (localizationNerveMap F)

-- G : D ⟶ C; ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category
lemma localizationNerveMap_essentiallySurjective_of_counit
  (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
  IsEssentiallySurjective (localizationNerveMap F)

lemma localizationNerveMap_isQCatEquivalence_of_hammock_counit
  (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y))
  (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
  IsQCatEquivalence (localizationNerveMap F)
```

両合成から恒等への元の弱自然変換がある場合の既存の hammock 判定を、この同じ
全 nerve へ移す系も記録する。元の全関手・Hom 射を保持する係数移送であり、
対象ごとの比較や h 上の同値には弱めない。
**一覧：済み 9／全体 42（うち追加 0）**。

### 7.4 同じ BE 底の模型の係数移送への適用（着手前）

前節の既存局所化の法則を、⑤a の元の二つの相対関手と指定弱比較に適用する。
⑤a のソースは変更しない。

```lean
lemma cAlgToAlgebraLocalization_isQCatEquivalence :
  IsQCatEquivalence (localizationNerveMap (cofibrantToAlgebraDKRelative A))
lemma algebraLocalizationToCAlg_isQCatEquivalence :
  IsQCatEquivalence (localizationNerveMap (algebraToCofibrantDKRelative A))
lemma moduleUnitSection_projection_isQCatEquivalence :
  IsQCatEquivalence (moduleUnitSection A ≫ moduleTotalProjection A)
```

二つの関手が同値であることだけでは、指定弱自然変換の全関手圏での回収や、
正則加群の実関手が指定された恒等底上の section となる全比較は完成しない。
その比較と native fiber・cocartesian 性は引き続き必要。
**一覧：済み 9／全体 42（うち追加 0）**。

### 7.5 検証済みの結果と実際の型（2026-11-14）

§7〜§7.4 の五ファイルを対象ビルドで検証した。今回追加は 491 行・33 宣言、
累計は新規 Lean 26 ファイル・2,479 行・141 宣言（private 3 を含む）。
IS-W2 §14 と同じソース全行で数え、200 行を超える補題はない。
外枠 17,000 行、約 8,500 行での途中報告の規約を維持する。

全て `scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- ...` の下で実行し、
五ファイルの対象ビルドと今回の公開 33 宣言の小さい公理監査が通過した。
監査の実出力は 33 件あり、依存公理は `propext`・`Classical.choice`・`Quot.sound`
のみ。`sorryAx`・追加公理はない。大きい監査は実施していない。
通常の fiber 同値と Cartesian lift、正則加群の実関手、
同じ二つの BE 底の局所化関手自身の準圏同値性までを得た。
指定弱自然変換の全関手圏での回収、半自由の native fiber との比較と
native cocartesian 性は依然未完了なので、M10 は完了に数えない。

既存の構成の係数移送・射影・自然性・合成則の分割として、今回の実際の宣言の型を
以下に記録する。共通文脈は各ソースの `universe u`、`A : Type u`、`[CommRing A]`、
および明記した名前空間・変数である。新しい一次 ID は追加しない。

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawFiber.lean`（121 行・9 宣言）：

```lean
def strictRawModuleFiberInclusion (X : (operad A).Algebra) :
    strictRawModuleCategory A X ⥤ strictRawModuleTotal A

lemma strictRawModuleFiberInclusion_projection (X : (operad A).Algebra) :
    strictRawModuleFiberInclusion A X ⋙ strictRawModuleProjection A =
      (Functor.const (strictRawModuleCategory A X)).obj X

lemma strictRawModuleFiberInclusion_forget (X : (operad A).Algebra) :
    strictRawModuleFiberInclusion A X ⋙ strictRawModuleTotalForget A = strictRawModuleUnderlying X

def strictRawModuleFiberEquivalence (X : (operad A).Algebra) :
    strictRawModuleCategory A X ≌ Functor.Fiber (strictRawModuleProjection A) X

def strictRawModuleFiberInclusionRelative (X : (operad A).Algebra) :
    strictRawModuleRelativeCategory A X ⟶ strictRawModuleTotalRelative A

def strictRawModuleFiberBaseRelative (X : (operad A).Algebra) :
    strictRawModuleRelativeCategory A X ⟶ algebraRelativeCategory A

lemma strictRawModuleFiberInclusionRelative_projection (X : (operad A).Algebra) :
    strictRawModuleFiberInclusionRelative A X ≫ strictRawModuleTotalProjectionRelative A =
      strictRawModuleFiberBaseRelative A X

def moduleRawFiberInclusion (X : (operad A).Algebra) :
    localizationNerve (strictRawModuleRelativeCategory A X) ⟶ moduleTotalInfinity A

lemma moduleRawFiberInclusion_projection (X : (operad A).Algebra) :
    moduleRawFiberInclusion A X ≫ moduleTotalProjection A =
      localizationNerveMap (strictRawModuleFiberBaseRelative A X ≫ algebraToCofibrantDKRelative A)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawCartesian.lean`（78 行・5 宣言）：

```lean
instance strictRawModuleProjection_isFibered : IsFibered (strictRawModuleProjection A)

def strictRawModuleCartesianLift {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    (strictRawModuleFiberInclusion A X).obj ((strictRawModuleRestrict f).obj M) ⟶
      (strictRawModuleFiberInclusion A Y).obj M

lemma strictRawModuleCartesianLift_isStronglyCartesian {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    IsStronglyCartesian (strictRawModuleProjection A) f (strictRawModuleCartesianLift A f M)

lemma strictRawModuleCartesianLift_underlying {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    (strictRawModuleTotalForget A).map (strictRawModuleCartesianLift A f M) =
      𝟙 ((strictRawModuleUnderlying Y).obj M)

lemma strictRawModuleCartesianLift_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    (strictRawModuleTotalRelative A).weakEquivalences
      ((ULiftHom.up.{u,u+1,u+1} (C
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRegularSection.lean`（137 行・11 宣言）：

```lean
-- M T : strictRawModuleTotal A; f g : M ⟶ T（hom_ext の暗黙引数）
lemma strictRawModuleTotal_hom_ext {M T : strictRawModuleTotal A} {f g : M ⟶ T}
    (hb : (strictRawModuleProjection A).map f = (strictRawModuleProjection A).map g)
    (hv : (strictRawModuleTotalForget A).map f = (strictRawModuleTotalForget A).map g) : f = g

def strictRawRegularObject (X : (operad A).Algebra) : strictRawModuleTotal A

lemma strictRawRegularObject_underlying (X : (operad A).Algebra) :
    (strictRawModuleTotalForget A).obj (strictRawRegularObject A X) = X.carrier

def strictRawRegularMap {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawRegularObject A X ⟶ strictRawRegularObject A Y

lemma strictRawRegularMap_underlying {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    (strictRawModuleTotalForget A).map (strictRawRegularMap A f) = f.hom

def strictRawModuleUnitSection : (operad A).Algebra ⥤ strictRawModuleTotal A

lemma strictRawModuleUnitSection_projection :
    strictRawModuleUnitSection A ⋙ strictRawModuleProjection A = 𝟭 (operad A).Algebra

def strictRawModuleUnitSectionRelative : algebraRelativeCategory A ⟶ strictRawModuleTotalRelative A

lemma strictRawModuleUnitSectionRelative_projection :
    strictRawModuleUnitSectionRelative A ≫ strictRawModuleTotalProjectionRelative A =
      𝟙 (algebraRelativeCategory A)

def moduleUnitSection : CAlg_R A ⟶ moduleTotalInfinity A

lemma moduleUnitSection_projection :
    moduleUnitSection A ≫ moduleTotalProjection A =
      localizationNerveMap (cofibrantToAlgebraDKRelative A ≫ algebraToCofibrantDKRelative A)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/AlgebraModelComparison.lean`（53 行・3 宣言）：

```lean
lemma cAlgToAlgebraLocalization_isQCatEquivalence :
    IsQCatEquivalence (localizationNerveMap (cofibrantToAlgebraDKRelative A))

lemma algebraLocalizationToCAlg_isQCatEquivalence :
    IsQCatEquivalence (localizationNerveMap (algebraToCofibrantDKRelative A))

lemma moduleUnitSection_projection_isQCatEquivalence :
    IsQCatEquivalence (moduleUnitSection A ≫ moduleTotalProjection A)
```

`SerrePositivity/EInfinity/Modules/RelativeLocalizationEquivalence.lean`（102 行・5 宣言）：

```lean
variable {C D : RelativeCategory.{u}} (F : C ⟶ D) (G : D ⟶ C)
lemma localizationHomMap_weak_of_hammock (X Y : C.category)
    (h : IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
    IsWeakHomotopyEquivalence (localizationHomMap F X Y)

lemma localizationNerveMap_fullyFaithful_of_hammock
    (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
    IsFullyFaithful (localizationNerveMap F)

lemma localizationNerveMap_essentiallySurjective_of_counit
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category)
    (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    IsEssentiallySurjective (localizationNerveMap F)

lemma localizationNerveMap_isQCatEquivalence_of_hammock_counit
    (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y))
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category)
    (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    IsQCatEquivalence (localizationNerveMap F)

lemma localizationNerveMap_isQCatEquivalence_of_weak_comparisons
    (η : F.functor ⋙ G.functor ⟶ 𝟭 C.category) (hη : ∀ X, C.weakEquivalences (η.app X))
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category) (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    IsQCatEquivalence (localizationNerveMap F)
```

**一覧：済み 9／全体 42（うち追加 0）**。

## 8. M10 の同じ底の弱比較を全関手間へ移す分割（11-14）

§7 の二つの係数関手について、同じ弱自然変換の通常の円筒を局所化する。
円筒の指定弱射は元の圏への射影の逆像であり、射影の逆候補には零端点を使う。
元の弱縮約と厳密な端点・射影の合成則から、同じ射影の局所化が同値になる。
その全関手単体集合の同型を同じ円筒関手で後合成して、
元の二つの局所化関手間の `FunctorIso` を得る。
これは既存の相対局所化の自然性・係数移送・単位・余単位の法則の証明の分割。
新しい一次 ID は追加しない。

元の `cofibrantDKComparison` と `algebraDKComparison` に適用して、
順方向・逆方向とも元の相対関手のままの `QCatEquivalence` を組み立てる。
同じ正則加群の実関手と射影の合成から恒等への全関手間の可逆比較も得る。
各頂点でのこの比較と元の指定弱辺の比較は引き続き照合し、
半自由 native fiber との比較・native cocartesian 性も残す。
したがって M10 は未完了である。

以下に追加する法則の実際の型を記録する。`C D : RelativeCategory.{u}`、
`F G : C ⟶ D`、BE 適用では `A : Type u` と `[CommRing A]` を共通文脈とする。

`SerrePositivity/EInfinity/Modules/RelativeCylinderLaws.lean`（89 行・7 宣言）：

```lean
def relativeCylinder : RelativeCategory.{u}

def relativeCylinderProjection : relativeCylinder C ⟶ C

def relativeCylinderEndpoint (i : Fin 2) : C ⟶ relativeCylinder C

lemma relativeCylinderEndpoint_projection (i : Fin 2) :
    relativeCylinderEndpoint C i ≫ relativeCylinderProjection C = 𝟙 C

def relativeCylinderContraction :
    (relativeCylinderProjection C).functor ⋙ (relativeCylinderEndpoint C 0).functor ⟶
      𝟭 (relativeCylinder C).category

lemma relativeCylinderContraction_weak (X : (relativeCylinder C).category) :
    (relativeCylinder C).weakEquivalences ((relativeCylinderContraction C).app X)

lemma relativeCylinderProjection_isQCatEquivalence :
    IsQCatEquivalence (localizationNerveMap (relativeCylinderProjection C))
```

`SerrePositivity/EInfinity/Modules/RelativeNaturalComparison.lean`（103 行・5 宣言）：

```lean
def relativeCylinderEndpointIso :
    FunctorIso (localizationNerveMap (relativeCylinderEndpoint C 0))
      (localizationNerveMap (relativeCylinderEndpoint C 1))

def relativeNaturalCylinder (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) : relativeCylinder C ⟶ D

lemma relativeNaturalCylinder_zero (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) :
    relativeCylinderEndpoint C 0 ≫ relativeNaturalCylinder η hη = F

lemma relativeNaturalCylinder_one (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) :
    relativeCylinderEndpoint C 1 ≫ relativeNaturalCylinder η hη = G

def localizationNerveMapIsoOfWeakNatTrans (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) :
    FunctorIso (localizationNerveMap F) (localizationNerveMap G)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/AlgebraRoundTripComparison.lean`（70 行・4 宣言）：

```lean
def cAlgModelRoundTripIso :
    FunctorIso (localizationNerveMap (cofibrantToAlgebraDKRelative A) ≫
      localizationNerveMap (algebraToCofibrantDKRelative A)) (𝟙 (CAlg_R A))

def algebraModelRoundTripIso :
    FunctorIso (localizationNerveMap (algebraToCofibrantDKRelative A) ≫
      localizationNerveMap (cofibrantToAlgebraDKRelative A))
      (𝟙 (localizationNerve (algebraRelativeCategory A)))

def cAlgAlgebraModelEquivalence :
    QCatEquivalence (CAlg_R A) (localizationNerve (algebraRelativeCategory A))

def moduleUnitSection_projectionIso :
    FunctorIso (moduleUnitSection A ≫ moduleTotalProjection A) (𝟙 (CAlg_R A))
```

### 8.1 実測と対象ビルド

§8 の追加は新規 Lean 3 ファイル・262 行・16 宣言。
累計は新規 Lean 29 ファイル・2,741 行・157 宣言（private 3 を含む）。
200 行を超える補題はない。一次 ID の追加はなく、M10 の同じ構成の法則の分割として扱う。
円筒の法則、同じ弱自然変換の局所化比較、BE 底の往復比較の三ファイルを
指定された共有鍵の下で対象ビルドし、全て通過した。

残る境界は、得た全関手比較の指定頂点での辺との照合、
同じ台・単位・随伴を保持した半自由 native fiber の比較と全族の native cocartesian 性。
M11 以降、RHom・完備反射・完備テンソルも引き続き未完。

**一覧：済み 9／全体 42（うち追加 0）**。

今回の公開 16 宣言の小さい公理監査も、指定の共有鍵の下で通過した。
`#print axioms` の実出力は 16 件で、依存公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。`sorryAx`・追加公理はない。
大きい監査や全体ビルドは実施していない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 9. 同じ自由局所化の係数移送の単位・合成則と B4（11-14）

M10 の指定局所化辺との照合に向け、既存の自由 hammock の係数写像について、
各自由次数の固定端点の写像との一致・空語の単位・全連結合成の保存を証明した。
対象ビルドは指定共有鍵の下で通過。新規 Lean 1 ファイル・78 行・3 宣言、
累計は 30 ファイル・2,819 行・160 宣言（private 3 を含む）。
一次 ID は増やさず、既存の係数移送の法則として扱う。
全 nerve の係数作用と源の自然性の二ファイルは未検証の下書きで、まだ実測に含めない。

着手中、main の `citation-attributes.md` §14（ab311d2d1）で B4 の手順が公開された。
⑤d も同じ手順の対象と明記されているため、M10 の Lean を区切って B4 を優先する。
取り込み前のソースと参照の採取・保留 0 のプレビューを先に行い、main の取り込み後に
対象ビルドと小さい監査を行う。未検証の下書きは保持する。

```lean
lemma freeHammockCoefficient_fixedColimitMap (X Y : C.category) (n : SimplexCategoryᵒᵖ) :
    (freeHammockMap F X Y).app n =
      Hammock.Relative.fixedColimitMap ((freeResolutionMap F).app n)
        (freeResolutionMap_object F n X) (freeResolutionMap_object F n Y)

lemma freeHammockCoefficient_unit (X : C.category) :
    freeHammockDiagonalUnit C X ≫ freeHammockDiagonalMap F X X =
      freeHammockDiagonalUnit D (F.functor.obj X)

lemma freeHammockCoefficient_comp (X Y Z : C.category) :
    freeHammockDiagonalComposition C X Y Z ≫ freeHammockDiagonalMap F X Z =
      (freeHammockDiagonalMap F X Y ⊗ₘ freeHammockDiagonalMap F Y Z) ≫
        freeHammockDiagonalComposition D (F.functor.obj X) (F.functor.obj Y) (F.functor.obj Z)
```

**一覧：済み 9／全体 42（うち追加 0）**。
