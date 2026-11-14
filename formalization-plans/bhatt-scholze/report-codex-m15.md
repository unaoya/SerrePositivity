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
    (moduleResolution A D).app (Opposite.op ⦋0⦌) (Simplex.vertex (A := A) M) =
      Simplex.vertex (A := A) (dgModuleOutputResolutionObject A (RightModule A D) D
        (DGFunctor.id (RightModule A D)) M).replacement

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

lemma strictRawModuleCartesianLift_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    (strictRawModuleTotalRelative A).weakEquivalences
      ((ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)).map
        (strictRawModuleCartesianLift A f M))
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
      ((ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)).map
        (strictRawModuleCartesianLift A f M))
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

## 10. B4：保留 2 件で停止（2026-11-14 昼）

`citation-attributes.md` §14・`bulk-w1-b3/B4-README.md` と調整役の指示に従い、
M15 の作業を区切って B4 を優先した。検証済みは `8593cc4b9` までコミット済み。
基準 `c5c4436c0` からこの枝で追加・変更したコミット済み Lean の Git 差分は
**30 ファイル**。未追跡の未検証下書き二つ（`FreeHammockCoefficientNerve.lean`、
`LocalizationSourceNaturality.lean`）は原文を別保存して作業木に保持した。

最初の採取は、Lake の依存の再ビルド要求で終了した。採取条件は外さず、
要求された五つと、その上の枝固有モジュールの正規 Lake 成果物を整え、
検証済み 30 モジュールの対象ビルドを通した。main の作業木には書き込んでいない。
その後 `bulk_namespace.py collect` を `--class impl --wait 3600`、
各組 `gtimeout --kill-after=3s 280` の下で 4 本・8 本・8 本に分けて実行し、
**20 ファイルの採取が成功**した。各索引内の原文・保存した原文・作業木のソースの
全バイト一致を再確認した。採取時の Lake options と脚本のハッシュも索引に残した。

`bulk_namespace.py rewrite` の最初の 4 本・次の 8 本は保留 0。
続く 8 本のプレビューでは、次の二つが保留になったため、**ここで B4 を止めた**。

| ファイル | 行 | 保留になった open |
| --- | --- | --- |
| `EInfinity/BarrattEccles/Modules/StrictUnderlyingComparison.lean` | 27 | `SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison` |
| `EInfinity/BarrattEccles/Modules/StrictUnderlyingRestriction.lean` | 23 | 同じ名前空間 |

両方の理由は `explicit opens policy needed for a renamed namespace`。
前者で採取された同名前空間の使用宣言は `complexClosedPresentation`、
`complexClosedPresentation_ring_evaluation`、`complexDerivedEvaluation`、
`semifreePointEquivalence`。後者は `semifreePointEquivalence`。
この open の方針を調整役が確認する必要がある。こちらで保留を消す置換はしていない。

main は **未取り込み**、プレビューのソースへの反映も **未実施**。
残り 10 ファイルの採取と、取り込み後の対象ビルド・小さい監査は未実施で、
B4 は完了していない。保存資料は
[`b4-m15-2026-11-14/summary.json`](b4-m15-2026-11-14/summary.json)、
[`review.json`](b4-m15-2026-11-14/review.json)、
[`before-index.json.gz`](b4-m15-2026-11-14/before-index.json.gz)、
[`checked-preview.diff.gz`](b4-m15-2026-11-14/checked-preview.diff.gz)。
索引は取り込み前の原文に限って有効であり、取り込み後のソースには流用しない。

M15 の一覧・型・ソースには B4 の変更をまだ加えていない。
累計は検証済み新規 Lean 30 ファイル・2,819 行・160 宣言（private 3 を含む）。

**一覧：済み 9／全体 42（うち追加 0）**。

## 11. B4 停止中の代替作業：A5 と M15 の実際の型の受け渡し（11-14、紙）

main `efa846fe8` の改名表の SHA は §10 のものと同じで、
`DiagramComparison` の明示的な open 方針はまだない。保留 2 件を維持し、
main の取り込み・プレビュー反映・M15 の Lean は再開していない。
`lane-goals-2026-11-14.md` の⑤dの代替作業に従って、A5 を読み取りだけで照合した。
ここでいう drafts は全て `formalization-plans/bhatt-scholze/drafts/` 以下。
読み取った次の七ファイルは、自分の枝と main の間で差分がないことも確認した。

- `Shared/Descendable.lean`
- `A5/StrongDescent.lean`、`A5/WeaklyInitialAndDescent.lean`
- `A4/Perfectoidization.lean`、`A2/DerivedPrismaticCohomology.lean`
- `DerivedGeneral/CompletionFunctor.lean`、`DerivedGeneral/Truncation.lean`

以下は §1 の既存出力の接続条件と利用側の差の記録であり、
新しい一次 ID・Lean 宣言・追加の仮定を導入したものではない。

### 11.1 BE 中核で進める範囲と、現在の実装の境界

本体の `BarrattEccles/Theory.lean:35` の `barrattEcclesCore.CAlg A` は
実際の `CAlg_R A`、その忘却は `cAlgForgetDerived A` に固定されている。
一方、`drafts/Shared/BarrattEcclesTheory.lean:28` の `barrattEcclesTheory` は
作業用の `sorry` を含み、本体の `barrattEcclesTheoryOfRemaining` は G12 などの
未供給欄を引数に取る。これを M15 の実装入力にすると、M15 の後に行う G12 を
先に要求する依存になる。D80 の指定どおり M15 の本体は実 `CAlg_R A` と中核で作り、
A5 の `E := barrattEcclesTheory` 特殊化は全界面の組み立て後の利用側の接続とする。
任意 E への輸送を作る理由にはしない。

現在の実出力の型は、厳密な BE 代数 `X Y : (operad A).Algebra` に対する
`strictModuleInfinity A X`、`strictModuleUnderlying A X`、`strictModuleUnit A X`、
`strictModuleExtend f`・`strictModuleRestrict f` とその随伴・同じ台の比較である。
M10 の実射影には

```lean
moduleUnitSection_projectionIso A :
  FunctorIso (moduleUnitSection A ≫ moduleTotalProjection A) (𝟙 (CAlg_R A))
```

を構成済み。しかしこの型は、任意の native な底 `R : (CAlg_R A) _⦋0⦌` の
指定 fiber の相対テンソル・内部 Hom や、その fiber の単位を供給する型ではない。
A5 の `deltaRootEdge` を厳密な一つの代数射の代表に取り替えて使う接続もまだない。
M10・C02 が指定した同じ U・単位・随伴と高次単体を保持する全族を作る必要が残る。

### 11.2 共通の厚さと Shared の厚さは定義上の等式ではない

本体の `InfinityCategories/HA/StableInfinityCategories/Thick.lean:27` は
零・同型・実 cofiber/fiber・ホモトピー圏の retract で閉じる `IsThick`。
`EInfinity/Modules/ThickTensorIdeal.lean:25` はこれを拡張し、
右からの `tensorWith M` の閉性を加える。
Shared の同名構造（`Shared/Descendable.lean:59`）は、全ての有限単体集合 K の
`JoinCocone` に対する有限余極限閉性、辺で表示した retract、shift、tensor を持つ。

M19 の接続では、有限余極限閉性と cofiber/fiber 閉性の相互変換、
`Nonempty (Retract (ho.mk x) (ho.mk y))` と二つの実辺・合成式の変換、
同型で移した頂点の所属を保持する法則が必要。
同じ名前であることや、生成閉包が双方とも述語の交わりであることだけでは、
M22 の単位底特殊化の述語の一致にはならない。この互換の証明は未実装である。

### 11.3 完備圏の単位：A 自身が完備でない離散底も残す

`Shared/Descendable.lean:302` の `isDescendable_complete` は、s と B を受け、
B の台の s 完備性だけを仮定する。底の環 A 自身の s 完備性は引数にない。
その結論の `IsDescendableComplete` は、完備テンソルイデアルが
**単位 A の完備化**を含むという定義（同ファイル:297）である。

これに対し §1.5 の M39 は一般の底 R・終域 B の台の完備性を仮定する。
従って R を離散底の単位 A に特殊化して M39 だけを当てる経路には、
利用側にない A の完備性が余分に必要になる。
§1.5 で約束した離散版全型の互換出力を保つには、M36・M37 の反射・テンソルの
法則から「生成元と単位を反射した thick イデアル」へ移す接続も必要。
Shared に A の完備性を追加して穴を埋めない。

接続条件の模式的な型を §1.5 の記法で固定する（下の名前はまだ Lean 宣言ではない）：

```lean
-- C_R, one_R, U_R, moduleCompletion, inclusion は M10・M36 の出力。
completeUnit R s : (completeModules R s) _⦋0⦌ :=
  (moduleCompletion R s).app (Opposite.op ⦋0⦌) one_R

FunctorIso
  (moduleCompletion R s ≫ completeModulesInclusion R s ≫ U_R)
  (U_R ≫ Derived.completion A s)

FunctorIso (completeTensorWith R s (completeUnit R s))
  (𝟙 (completeModules R s))
```

R の台が完備な場合に `completeUnit` の忘却と `one_R` を比較する。
その仮定がない場合の単位は反射した単位として保持する。
これは M36・M37 の同じ構成の単位・係数移送の法則であり、
通常版と完備版の descendability の同値を定義にする変更ではない。

### 11.4 A5 の Amitsur データは完備圏で組み立てる必要がある

`A4/Perfectoidization.lean:344–349` の `directPerfectionFunctor` は
`completePerfectionFunctor ≫ completeCAlgInclusion`。
`A2/DerivedPrismaticCohomology.lean:66–70` の完備 CAlg は、
忘却した台が p と prism の generator で完備である充満部分準圏。
`A5/WeaklyInitialAndDescent.lean:302–307` の結論は、この包含後の同じ
根被覆増大錐 c の `IsLimitCone c` を要求している。

一方 `Shared/Descendable.lean:179–189` の `AmitsurData.term n` は、
**通常の CAlg** における各段の `IsColimitCone` を要求する。
完備テンソルで作った各段を包含で通常の CAlg に送っただけでは、この引数を得ない。
包含の極限保存と余極限保存を混同しない。

接続経路は M42 の `CompleteAmitsurData` を完備圏で構成し、
その同じ増大・base・zero・leg・全 term を使って完備圏での極限性を得た後、
包含の極限保存で A5 が表示する c の極限性へ送るものとして記録する。
指定された root-cover の脚を別の Amitsur 図式に置き換えない。
この経路のために A5 の降下述語を完備版へ接続する判断は利用側に残り、
完備版の降下を通常版の `IsDescendableOver` の証明済み結果とは数えない。
M41 も同様に、完備な射の圏で与えられた余錐の `IsColimitCone` をその圏で使う。
通常の射の圏との比較は別途供給する。

### 11.5 RHom の係数と零次評価の接続

`A5/StrongDescent.lean:97` の `fiberSquareRHom f L` は
`U_R RHom_R(F ⊗_R F, moduleFromBase R L)` の型を要求する。
同ファイル:101 の `rootDual` の L は `moduleHeartVertex A (ModuleCat.of A A)`。
これを `U_R RHom_R(F ⊗_R F, one_R)` と比較するためには、M34 の係数作用の単位則

```lean
-- §1.5 の記法。M34 の同じ係数作用の未実装の単位法則。
VertexIso
  ((moduleFromBase R).app (Opposite.op ⦋0⦌) (unitComplex A))
  one_R
```

が要る。構成済みの `strictModuleUnitUnderlyingIso` は厳密底 X 上の
正則加群の**台**を `complexDerivedEvaluation A X.carrier` と比較する型であり、
この一般 R 加群の係数作用の単位則の代わりにはならない。

`DerivedGeneral/Truncation.lean:53` の `IsConnectiveAt A (-1) x` は
`∀ i, -1 < i → Subsingleton (derivedInfinityHomology A i x)`。
M33 の加法的な零次 Hom 比較で i=0 の零性へ移し、
M35 は指定された `fiberPowerMap f 2` の零性と接続する。
Shared の `hasDescentIndexLEOver_two_of_rhom : True`（同ファイル:202）は
この入力・出力を全く持たないため、呼び出し名があるだけでは API ではない。

任意の離散 L を使う `squareZero_rhom_coconnective` と
`rhom_baseChange_koszul_connection` の係数はそのまま保持する。
双対可能な Koszul K での Hom–tensor 比較と、任意 L に対する比較を分ける。
Koszul の計算、最高次の全射、Nakayama、(p,d) と
(p,φ⁻¹(d)) の完備性を結ぶ A5 の個々の証明は A5 に残す。

### 11.6 変更・検証の範囲

今回変更したのはこの紙の報告だけ。drafts・Lean ソース・B4 の保存索引は変更していない。
Lean の新しい対象ビルド・監査は実施していない。B4 の保留は引き続き 2 件。
新規 Lean の実測は 30 ファイル・2,819 行・160 宣言のまま。
M10 以降と RHom・完備反射・完備テンソルを完了に数えていない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 12. B4 の同一保留の第3回確認とゴールの blocked 判定（11-14）

§10 の初回停止、§11 の代替作業時の再確認に続いて、
main `efa846fe8` と現在の改名表を再確認した。
`namespace-rewrite-map.json` の SHA は引き続き
`67ba053988c420d4a43dc026da90b93dca531e393c94bcfce7ca420673bd9d87`。
`DiagramComparison` の明示的な `opens` 方針も、保留となった二モジュールの
`module_opens` 方針も追加されていない。

取り込み前の原文が保存索引と一致することを確認し、同じ八ファイルの manifest と
同じ採取範囲の索引を使って、現行の `bulk_namespace.py rewrite` を再実行した。
終了コード 1 と `review.json` に、§10 と同じ二か所・同じ理由の保留を再現した。
これは生存中のジョブの待機ではなく、未解決の open 方針による停止である。
新しい採取や Lean ビルドは投入していない。

調整役の B4 指示 3 は「保留が出たら止まって報告」。
従ってこちらで open 方針を選んで保留を消したり、main の取り込みを先に行ったりはしない。
指定された代替の A5・Shared の型の照合は §11 に記録済み。
M15・G12 の目的は未達のまま保持し、同じ阻害が三回の連続したゴールターンで
確認されたため、今回ゴールを `blocked` として調整役の方針の更新を待つ。

再開に必要なのは、当該二か所の open 方針が正式な改名表に供給されるか、
調整役からその扱いの明示的な指示を受けること。
再開後は、未採取の残り 10 ファイルを取り込み前に採取し、全 30 本の原文一致と
保留 0 のプレビューを確認してから、main の取り込み・反映・対象ビルド・
小さい公理監査を行う。B4 完了後に M15 の続きへ戻る。

検証済み新規 Lean は 30 ファイル・2,819 行・160 宣言、未検証の下書きは二つのまま。
M10・RHom・完備反射・完備テンソルおよび G12 は完成として扱っていない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 13. B4 再開：恒等 open 方針による保留の解消と main 取り込み（11-14 午後）

調整役の明示指示と main `2be485f04` の `citation-attributes.md` §14 追記により、
§10〜§12 の二つの `DiagramComparison` の open は原文のまま保持する。
使用する四宣言が main に同じ完全名で残ることは調整役が確認済み。
この明示方針により §12 の阻害を解消し、B4 を再開した。
正式な改名表自体は変更せず、ローカルのプレビュー用の表に
`opens[DiagramComparison] = DiagramComparison` の恒等方針を追加した。
原表と適用表の SHA・指示の出所は `approved-opens.json` に保存した。

main 取り込み前に残り 10 ファイルを、指定共有鍵の下で 280 秒上限の組として採取。
既存の 20 本を含め、**全 30 ファイル・19,245 件の参照**がそろった。
全ての採取原文・保存した原文・取り込み前のソースの全バイト一致を確認してから
索引を集約し、承認された方針で全体のプレビューを作った。**保留は 0**。
変更は 15 ファイル、通常 import の移動と参照先の完全名への追従である。
自分のモジュールのファイルパスの移動はない。

その後 `git merge main` を実行し、main `2be485f04` を取り込んだ
（マージコミット `d9a5e6b98`）。取り込み前に作成したプレビューを
`bulk_apply_preview.py` の原文ハッシュ・出力ハッシュ・出力先・プレビュー一致の
検査付きで反映した。削除 0、書き込み先は自分の 15 ファイルのみ。
取り込み後のソースに旧索引で名前解決・再書き換えを行っていない。
反映後の全 30 ファイルがプレビューと全バイト一致することも確認した。

### 13.1 対象ビルドと保存資料

`with_build_lock.sh --class impl --wait 3600` の下で、
自分の 30 モジュールを明示した正規 Lake 対象ビルドを実行し、全て通過した。
二つの `open ...DiagramComparison` を原文のまま残した
`StrictUnderlyingComparison`・`StrictUnderlyingRestriction` も通過した。
公開宣言の名前の一覧は取り込み前と一致する **157 宣言**。
この 157 宣言だけの小さい公理監査を別の共有鍵の組で投入した。
監査の最終結果は次節で記録する。

保存資料は `b4-m15-2026-11-14/` 以下：

- `before-index-complete.json.gz`：取り込み前の全 30 本の採取原文・参照・設定。
- `approved-opens.json`：調整役が承認した恒等 open 方針と改名表の SHA。
- `review-complete.json`：全体プレビューの保留 0。
- `checked-preview-complete.diff.gz`：取り込み前に確認した全差分。
- `approved-apply-bundle.json.gz`：適用した原文・出力ハッシュ付きの束。

§10 の `summary.json`・`review.json` は停止時の履歴として保持している。
現在の保留は解消しており、最新状態はこの §13 と完了時の記録で示す。
未検証の下書き二つは B4 の採取・反映対象の外に保持した。

今回の追従で数学的な宣言は追加していない。
新規 Lean の実測は 30 ファイル・2,819 行・160 宣言（private 3 を含む）のまま。
大きい監査・全体ビルドは実施していない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 13.2 小さい公理監査と B4 の完了

共有鍵の別の組で、公開 **157 宣言**の `#print axioms` を実行し、終了コード 0。
実出力の宣言名の集合・件数が採取した公開宣言の一覧と完全一致した。
依存公理は `propext`・`Classical.choice`・`Quot.sound` のみで、
`sorryAx`・追加公理はない。
この結果と対象ビルド通過により **B4 の追従は完了**。
承認された二つの open は原文を保持したまま検証できた。

最新の完了資料は
[`completion.json`](b4-m15-2026-11-14/completion.json)、
[`audit-declarations.json`](b4-m15-2026-11-14/audit-declarations.json)、
[`audit-public157.txt.gz`](b4-m15-2026-11-14/audit-public157.txt.gz)。
§10〜§12 は以前の停止と確認の履歴であり、調整役の今回の方針と §13 の検証で
その阻害は解消した。M15・G12 自体の完成とは区別し、ここから M15 の続きへ戻る。

**一覧：済み 9／全体 42（うち追加 0）**。

## 14. M15 再開：同じ自由局所化の全係数自然性（11-14）

B4 は §13・`735c38752` で完了したので、保持していた下書き二つの検証へ戻る。
M10 の同じ相対局所化の係数移送の法則として、既存の自由 hammock の全 Hom 作用を
豊穣関手・同じ Kan 化・全 coherent nerve へ束ねる。
元の左右比較の可換正方形を全 nerve の等式にし、同じ augmentation の逆の
既存の選択を通して、局所化の源の写像との全関手間の自然性を回収する。
全単体を保持し、頂点ごとの同型の族だけにはしない。

以下が今回検証する実際の型。新しい一次 ID は追加せず、既存の係数移送・自然性・
貼り合わせの証明の分割として扱う。共通文脈は `C D : RelativeCategory.{u}`、`F : C ⟶ D`。

`SerrePositivity/EInfinity/Modules/FreeHammockCoefficientNerve.lean`：

```lean
def freeHammockCoefficientEnriched :
    EnrichedFunctor SSet.{u} (FreeHammockObjects C) (FreeHammockObjects D)

def kanFreeHammockCoefficientFunctor :
    EnrichedFunctor SSet.{u} (KanFreeHammockCategory C) (KanFreeHammockCategory D)

def kanFreeHammockCoefficientNerve : kanFreeHammockNerve C ⟶ kanFreeHammockNerve D

lemma kanFreeHammockCoefficient_augmentation :
    (kanFreeHammockCoefficientFunctor F).comp SSet (kanFreeHammockAugmentationFunctor D) =
      (kanFreeHammockAugmentationFunctor C).comp SSet (relativeKanHammockFunctor F)

lemma kanFreeHammockCoefficient_comparison :
    (kanFreeHammockCoefficientFunctor F).comp SSet (kanFreeHammockComparisonFunctor D) =
      (kanFreeHammockComparisonFunctor C).comp SSet (kanLocalizationEnrichedMap F)

lemma kanFreeHammockCoefficientNerve_augmentation :
    kanFreeHammockCoefficientNerve F ≫ kanFreeHammockAugmentationNerve D =
      kanFreeHammockAugmentationNerve C ≫ relativeKanHammockNerve F

lemma kanFreeHammockCoefficientNerve_comparison :
    kanFreeHammockCoefficientNerve F ≫ kanFreeHammockComparisonNerve D =
      kanFreeHammockComparisonNerve C ≫ localizationNerveMap F
```

`SerrePositivity/EInfinity/Modules/LocalizationSourceNaturality.lean`：

```lean
def kanHammockLocalizationCoefficientIso :
    FunctorIso (relativeKanHammockNerve F ≫ (kanHammockLocalizationEquivalence D).hom)
      ((kanHammockLocalizationEquivalence C).hom ≫ localizationNerveMap F)

def localizationNerveSourceNaturalityIso :
    FunctorIso (localizationNerveSourceMap C ≫ localizationNerveMap F)
      (nerveMap F.functor ≫ localizationNerveSourceMap D)
```

文献属性は、coherent nerve の作用を HTT Definition 1.1.5.5 の `component`、
同じ全関手間の比較を HTT §1.2.7 の `component` として、各宣言に対応範囲を記す。
Definition 1.1.5.5 の原文は [HTT 原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf)
で確認した。一般の局所化の普遍性をこれらの宣言で証明したという属性にはしない。

この自然性ができても、指定弱自然変換の成分の辺との全照合、
半自由 native fiber の比較と全族の native cocartesian 性は引き続き必要。
M10 の完了には数えていない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 14.1 検証済みの結果と実測

二つのモジュールの正規 Lake 対象ビルドが、指定の共有鍵の下で通過した。
同じ自由局所化の Kan 豊穣係数関手、左右の全 nerve 正方形、
`kanHammockLocalizationCoefficientIso` と `localizationNerveSourceNaturalityIso` を
全て実際の型で構成できた。型指定・宇宙指定を明示し、元の全 Hom 写像は保持した。

公開 9 宣言の `#print axioms` と、その同じ 9 宣言の文献属性の環境検査を、
別の共有鍵の組で行い、終了コード 0。実出力の宣言名集合・件数が一致し、
依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
`sorryAx`・追加公理はない。全 9 件に HTT の `component` 属性が一件ずつ登録され、
番号は 7 件が `1.1.5.5`、2 件が `1.2.7` と確認した。

今回の追加は新規 Lean 2 ファイル・181 行・9 宣言（公開）。
`FreeHammockCoefficientNerve.lean` が 110 行・7 宣言、
`LocalizationSourceNaturality.lean` が 71 行・2 宣言。
200 行を超える補題はない。
累計は新規 Lean **32 ファイル・3,000 行・169 宣言（private 3 を含む）**。
既存構成の係数移送・自然性・貼り合わせの法則の分割なので一次 ID の追加はない。

B4 追従は §13 で完了済み。M15 は再開しているが、M10 の native fiber・
cocartesian 性、相対テンソル、RHom・完備反射・完備テンソルと G12 は引き続き未完。

**一覧：済み 9／全体 42（うち追加 0）**。

## 15. M10 の指定生成射と係数作用の照合（11-14、着手）

§14 の全係数自然性を元の指定弱辺に接続するため、既存の同じ係数作用について、
自由解像の零次の一文字の射、hammock の指定零単体・点、Kan 化した同じ射、
coherent nerve の実一単体の保存を照合する。
新しい模型や対象ごとの別の辺を選ばず、元の射 f と同じ二端点を保持する。
M10 の既存構成の係数移送・自然性の法則の分割で、一次 ID の追加はない。

`EInfinity/Modules/LocalizationArrowCoefficients.lean` の今回の型を記録する。
共通文脈は `C D : RelativeCategory.{u}`、`F : C ⟶ D`、`X Y : C.category`。

```lean
lemma freeResolutionArrowZero_coefficient (f : X ⟶ Y) :
    eqToHom (freeResolutionMap_object F (op ⦋0⦌) X).symm ≫
      ((freeResolutionMap F).app (op ⦋0⦌)).functor.map (freeResolutionArrowZero C f) ≫
        eqToHom (freeResolutionMap_object F (op ⦋0⦌) Y) =
      freeResolutionArrowZero D (F.functor.map f)

lemma freeHammockArrowZero_coefficient (f : X ⟶ Y) :
    (freeHammockDiagonalMap F X Y).app (op ⦋0⦌) (freeHammockArrowZero C f) =
      freeHammockArrowZero D (F.functor.map f)

lemma freeHammockArrowPoint_coefficient (f : X ⟶ Y) :
    freeHammockArrowPoint C f ≫ freeHammockDiagonalMap F X Y =
      freeHammockArrowPoint D (F.functor.map f)

lemma localizationArrowPoint_coefficient (f : X ⟶ Y) :
    localizationArrowPoint C f ≫ localizationHomMap F X Y =
      localizationArrowPoint D (F.functor.map f)

lemma kanLocalizationStrictHom_coefficient (f : X ⟶ Y) :
    (kanLocalizationFunctor F).map (kanLocalizationStrictHom C f) =
      kanLocalizationStrictHom D (F.functor.map f)

lemma kanFreeHammockStrictHom_coefficient (f : X ⟶ Y) :
    (kanFreeHammockCoefficientFunctor F).forget.map (kanFreeHammockStrictHom C f) =
      kanFreeHammockStrictHom D (F.functor.map f)

lemma localizationStrictEdge_coefficient (f : X ⟶ Y) :
    ((coherentNerveEdge (kanLocalizationStrictHom C f)).map (localizationNerveMap F)).edge =
      (coherentNerveEdge (kanLocalizationStrictHom D (F.functor.map f))).edge

lemma freeHammockStrictEdge_coefficient (f : X ⟶ Y) :
    ((coherentNerveEdge (kanFreeHammockStrictHom C f)).map (kanFreeHammockCoefficientNerve F)).edge =
      (coherentNerveEdge (kanFreeHammockStrictHom D (F.functor.map f))).edge
```

この辺の保存の後には、既存の `SourceHom.localizationStrictSourceIso_naturality` を
使って、元の弱射の反転と同じ native 辺を接続する。
これらはまだ半自由 native fiber の同定や全族の cocartesian 性を供給していない。
検証済みの一覧の数は据え置く。

**一覧：済み 9／全体 42（うち追加 0）**。

### 15.1 指定弱射の実辺と BE の同じ標準 lift（検証中）

`LocalizationStrictWeak.lean` は、既存の源の反転性を
`localizationStrictSourceIso_naturality` の四角形で共役し、元の指定射から作った
同じ辺そのものの可逆性を示す。共通文脈は `C : RelativeCategory.{u}`。

```lean
lemma localizationStrictEdge_invertible_of_weak {X Y : C.category}
    (f : X ⟶ Y) (hf : C.weakEquivalences f) :
    IsInvertibleEdge (coherentNerveEdge (kanLocalizationStrictHom C f)).toTruncated
```

`BarrattEccles/Modules/NativeCartesianWeak.lean` では、同じ標準 lift の局所化辺と
底への射影を指定する。共通文脈は `A : Type u`、`[CommRing A]`。

```lean
def moduleTotalVertex (M : strictRawModuleTotal A) : (moduleTotalInfinity A) _⦋0⦌

def moduleCartesianLiftEdge {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    SSet.Edge (moduleTotalVertex A
      ((strictRawModuleFiberInclusion A X).obj ((strictRawModuleRestrict f).obj M)))
      (moduleTotalVertex A ((strictRawModuleFiberInclusion A Y).obj M))

lemma moduleCartesianLiftEdge_invertible {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsInvertibleEdge (moduleCartesianLiftEdge A f M).toTruncated

lemma moduleCartesianLiftEdge_projection {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    ((moduleCartesianLiftEdge A f M).map (moduleTotalProjection A)).edge =
      (coherentNerveEdge (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
        ((algebraToCofibrantDKRelative A).functor.map
          ((ULiftHom.up.{u,u+1,u+1} (C := (operad A).Algebra)).map f)))).edge

```

可逆性の文献番号は、[HTT 原典](https://www.math.ias.edu/~lurie/papers/HTT.pdf)
§1.2.4 の「同じ辺の像がホモトピー圏で同型」という定義に対応させる。
Proposition 1.2.4.3 の外側 horn の持ち上げによる判定そのものを証明したとはしない。
BE の底が弱同値の場合の標準 lift に適用し、別の可逆辺へ取り替えない。
これらも M10 の指定射・係数作用・反転の法則の分割で、追加の一次 ID はない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 15.2 検証済みの結果と実測

三つの新規モジュールの正規 Lake 対象ビルドが、指定の共有鍵の下で通過した。
自由解像の零次から実一単体までの指定生成射の保存、同じ弱射の指定辺の可逆性、
BE の元の標準 lift の実局所化辺と射影先の指定辺との等式が得られた。
切り詰め写像の元の準圏を明示し、源の選択逆を含む型照合に限って
`LocalizationStrictWeak` の一補題の `maxHeartbeats` を局所的に 800,000 とした。

今回の公開 13 宣言の `#print axioms` と文献属性の環境検査も、別の共有鍵で
終了コード 0。実出力は同じ 13 宣言と 13 属性に一致する。
依存公理は `propext`・`Classical.choice`・`Quot.sound` のみで、
`sorryAx`・追加公理はない。文献属性は全て HTT の `component` で一件ずつ、
11 件が `1.1.5.5`、弱辺反転の 2 件が `1.2.4` と各宣言について確認した。

追加は新規 Lean **3 ファイル・286 行・13 宣言（公開）**。
`LocalizationArrowCoefficients.lean` が 139 行・8 宣言、
`LocalizationStrictWeak.lean` が 68 行・1 宣言、
`NativeCartesianWeak.lean` が 79 行・4 宣言。
200 行を超える補題はない。
累計は新規 Lean **35 ファイル・3,286 行・182 宣言（private 3 を含む）**。
既存構成の係数移送・反転・指定射の照合の法則の分割で、一次 ID の追加はない。

B4 は §13 で完了済み。M10 の全関手比較と指定弱自然変換の成分の辺の照合、
半自由 native fiber の同定と全族の native cocartesian 性は引き続き必要。
今回の可逆性だけで M10 を完了とは数えない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 16. M10 の全比較の成分と指定された円筒辺（11-14、着手）

前の goal ターンは、§15 の三つの対象ビルドと 13 宣言の小さい監査を通し、
`e5b5413b9` で検証済みの実辺の保存・弱 lift の反転をコミットした進捗。
今回は、円筒の同値の選択逆から作った全関手間の比較の成分が、
元の弱自然変換の指定辺と一致することを照合する。
対象ごとの別の可逆辺を選ぶのではなく、元の比較・元の射を保持する。
M10 の既存構成の前合成・成分評価・恒等・自然性の法則の分割で、一次 ID は足さない。

最初に使う補助法則の型は次のとおり。
`LocalizationComparisonEvaluation.lean` の文脈は `A B Y : SSet.{u}`、
`[Quasicategory Y]`。既存の後合成・合成・反転の評価則は import して使う。

```lean
lemma functorHomotopyEvaluation_precomp_map_app
    (q : A ⟶ B) {v w : ((ihom B).obj Y) _⦋0⦌}
    (a : (SSet.HomotopyCategory.mk v : hoFunctor.obj ((ihom B).obj Y)) ⟶
      SSet.HomotopyCategory.mk w) (x : A _⦋0⦌) :
    ((functorHomotopyEvaluation A Y).map
      ((hoFunctor.map ((pre q).app Y)).toFunctor.map a)).app (SSet.HomotopyCategory.mk x) =
      ((functorHomotopyEvaluation B Y).map a).app
        (SSet.HomotopyCategory.mk (q.app (Opposite.op ⦋0⦌) x))

lemma functorIso_precomp_hom_app {f g : B ⟶ Y}
    (e : FunctorIso f g) (q : A ⟶ B) (x : A _⦋0⦌) :
    (e.precomp q).toNatIso.hom.app (SSet.HomotopyCategory.mk x) =
      e.toNatIso.hom.app (SSet.HomotopyCategory.mk (q.app (Opposite.op ⦋0⦌) x))
```

`LocalizationStrictIdentity.lean` の文脈は `C : RelativeCategory.{u}`。
指定生成辺そのものが退化辺と等しいとは仮定しない。

```lean
lemma localizationStrictHom_id (X : C.category) :
    SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom C (𝟙 X))) =
      𝟙 _
```

**一覧：済み 9／全体 42（うち追加 0）**。

### 16.1 同じ選択逆の比較と指定交差射の型

前合成・等式比較の評価は次も使う。共通文脈は `A Y : SSet.{u}`。

```lean
lemma functorIso_eqToIso_hom_app {f g : A ⟶ Y} (h : f = g) (x : A _⦋0⦌) :
    (show FunctorIso f g from
      eqToIso (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) h)).toNatIso.hom.app
      (SSet.HomotopyCategory.mk x) =
    eqToHom (congrArg (fun k : A ⟶ Y => SSet.HomotopyCategory.mk
      (k.app (Opposite.op ⦋0⦌) x)) h)
```

自分の既存 `RelativeNaturalComparison` の局所的な端点比較を、次の名前付きの
法則に分けた。同じ射影の同じ選択逆と可逆二胞体を保持し、全関手の等式による
輸送だけを明示する。既存の両端点比較・弱自然変換比較の型は変更しない。

```lean
def relativeCylinderInverseEndpointIso (C : RelativeCategory.{u}) (i : Fin 2) :
    FunctorIso (relativeCylinderProjection_isQCatEquivalence C).choose.inv
      (localizationNerveMap (relativeCylinderEndpoint C i))
```

以下は `RelativeCylinderPrescribedEdge` と `RelativeCylinderComponent` の今回の型。
同じ円筒を使い、最後の成分の主張へつなぐ法則の分割。

`RelativeCylinderPrescribedEdge.lean`：

```lean
lemma localizationStrictHom_coefficient_class {C D : RelativeCategory.{u}} (F : C ⟶ D)
    {X Y : C.category} (f : X ⟶ Y) :
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex F X)).symm ≫
      (hoFunctor.map (localizationNerveMap F)).toFunctor.map
        (SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom C f))) ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex F Y)) =
        SSet.HomotopyCategory.homMk
          (coherentNerveEdge (kanLocalizationStrictHom D (F.functor.map f)))

lemma relativeCylinderEndpoint_projection_vertex (i : Fin 2) (x : (localizationNerve C) _⦋0⦌) :
    (localizationNerveMap (relativeCylinderProjection C)).app (Opposite.op ⦋0⦌)
      ((localizationNerveMap (relativeCylinderEndpoint C i)).app (Opposite.op ⦋0⦌) x) = x

def relativeCylinderCrossingClass (X : C.category) :
    SSet.HomotopyCategory.mk
      ((localizationNerveMap (relativeCylinderEndpoint C 0)).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv C X)) ⟶
    SSet.HomotopyCategory.mk
      ((localizationNerveMap (relativeCylinderEndpoint C 1)).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv C X))

lemma relativeCylinderCrossingClass_projection (X : C.category) :
    eqToHom (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C 0 (localizationNerveVertexEquiv C X))).symm ≫
    (hoFunctor.map (localizationNerveMap (relativeCylinderProjection C))).toFunctor.map
      (relativeCylinderCrossingClass C X) ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C 1 (localizationNerveVertexEquiv C X))) = 𝟙 _

```

`RelativeCylinderComponent.lean`：

```lean
lemma relativeCylinderInverseEndpointIso_component (i : Fin 2)
    (x : (localizationNerve C) _⦋0⦌) :
    ((relativeCylinderInverseEndpointIso C i).app x).hom =
      eqToHom (congrArg (fun v => SSet.HomotopyCategory.mk
        ((relativeCylinderProjection_isQCatEquivalence C).choose.inv.app (Opposite.op ⦋0⦌) v))
        (relativeCylinderEndpoint_projection_vertex C i x)).symm ≫
      (((relativeCylinderProjection_isQCatEquivalence C).choose.homInvIso).app
        ((localizationNerveMap (relativeCylinderEndpoint C i)).app (Opposite.op ⦋0⦌) x)).hom

lemma relativeCylinderEndpointIso_component_of_projection
    (x : (localizationNerve C) _⦋0⦌)
    (a : SSet.HomotopyCategory.mk
      ((localizationNerveMap (relativeCylinderEndpoint C 0)).app (Opposite.op ⦋0⦌) x) ⟶
      SSet.HomotopyCategory.mk
      ((localizationNerveMap (relativeCylinderEndpoint C 1)).app (Opposite.op ⦋0⦌) x))
    (ha : eqToHom (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C 0 x)).symm ≫
      (hoFunctor.map (localizationNerveMap (relativeCylinderProjection C))).toFunctor.map a ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk
        (relativeCylinderEndpoint_projection_vertex C 1 x)) = 𝟙 _) :
    ((relativeCylinderEndpointIso C).app x).hom = a

lemma relativeCylinderEndpointIso_component (X : C.category) :
    ((relativeCylinderEndpointIso C).app (localizationNerveVertexEquiv C X)).hom =
      relativeCylinderCrossingClass C X

```

ここで `relativeCylinderEndpointIso_component` は、全関手間の比較そのものの
元の頂点での成分を、同じ指定交差射のホモトピー圏の類に等置する主張。
M10 の出力をホモトピー圏へ置き換えるものではなく、既存の native 比較の成分の法則。
全族の fiber の同定と cocartesian 性は別に必要。

**一覧：済み 9／全体 42（うち追加 0）**。

### 16.2 元の弱自然変換の指定成分への接続（検証中）

`localizationNerveMapIsoOfWeakNatTrans` でも、同じ円筒比較・同じ後合成を保持し、
全関手の零・一端点の等式による輸送を明示した。公開の型は変更していない。
指定単位・余単位を持つ弱自然変換に適用できるよう、次の成分の法則を作る。
文脈は `C D : RelativeCategory.{u}`、`F G : C ⟶ D`。

```lean
lemma relativeNaturalCylinder_crossing (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (X : C.category) :
    (relativeNaturalCylinder η hη).functor.map ((relativeCylinderContraction C).app (1, X)) =
      η.app X

lemma localizationNerveMapIsoOfWeakNatTrans_component (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (X : C.category) :
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex F X)).symm ≫
      ((localizationNerveMapIsoOfWeakNatTrans η hη).app (localizationNerveVertexEquiv C X)).hom ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex G X)) =
      SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom D (η.app X)))

```

最後の等式は、頂点比較の等式だけで両端を移した同じ全比較の成分を、元の
`η.app X` の指定生成辺の類に等置する。対象ごとの別の同型の存在に弱めない。
BE の往復比較がこの構成を使うため、影響する
`BarrattEccles/Modules/AlgebraRoundTripComparison` も対象ビルドに含める。

**一覧：済み 9／全体 42（うち追加 0）**。

## 17. M10 の同じ全射影の inner fibration 置換と弱 lift（11-14、下書き）

§16 の最後の検証の共有鍵待ちの間に、M10 の実射影の構成も進める。
元の `moduleTotalProjection` は任意の内ホーンの相対充填性をまだ持たないため、
既存の内ホーンの小対象論法を同じ射影に適用し、同じ CAlg 上で置換する。
元の全圏からの包含は inner anodyne で準圏同値、射影の合成は全単体で等しい。
新しい `[ModelCategory SSet]` や外部の分解データは入力に加えない。
これは M10 の既存の全族の射影構成の証明の分割で、一次 ID の追加はない。

指定弱 lift は元の実辺をこの包含で写したものとし、構成した inner fibration と
同じ辺の可逆性から、native な Cartesian・cocartesian 条件を適用する。
弱底変更の場合に限る。一般の底の辺の lift の存在・相対性や半自由 fiber の同定を
この置換で証明済みとはしない。
文献は HTT Theorem 2.0.0.6、Proposition 2.4.1.5、
Kerodon Theorem 5.2.4.1（Tag 024N）・Proposition 5.1.1.9（Tag 01TB）。

以下の型は文脈 `A : Type u`、`[CommRing A]`。分解データはファイル内で一度選ぶ。

`TotalInnerReplacement.lean`：

```lean
def moduleTotalInnerFactorization :
    MapFactorizationData innerHornInclusions.rlp.llp innerHornInclusions.rlp
      (moduleTotalProjection A)

def moduleTotalInnerInfinity : SSet.{u+1}

def moduleTotalInnerInclusion : moduleTotalInfinity A ⟶ moduleTotalInnerInfinity A

def moduleTotalInnerProjection : moduleTotalInnerInfinity A ⟶ CAlg_R A

instance moduleTotalInnerProjection_innerFibration : InnerFibration (moduleTotalInnerProjection A)

instance moduleTotalInnerInfinity_quasicategory : Quasicategory (moduleTotalInnerInfinity A)

lemma moduleTotalInnerInclusion_innerAnodyne : innerAnodyneExtensions (moduleTotalInnerInclusion A)

lemma moduleTotalInnerInclusion_projection :
    moduleTotalInnerInclusion A ≫ moduleTotalInnerProjection A = moduleTotalProjection A

lemma moduleTotalInnerInclusion_isQCatEquivalence : IsQCatEquivalence (moduleTotalInnerInclusion A)

```

`NativeInnerWeakLift.lean`：

```lean
def moduleInnerCartesianLiftEdge {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    SSet.Edge ((moduleTotalInnerInclusion A).app (Opposite.op ⦋0⦌)
      (moduleTotalVertex A ((strictRawModuleFiberInclusion A X).obj
        ((strictRawModuleRestrict f).obj M))))
      ((moduleTotalInnerInclusion A).app (Opposite.op ⦋0⦌)
        (moduleTotalVertex A ((strictRawModuleFiberInclusion A Y).obj M)))

lemma moduleInnerCartesianLiftEdge_invertible {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsomorphismsAndIsofibrations.IsInvertibleEdge (moduleInnerCartesianLiftEdge A f M).toTruncated

lemma moduleInnerCartesianLiftEdge_projection {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    ((moduleInnerCartesianLiftEdge A f M).map (moduleTotalInnerProjection A)).edge =
      (coherentNerveEdge (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
        ((algebraToCofibrantDKRelative A).functor.map
          ((ULiftHom.up.{u,u+1,u+1} (C := (operad A).Algebra)).map f)))).edge

lemma moduleInnerCartesianLiftEdge_cartesian {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsCartesianEdge (moduleTotalInnerProjection A) (moduleInnerCartesianLiftEdge A f M).edge

lemma moduleInnerCartesianLiftEdge_cocartesian {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsCocartesianEdge (moduleTotalInnerProjection A) (moduleInnerCartesianLiftEdge A f M).edge

```

これら二ファイルはまだ対象ビルド・小さい監査の前の下書き。
検証済み実測には加えず、M10 の完了にも数えていない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 17.1 検証済みの結果・実測と残る kernel 照合

§16 の前合成の評価・指定恒等辺・交差辺の係数作用と射影、
`relativeCylinderEndpointIso_component` までの全円筒比較の成分の一致、
§17 の同じ射影の inner fibration 置換と元の弱 lift の native な
Cartesian・cocartesian 性は、正規 Lake の対象ビルドが通過した。
影響する自分の `AlgebraRoundTripComparison` の対象も通過している。
全て指定の共有鍵 `--class impl --wait 3600` の下、各実行の上限を 280 秒とした。

上記の新規公開 26 宣言、同じ全比較の既存 2 宣言、影響する BE 往復比較の
既存 4 宣言の計 32 宣言について、小さい `#print axioms` 監査は終了コード 0。
32 件の出力と対象名を機械照合し、依存公理は `propext`・`Classical.choice`・
`Quot.sound` のみと確認した。追加公理・`sorryAx` はない。
文献属性も同じ新規 26・既存比較 2 の計 28 宣言について一件ずつ、HTT の
`component` と各宣言の指定番号に一致することを環境から検査し、終了コード 0。
大きい監査やルートビルドは行っていない。

検証済みの新規 Lean は **6 ファイル・539 行・25 宣言**。
内訳は `LocalizationComparisonEvaluation` 81 行・3 宣言、
`LocalizationStrictIdentity` 42 行・1 宣言、
`RelativeCylinderPrescribedEdge` 116 行・4 宣言、
`RelativeCylinderComponent` 118 行・3 宣言、
`TotalInnerReplacement` 91 行・9 宣言、
`NativeInnerWeakLift` 91 行・5 宣言。
自分の既存 `RelativeNaturalComparison` の証明の分割は差引 23 行・1 宣言追加。
200 行を超える補題はない。
検証済み累計は新規 Lean **41 ファイル・3,848 行・208 宣言（private 3 を含む）**。
一次 ID は追加していない。

§16.2 の `LocalizationWeakNatComponent` は未コミットの下書きとして残す。
最後の全弱自然変換の成分式は、型だけを仮定して返す独立した kernel 照合を行い、
終了コード 0 で型自体は確認した。一つの宣言にした証明は kernel の計算上限
（200,000・800,000）に達したため、個別の法則の宣言に分けて照合を続ける。
証明の範囲や型を弱めること、追加公理で埋めることはしていない。
この下書きは上記の検証済み実測に含めないが、17,000 行の外枠には含めて管理する。

M10 は、最後の全弱自然変換の指定成分への接続、半自由 native fiber の同定、
一般の底の辺の lift・transport と全族の cocartesian 性が引き続き必要。
今回の inner fibration と弱 lift だけで M10 の完了とは数えない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 17.2 最後の成分の kernel 照合の分割（着手）

型だけの独立照合が通ったため、元の成分の型は保持して証明を分割する。
全比較の後合成の評価と同じ射の Arrow の一致を別の宣言にし、最後に同じ
`localizationNerveMap_vertex F/G` の等式による端点輸送へ戻す。
Arrow の等式には同じ射と両端の等式が含まれ、最後の主張は §16.2 の型のまま。
新たな数学の主張への範囲拡張ではなく、M10 の同じ成分の法則の証明の分割。
追加する分割の型は以下。共通文脈は `C D : RelativeCategory.{u}`、`F G : C ⟶ D`。

```lean
lemma localizationWeakNat_component_factorization (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (x : (localizationNerve C) _⦋0⦌) :
    Arrow.mk (((localizationNerveMapIsoOfWeakNatTrans η hη).app x).hom) =
      Arrow.mk ((hoFunctor.map (localizationNerveMap (relativeNaturalCylinder η hη))).toFunctor.map
        (((relativeCylinderEndpointIso C).app x).hom))

lemma localizationWeakNat_component_arrow (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (X : C.category) :
    Arrow.mk (((localizationNerveMapIsoOfWeakNatTrans η hη).app
      (localizationNerveVertexEquiv C X)).hom) =
      Arrow.mk (SSet.HomotopyCategory.homMk
        (coherentNerveEdge (kanLocalizationStrictHom D (η.app X))))

```

**一覧：済み 9／全体 42（うち追加 0）**。

### 17.3 同じ全比較の等式輸送の分割（着手）

全比較を両端の等式で移す法則を一般の関手比較について一度証明し、同じ弱自然変換の
比較はその法則を呼ぶ形にする。`localizationNerveMapIsoOfWeakNatTrans` は元の円筒比較・
後合成・二つの端点等式を保持する。公開の型や元の可逆二胞体は変えない。
`LocalizationComparisonEvaluation` に追加する法則は次の二つ。

```lean
def functorIsoTransport {A Y : SSet.{u}} {f g f' g' : A ⟶ Y}
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') : FunctorIso f' g'

lemma functorIsoTransport_component_arrow {A Y : SSet.{u}}
    [Quasicategory A] [Quasicategory Y] {f g f' g' : A ⟶ Y}
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') (x : A _⦋0⦌) :
    Arrow.mk (((functorIsoTransport e hf hg).app x).hom) = Arrow.mk ((e.app x).hom)
```

既存の全比較の等式輸送・成分評価の法則であり、一次 ID は追加しない。
元の §16.2 の成分式の型を保ち、kernel の計算のために範囲を縮めない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 17.4 最後の指定成分までの検証済み結果と実測

§16.2 の `localizationNerveMapIsoOfWeakNatTrans_component` は、元の型を保持して
正規 Lake の対象ビルド・kernel 照合を通過した。
等式輸送を `functorIsoTransport` の一般の法則へ分け、その同じ成分の法則を使い、
全比較の後合成、同じ射の Arrow の一致、元の頂点比較による両端の輸送へ分けた。
この最終ファイルの対象ビルドは 15 秒、計算上限の局所的変更は不要になった。
元の円筒の選択逆・可逆二胞体・同じ全比較を保持し、最後の主張の範囲も型も変更していない。
影響する `AlgebraRoundTripComparison` の対象も通過した。

今回の新規公開 32 宣言、同じ全比較の既存 2 宣言、BE 往復比較の既存 4 宣言の
計 38 宣言について、小さい `#print axioms` 監査が終了コード 0。
38 件の宣言名と実出力を機械照合し、依存公理は標準の
`propext`・`Classical.choice`・`Quot.sound` の範囲内。
追加公理・`sorryAx` はない。新規 32・既存比較 2 の計 34 宣言の文献属性も、
一件ずつの HTT `component` と、各宣言の指定した番号に一致することを環境から検査し、
終了コード 0。全て指定の共有鍵、実行上限 280 秒の組で行った。

この goal ターンの新規 Lean は **7 ファイル・667 行・31 宣言（公開）**。
`LocalizationComparisonEvaluation` は最終 99 行・5 宣言、
`LocalizationWeakNatComponent` は最終 110 行・4 宣言。
他の五つのファイルの実測は §17.1 と同じ。
自分の既存 `RelativeNaturalComparison` はこのターン全体で差引 21 行・1 宣言追加。
200 行を超える補題はない。
検証済み累計は新規 Lean **42 ファイル・3,974 行・214 宣言（private 3 を含む）**。
§16.2・§17.1 で下書きとしていたファイルも今回検証済みとなり、未検証の Lean 下書きはない。
全て既存構成の等式輸送・係数作用・恒等・成分評価・自然性・射影構成の証明の分割で、
一次 ID は追加していない。

M10 の全弱自然変換の指定成分への接続はできた。
半自由 native fiber の同定、一般の底の辺の lift・transport と全族の cocartesian 性、
同じ U・単位・随伴を持つ `moduleFamily` の組み立ては引き続き必要。
M11 以降の相対テンソル・RHom・完備反射・完備テンソルと G12 も未完。
M10 を完了とは数えず、元の全目標を維持して続ける。

**一覧：済み 9／全体 42（うち追加 0）**。

## 18. M10 の固定底の通常加群から指定半自由模型への源（11-14、着手）

前の goal ターンは、全弱自然変換の指定成分までの kernel 照合を通し、
`621a7b739`・`f9da36f0d` に検証済みの実装と監査をコミットした進捗。
今回は通常の閉零加群圏の DK 局所化と、半自由加群の dg nerve の間の fiber 比較を進める。
既存の `DGModuleResolutionLocalization.dgModuleResolution_isLocalization` は、
全 dg 加群の **dg nerve** から半自由模型への局所化を与える。
元の通常の閉零圏の nerve からの普遍性とは源が異なり、同じ主張として流用しない。
BE の `CAlgLocalizationUniversal.cAlgLocalizationSource_isLocalization` は既にある。
いずれも他レーンのファイルは読んで import するだけで変更しない。

まず同じ通常の閉零加群の全 nerve を元の dg nerve へ送り、同じ指定半自由分解を適用する。
元の擬同型の反転と本質的全射性を照合し、次に制限に関する全関手間の比較へつなぐ。
Hom の ULift を戻す際には通常の `nerveMap` の同一 Hom 宇宙の制約を避け、
元の列の Hom を戻して同じ閉零 dg 単体にする。
これは M10/C02 の既存構成の源・係数移送・指定辺と分解比較の証明の分割で、一次 ID は追加しない。
通常 nerve からの局所化普遍性と、全圏の fiber の同定は引き続き必要。

`RawModuleDerivedSource.lean` の今回の型。文脈は `A : Type u`、`[CommRing A]`。

```lean
def strictRawModuleDGSource (X : (operad A).Algebra) :
    nerve (strictRawModuleRelativeCategory A X).category ⟶
      dgModuleNerve A (dgAlgebraCategory A ((assocForget A).obj X))

def strictRawModuleSource (X : (operad A).Algebra) :
    nerve (strictRawModuleRelativeCategory A X).category ⟶ strictModuleInfinity A X

lemma strictRawModuleDGSource_vertex (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    (strictRawModuleDGSource A X).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M) =
      Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A)
        ((ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj M))

lemma strictRawModuleDGSource_edge (X : (operad A).Algebra)
    {M N : (strictRawModuleRelativeCategory A X).category} (f : M ⟶ N) :
    (strictRawModuleDGSource A X).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      (dgClosedEdge A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) f.down).edge

lemma strictRawModuleSource_vertex (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    (strictRawModuleSource A X).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M) =
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))).app (Opposite.op ⦋0⦌)
        (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A)
          ((ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj M)))

lemma strictRawModuleSource_inverts (X : (operad A).Algebra) :
    InvertsEdges (strictRawModuleSource A X) (weakNerveEdges (strictRawModuleRelativeCategory A X))

lemma strictRawModuleSource_essentiallySurjective (X : (operad A).Algebra) :
    IsEssentiallySurjective (strictRawModuleSource A X)
```

文献は閉零 nerve の包含が HA Construction 1.3.1.9、
指定半自由分解への反転・本質的全射性は HA Proposition 1.3.5.13 の同じ dg 加群模型の成分。
同じ通常の源を局所化とする普遍性はこの属性では主張しない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 18.1 同じ通常の源と制限・台・単位の全比較の型

`RawModuleSourceRestriction.lean` の文脈は `A : Type u`、`[CommRing A]`。
全 dg 加群の分解の前後の制限を、元の擬同型保存と同じ入力前合成則で比較し、
元の通常の源の全単体自然性と貼り合わせる。
既存の `strictModuleResolvedUnderlyingIso` を同じ源で前合成し、正則加群の値も
同じ頂点の式で指定単位へ等置する。いずれも M10/C02 の元の構成の法則の分割。

```lean
lemma strictRawModuleDGSource_restrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    nerveMap (strictRawModuleRestrictRelative f).functor ≫ strictRawModuleDGSource A X =
      strictRawModuleDGSource A Y ≫
        N (dgModuleRestriction A (dgAlgebraCategory A ((assocForget A).obj X))
          (dgAlgebraCategory A ((assocForget A).obj Y)) (dgAlgebraMap A ((assocForget A).map f)).op)

def strictRawResolvedRestrictionIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj Y)) ≫ strictModuleRestrict f)
      (N (dgModuleRestriction A (dgAlgebraCategory A ((assocForget A).obj X))
        (dgAlgebraCategory A ((assocForget A).obj Y)) (dgAlgebraMap A ((assocForget A).map f)).op) ≫
        moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)))

def strictRawModuleSource_restrictIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (nerveMap (strictRawModuleRestrictRelative f).functor ≫ strictRawModuleSource A X)
      (strictRawModuleSource A Y ≫ strictModuleRestrict f)

def strictRawModuleSource_underlyingIso (X : (operad A).Algebra) :
    FunctorIso (strictRawModuleSource A X ≫ strictModuleUnderlying A X)
      (strictRawModuleDGSource A X ≫
        N (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
          (Opposite.op DGAlgebraPoint.star)) ≫
        dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
          (DiagramComparison.semifreePointEquivalence A).hom)

lemma strictRawModuleSource_regular (X : (operad A).Algebra) :
    (strictRawModuleSource A X).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ ((ULiftHom.up.{u,u+1,u+1}
        (C := strictRawModuleCategory A X)).obj (strictRawRegularObject A X).fiber)) =
      strictModuleUnit A X
```

上の自然性は全ての厳密 BE 代数射 `f` に対する、同じ実関手間の主張。
一般の native CAlg の辺上の transport の構成や fiber 比較の普遍性は、これから必要。
他レーンのファイルや `EInfinity/Interface/` は変更していない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 19. M10/C02 の次の経路：通常 dg 加群の projective モデル構造（N01、追加案）

### 19.1 現在の入力と差

§18 の源は通常の閉零加群の全 nerve から指定半自由模型へ送るが、反転と
本質的全射性だけでは局所化普遍性にはならない。
`DGModuleResolutionLocalization.dgModuleResolution_isLocalization` の源は dg nerve。
通常 nerve と dg nerve の間の比較を、同じ定理の代入だけで埋めることはできない。
リポジトリの `ModelCategory` を持つ定義と `RightModule`・`ModuleCategory` 等が共存する
ファイルを調べたが、現在の `strictRawModuleCategory A X` のモデル構造は見つからなかった。
これは不在の形式的証明ではなく、この経路の既存入力を探した結果。

採る経路の案は、同じ通常加群圏に projective モデル構造を実際に構成し、
既存の `SimplicialLocalization/ModelBifibrantLocalization`・`ModelHammockLocalization` の
全圏・bifibrant 比較と全標的の局所化普遍性を再利用するもの。
元の弱同値類と半自由模型を同じものに照合する。
新しい `[ModelCategory SSet]` や未証明の加群モデル構造を入力に加える案ではない。

### 19.2 N01 の型と仕様（未実装・採否の確認用）

新しい一次項目の追加案 **N01** は、同じ BE 固定底の通常加群圏のモデル構造を返す構成。
文脈は `A : Type u`、`[CommRing A]`、`X : (operad A).Algebra`。

```lean
def strictRawModuleModelCategory (X : (operad A).Algebra) :
    HomotopicalAlgebra.ModelCategory (strictRawModuleCategory A X)

lemma strictRawModuleModelCategory_weakEquivalences (X : (operad A).Algebra) :
    @HomotopicalAlgebra.weakEquivalences (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithWeakEquivalences =
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))

lemma strictRawModuleModelCategory_fibrations (X : (operad A).Algebra) :
    @HomotopicalAlgebra.fibrations (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithFibrations =
    (projectiveFibrations A).inverseImage (strictRawModuleUnderlying X)

lemma strictRawModuleModelCategory_allFibrant (X : (operad A).Algebra)
    (M : strictRawModuleCategory A X) :
    letI := strictRawModuleModelCategory A X
    HomotopicalAlgebra.IsFibrant M

lemma strictRawModuleModelCategory_semifreeCofibrant (X : (operad A).Algebra)
    (P : SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X))) :
    letI := strictRawModuleModelCategory A X
    HomotopicalAlgebra.IsCofibrant (ForgetEnrichment.of (Complex A) P.val)
```

モデル構造の弱同値・fibration・元の半自由対象の条件までを仕様に含める。
大域 instance にはせず、必要な比較で局所的に選ぶ。
X の carrier の平坦性・cofibrancy は追加仮定にしない。
この仕様は型の案で、Lean での検証済み宣言ではない。

その後の M10/C02 内の比較の目標は、既存の型のまま次を閉じること。

```lean
lemma strictRawModuleSource_isLocalization (X : (operad A).Algebra) :
    IsLocalization (strictRawModuleSource A X)
      (weakNerveEdges (strictRawModuleRelativeCategory A X))
```

N01 の存在だけでこの局所化や全族の fiber 同定が従うとは数えない。
実 frame Hom と同じ dg Hom の比較、指定源の同じ全関手比較を実装し、
その後に全族の fiber と一般の底の辺の lift・transport を証明する。

### 19.3 再利用・見込み・文献

既存の `moduleEvaluation`・`freeEvaluationAdjunction`（`Module/TensorFree.lean`）、
`Module/ActionLimits.lean` の加群の極限・余極限、
`Module/ShiftResolution.lean` の実半自由 filtration と解像度、
`ProjectiveModel` と `ModelGeneration.rightTransfer` を再利用する。
新たに必要になるのは、同じ自由加群で移した生成 I/J の小対象性、
自由な J-cell の擬同型性、モデル構造の選択とクラスの照合、半自由対象の cofibrancy。

N01 単体の暫定見込みは **1,000〜2,200 行**。
小対象性・自由な J-cell の部分を実測して再評価する。M10 の比較の残りや
M11 以降をこの見込みに入れて完成見込みとすることはしない。
M15 の外枠 **17,000 行は据え置く**。N01 の採否が決まるまで実装は始めない。

文献は [Keller, On differential graded categories, Theorem 3.2 (1)](https://webusers.imj-prg.fr/~bernhard.keller/publ/dgcat.pdf) の projective 構造。
HA Proposition 4.3.3.15 も W/F の転送を述べるが、一般のモノイダル模型では
作用する代数の cofibrancy を仮定する。その仮定を今回の任意 X へ黙って追加しない。
[HA 原典 §4.3.3](https://www.math.ias.edu/~lurie/papers/HA.pdf) を確認した。

### 19.4 止める規則との関係

`lane-goals-2026-11-14.md` 共通規則の
「**止まって報告するのは、新しい構成・新しい定理（既存の構成の法則でないもの）**」
に照らし、通常加群圏の ModelCategory を返す構成は、元の M01〜M42 に型のない
新しい構成と判断した。この判断は当レーンの解釈であり、M10/C02 の単なる証明分割
として追加承認を不要とする指示があればそれに従う。
N01 を採用する場合だけ一次 ID の追加として数える案で、現在の一覧にはまだ追加しない。
§18 の承認範囲内の実装・検証は完了まで進める。
その後は N01 の採否を確認し、待つ間は指示どおり drafts/A5 の受け渡しを紙で照合する。

**一覧：済み 9／全体 42（うち追加 0）**。


### 19.5 N01 の追加承認と着手（11-14、調整役）

N01 は調整役の返答で追加承認された。§19.2 の仕様のまま、モデル構造を実際に
構成し、元の擬同型・次数別全射・半自由対象の cofibrancy と照合する。
ModelCategory を引数の instance として仮定しない。外枠は 17,000 行のまま。
先に既存の `HomotopicalAlgebra/Diagram/Projective.modelCategory` と
`BarrattEccles.Diagram.projectiveModelCategory`、一般の転送の構成を確認する。
N01 は未完で、一次一覧は M01〜M42 と N01 の計 43 項目となった。

**一覧：済み 9／全体 43（うち追加 1）**。


## 20. §18 の検証完了と N01 の既存部品の確認（11-14）

§18 の `RawModuleDerivedSource`（168 行・7 宣言）と
`RawModuleSourceRestriction`（137 行・5 宣言）の二つの通常対象ビルドは成功。
新規公開 12 宣言の小さい依存公理監査は、12 件の実出力を宣言名と機械照合して成功した。
依存公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
12 宣言の HA 文献属性も、各一件・component・指定番号を環境から照合して成功。
共有 impl 鍵、各組 280 秒上限。200 行を超える補題はない。
検証済み累計は **44 ファイル・4,279 行・226 宣言（private 3 を含む）**。
通常 nerve からの局所化普遍性や M10 全体の完成とは数えない。

§18 の型の転記に、名前付き引数の `:=` を宣言本体の区切りと誤認して途中で
切れた箇所があった。括弧の深さを追って区切る方法に直し、同節の全 12 型を
実ソースから完全な形で転記し直した。

N01 について、指定された既存の二つの構成を先に読んだ。
`HomotopicalAlgebra/Diagram/Projective.modelCategory` は通常の `K ⥤ C` を対象とし、
基礎モデルと locally presentable 性を入力に持つ。
`BarrattEccles.Diagram.projectiveModelCategory` は `K ⥤ (operad A).Algebra` を対象とし、
実自由評価族と証明済みの cell 非輪状性を一般転送に渡している。
今回の元の dg 加群圏はそのいずれの通常関手圏でもないので、直接の代入にはしない。
代わりに同じ設計の既存 `ModelGeneration.rightTransfer` を再利用する。
`EInfinity/DGAlgebra/ModelCategory` と `SmallObject` の使い方も確認した。

さらに既存 `DGModuleDiskCoverAcyclic` に、任意 dg 底の実 disk 被覆の非輪状性と、
非輪状直和項からの射影の擬同型性がある。自由 disk 被覆の全次数全射性も既存。
これらをそのまま import し、全射の左類の射 f を
`M → M ⊕ diskCover(N)` の retract として非輪状性を証明する経路にした。
新しい path object や底 X の cofibrancy 仮定を必要としない。
自由 I/J の実小対象性とこの非輪状性の実装は、次の対象ビルドで検証中。
他レーンの既存ファイルは変更していない。

N01 は着手したが未完。追加した一次 ID は N01 一件だけ。

**一覧：済み 9／全体 43（うち追加 1）**。


## 21. N01 の実構成・照合の型（11-14）

共通の文脈は `A : Type u`、`[CommRing A]`。一般の二ファイルではさらに
`D : Type v`、`[DGCategory A D]`、`[Small.{u} D]` を使う。
以下は承認済み N01 の実装とその生成射・自然性・貼り合わせ・持ち上げの証明分割。
検証結果と最終の実測は本節末尾に記録する。

### RawModuleGenerators

```lean
abbrev strictRawModuleFree (X : (operad A).Algebra) :
    Complex A ⥤ strictRawModuleCategory A X

def strictRawModuleFreeAdjunction (X : (operad A).Algebra) :
    strictRawModuleFree A X ⊣ strictRawModuleUnderlying X

def strictRawModuleGeneratingCofibrations (X : (operad A).Algebra) :
    MorphismProperty (strictRawModuleCategory A X)

def strictRawModuleGeneratingTrivialCofibrations (X : (operad A).Algebra) :
    MorphismProperty (strictRawModuleCategory A X)

lemma strictRawModuleQuasiIso_eq (X : (operad A).Algebra) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) =
      (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (strictRawModuleUnderlying X)

lemma strictRawModuleGeneratingCofibrations_rlp (X : (operad A).Algebra) :
    (strictRawModuleGeneratingCofibrations A X).rlp =
      ((projectiveFibrations A) ⊓ quasiIso (ModuleCat A) (.up ℤ)).inverseImage
        (strictRawModuleUnderlying X)

lemma strictRawModuleGeneratingTrivialCofibrations_rlp (X : (operad A).Algebra) :
    (strictRawModuleGeneratingTrivialCofibrations A X).rlp =
      (projectiveFibrations A).inverseImage (strictRawModuleUnderlying X)

lemma strictRawModuleUnderlying_accessible (X : (operad A).Algebra)
    (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    (strictRawModuleUnderlying X).IsCardinalAccessible κ

lemma strictRawModuleFree_finitelyPresentable (X : (operad A).Algebra)
    (K : Complex A) [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} ((strictRawModuleFree A X).obj K)

lemma strictRawModuleFreeFamily_smallObjectArgument (X : (operad A).Algebra)
    {ι : Type v} [Small.{u} ι] {K L : ι → Complex A}
    (f : ∀ i, K i ⟶ L i) [∀ i, IsFinitelyPresentable.{u} (K i)] :
    ((MorphismProperty.ofHoms f).strictMap (strictRawModuleFree A X)).HasSmallObjectArgument.{u}

lemma strictRawModuleGeneratingCofibrations_smallObjectArgument (X : (operad A).Algebra) :
    (strictRawModuleGeneratingCofibrations A X).HasSmallObjectArgument.{u}

lemma strictRawModuleGeneratingTrivialCofibrations_smallObjectArgument
    (X : (operad A).Algebra) :
    (strictRawModuleGeneratingTrivialCofibrations A X).HasSmallObjectArgument.{u}
```

### RawModuleAcyclicity

```lean
lemma strictRawModuleBiprodInl_quasiIso (X : (operad A).Algebra)
    (M K : strictRawModuleCategory A X)
    (hK : moduleAcyclic A (dgAlgebraCategory A ((assocForget A).obj X)) K) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      (moduleBiprodInl A _ M K)

lemma strictRawModuleFibrations_llp_quasiIso (X : (operad A).Algebra)
    {M N : strictRawModuleCategory A X} (f : M ⟶ N)
    (hf : ((projectiveFibrations A).inverseImage (strictRawModuleUnderlying X)).llp f) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) f

lemma strictRawModuleFreeCells_acyclic (X : (operad A).Algebra) :
    MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u}
        (strictRawModuleGeneratingTrivialCofibrations A X)).pushouts ≤
      moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
```

### RawModuleModel

```lean
lemma strictRawModule_hasFiniteLimits (X : (operad A).Algebra) :
    HasFiniteLimits (strictRawModuleCategory A X)

lemma strictRawModule_hasFiniteColimits (X : (operad A).Algebra) :
    HasFiniteColimits (strictRawModuleCategory A X)

def strictRawModuleModelCategory (X : (operad A).Algebra) :
    ModelCategory (strictRawModuleCategory A X)

lemma strictRawModuleModelCategory_weakEquivalences (X : (operad A).Algebra) :
    @weakEquivalences (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithWeakEquivalences =
        moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))

lemma strictRawModuleModelCategory_fibrations (X : (operad A).Algebra) :
    @fibrations (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithFibrations =
        (projectiveFibrations A).inverseImage (strictRawModuleUnderlying X)

lemma strictRawModuleModelCategory_cofibrantlyGenerated (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (strictRawModuleGeneratingCofibrations A X)
      (strictRawModuleGeneratingTrivialCofibrations A X)

lemma strictRawModuleModelCategory_allFibrant (X : (operad A).Algebra)
    (M : strictRawModuleCategory A X) :
    let := strictRawModuleModelCategory A X
    IsFibrant M
```

### RawModuleCofibrancy

```lean
lemma strictRawModuleSemifree_strict_lift (X : (operad A).Algebra)
    {P M N : strictRawModuleCategory A X}
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    (p : M ⟶ N) (hs : (projectiveFibrations A) ((strictRawModuleUnderlying X).map p))
    (hq : moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) p) (g : P ⟶ N) :
    ∃ l : P ⟶ M, l ≫ p = g

lemma strictRawModuleModelCategory_semifreeCofibrant (X : (operad A).Algebra)
    (P : SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X))) :
    let := strictRawModuleModelCategory A X
    IsCofibrant (ForgetEnrichment.of (Complex A) P.val)
```

### SemifreeGradedLifting

```lean
lemma moduleHom_post_pre_component {M N T U : ModuleCategory A D}
    (i : M ⟶ N) (p : T ⟶ U) (q : ℤ)
    (z : (N ⟶[Complex A] T).X q) :
    (eHomWhiskerRight (Complex A) i U).f q
      ((eHomWhiskerLeft (Complex A) N p).f q z) =
    (eHomWhiskerLeft (Complex A) M p).f q
      ((eHomWhiskerRight (Complex A) i T).f q z)

lemma moduleGradedSplit_postcompose_lift {M N Q T U : ModuleCategory A D}
    {i : M ⟶ N} {g : N ⟶ Q} (s : ModuleGradedSplit A D i g)
    (p : T ⟶ U) (q : ℤ)
    (hQ : Function.Surjective ((eHomWhiskerLeft (Complex A) Q p).f q))
    (a : (M ⟶[Complex A] T).X q)
    (z : (N ⟶[Complex A] U).X q)
    (h : (eHomWhiskerLeft (Complex A) M p).f q a =
      (eHomWhiskerRight (Complex A) i U).f q z) :
    ∃ b : (N ⟶[Complex A] T).X q,
      (eHomWhiskerLeft (Complex A) N p).f q b = z ∧
      (eHomWhiskerRight (Complex A) i T).f q b = a
```

### SemifreeGradedProjectivity

```lean
lemma moduleHom_postcompose_surjective_of_iso {M N T U : ModuleCategory A D}
    (e : M ≅ N) (p : T ⟶ U) (q : ℤ)
    (hN : Function.Surjective ((eHomWhiskerLeft (Complex A) N p).f q)) :
    Function.Surjective ((eHomWhiskerLeft (Complex A) M p).f q)

lemma moduleSphereFreePresentation_postcompose_surjective {M T U : ModuleCategory A D}
    (S : ModuleSphereFreePresentation A D M) (p : T ⟶ U)
    (hp : moduleDegreewiseSurjective A D p) (q : ℤ) :
    Function.Surjective ((eHomWhiskerLeft (Complex A) M p).f q)

lemma moduleSemifreeFiltration_postcompose_surjective {M T U : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (p : T ⟶ U)
    (hp : moduleDegreewiseSurjective A D p) (q : ℤ) :
    Function.Surjective ((eHomWhiskerLeft (Complex A) M p).f q)
```


## 22. M10/C02 の次の接続：同じ実モデルへの frame の代入（11-14）

N01 の次には、既存の一般の関手的分解・Reedy frame・全モデル圏の hammock 普遍性を
同じ実加群モデルへ代入する。これらの一般の構成を作り直さず、ModelCategory や分解の
存在を引数の仮定として残さない。次の五つは既存構成の特殊化・証明の分割で、一次 ID は
追加しない。対象ビルドと監査の結果は本節の末尾へ追記する。

`RawModuleFrameInput.lean`。文脈は `A : Type u`、`[CommRing A]`。

```lean
def strictRawModuleCofibrantFactorization (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    MorphismProperty.FunctorialFactorizationData (cofibrations (strictRawModuleCategory A X))
      (trivialFibrations (strictRawModuleCategory A X))

def strictRawModuleFibrantFactorization (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    MorphismProperty.FunctorialFactorizationData (trivialCofibrations (strictRawModuleCategory A X))
      (fibrations (strictRawModuleCategory A X))

def strictRawModuleSourceFrameFamily (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    CofibrantResolutionFamily (C := strictRawModuleCategory A X) simplex

def strictRawModuleRightFrameFamily (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    CofibrantResolutionFamily (C := (strictRawModuleCategory A X)ᵒᵖ) simplex

lemma strictRawModuleModelHammock_isLocalization (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    IsLocalization
      (hammockLocalizationNerveMap
        (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
          (strictRawModuleCategory A X)))
      (weakNerveEdges
        (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
          (strictRawModuleCategory A X)))
```

ここで既存 `modelRelativeCategory` は AsSmall 表示であり、§18 の源の ULiftHom 表示と
定義上同じとはしない。同じ元の圏・同じ擬同型を保つ宇宙表示の比較が必要。
さらに、この hammock の普遍性を得ても、§18 の通常源から半自由 dg nerve への
`strictRawModuleSource` が局所化であることは未完のまま。同じ frame Hom と実 dg Hom、
その全標的自然性と指定源の比較をつなぐ必要がある。
M10 の全族の一般の辺・fiber の同定も、ここで終わったとは数えない。

**一覧：済み 9／全体 43（うち追加 1）**。


### 22.1 同じ通常圏の二つの宇宙表示の型

`RawModuleRelativeModel.lean` は、既存の ULiftHom・AsSmall の圏同値を合成し、
N01 の W の等式で両方向の相対関手を作る。元の通常圏の表示・弱同値検出の法則であり、
一次 ID は追加しない。これだけで半自由 dg nerve への比較を済ませたとはしない。

```lean
def strictRawModuleUniverseEquivalence (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    (strictRawModuleRelativeCategory A X).category ≌
      (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)).category

def strictRawModuleToModelRelative (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    strictRawModuleRelativeCategory A X ⟶
      SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)

def strictRawModuleFromModelRelative (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
      (strictRawModuleCategory A X) ⟶ strictRawModuleRelativeCategory A X
```


### 22.2 元の通常加群 DK 源の全標的普遍性の型

同じ宇宙表示の単位・余単位は同型であり、元の弱射でもある。
これらを既存の `isLocalization_of_weakDeformation` と同じ hammock nerve の標的比較へ
渡す実装を準備した。以下は元の通常圏の自由 DK 局所化の法則の証明分割で、一次 ID は
追加しない。半自由標的への `strictRawModuleSource` の普遍性とは別の主張である。

`RawModuleLocalizationUniversal.lean`、同じ `A : Type u`、`[CommRing A]`。

```lean
lemma strictRawModuleUniverseUnit_weak (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    (strictRawModuleRelativeCategory A X).weakEquivalences
      ((strictRawModuleUniverseEquivalence A X).unitIso.inv.app M)

lemma strictRawModuleUniverseCounit_weak (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    ∀ M : (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)).category,
      (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)).weakEquivalences
          ((strictRawModuleUniverseEquivalence A X).counitIso.hom.app M)

lemma strictRawModuleHammockUniverse_isQCatEquivalence (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    IsQCatEquivalence (relativeKanHammockNerve (strictRawModuleToModelRelative A X))

lemma strictRawModuleHammock_isLocalization (X : (operad A).Algebra) :
    IsLocalization (hammockLocalizationNerveMap (strictRawModuleRelativeCategory A X))
      (weakNerveEdges (strictRawModuleRelativeCategory A X))

lemma strictRawModuleLocalization_isLocalization (X : (operad A).Algebra) :
    IsLocalization (localizationNerveSourceMap (strictRawModuleRelativeCategory A X))
      (weakNerveEdges (strictRawModuleRelativeCategory A X))
```

本小節の実装は、前の対象ビルドが共有鍵を待っている間に準備したもの。
対象ビルド・小さい監査に通るまでは検証済みと数えない。

**一覧：済み 9／全体 43（うち追加 1）**。



### 22.3 実 dg Hom との接続で再利用できる部品（紙、未実装）

通常源と dg nerve の比較で使う点ごとの Hom 加群も、作用から作り直す必要はない。
`DifferentialGraded/Module/Basic.leftRepresentable` は共変 Hom の実 dg 関手である。
そのため `D : Type v`、`[DGCategory A D]`、`K : Complex A`、
`M : RightModule A D` に対して、次の既存の合成は型として同じ右加群を返す。

```lean
M.comp (leftRepresentable A K) : RightModule A D
```

点での値は `homComplex A K (M.obj x)`。高次の作用の符号は既存の
`leftRepresentable_action` に保持されている。
標準単体の複体を K に入れる候補では、既存の
`AlexanderWhitney.simplexCochainComonFunctor` の台を再利用できる。
`KST/LocalizingInvariants/DGAlgebraMultiplicativeSimplices` も同じ単体複体に対する
内部 Hom の族を使っていることを読んだが、代数の乗法の構成を加群へコピーしない。

この式だけでは、全単体を持つ選んだ right frame との比較、Reedy fibrancy、
指定 coaugmentation の弱同値性、元の dg Hom との全標的自然性はまだ証明していない。
N01 の実モデルを得た後に、既存の tensor/Hom の随伴・標準単体の分裂と照合する。
本小節は再利用候補の紙の記録であり、検証済み Lean の追加ではない。


## 23. A5 への受け渡しの補足：§18 と N01 の到達点から（11-14、紙）

対象ビルドの共有鍵を待つ間に、`drafts/Shared/Descendable` と
`drafts/A5/StrongDescent` を再読した。drafts は変更していない。
§11 の完備反射・完備テンソル・Koszul の受け渡しに加え、今回の実装からの差を記録する。

`StrongDescent.deltaRootEdge` は `polynomialRootArrow` の nerve の辺を
`discreteDeltaFunctor` で送った辺である。通常圏の一辺を入力にしているが、型から得られる
出力は native CAlg の辺であり、厳密 BE 代数射そのものは返さない。
§18 の制限比較は厳密 BE 代数射に対する同じ全関手比較なので、この辺を代入するには
M10 の全族の transport との接続が要る。BE 特殊化の方針を維持し、任意 E の輸送を作らない。

§18 の `strictRawModuleSource_regular` と `strictRawModuleSource_underlyingIso` は、
固定した厳密 BE 底について、同じ通常の源の正則加群を指定単位へ送り、同じ台の評価と
全関手間で比較する法則である。これにより、N01 の通常モデルから出る入力の U・単位を
照合する入口ができた。A5 の一般の `deltaRootEdge` の台・単位・fiber の coherence と、
完備反射の単位・余単位は引き続き M10 および M36–M37 の実出力を使う。

N01 の `strictRawModuleModelCategory_allFibrant` は、通常 dg 加群の projective モデルの
終対象への射が次数ごとに全射、という fibrancy である。
A5 で必要な `Derived.IsDerivedComplete A s` は完備反射の固定点の条件なので、
前者から後者を得たことにはしない。実際、N01 の fibrancy の結論は全通常加群に対するもの。
`Shared/Descendable.isDescendable_complete` の入力 `hB` と、
`StrongDescent.rhom_baseChange_koszul_connection` の導来完備性の証明は、各々の型のまま残る。

N01 の半自由 cofibrancy の照合は、元の `SemifreeDGModules` の対象を別の置換へ変えない。
ただし、A5 の個別の Koszul 対象・fiber やその二乗が半自由・双対可能であることを、
この照合の名前だけで供給したとはしない。M15 が返す一般の相対テンソル・RHom・完備版の
法則を受け取り、A5 が個別の Koszul・Nakayama の証明を閉じる、という分担を維持する。

本節は利用側の型の照合だけで、一次 ID の追加はない。
N01 の最終対象ビルドと監査は待機中であり、完了数はまだ更新しない。

**一覧：済み 9／全体 43（うち追加 1）**。


## 24. N01 の完成・検証・実測（11-14）

承認された N01 は、§19.2 の仕様のまま完成した。
`strictRawModuleModelCategory` の引数は基礎可換環 A と厳密 BE 底 X であり、
ModelCategory の存在を引数の instance として仮定しない。
元の `moduleQuasiIso` と台の全整数次数全射に W/F を同定し、全対象の fibrancy と
同じ `SemifreeDGModules` の対象の cofibrancy を、実構成したモデルで証明した。
底 X の平坦性・cofibrancy や SSet のモデル構造の仮定は追加していない。

先に指定された既存部品を確認した記録は §20。
実装は構成済みの複体の `projectiveModelCategory`、元の自由評価随伴、
評価ごとの実極限・余極限、`ModelGeneration.rightTransfer` を使用した。
転送の非輪状性には既存の実自由 disk 被覆と直和射影の擬同型性を使い、
半自由 cofibrancy には既存の全作用付き filtration・全 Hom の極限と擬同型性を使った。

| 新規ファイル | 行数 | 公開宣言 |
|---|---:|---:|
| BE `Modules/RawModuleGenerators` | 176 | 12 |
| BE `Modules/RawModuleAcyclicity` | 117 | 3 |
| BE `Modules/RawModuleModel` | 129 | 7 |
| BE `Modules/RawModuleCofibrancy` | 89 | 2 |
| `Modules/SemifreeGradedLifting` | 65 | 2 |
| `Modules/SemifreeGradedProjectivity` | 117 | 3 |
| 合計 | **693** | **29** |

200 行を超える補題はない。一次 ID は承認された N01 一件だけで、
残りは同じ構成の生成射・持ち上げ・表示の等式・貼り合わせの法則と証明の分割。
全 29 型を §21 に記載した。
当初の見込み 1,000〜2,200 行より短くなったのは、§20 の既存の実部品を再利用したため。
M15 の外枠 17,000 行は維持する。

最終の通常対象ビルド `RawModuleCofibrancy:olean` は終了コード 0。
その依存の生成射・非輪状性・実モデル・全次数の半自由持ち上げも通常対象として成功した。
新規公開 29 宣言の `#print axioms` の実出力を宣言名と機械照合し、監査は終了コード 0。
全て標準の `propext`・`Classical.choice`・`Quot.sound` の範囲内で、追加公理・sorryAx はない。
自由加群と自由評価随伴の既存 HA 文献番号に付けた二件の属性も、各一件、
HA 4.2.4.4 の component であることを環境から検査して成功した。
N01 の原典の projective モデルの番号は、宣言 docstring の Keller Theorem 3.2 (1)。
いずれも共有 impl 鍵、実行上限 280 秒の組で行った。

監査まで済んだ累計は、新規 Lean **50 ファイル・4,972 行・255 宣言（private 3 を含む）**。
M10 の続きの `RawModuleFrameInput` と `RawModuleRelativeModel` の対象ビルドは通ったが、
`RawModuleLocalizationUniversal` に結果型の let の導入の修正が一箇所あり、修正後の対象ビルドと
13 宣言の監査を待つ。これら三ファイルは今回の N01 コミットに含めず、作業木に残す。
過去の報告の型転記で途中が切れていた四宣言も、§18 と同じ抽出の修正により完全な型へ補った。

N01 を完了に数える。M10 の同じ通常源と半自由 native 模型の全比較、全族の一般の辺と fiber、
M11 以降の相対テンソル・RHom・完備反射・完備テンソル、G12 は引き続き進める。

**一覧：済み 10／全体 43（うち追加 1）**。


## 25. M10/C02：元の通常加群 DK 源の普遍性まで検証（11-14）

§22 の三つのファイルの通常対象ビルドと小さい監査が完了した。
`RawModuleFrameInput` 88 行・5 宣言、`RawModuleRelativeModel` 69 行・3 宣言、
`RawModuleLocalizationUniversal` 118 行・5 宣言、計 **275 行・13 公開宣言**。
修正は結果型のモデル選択 let の導入と、BE 代数の同名判定に隠れた
`HomotopicalAlgebra.weakEquivalence_iff` の完全名指定であり、仕様を変えていない。

最終の対象 `RawModuleLocalizationUniversal:olean` は終了コード 0。
13 宣言の `#print axioms` は宣言名と実出力を機械照合し、監査は終了コード 0。
全て `propext`・`Classical.choice`・`Quot.sound` の範囲内で、追加公理・sorryAx はない。
共有 impl 鍵、実行上限 280 秒の組で行った。200 行を超える補題はない。

同じ通常加群圏の ULiftHom と AsSmall の相対比較を通じ、元の自由 DK 源
`localizationNerveSourceMap (strictRawModuleRelativeCategory A X)` が、元の擬同型を反転する
全 quasicategory 標的への局所化であることを得た。
これにより、同じ通常源から指定半自由模型への §18 の関手を全関手のまま降下できる。
その降下と指定三角比較を次に作り、完全忠実性と同じ全族の fiber の同定へ接続する。
反転・本質的全射性だけで同値・普遍性と数えることはしない。

監査まで済んだ累計は、新規 Lean **53 ファイル・5,247 行・268 宣言（private 3 を含む）**。
いずれも同じ実モデル・同じ相対局所化の比較・源移送の法則と証明分割で、一次 ID は追加しない。
M10 はまだ未完。一次一覧の完了数は M01–M09 と N01 の計 10 のまま。

**一覧：済み 10／全体 43（うち追加 1）**。


## 26. M10/C02：指定半自由模型への全比較の降下と制限の法則（11-14）

§25 の元の通常 DK 源の全標的普遍性に、§18 の同じ通常源から指定半自由模型への関手を
渡した。既存の `localizationDescend` と同じ `localizationDescendIso` により、
全単体の比較関手 K と全関手間の指定三角同型を得る。
標準局所化頂点、正則加群の指定単位、元の U との源上の比較も同じ三角から回収する。

さらに源の全係数自然性、両端の同じ三角、§18 の同じ制限比較を貼り、
実局所化の前合成の充満忠実性で全関手間の同型を降ろす。
全厳密 BE 代数射を対象とし、元の制限が半自由対象を保つという仮定は置かない。
これは既存の M10/C02 の構成の降下・自然性・単位・貼り合わせの法則と証明分割で、
一次 ID は追加しない。

型の文脈は `A : Type u`、`[CommRing A]`。

### RawModuleComparison

```lean
def strictRawModuleComparison (X : (operad A).Algebra) :
    localizationNerve (strictRawModuleRelativeCategory A X) ⟶ strictModuleInfinity A X

def strictRawModuleComparison_sourceIso (X : (operad A).Algebra) :
    FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫
        strictRawModuleComparison A X)
      (strictRawModuleSource A X)

def strictRawModuleComparison_vertexIso (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    VertexIso
      ((strictRawModuleComparison A X).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv (strictRawModuleRelativeCategory A X)
          (show KanLocalizationCategory (strictRawModuleRelativeCategory A X) from M)))
      ((strictRawModuleSource A X).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M))

lemma strictRawModuleComparison_essentiallySurjective (X : (operad A).Algebra) :
    IsEssentiallySurjective (strictRawModuleComparison A X)

def strictRawModuleComparison_regularIso (X : (operad A).Algebra) :
    VertexIso
      ((strictRawModuleComparison A X).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv (strictRawModuleRelativeCategory A X)
          (show KanLocalizationCategory (strictRawModuleRelativeCategory A X) from
            (ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj
              (strictRawRegularObject A X).fiber)))
      (strictModuleUnit A X)

def strictRawModuleComparison_sourceUnderlyingIso (X : (operad A).Algebra) :
    FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫
        strictRawModuleComparison A X ≫ strictModuleUnderlying A X)
      (strictRawModuleSource A X ≫ strictModuleUnderlying A X)
```

### RawModuleComparisonRestriction

```lean
def strictRawModuleLocalization_descendIso (X : (operad A).Algebra)
    {Y : SSet.{u+1}} [Quasicategory Y]
    {F G : localizationNerve (strictRawModuleRelativeCategory A X) ⟶ Y}
    (e : FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫ F)
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫ G)) :
    FunctorIso F G

def strictRawModuleComparison_restrictSourceIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A Y) ≫
        localizationNerveMap (strictRawModuleRestrictRelative f) ≫ strictRawModuleComparison A X)
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A Y) ≫
        strictRawModuleComparison A Y ≫ strictModuleRestrict f)

def strictRawModuleComparison_restrictIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (localizationNerveMap (strictRawModuleRestrictRelative f) ≫ strictRawModuleComparison A X)
      (strictRawModuleComparison A Y ≫ strictModuleRestrict f)
```


K の本質的全射性は元の通常源の本質的全射性と同じ三角から従うが、完全忠実性は未完。
K を同値・fiber 同定とまだ呼ばない。一般の native な底の辺・全族の cocartesian 性、
M11 以降と G12 は引き続き残る。
対象ビルドと小さい監査の結果は、この節の末尾に追記する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 26.1 全比較と制限の対象ビルド・小さい監査

`RawModuleComparison`（107 行・6 宣言）と `RawModuleComparisonRestriction`（77 行・3 宣言）の
通常対象ビルドが完了し、終了コード 0。新規 9 宣言の `#print axioms` について、実出力を
宣言名と機械照合して監査も終了コード 0。依存公理は標準の
`propext`・`Classical.choice`・`Quot.sound` の範囲内で、追加公理・sorryAx はない。
共有 impl 鍵、実行上限 280 秒の組で行った。200 行を超える補題はない。

前合成の表記は、通常圏の同名 `pre` ではなく `MonoidalClosed.pre` を選ぶよう明示した。
構成された K・全三角・頂点・単位・台・全厳密制限との比較の型は上記のまま。
K の完全忠実性、一般の native 底の辺・同じ全族の fiber 同定はまだ未完なので、
M10 の完了数は更新しない。

監査まで済んだ累計は、新規 Lean **55 ファイル・5,431 行・277 宣言（private 3 を含む）**。
次は §22.3 の既存共変 Hom の合成を使い、実 frame と元の dg Hom の比較を進める。

**一覧：済み 10／全体 43（うち追加 1）**。


## 27. M10 の Hom 比較の部品：同じ点ごとの cotensor 関手（11-14）

§22.3 の既存部品をさらに確認すると、`Complexes/Cone.homCovariantDG` が
同じ `leftRepresentable` を複体の共変 Hom の実 dg 関手として公開している。
全次数の作用と、同じ閉零射が元の Hom 後合成に一致することも既に証明されている。
これを同じ加群 dg 関手に後合成し、元の加群射は点ごとの `homPostcompose` で送る。
既存の enriched 前後合成の交換を使い、全作用の自然性と通常関手の単位・合成を照合する。

以下は既存の合成・閉零射・評価の法則の分割で、一次 ID は追加しない。
文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`。
閉零圏の箇所ではさらに `[Small.{u} D]`。

`Modules/CotensorPointwise.lean` の型：

```lean
def dgModuleCotensor (K : Complex A) (M : RightModule A D) : RightModule A D

abbrev moduleCotensor (K : Complex A) (M : ModuleCategory A D) : ModuleCategory A D

lemma moduleCotensor_eval (K : Complex A) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).obj (moduleCotensor A D K M) =
      homComplex A K ((moduleEvaluation A D x).obj M)

lemma moduleCotensorMap_naturality (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x y : Dᵒᵖ) :
    (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPostcompose _ (homPostcompose K ((moduleEvaluation A D y.unop).map f)) =
    (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) N)).map x y ≫
      homPrecompose (homPostcompose K ((moduleEvaluation A D x.unop).map f)) _

def moduleCotensorMap (K : Complex A) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCotensor A D K M ⟶ moduleCotensor A D K N

lemma moduleCotensorMap_eval (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleCotensorMap A D K f) =
      homPostcompose K ((moduleEvaluation A D x).map f)

def moduleCotensorFunctor (K : Complex A) : ModuleCategory A D ⥤ ModuleCategory A D

lemma moduleCotensorFunctor_evaluation (K : Complex A) (x : D) :
    moduleCotensorFunctor A D K ⋙ moduleEvaluation A D x =
      moduleEvaluation A D x ⋙ (eHomFunctor (Complex A) (Complex A)).obj (op K)
```

この時点で標準単体を入れた全 simplicial frame の Reedy fibrancy や coaugmentation の
弱同値性まで主張するものではない。元の dg Hom とモデル frame Hom の比較、
K の完全忠実性へ向けた部品として対象ビルド・小さい監査を行う。

**一覧：済み 10／全体 43（うち追加 1）**。


### 27.1 対象ビルド・小さい監査と次の接続

`CotensorPointwise:olean` の通常対象ビルドは終了コード 0。
8 宣言の `#print axioms` は、宣言名と実出力を機械照合して監査も終了コード 0。
全て標準の `propext`・`Classical.choice`・`Quot.sound` の範囲内で、追加公理・sorryAx はない。
共有 impl 鍵、実行上限 280 秒の組で行った。

評価の対象と元の dg 関手の対象は定義上同じだが、`rw` の照合では表示を揃える必要が
あったため、自然性の二つの交換式の型を明示した。単位則にも同じ定義上の等式を補った。
全て §27 の型のままであり、対象の射影性や底の平坦性を仮定していない。
新規 1 ファイル **130 行・8 公開宣言**。200 行を超える補題はない。

監査まで済んだ累計は、新規 Lean **56 ファイル・5,561 行・285 宣言（private 3 を含む）**。
この goal ターンで完成したものは、元の通常 DK 源の普遍性、指定半自由模型への全比較と
全厳密制限との比較、同じ Hom の合成による cotensor 関手の法則。
§25・§26.1 と本小節は具体的な検証済みの進捗であり、M10 全体の完了ではない。

続きは、標準単体を係数とするこの cotensor の反変作用・全 simplicial 族を照合し、
選んだ実 right frame と同じ dg Hom の比較へ進む。
比較関手 K の完全忠実性、同じ全族の一般の native 辺と fiber の同定、
M11 以降と G12 の本来の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 28. M10 の同じ cotensor の係数反変性と全 simplicial 族（11-14）

前の goal ターンは §25–§27 の通常 DK 源の普遍性・全比較・cotensor の法則を
対象ビルドと小さい監査まで通した進捗。今回は既存の cochain 合成の結合則を使い、
同じ `homPrecompose` が cotensor の全 dg 作用と可換することを照合した。
係数の前合成は全加群射に自然であり、単位・逆順の合成の法則を満たす。

その反変関手に、既存の `SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A` を代入し、
面・退化・全加群射を持つ同じ simplicial 加群の全族を構成した。
点ごとの値と全作用は元の AW 正規化複体からの内部 Hom の前後合成に一致する。
同じ通常 Hom の後合成で全標的の写像単体集合も束ねる。

いずれも既存の cotensor の係数移送・合成・自然性・評価・貼り合わせの法則と
証明の分割で、一次 ID は追加しない。
文脈は `A : Type u`、`[CommRing A]`。
加群の箇所はさらに `D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。

### CotensorScalar

```lean
lemma homCovariantDG_precomposition {K L : Complex A} (f : K ⟶ L) (P Q : Complex A) :
    (homCovariantDG A L).map P Q ≫ homPostcompose _ (homPrecompose f Q) =
      (homCovariantDG A K).map P Q ≫ homPrecompose (homPrecompose f P) _

lemma moduleCotensorPre_naturality {K L : Complex A} (f : K ⟶ L)
    (M : ModuleCategory A D) (x y : Dᵒᵖ) :
    (dgModuleCotensor A D L (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPostcompose _ (homPrecompose f ((ForgetEnrichment.to (Complex A) M).obj y)) =
    (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPrecompose (homPrecompose f ((ForgetEnrichment.to (Complex A) M).obj x)) _

def moduleCotensorPreMap {K L : Complex A} (f : K ⟶ L) (M : ModuleCategory A D) :
    moduleCotensor A D L M ⟶ moduleCotensor A D K M

lemma moduleCotensorPreMap_eval {K L : Complex A} (f : K ⟶ L) (M : ModuleCategory A D)
    (x : D) :
    (moduleEvaluation A D x).map (moduleCotensorPreMap A D f M) =
      homPrecompose f ((moduleEvaluation A D x).obj M)

def moduleCotensorPreNat {K L : Complex A} (f : K ⟶ L) :
    moduleCotensorFunctor A D L ⟶ moduleCotensorFunctor A D K

def moduleCotensorScalarFunctor : (Complex A)ᵒᵖ ⥤ (ModuleCategory A D ⥤ ModuleCategory A D)
```

### CotensorSimplices

```lean
def moduleCotensorSimplexFamily :
    SimplexCategoryᵒᵖ ⥤ (ModuleCategory A D ⥤ ModuleCategory A D)

def moduleCotensorSimplicesFunctor :
    ModuleCategory A D ⥤ (SimplexCategoryᵒᵖ ⥤ ModuleCategory A D)

abbrev moduleCotensorSimplices (M : ModuleCategory A D) :
    SimplexCategoryᵒᵖ ⥤ ModuleCategory A D

lemma moduleCotensorSimplices_obj_eval (M : ModuleCategory A D)
    (n : SimplexCategoryᵒᵖ) (x : D) :
    (moduleEvaluation A D x).obj ((moduleCotensorSimplices A D M).obj n) =
      homComplex A (SerrePositivity.EInfinity.AlexanderWhitney.cochains A (SSet.stdSimplex.obj n.unop))
        ((moduleEvaluation A D x).obj M)

lemma moduleCotensorSimplices_map_eval (M : ModuleCategory A D)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : D) :
    (moduleEvaluation A D x).map ((moduleCotensorSimplices A D M).map f) =
      homPrecompose
        (SerrePositivity.EInfinity.AlexanderWhitney.cochainMap A (SSet.stdSimplex.map f.unop))
        ((moduleEvaluation A D x).obj M)

lemma moduleCotensorSimplicesFunctor_map_eval {M N : ModuleCategory A D} (g : M ⟶ N)
    (n : SimplexCategoryᵒᵖ) (x : D) :
    (moduleEvaluation A D x).map (((moduleCotensorSimplicesFunctor A D).map g).app n) =
      homPostcompose
        (SerrePositivity.EInfinity.AlexanderWhitney.cochains A (SSet.stdSimplex.obj n.unop))
        ((moduleEvaluation A D x).map g)

def moduleCotensorMappingSimplices (P M : ModuleCategory A D) : SSet.{u}

def moduleCotensorMappingFunctor (P : ModuleCategory A D) :
    ModuleCategory A D ⥤ SSet.{u}
```


対象ビルドは成功した。小さい依存公理監査と最終実測は本節の末尾に追記する。
この simplicial 族の Reedy fibrancy、同じ coaugmentation の弱同値性、選んだモデル frame
との比較、K の完全忠実性はまだ未完。元の全族と M11 以降・G12 の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。

### §28.1 検証と実測

CotensorScalar と CotensorSimplices の通常の対象ビルドは成功した。
同じ impl 鍵の下で新しい公開宣言 14 本の依存公理を監査し、すべて
propext・Classical.choice・Quot.sound の範囲であることを確認した。
新規 Lean は本節の 2 ファイル 223 行を加え、累計 58 ファイル・5,784 行・
明示宣言 299 本（private 3 本）。200 行を超える証明はない。
Reedy fibrancy と単位 cotensor の同定、K の完全忠実性は引き続き未完。

**一覧：済み 10／全体 43（うち追加 1）**。


## 29. M10 の同じ全単体 cotensor の余単位比較（11-14）

既存の `cochainCounitStdSimplexHomotopyEquiv` は、AW 余単位そのものを順射とする
全次元の実鎖ホモトピー同値を保持している。これを既存の
`homPrecomposeHomotopyEquiv` へ送り、値域加群に追加の仮定を課さず、元の全評価で
係数前合成が擬同型となることを証明した。

同じ AW 余単位の自然性から、単位係数 cotensor の定数図式から同じ全単体族への
比較を構成した。この比較は元の全加群射について自然で、全次数で擬同型。
その自然性と二つから三つにより、同じ simplicial 加群の全ての面・退化も擬同型になる。
いずれも既存の cotensor の余単位・自然性・係数移送・合成の法則と証明の分割で、
一次 ID は追加しない。

比較の始域は正確に `moduleCotensor A D (𝟙_ (Complex A)) M` である。
元の加群 M との同定はまだ残る。この比較だけで Reedy fibrancy や
元の加群からの frame coaugmentation、K の完全忠実性を主張しない。
文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。

```lean
lemma moduleCotensorPreMap_quasiIso {K L : Complex A} (f : K ⟶ L)
    (hf : HomologicalComplex.homotopyEquivalences (ModuleCat A) (.up ℤ) f)
    (M : ModuleCategory A D) :
    moduleQuasiIso A D (moduleCotensorPreMap A D f M)

def moduleCotensorCounitNat (M : ModuleCategory A D) :
    (Functor.const SimplexCategoryᵒᵖ).obj (moduleCotensor A D (𝟙_ (Complex A)) M) ⟶
      moduleCotensorSimplices A D M

lemma moduleCotensorCounitNat_weak (M : ModuleCategory A D) (n : SimplexCategoryᵒᵖ) :
    moduleQuasiIso A D ((moduleCotensorCounitNat A D M).app n)

def moduleCotensorCounitFamily :
    moduleCotensorFunctor A D (𝟙_ (Complex A)) ⋙ Functor.const SimplexCategoryᵒᵖ ⟶
      moduleCotensorSimplicesFunctor A D

lemma moduleCotensorSimplices_maps_weak (M : ModuleCategory A D)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    moduleQuasiIso A D ((moduleCotensorSimplices A D M).map f)
```

検証結果は本節の末尾へ追記する。

**一覧：済み 10／全体 43（うち追加 1）**。

### §29.1 検証と実測

CotensorCounit の通常の対象ビルドは成功し、新しい公開宣言 5 本の依存公理監査も
成功した（標準の propext・Classical.choice・Quot.sound のみ）。どちらも指定の
共有鍵・280 秒の塊で実行した。新規 Lean は本節の 1 ファイル 102 行を加えて、
検証済み累計 59 ファイル・5,886 行・明示宣言 304 本（private 3 本）。
200 行を超える証明はない。単位則の実装は次節で検証する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 30. M10 の同じ cotensor の単位則（11-14）

単位複体からの全次数 Hom は、その唯一の生成元での評価により元の複体と線形同値。
既存の single 複体からの cochain 微分の式を使い、これを実複体同型へ組み立てる。
全次数の dg Hom 作用と可換する式を照合し、同じ主 Hom end による加群同型へ持ち上げる。
元の全加群射への自然性も同じ後合成の評価で確認する。
既存の cotensor の単位・自然性の法則と証明の分割で、一次 ID は追加しない。
文脈は `A : Type u`、`[CommRing A]`。
加群ではさらに `D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。

```lean
def cotensorUnitDegreeEquiv (K : Complex A) (p : ℤ) :
    (homComplex A (𝟙_ (Complex A)) K).X p ≃ₗ[A] K.X p

def cotensorUnitComplexIso (K : Complex A) :
    homComplex A (𝟙_ (Complex A)) K ≅ K

lemma cotensorUnitComplexIso_naturality (P Q : Complex A) :
    (homCovariantDG A (𝟙_ (Complex A))).map P Q ≫
        homPostcompose _ (cotensorUnitComplexIso A Q).hom =
      homPrecompose (cotensorUnitComplexIso A P).hom Q

lemma cotensorUnitComplexIso_postcompose {P Q : Complex A} (f : P ⟶ Q) :
    homPostcompose (𝟙_ (Complex A)) f ≫ (cotensorUnitComplexIso A Q).hom =
      (cotensorUnitComplexIso A P).hom ≫ f

def moduleCotensorUnitIsoObj (M : ModuleCategory A D) :
    moduleCotensor A D (𝟙_ (Complex A)) M ≅ M

lemma moduleCotensorUnitIsoObj_hom_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleCotensorUnitIsoObj A D M).hom =
      (cotensorUnitComplexIso A ((moduleEvaluation A D x).obj M)).hom

def moduleCotensorUnitIso : moduleCotensorFunctor A D (𝟙_ (Complex A)) ≅
    𝟭 (ModuleCategory A D)
```

検証結果は §32.2 に記録した。Reedy fibrancy と K の完全忠実性は引き続き未完。

**一覧：済み 10／全体 43（うち追加 1）**。


## 31. M10 の元の加群からの coaugmentation（11-14）

§30 の単位自然同型の逆と §29 の余単位自然変換を貼り合わせ、
元の加群 M の定数図式から同じ全単体族への比較を作る。
全加群射の自然性は同じ自然変換の合成に含まれる。
各次数の射自身の式を回収し、同じ単位同型と余単位の擬同型性から
元の全評価で擬同型となることを確認する。
これは既存の cotensor の単位・余単位・貼り合わせの法則と証明の分割であり、
一次 ID は追加しない。Reedy fibrancy と K の完全忠実性は引き続き未完。
文脈は A : Type u、[CommRing A]、D : Type v、[DGCategory A D]、[Small.{u} D]。

```lean
def moduleCotensorCoaugmentationFamily :
    Functor.const SimplexCategoryᵒᵖ ⟶ moduleCotensorSimplicesFunctor A D

lemma moduleCotensorCoaugmentationFamily_app (M : ModuleCategory A D)
    (n : SimplexCategoryᵒᵖ) :
    ((moduleCotensorCoaugmentationFamily A D).app M).app n =
      (moduleCotensorUnitIsoObj A D M).inv ≫ (moduleCotensorCounitNat A D M).app n

lemma moduleCotensorCoaugmentationFamily_weak (M : ModuleCategory A D)
    (n : SimplexCategoryᵒᵖ) :
    moduleQuasiIso A D (((moduleCotensorCoaugmentationFamily A D).app M).app n)
```

検証結果は §32.2 に記録した。

**一覧：済み 10／全体 43（うち追加 1）**。


## 32. M10 の同じ半自由 Hom の Quillen 条件（11-14）

N01 の厳密な持ち上げで使った同じ実半自由 filtration の全次数 Hom の全射性と、
既存の半自由 Hom の擬同型保存を、同じ全 Hom 関手の右 Quillen 条件へ束ねる。
両モデル構造は構成済みの実モデルであり、モデル構造を引数に置かない。
同じ正規化単体を使う source frame 側にも利用できる入力である。
これは既存の Hom の係数移送の法則と M10 の証明の分割で、一次 ID は追加しない。
右 Quillen 条件だけで K の完全忠実性や元の全族の完成を主張しない。
文脈は A : Type u、[CommRing A]。

```lean
lemma strictRawModuleSemifree_hom_fibration (X : (operad A).Algebra)
    {P M N : strictRawModuleCategory A X}
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    (p : M ⟶ N) (hp : projectiveFibrations A ((strictRawModuleUnderlying X).map p)) :
    projectiveFibrations A (eHomWhiskerLeft (Complex A) P p)

lemma strictRawModuleSemifree_hom_isRightQuillen (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    letI := strictRawModuleModelCategory A X
    letI := projectiveModelCategory A
    SerrePositivity.Quillen.IsRightQuillen
      ((eHomFunctor (Complex A) (strictRawModuleCategory A X)).obj (op P))
```

検証結果は §32.2 に記録した。

**一覧：済み 10／全体 43（うち追加 1）**。

### 32.1 同じ source frame に向けた既存の随伴の部品（紙）

`DifferentialGraded/Module/Hom/HomotopyAndOperations.tensorModuleFunctor` は、固定した
元の加群 P に対する `Complex A ⥤ ModuleCategory A D` を既に構成している。
`Module/Hom/ColimitsAndRightHom.moduleParamCurry` と `TensorFree.moduleParamUncurry` は
同じ二つの Hom 集合の間を往復し、`moduleParamUncurry_curry`・
`moduleParamCurry_uncurry` が両逆を証明している。係数射の自然性は
`moduleParamUncurry_precomp`、固定加群変数の自然性は
`moduleParamUncurry_naturality_source` にある。

したがって §32 の同じ Hom 関手の右 Quillen 条件は、これらの既存の転置の法則を
随伴へ束ねた後、`leftQuillen_frame_reedyCofibrant` と既存の
`ComplexLimits.normalizedSimplex_reedyCofibrant` に接続する候補となる。
元の加群への随伴と同じ frame Hom の比較はまだ実装していない。この紙の候補を
Reedy 条件や K の完全忠実性の証明として数えない。


### 32.2 §30–§32 の検証・実測

CotensorUnit、CotensorCoaugmentation、RawModuleHomQuillen の通常の対象ビルドは
すべて成功した。新しい公開宣言 12 本の依存公理監査も成功し、使用する公理は
propext・Classical.choice・Quot.sound のみ。指定の impl 鍵で、一回 280 秒の塊を
使った。大きい監査・root ビルドはこのレーンでは実行していない。

新規 Lean の今回の三ファイルはそれぞれ 148・57・67 行、計 272 行、公開宣言 12 本。
§29.1 の累計に加え、検証済み累計は 62 ファイル・6,158 行・明示宣言 316 本
（private 3 本）。200 行を超える証明はない。一次 ID の追加はない。

同じ単位 cotensor と元の加群の自然同型、元の加群を始域とする全単体の比較と
その各次数の擬同型性までが検証済みになった。Reedy 条件とモデル frame Hom から
元の dg Hom への全標的自然な比較、K の完全忠実性、M10 の一般の native な辺・fiber
と全族の完成は残る。M11 以降と G12 の目標も維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 33. M10 の同じ半自由 source frame と全標的 Hom（11-14）

前の goal ターンは §28–§32 の単位則・全単体 coaugmentation と半自由 Hom の
Quillen 条件を対象ビルドと小さい監査まで通した進捗。
今回、§32.1 で確認した既存の転置・逆転置の両逆を実随伴に束ねた。
標的への自然性は元の主 Hom end の評価ごとに Hom 後合成の式から証明した。

同じ `SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A` を既存の
`tensorModuleFunctor` で送り、元の全加群射に自然な source frame の全族を作る。
元の AW 余単位と既存の左単位同型から、元の加群への全自然 augmentation を保持する。

BE 固定底では N01 の実モデルと同じ Hom の右 Quillen 条件を使い、係数テンソルの
左 Quillen 条件を得る。既存の `normalizedSimplex_reedyCofibrant` と
`leftQuillen_frame_reedyCofibrant` を使い、Reedy 条件を作り直さない。
同じ AW 余単位の実鎖収縮と Brown の補題により、全作用素の弱同値性と指定 augmentation
の弱同値性を照合する。実モデルの全対象の fibrancy から、元の任意の標的への同じ
cosimplicial Hom の Kan 性を得る。

いずれも既存の tensor/Hom の随伴・自然性・単位/余単位の貼り合わせの法則と、
M10 の証明の分割であり、一次 ID は追加しない。半自由であるのは始域の probe P。
標的 N は元の任意の通常 dg 加群である。単体集合のモデル構造を仮定しない。
一般の文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。
BE の文脈では `A : Type u`、`[CommRing A]` と表示された固定 BE 底 X を使う。

### TensorHomAdjunction

```lean
lemma moduleParamCurry_postcompose {K : Complex A} {M N P : ModuleCategory A D}
    (f : moduleTensorLeftObj A D K M ⟶ N) (g : N ⟶ P) :
    moduleParamCurry A D (f ≫ g) =
      moduleParamCurry A D f ≫ eHomWhiskerLeft (Complex A) M g

def moduleTensorHomEquiv (M : ModuleCategory A D) (K : Complex A)
    (N : ModuleCategory A D) :
    ((tensorModuleFunctor (ForgetEnrichment.to (Complex A) M)).obj K ⟶ N) ≃
      (K ⟶ ((eHomFunctor (Complex A) (ModuleCategory A D)).obj (op M)).obj N)

def moduleTensorHomAdjunction (M : ModuleCategory A D) :
    tensorModuleFunctor (ForgetEnrichment.to (Complex A) M) ⊣
      (eHomFunctor (Complex A) (ModuleCategory A D)).obj (op M)
```

### TensorSimplices

```lean
def moduleTensorSimplicesFunctor :
    ModuleCategory A D ⥤ (SimplexCategory ⥤ ModuleCategory A D)

lemma moduleTensorSimplices_obj_eval (M : ModuleCategory A D) (n : SimplexCategory) (x : D) :
    (moduleEvaluation A D x).obj (((moduleTensorSimplicesFunctor A D).obj M).obj n) =
      AlexanderWhitney.cochains A (SSet.stdSimplex.obj n) ⊗
        (moduleEvaluation A D x).obj M

lemma moduleTensorSimplices_map_eval {M N : ModuleCategory A D} (f : M ⟶ N)
    (n : SimplexCategory) (x : D) :
    (moduleEvaluation A D x).map (((moduleTensorSimplicesFunctor A D).map f).app n) =
      𝟙 (AlexanderWhitney.cochains A (SSet.stdSimplex.obj n)) ⊗ₘ
        (moduleEvaluation A D x).map f

def moduleTensorSimplicesAugmentation (M : ModuleCategory A D) :
    (moduleTensorSimplicesFunctor A D).obj M ⟶ (Functor.const SimplexCategory).obj M

lemma moduleTensorSimplicesAugmentation_eval (M : ModuleCategory A D)
    (n : SimplexCategory) (x : D) :
    (moduleEvaluation A D x).map ((moduleTensorSimplicesAugmentation A D M).app n) =
      (AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) ⊗ₘ
        𝟙 ((moduleEvaluation A D x).obj M)) ≫ (λ_ ((moduleEvaluation A D x).obj M)).hom

def moduleTensorSimplicesAugmentationFamily :
    moduleTensorSimplicesFunctor A D ⟶ Functor.const SimplexCategory
```

### RawModuleTensorFrame

```lean
lemma strictRawModuleSemifree_tensor_isLeftQuillen (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    letI := projectiveModelCategory A
    letI := strictRawModuleModelCategory A X
    SerrePositivity.Quillen.IsLeftQuillen
      (tensorModuleFunctor (ForgetEnrichment.to (Complex A) P))

lemma strictRawModuleTensorFrame_reedyCofibrant (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    letI := strictRawModuleModelCategory A X
    reedyLeft simplex (cofibrations (strictRawModuleCategory A X))
      (initial.to ((moduleTensorSimplicesFunctor A
        (dgAlgebraCategory A ((assocForget A).obj X))).obj P))

lemma strictRawModuleTensorFrame_homotopicallyConstant (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    {n m : SimplexCategory} (f : n ⟶ m) :
    letI := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((moduleTensorSimplicesFunctor A
        (dgAlgebraCategory A ((assocForget A).obj X))).obj P).map f)

lemma strictRawModuleTensorFrame_augmentation_weak (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    (n : SimplexCategory) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((moduleTensorSimplicesAugmentation A
        (dgAlgebraCategory A ((assocForget A).obj X)) P).app n)

lemma strictRawModuleTensorHom_kanComplex (X : (operad A).Algebra)
    (P N : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    SSet.KanComplex
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
        ((moduleTensorSimplicesFunctor A
          (dgAlgebraCategory A ((assocForget A).obj X))).obj P)).obj N)
```


対象ビルド・小さい監査の結果と最終実測は §34.1 に記録した。
同じ source frame Hom と元の dg Hom との全標的自然な同型は §34 で実装した。
モデルで選んだ frame との比較、K の完全忠実性と元の全族の一般の native な辺・fiber
の完成は引き続き残る。

**一覧：済み 10／全体 43（うち追加 1）**。


## 34. M10 の同じ source frame Hom と元の dg Hom の全比較（11-14）

§33 の同じ全単体 source frame Hom を、元の主 Hom end の
`DK(τ≤0 moduleHom(P,N))` に全単体で同定する。
既存の `normalizedSimplexHomEquiv` に同じ実 tensor/Hom 転置を前置するだけであり、
Dold–Kan の部品・smart 切断・自由単体の評価は作り直さない。

同じ転置の係数前合成自然性を両逆と逆転置の法則から回収し、全ての面・退化と可換する
実単体集合同型を得る。標的射については §33 の転置の後合成自然性と既存の
`normalizedSimplexHomEquiv_postcomp` を貼り合わせる。
従って標的 N を動かす同じ全関手の自然同型となる。

比較対象の dg 圏は正確に `RightModule A D`、対象は元の P,N を
`ForgetEnrichment.to (Complex A)` で戻したもの。零次数をホモロジーの商へ変えない。
これは M10 の既存の写像空間比較の証明分割と、既存の転置・自然性の法則で、
一次 ID は追加しない。文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、
`[DGCategory A D]`、`[Small.{u} D]`。
略記 `doldKanHomModule`・`doldKanHomSpace` は Kerodon の
`ExamplesOfInfinityCategories.DifferentialGradedCategories` の実 Dold–Kan。
`cosimplicialHom` は既存の `Project.HomotopyDiagramComparison.CosimplicialHom`、
`truncatedDoldKanFunctor` は既存の `EInfinity.ComplexLimits` の関手である。

```lean
lemma moduleParamCurry_precompose {K L : Complex A} {P N : ModuleCategory A D}
    (g : K ⟶ L) (f : moduleTensorLeftObj A D L P ⟶ N) :
    moduleParamCurry A D (tensorModuleMap g (ForgetEnrichment.to (Complex A) P) ≫ f) =
      g ≫ moduleParamCurry A D f

def moduleTensorSimplexHomEquiv (P N : ModuleCategory A D) (n : SimplexCategory) :
    (((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) ≃
      (doldKanHomModule (R := A) (D := RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)).obj (op n)

def moduleTensorHomDoldKanIso (P N : ModuleCategory A D) :
    (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).obj N ≅
      doldKanHomSpace (R := A) (D := RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)

def moduleTensorHomDoldKanNatIso (P : ModuleCategory A D) :
    cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P) ≅
      (eHomFunctor (Complex A) (ModuleCategory A D)).obj (op P) ⋙
        truncatedDoldKanFunctor A
```

対象ビルドと小さい監査の結果・最終実測は §34.1 に記録した。
モデルで選んだ frame とこの具体的な source frame の全比較、K の完全忠実性、
元の全族の一般の native な辺・fiber の完成は残る。M11 以降・G12 の目標も維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 34.1 §33–§34 の検証と実測

通常の対象ビルドは TensorHomAdjunction、TensorSimplices、RawModuleTensorFrame、
TensorDoldKanHom のすべてで成功した。新しい公開宣言 18 本の依存公理監査も成功し、
propext・Classical.choice・Quot.sound のみを使う。すべて指定の impl 鍵と
一回 280 秒の塊で実行した。

新規 Lean は四ファイル、それぞれ 78・147・147・97 行、計 469 行、公開宣言 18 本。
§32.2 の累計に加え、検証済み累計は 66 ファイル・6,627 行・明示宣言 334 本
（private 3 本）。200 行を超える証明はない。一次 ID の追加はない。

同じ元の半自由 P の具体的 source frame が実モデルの条件を満たし、任意の元の標的 N
への全単体 Hom が元の dg Hom の実 Dold–Kan に全標的自然に同型になることまで検証した。
モデルで選んだ frame との全比較、通常源からの局所化比較 K の完全忠実性、
M10 の一般の native な辺・fiber と全族の完成は未完。
M11 以降と G12 を含む元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 35. M10 の選択済み frame と同じ source frame の全自然比較（11-14）

前の goal ターンは §33–§34 の実 source frame 条件と元の dg Hom の実 Dold–Kan
への全単体・全標的自然な比較を検証してコミットした進捗。
今回は元の `SemifreeDGModules` の閉零圏と同じ dg 全包含を probe のパラメータにする。
元の全閉零射を持つ全包含であり、対象の離散族に置き換えない。
N01 の同じモデル構造・同じ関手的分解・同じ `strictRawModuleSourceFrameFamily` を使う。

既存の `FrameOverFunctor.commonObj` に同じ二つの augmentation を渡し、
元の probe を底に持つ共通 Reedy cofibrant 族を得る。二つの実射と、同じ augmentation
の上で可換する全自然変換の等式を保持する。
三つの cosimplicial Hom を全 probe に反変・元の任意の標的に共変な二変数関手として構成し、
標準 Hom とテンソル Hom から同じ共通 Hom への二つの自然変換を回収する。

両脚の同じ射に `fixedFrameOverFunctor_homLeft_homotopyEquivalence` と
`fixedFrameOverFunctor_homRight_homotopyEquivalence` を適用する。
三つの元の Hom は Kan であり、二つの比較射は各 probe・各標的で実単体的ホモトピー同値。
単体集合のモデル構造を仮定せず、比較を homotopy category だけへ落とさない。

これは M10 の既存の frame/Hom 比較の証明分割と、既存の augmentation・自然性・
貼り合わせの法則であり、一次 ID は追加しない。
文脈は `A : Type u`、`[CommRing A]`。`IsSimplicialHomotopyEquivalence` は Kerodon の
`KanComplexes.TheHomotopyTheoryOfKanComplexes` の実ホモトピー同値。

### RawModuleProbeFrame

```lean
abbrev strictRawModuleProbeCategory (X : (operad A).Algebra) : Type (u + 1)

def strictRawModuleProbeFunctor (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ strictRawModuleCategory A X

lemma strictRawModuleProbeFunctor_semifree (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleProbeFunctor A X).obj P)

lemma strictRawModuleProbeFunctor_cofibrant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    let := strictRawModuleModelCategory A X
    IsCofibrant ((strictRawModuleProbeFunctor A X).obj P)

def strictRawModuleProbeTensorFrame (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (SimplexCategory ⥤ strictRawModuleCategory A X)

def strictRawModuleProbeTensorAugmentation (X : (operad A).Algebra) :
    strictRawModuleProbeTensorFrame A X ⟶
      strictRawModuleProbeFunctor A X ⋙ Functor.const SimplexCategory

lemma strictRawModuleProbeTensorFrame_cofibrant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    let := strictRawModuleModelCategory A X
    reedyLeft simplex (cofibrations (strictRawModuleCategory A X))
      (initial.to ((strictRawModuleProbeTensorFrame A X).obj P))

lemma strictRawModuleProbeTensorAugmentation_weak (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) (n : SimplexCategory) :
    let := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((strictRawModuleProbeTensorAugmentation A X).app P).app n)

lemma strictRawModuleProbeTensorFrame_homotopicallyConstant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) {n m : SimplexCategory} (f : n ⟶ m) :
    let := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((strictRawModuleProbeTensorFrame A X).obj P).map f)
```

### RawModuleProbeCommonFrame

```lean
def strictRawModuleProbeStandardFrame (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (SimplexCategory ⥤ strictRawModuleCategory A X)

def strictRawModuleProbeCommonFrame (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (SimplexCategory ⥤ strictRawModuleCategory A X)

def strictRawModuleProbeCommonToStandard (X : (operad A).Algebra) :
    strictRawModuleProbeCommonFrame A X ⟶ strictRawModuleProbeStandardFrame A X

def strictRawModuleProbeCommonToTensor (X : (operad A).Algebra) :
    strictRawModuleProbeCommonFrame A X ⟶ strictRawModuleProbeTensorFrame A X

lemma strictRawModuleProbeCommon_over (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    strictRawModuleProbeCommonToStandard A X ≫
        Functor.whiskerLeft (strictRawModuleProbeFunctor A X)
          (strictRawModuleSourceFrameFamily A X).augmentation =
      strictRawModuleProbeCommonToTensor A X ≫ strictRawModuleProbeTensorAugmentation A X

def strictRawModuleProbeStandardHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u}

def strictRawModuleProbeTensorHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u}

def strictRawModuleProbeCommonHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u}

def strictRawModuleProbeHomFromStandard (X : (operad A).Algebra) :
    strictRawModuleProbeStandardHom A X ⟶ strictRawModuleProbeCommonHom A X

def strictRawModuleProbeHomFromTensor (X : (operad A).Algebra) :
    strictRawModuleProbeTensorHom A X ⟶ strictRawModuleProbeCommonHom A X
```

### RawModuleProbeHomComparison

```lean
lemma strictRawModuleProbeHomFromStandard_homotopyEquivalence (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    IsSimplicialHomotopyEquivalence (((strictRawModuleProbeHomFromStandard A X).app P).app N)

lemma strictRawModuleProbeHomFromTensor_homotopyEquivalence (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    IsSimplicialHomotopyEquivalence (((strictRawModuleProbeHomFromTensor A X).app P).app N)

lemma strictRawModuleProbeStandardHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeStandardHom A X).obj P).obj N)

lemma strictRawModuleProbeTensorHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeTensorHom A X).obj P).obj N)

lemma strictRawModuleProbeCommonHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeCommonHom A X).obj P).obj N)
```


対象ビルドと小さい監査の結果・実測は §35.2 に記録した。
K の完全忠実性と元の全族の一般の native な辺・fiber の完成はまだ残る。
M11 以降と G12 を含む元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 35.1 同じ共通 frame 条件の証明分割

共通 Hom の Kan 条件へ直接実共通置換の構成を渡すと、深い定義の展開により
200,000 heartbeats に達した。同じ共通 frame の Reedy 条件と定数性を、その具体的な
族の型を持つ二本の補題へ分割して渡す。新しい数学の条件は加えず、モデルも同じ実構成。
いずれも既存の共通 frame の法則と M10 の証明分割であり、一次 ID は追加しない。

```lean
lemma strictRawModuleProbeCommonFrame_cofibrant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    let := strictRawModuleModelCategory A X
    reedyLeft simplex (cofibrations (strictRawModuleCategory A X))
      (initial.to ((strictRawModuleProbeCommonFrame A X).obj P))

lemma strictRawModuleProbeCommonFrame_homotopicallyConstant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) {n m : SimplexCategory} (f : n ⟶ m) :
    let := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((strictRawModuleProbeCommonFrame A X).obj P).map f)
```

**一覧：済み 10／全体 43（うち追加 1）**。


### 35.2 検証と実測

RawModuleProbeFrame、RawModuleProbeCommonFrame、RawModuleProbeHomComparison の
通常の対象ビルドはすべて成功した。新しい公開宣言 26 本の依存公理監査も成功し、
propext・Classical.choice・Quot.sound の範囲である。指定の impl 鍵と
一回 280 秒の塊で実行した。

§35.1 の分割に加え、共通族の関手等式から弱同値の命題を congrArg で明示的に移送した。
大きい実共通置換の定義どうしを展開して照合することを避け、200,000 heartbeats の
制限を上げずに通った。型・数学の条件・元の比較射は変えていない。

新規 Lean は三ファイル、それぞれ 109・157・90 行、計 356 行、公開宣言 26 本。
§34.1 の累計に加え、検証済み累計は 69 ファイル・6,983 行・明示宣言 360 本
（private 3 本）。200 行を超える証明はない。一次 ID は追加していない。

同じ元の半自由 probe をパラメータとする三つの全 Hom が Kan であり、同じ二変数の
実自然変換の両脚が各 probe・任意の標的で実単体的ホモトピー同値であることまで検証した。
元の augmentation の底の全等式も保持する。
§34 の dg Hom 同型の probe 変数への自然性の束ね、通常源の局所化比較 K の同じ作用の照合と
完全忠実性、M10 の一般の native な辺・fiber と全族の完成は引き続き残る。
M11 以降と G12 を含む元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 36. M10 の元の dg Hom への二変数自然な端点同定（11-14）

前の goal ターンは §35 の同じ全 probe・全標的の frame 比較を検証・コミットした進捗。
今回は §34 の実 Dold–Kan Hom 同型に、probe 変数の自然性を付ける。
既存の逆転置の加群始域射への自然性を、同じ転置との両逆の式で戻した。
元の `eHomFunctor` と `truncatedDoldKanFunctor` を合成し、元の主 Hom end の
実 Dold–Kan を二変数関手として保持する。
源は元の閉零加群圏であり、対象の離散族に置き換えない。

同じ二変数同型を元の半自由 probe 全包含で前合成し、その逆と §35 の同じ右脚を合成する。
これにより元の dg Hom から共通 Hom への実二変数自然変換を得る。
同じ実 Dold–Kan の Kan 性と、三つの同じ Kan Hom の比較の合成則を使い、
その同じ射が各 probe・任意の元の標的で実単体的ホモトピー同値となることを照合する。

いずれも既存の tensor/Hom の始域自然性・係数移送・同型の逆・貼り合わせの法則と、
M10 の写像空間比較の証明分割であり、一次 ID は追加しない。
一般部分の文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。
BE 部分では表示された固定 BE 底 X を使う。
`cosimplicialHomBifunctor` は既存の `Project.HomotopyDiagramComparison.CosimplicialHom`、
`IsSimplicialHomotopyEquivalence` は既存の Kerodon の Kan 複体の実ホモトピー同値である。

### TensorDoldKanBifunctor

```lean
lemma moduleParamCurry_sourceMap {K : Complex A} {M P N : ModuleCategory A D}
    (g : M ⟶ P) (f : moduleTensorLeftObj A D K P ⟶ N) :
    moduleParamCurry A D (moduleTensorLeftMap A D K g ≫ f) =
      moduleParamCurry A D f ≫ eHomWhiskerRight (Complex A) g N

def moduleDoldKanHomBifunctor :
    (ModuleCategory A D)ᵒᵖ ⥤ ModuleCategory A D ⥤ SSet.{u}

def moduleTensorHomDoldKanBifunctorIso :
    (moduleTensorSimplicesFunctor A D).op ⋙ cosimplicialHomBifunctor ≅
      moduleDoldKanHomBifunctor A D
```

### RawModuleProbeDoldKanHom

```lean
def strictRawModuleProbeDoldKanHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u}

def strictRawModuleProbeTensorDoldKanIso (X : (operad A).Algebra) :
    strictRawModuleProbeTensorHom A X ≅ strictRawModuleProbeDoldKanHom A X

def strictRawModuleProbeHomFromDoldKan (X : (operad A).Algebra) :
    strictRawModuleProbeDoldKanHom A X ⟶ strictRawModuleProbeCommonHom A X

lemma strictRawModuleProbeDoldKanHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeDoldKanHom A X).obj P).obj N)

lemma strictRawModuleProbeHomFromDoldKan_homotopyEquivalence (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    IsSimplicialHomotopyEquivalence (((strictRawModuleProbeHomFromDoldKan A X).app P).app N)
```


対象ビルド・小さい監査の結果と最終実測は §36.1 に記録した。
同じ局所化比較 K が誘導する写像空間の射の照合と完全忠実性、M10 の一般の native な辺・fiber
と全族の完成はまだ残る。M11 以降と G12 を含む元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 36.1 検証と実測

TensorDoldKanBifunctor と RawModuleProbeDoldKanHom の通常の対象ビルドは成功した。
新しい公開宣言 8 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。すべて指定の impl 鍵と一回 280 秒の塊で実行した。

新規 Lean は二ファイル、それぞれ 72・79 行、計 151 行、公開宣言 8 本。
§35.2 の累計に加え、検証済み累計は 71 ファイル・7,134 行・明示宣言 368 本
（private 3 本）。200 行を超える証明はない。一次 ID は追加していない。

同じテンソル Hom と元の dg Hom の実 Dold–Kan の同型が、元の始域・標的の両変数に
自然になった。同じ実二変数自然変換の標準側・dg Hom 側の二脚を共通 Hom に保ち、
各 probe と任意の元の標的でホモトピー同値となることまで検証した。
指定半自由模型の実 pinched Hom への端点同定、K の同じ誘導射の照合と完全忠実性、
M10 の一般の native な辺・fiber と全族の完成は未完。元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 37. M10 の指定 pinched Hom と同じ K の実誘導射（11-14）

§36 の同じ二変数 dg Hom 端点を、元の指定半自由模型の実 pinched Hom に同定する。
既存の `doldKanHomPinchedIso` を、元の二つの半自由 probe に直接適用する。
全単体テンソル Hom の端点も同じ二変数 Dold–Kan 同型と合成して同定する。
任意の同じ Hom 鎖写像への可換性は、既存の `doldKanHomPinchedIso_chainMap` の特殊化。
Dold–Kan・pinched 模型を作り直さない。

次に元の probe 全包含を同じ ULiftHom 表示へ送る全関手を作り、その標準局所化頂点を保持する。
同じ `dgModuleResolutionRetractIso` の成分から、元の通常源の値を指定半自由頂点へ戻す。
既存の同じ `strictRawModuleComparison_vertexIso` の成分を合成し、K の値の指定端点同型を得る。
対象ごとの別の同型を選ぶものではない。

その同じ K の実 `pinchedHomMap` の後に、同じ二つの端点成分による
`pinchedEndpointEquivalence` を合成する。さらに同じ実 Dold–Kan/pinched 同型の逆を合成し、
K の誘導射を元の dg Hom 座標で具体化する。その同じ座標射は、端点同型の順射を
後合成すると元の指定 pinched Hom 射を全単体で回収する。

これは M10 の既存比較の単位/余単位・係数移送・自然性・貼り合わせの法則と証明の分割であり、
一次 ID は追加しない。K の誘導射の同値性を仮定として置いていない。
この具体化だけでその射の同値性や K の完全忠実性を証明したとは数えない。
文脈は `A : Type u`、`[CommRing A]`。
`PinchedHom.pinchedHom` は既存の dg nerve の実 pinched Hom、`Basic.pinchedHom` は
既存の `TheHomotopyTheoryOfInfinityCategories.MorphismSpaces` のもの。
`Simplex.vertex` と `DifferentialGradedCategories.Functor.map` は既存の dg nerve の関手である。

### RawModuleProbeNativeHom

```lean
def strictRawModuleProbeNativeHomIso (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((strictRawModuleProbeDoldKanHom A X).obj (op P)).obj
        ((strictRawModuleProbeFunctor A X).obj Q)) ≅
      PinchedHom.pinchedHom A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q)

def strictRawModuleProbeTensorNativeHomIso (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((strictRawModuleProbeTensorHom A X).obj (op P)).obj
        ((strictRawModuleProbeFunctor A X).obj Q)) ≅
      PinchedHom.pinchedHom A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q)

lemma strictRawModuleProbeNativeHomIso_chainMap (X : (operad A).Algebra)
    (P Q P' Q' : strictRawModuleProbeCategory A X)
    (φ : homObject A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q) ⟶
        homObject A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
          (ForgetEnrichment.to (Complex A) P') (ForgetEnrichment.to (Complex A) Q')) :
    SSet.uliftFunctor.{u + 1, u}.map (doldKanHomSpaceChainMap
      (D := SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (E := SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (x := ForgetEnrichment.to (Complex A) P) (y := ForgetEnrichment.to (Complex A) Q)
      (x' := ForgetEnrichment.to (Complex A) P') (y' := ForgetEnrichment.to (Complex A) Q') φ) ≫
        (strictRawModuleProbeNativeHomIso A X P' Q').hom =
      (strictRawModuleProbeNativeHomIso A X P Q).hom ≫ pinchedHomChainMap φ
```

### RawModuleProbeComparisonMap

```lean
def strictRawModuleProbeRelativeFunctor (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (strictRawModuleRelativeCategory A X).category

def strictRawModuleProbeLocalizationVertex (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    (localizationNerve (strictRawModuleRelativeCategory A X)) _⦋0⦌

def strictRawModuleProbeSourceVertexIso (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    VertexIso
      ((strictRawModuleSource A X).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((strictRawModuleProbeRelativeFunctor A X).obj P)))
      (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A) P))

def strictRawModuleProbeComparisonVertexIso (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    VertexIso
      ((strictRawModuleComparison A X).app (op ⦋0⦌) (strictRawModuleProbeLocalizationVertex A X P))
      (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A) P))

def strictRawModuleProbeComparisonPinchedMap (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    Basic.pinchedHom (X := localizationNerve (strictRawModuleRelativeCategory A X))
      (strictRawModuleProbeLocalizationVertex A X P) (strictRawModuleProbeLocalizationVertex A X Q) ⟶
      PinchedHom.pinchedHom A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q)

def strictRawModuleProbeComparisonDoldKanMap (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    Basic.pinchedHom (X := localizationNerve (strictRawModuleRelativeCategory A X))
      (strictRawModuleProbeLocalizationVertex A X P) (strictRawModuleProbeLocalizationVertex A X Q) ⟶
      SSet.uliftFunctor.{u + 1, u}.obj
        (((strictRawModuleProbeDoldKanHom A X).obj (op P)).obj
          ((strictRawModuleProbeFunctor A X).obj Q))

lemma strictRawModuleProbeComparisonDoldKanMap_triangle (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    strictRawModuleProbeComparisonDoldKanMap A X P Q ≫ (strictRawModuleProbeNativeHomIso A X P Q).hom =
      strictRawModuleProbeComparisonPinchedMap A X P Q
```


対象ビルド・小さい監査の結果と最終実測は §37.1 に記録した。
未完の中心は、ここで具体化した同じ K の全誘導射が §35–§36 の実 frame 比較と一致することと、
その射の同値性・完全忠実性である。零単体・π₀ だけの一致で代用しない。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 37.1 検証と実測

RawModuleProbeNativeHom と RawModuleProbeComparisonMap の通常の対象ビルドは成功した。
新しい公開宣言 10 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。

新規 Lean は二ファイル、それぞれ 76・120 行、計 196 行、公開宣言 10 本。
§36.1 の累計に加え、検証済み累計は 73 ファイル・7,330 行・明示宣言 378 本
（private 3 本）。200 行を超える証明はない。一次 ID は追加していない。

同じ局所化比較 K の実 pinched Hom 射を、指定半自由端点と元の dg Hom の Dold–Kan 座標で
具体化し、元の射を全単体で回収する三角等式まで検証した。その射と実 frame 比較との
全高次照合・同値性・K の完全忠実性は未完。M10 の一般の native な辺・fiber と全族、
M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 38. M10 の元の probe 全通常 nerve 上の同じ三角比較（11-14）

§37 の頂点比較の元になっている同じ全解像度 retract を、probe の全通常 nerve へ前合成する。
通常相対圏と同じ Hom 宇宙を保つため、元の probe 閉零圏に同じ ULiftHom 表示を適用する。
元の全包含を関手として保持し、その全通常鎖を既存の `closedNerveSimplex` で指定半自由模型へ送る。

同じ dg 包含に関する `dgFunctor_closedNerveSimplex` の全次元自然性から、
全加群の元の dg 源と厳密に可換する全関手の等式を証明した。
その等式で、同じ `dgModuleResolutionRetractIso` の前合成を移送する。
さらに、同じ `strictRawModuleComparison_sourceIso` の前合成と合成し、
K の同じ三角比較を probe の全通常 nerve 上の同じ関手同型として保持する。

これは M10 の既存比較の係数移送・自然性・単位/余単位の貼り合わせの法則と証明の分割で、
一次 ID は追加しない。比較は元の全通常鎖の上にある。
frame 係数から作る全高次の評価円柱と同じ K の Hom 誘導射との照合は引き続き必要。
文脈は `A : Type u`、`[CommRing A]`。`DifferentialGradedCategories.Functor.map` は
既存の dg 関手の nerve。モデル構造や比較射の同値性を引数に置かない。

```lean
abbrev strictRawModuleLiftedProbeCategory (X : (operad A).Algebra) : Type (u + 1)

def strictRawModuleLiftedProbeFunctor (X : (operad A).Algebra) :
    strictRawModuleLiftedProbeCategory A X ⥤ (strictRawModuleRelativeCategory A X).category

def strictRawModuleLiftedProbeDGSource (X : (operad A).Algebra) :
    nerve (strictRawModuleLiftedProbeCategory A X) ⟶ strictModuleInfinity A X

lemma strictRawModuleLiftedProbeDGSource_inclusion (X : (operad A).Algebra) :
    nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫ strictRawModuleDGSource A X =
      strictRawModuleLiftedProbeDGSource A X ≫
        DifferentialGradedCategories.Functor.map
          (semifreeInclusion A (dgAlgebraCategory A ((assocForget A).obj X)))

def strictRawModuleLiftedProbeSourceIso (X : (operad A).Algebra) :
    FunctorIso
      (nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫ strictRawModuleSource A X)
      (strictRawModuleLiftedProbeDGSource A X)

def strictRawModuleLiftedProbeComparisonIso (X : (operad A).Algebra) :
    FunctorIso
      (nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫
        (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫
          strictRawModuleComparison A X))
      (strictRawModuleLiftedProbeDGSource A X)
```

対象ビルド・小さい監査の結果と最終実測は §38.1 に記録した。
K の同じ Hom 誘導射の同値性・完全忠実性、M10 の一般の native な辺・fiber と全族、
M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 38.1 検証と実測

RawModuleProbeSourceTriangle の通常の対象ビルドは成功した。
新しい公開宣言 6 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。

新規 Lean は一ファイル 113 行、公開宣言 6 本。
§37.1 の累計に加え、検証済み累計は 74 ファイル・7,443 行・明示宣言 384 本
（private 3 本）。200 行を超える証明はない。一次 ID は追加していない。

元の probe の同じ全通常 nerve に沿い、元の dg 源との厳密な包含等式、同じ解像度 retract
の全関手比較、同じ K の局所化三角の全関手比較まで検証した。
frame 係数からの実全高次評価円柱を、§37 の同じ K の Hom 誘導射へ結ぶ照合とその同値性は
引き続き未完であり、完全忠実性には数えない。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 39. M10 の全 frame 単体の同じ実評価図式と源内の屋根（11-14）

§35–§38 の同じテンソル frame Hom の反対要素圏を、元の相対圏と同じ
対象・射の宇宙へ持ち上げた。全単体と全作用素の次数射影、その射影で前合成した
元の加群 frame 図式、元の augmentation と実評価を保持する。
augmentation の各成分と図式の全作用素は、検証済みの元の擬同型である。
標的 Q は任意の元の通常 dg 加群であり、frame の各対象の半自由性は仮定しない。

通常加群図式とその自然変換の全 nerve 円柱を、元の同じ
`strictRawModuleSource` へ送る。各成分が擬同型なら、その同じ円柱の辺は
全関手圏で同型になる。元の辺と切断された辺の表示の照合は、小さい私有補題に分割した。
これは元の辺の可逆性の移送で、モデル構造や比較射の同値性を仮定に加えていない。

この同じ全 augmentation の逆と同じ実評価を合成して、指定模型内の全屋根を作る。
元の通常加群の指定された二つの頂点の定値図式へ端点を移し、元の全評価円柱を回収する
三角等式を保持する。単体ごとの π₀ の屋根への置換はしていない。
本節は M10 の既存比較の自然性・係数移送・単位/余単位の貼り合わせと証明の分割で、
一次 ID は追加しない。全宣言の型は以下のとおり。

`RawModuleTensorElementDiagram`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

abbrev strictRawModuleTensorElementIndex : Type (u + 1)

instance strictRawModuleTensorElementIndexCategory :
    Category.{u + 1} (strictRawModuleTensorElementIndex A X P Q)

def strictRawModuleTensorElementDegree :
    strictRawModuleTensorElementIndex A X P Q ⥤ SimplexCategory

def strictRawModuleTensorElementDiagram :
    strictRawModuleTensorElementIndex A X P Q ⥤ strictRawModuleCategory A X

def strictRawModuleTensorElementAugmentation :
    strictRawModuleTensorElementDiagram A X P Q ⟶
      (Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
        ((strictRawModuleProbeFunctor A X).obj P)

def strictRawModuleTensorElementEvaluation :
    strictRawModuleTensorElementDiagram A X P Q ⟶
      (Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj Q

lemma strictRawModuleTensorElementAugmentation_weak (s : strictRawModuleTensorElementIndex A X P Q) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleTensorElementAugmentation A X P Q).app s)

lemma strictRawModuleTensorElementDiagram_map_weak
    {s t : strictRawModuleTensorElementIndex A X P Q} (f : s ⟶ t) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleTensorElementDiagram A X P Q).map f)
```

`RawModuleDiagramSource`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  {I : Type (u + 1)} [Category.{u + 1} I]
  {F G : I ⥤ strictRawModuleCategory A X}

def strictRawModuleDiagramSource (F : I ⥤ strictRawModuleCategory A X) :
    nerve I ⟶ strictModuleInfinity A X

private lemma mappedNerveEdge_invertible {C : Type (u + 1)} [Category.{u + 1} C]
    {Y : SSet.{u + 1}} (F : nerve C ⟶ Y) {c d : C} (f : c ⟶ d)
    (h : IsInvertibleEdge (X := Y)
      ((edgeOfSimplex (ComposableArrows.mk₁ f)).map ((truncation 2).map F))) :
    IsInvertibleEdge (((nerve.edgeMk f).map F).toTruncated)

lemma strictRawModuleSource_edge_weak {M N : strictRawModuleCategory A X} (f : M ⟶ N)
    (hf : moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) f) :
    IsInvertibleEdge
      (((nerve.edgeMk ((ULiftHom.up.{u, u + 1, u + 1}
        (C := strictRawModuleCategory A X)).map f)).map (strictRawModuleSource A X)).toTruncated)

def strictRawModuleDiagramNatTransHomotopy (η : F ⟶ G) :
    SSet.Homotopy (strictRawModuleDiagramSource A X F) (strictRawModuleDiagramSource A X G)

lemma strictRawModuleDiagramNatTransHomotopy_component (η : F ⟶ G) (i : I) :
    (simplicialHomotopyVertexEdge (strictRawModuleDiagramNatTransHomotopy A X η)
      (nerveVertex i)).edge =
    ((nerve.edgeMk ((ULiftHom.up.{u, u + 1, u + 1}
      (C := strictRawModuleCategory A X)).map (η.app i))).map (strictRawModuleSource A X)).edge

def strictRawModuleDiagramNatTransHom (η : F ⟶ G) :
    FunctorHom (strictRawModuleDiagramSource A X F) (strictRawModuleDiagramSource A X G)

def strictRawModuleDiagramNatTransIso (η : F ⟶ G)
    (hη : ∀ i, moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) (η.app i)) :
    FunctorIso (strictRawModuleDiagramSource A X F) (strictRawModuleDiagramSource A X G)

lemma strictRawModuleDiagramNatTransIso_hom (η : F ⟶ G)
    (hη : ∀ i, moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) (η.app i)) :
    (strictRawModuleDiagramNatTransIso A X η hη).hom =
      strictRawModuleDiagramNatTransHom A X η

lemma strictRawModuleDiagramSource_const (M : strictRawModuleCategory A X) :
    strictRawModuleDiagramSource A X ((Functor.const I).obj M) =
      SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1}
          (C := strictRawModuleCategory A X)).obj M)))

def strictRawModuleDiagramSourceConstantIso (M : strictRawModuleCategory A X) :
    FunctorIso (strictRawModuleDiagramSource A X ((Functor.const I).obj M))
      (SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1}
          (C := strictRawModuleCategory A X)).obj M))))
```

`RawModuleTensorElementSourceRoof`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementSourceAugmentationIso :
    FunctorIso
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q))
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
          ((strictRawModuleProbeFunctor A X).obj P)))

def strictRawModuleTensorElementSourceEvaluation :
    FunctorHom
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q))
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj Q))

def strictRawModuleTensorElementSourceRoof :
    FunctorHom
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
          ((strictRawModuleProbeFunctor A X).obj P)))
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj Q))

lemma strictRawModuleTensorElementSourceRoof_triangle :
    (strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom ≫
      strictRawModuleTensorElementSourceRoof A X P Q =
        strictRawModuleTensorElementSourceEvaluation A X P Q

def strictRawModuleTensorElementSourceRoofFamily :
    ConstantFunctorHom (nerve (strictRawModuleTensorElementIndex A X P Q)) (strictModuleInfinity A X)
      ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj
          ((strictRawModuleProbeFunctor A X).obj P))))
      ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj Q)))

lemma strictRawModuleTensorElementSourceRoofFamily_triangle :
    ((strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom ≫
      (strictRawModuleDiagramSourceConstantIso A X (I := strictRawModuleTensorElementIndex A X P Q)
        ((strictRawModuleProbeFunctor A X).obj P)).hom) ≫
          strictRawModuleTensorElementSourceRoofFamily A X P Q =
      strictRawModuleTensorElementSourceEvaluation A X P Q ≫
        (strictRawModuleDiagramSourceConstantIso A X (I := strictRawModuleTensorElementIndex A X P Q) Q).hom
```

対象ビルド・小さい監査の結果と実測は §39.1 に記録した。
同じ K の実 Hom 誘導射と、この全評価屋根を結ぶ正規化 dg 係数の全高次照合、
その射の同値性・K の完全忠実性は引き続き未完。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 39.1 検証と実測

RawModuleTensorElementDiagram・RawModuleDiagramSource・RawModuleTensorElementSourceRoof
の通常の対象ビルドは成功した。新しい公開宣言 23 本の依存公理監査も成功し、
propext・Classical.choice・Quot.sound の範囲である。
指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は三ファイル、それぞれ 99・146・107 行、計 352 行、明示宣言 24 本
（private 1 本、名前つき instance 1 本を含む）。§38.1 の累計に加え、
検証済み累計は 77 ファイル・7,795 行・明示宣言 408 本（private 4 本）。
200 行を超える証明はない。一次 ID は追加していない。

元の全 frame Hom の要素圏、同じ全 augmentation と実評価、同じ源の全円柱と
その反転、指定定値端点への屋根と三角式まで検証した。
同じ K の実 Hom 誘導射との全高次照合・同値性・完全忠実性は未完であり、
M10 完了には数えない。M10 の一般の native な辺・fiber と全族、M11 以降、
G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 40. M10 の同じ普遍 dg Hom 族と全要素列の再添字（11-14）

§39 の全評価屋根に対して、元の tensor/Hom 同型の係数を保つ全普遍評価族を具体化する。
元の frame 射を Yoneda 同値で同じ代表可能族へ送り、§36 の同じ二変数 Dold–Kan 同型を
後合成する。標的射との後合成則、全単体作用素との再添字則を保持し、元の恒等射を
代入した普遍族の評価式と全作用素自然性を得る。

その普遍族を、同じ反対要素圏の全通常単体列の終端パラメータで前合成する。
元の評価自然変換の終端成分との合成式を保持する。
再添字は終端を変える作用素も含み、列の元の末尾射による dg Hom の作用と厳密に整合する。
frame の係数加群を半自由と仮定せず、元の全通常 dg 加群圏内で構成する。

本節は M10 の既存 tensor/Hom 構成の自然性・係数移送・恒等・合成則と証明の分割であり、
一次 ID は追加しない。全宣言の型は以下のとおり。

`TensorHomUniversal.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleTensorHomRepresentable (P N : ModuleCategory A D) (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    stdSimplex.obj n ⟶ (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).obj N

lemma moduleTensorHomRepresentable_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) (h : N ⟶ N') :
    moduleTensorHomRepresentable A D P N n g ≫
      (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).map h =
        moduleTensorHomRepresentable A D P N' n (g ≫ h)

lemma moduleTensorHomRepresentable_reindex (P N : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj m ⟶ N) :
    stdSimplex.map f ≫ moduleTensorHomRepresentable A D P N m g =
      moduleTensorHomRepresentable A D P N n
        (((moduleTensorSimplicesFunctor A D).obj P).map f ≫ g)

def moduleTensorHomDoldKanSimplex (P N : ModuleCategory A D) (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    stdSimplex.obj n ⟶ ((moduleDoldKanHomBifunctor A D).obj (op P)).obj N

lemma moduleTensorHomDoldKanSimplex_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) (h : N ⟶ N') :
    moduleTensorHomDoldKanSimplex A D P N n g ≫
      ((moduleDoldKanHomBifunctor A D).obj (op P)).map h =
        moduleTensorHomDoldKanSimplex A D P N' n (g ≫ h)

lemma moduleTensorHomDoldKanSimplex_reindex (P N : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj m ⟶ N) :
    stdSimplex.map f ≫ moduleTensorHomDoldKanSimplex A D P N m g =
      moduleTensorHomDoldKanSimplex A D P N n
        (((moduleTensorSimplicesFunctor A D).obj P).map f ≫ g)

def moduleTensorUniversalDoldKanSimplex (P : ModuleCategory A D) (n : SimplexCategory) :
    stdSimplex.obj n ⟶ ((moduleDoldKanHomBifunctor A D).obj (op P)).obj
      (((moduleTensorSimplicesFunctor A D).obj P).obj n)

lemma moduleTensorUniversalDoldKanSimplex_evaluation (P N : ModuleCategory A D)
    (n : SimplexCategory) (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    moduleTensorUniversalDoldKanSimplex A D P n ≫
      ((moduleDoldKanHomBifunctor A D).obj (op P)).map g =
        moduleTensorHomDoldKanSimplex A D P N n g

lemma moduleTensorUniversalDoldKanSimplex_naturality (P : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m) :
    stdSimplex.map f ≫ moduleTensorUniversalDoldKanSimplex A D P m =
      moduleTensorUniversalDoldKanSimplex A D P n ≫
        ((moduleDoldKanHomBifunctor A D).obj (op P)).map
          (((moduleTensorSimplicesFunctor A D).obj P).map f)
```

`RawModuleTensorElementUniversal.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

abbrev strictRawModuleTensorElementTerminalParameter {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ⦋n⦌ ⟶ (strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n))

def strictRawModuleTensorElementUniversalFamily {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    SSet.stdSimplex.obj ⦋n⦌ ⟶
      ((strictRawModuleProbeDoldKanHom A X).obj (op P)).obj
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))

lemma strictRawModuleTensorElementUniversalFamily_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementUniversalFamily A X P Q c ≫
      ((strictRawModuleProbeDoldKanHom A X).obj (op P)).map
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))) =
    SSet.stdSimplex.map (strictRawModuleTensorElementTerminalParameter A X P Q c) ≫
      moduleTensorHomDoldKanSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P) Q
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))

lemma strictRawModuleTensorElementUniversalFamily_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.stdSimplex.map θ ≫ strictRawModuleTensorElementUniversalFamily A X P Q c =
      strictRawModuleTensorElementUniversalFamily A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      ((strictRawModuleProbeDoldKanHom A X).obj (op P)).map
        ((strictRawModuleTensorElementDiagram A X P Q).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))
```

対象ビルド・小さい監査の結果と実測は §40.1 に記録した。
ここでは全高次の普遍評価とその自然性を保持するが、元の dg nerve の全 cone/prism 方程式、
§39 の同じ屋根との比較、同じ K の実 Hom 誘導射の同値性・完全忠実性は未完である。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 40.1 検証と実測

TensorHomUniversal・RawModuleTensorElementUniversal の通常の対象ビルドは成功した。
新しい公開宣言 13 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は二ファイル、それぞれ 128・96 行、計 224 行、公開宣言 13 本。
§39.1 の累計に加え、検証済み累計は 79 ファイル・8,019 行・明示宣言 421 本
（private 4 本）。200 行を超える証明はない。一次 ID は追加していない。

同じ tensor/Hom 二関手の元の射からの全代表可能族、全後合成・再添字、
恒等射による普遍族と全評価、同じ全要素列の終端パラメータによる前合成、
終端を変える作用素も含む再添字式まで検証した。
次はこの同じ全族を元の全通常 dg 加群の pinched Hom の線形成分へ送り、
元の dg nerve 内の全 cone/prism と同じ実評価屋根を照合する。
既存の `doldKanHomPinchedIso`・任意 Hom 鎖写像への自然性・
`SimplexTerminalParameter.reindex` と一般の単射方程式移送を使う。
ComplexLimits の既存ファイルは読み取りだけに留め、既存の構成を置き換えない。

同じ K の実 Hom 誘導射の全高次照合・同値性・完全忠実性、M10 の一般の native な辺・fiber と
全族は未完。M11 以降と G12 の元の目標を維持し、約 8,500 行での途中見積りを予定する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 41. M10 の元の全 pinched 評価・線形成分・選択 cochain（11-14）

§40 の同じ実 Dold–Kan 族を、元の全通常 dg 加群の dg nerve の pinched Hom へ移す。
既存の `doldKanHomPinchedIso` と任意 Hom 鎖写像への自然性を使い、
同じ標的加群射による後合成、全単体作用素、恒等射による普遍族と実評価を保持する。
係数 dg 圏の対象宇宙 v と環の宇宙 u を区別し、実加群対象宇宙
`max (u + 1) v` へ持ち上げる。BE の一対象 dg 圏では v = 0 である。
係数加群の半自由性も比較射の同値性も、引数の仮定に加えない。

同じ全要素列の終端パラメータで普遍 pinched 族を前合成し、実評価・全再添字を保つ。
同じ恒等単体で評価した実単体を、既存の `PinchedHom.toLinearSimplex` で元の線形成分へ送る。
全有限部分集合・正しい次数の微分方程式、終端を変える全作用素の線形再添字、
単射による像部分集合の成分式、非単射による退化成分の零を保持する。

元の有限部分集合を昇順に選び、同じ制限列の最上位 cochain を取る。
元の末尾射で送ると元の部分集合の成分に戻ることを同じ単射再添字式で照合し、
同じ最大元への型の移送を保持する。
これは M10 の既存比較の係数移送・自然性・恒等・合成則と証明の分割で、一次 ID は追加しない。
各証明は 200 行以下。全宣言の型は以下のとおり。

`TensorHomPinched.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDoldKanPinchedIso (P N : ModuleCategory A D) :
    SSet.uliftFunctor.{max (u + 1) v, u}.obj
      (((moduleDoldKanHomBifunctor A D).obj (op P)).obj N) ≅
    PinchedHom.pinchedHom A (RightModule A D)
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)

lemma moduleDoldKanPinchedIso_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (h : N ⟶ N') :
    SSet.uliftFunctor.{max (u + 1) v, u}.map
      (((moduleDoldKanHomBifunctor A D).obj (op P)).map h) ≫
        (moduleDoldKanPinchedIso A D P N').hom =
    (moduleDoldKanPinchedIso A D P N).hom ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P h)

def moduleTensorHomPinchedSimplex (P N : ModuleCategory A D) (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    SSet.uliftFunctor.{max (u + 1) v, u}.obj (SSet.stdSimplex.obj n) ⟶
    PinchedHom.pinchedHom A (RightModule A D)
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)

lemma moduleTensorHomPinchedSimplex_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) (h : N ⟶ N') :
    moduleTensorHomPinchedSimplex A D P N n g ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P h) =
        moduleTensorHomPinchedSimplex A D P N' n (g ≫ h)

lemma moduleTensorHomPinchedSimplex_reindex (P N : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj m ⟶ N) :
    SSet.uliftFunctor.{max (u + 1) v, u}.map (SSet.stdSimplex.map f) ≫
      moduleTensorHomPinchedSimplex A D P N m g =
    moduleTensorHomPinchedSimplex A D P N n
      (((moduleTensorSimplicesFunctor A D).obj P).map f ≫ g)

def moduleTensorUniversalPinchedSimplex (P : ModuleCategory A D) (n : SimplexCategory) :
    SSet.uliftFunctor.{max (u + 1) v, u}.obj (SSet.stdSimplex.obj n) ⟶
    PinchedHom.pinchedHom A (RightModule A D) (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) (((moduleTensorSimplicesFunctor A D).obj P).obj n))

lemma moduleTensorUniversalPinchedSimplex_evaluation (P N : ModuleCategory A D)
    (n : SimplexCategory) (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P g) =
        moduleTensorHomPinchedSimplex A D P N n g

lemma moduleTensorUniversalPinchedSimplex_naturality (P : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.uliftFunctor.{max (u + 1) v, u}.map (SSet.stdSimplex.map f) ≫
      moduleTensorUniversalPinchedSimplex A D P m =
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P
        (((moduleTensorSimplicesFunctor A D).obj P).map f))
```

`RawModuleTensorElementPinched.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementPinchedFamily {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A)
          ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n))))

lemma strictRawModuleTensorElementPinchedFamily_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementPinchedFamily A X P Q c ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))) =
    SSet.uliftFunctor.{u + 1, u}.map
      (SSet.stdSimplex.map (strictRawModuleTensorElementTerminalParameter A X P Q c)) ≫
      moduleTensorHomPinchedSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P) Q
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))

lemma strictRawModuleTensorElementPinchedFamily_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map θ) ≫
      strictRawModuleTensorElementPinchedFamily A X P Q c =
    strictRawModuleTensorElementPinchedFamily A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
    pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))

def strictRawModuleTensorElementPinchedSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n))))) _⦋n⦌

lemma strictRawModuleTensorElementPinchedSimplex_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n))))).map θ.op
      (strictRawModuleTensorElementPinchedSimplex A X P Q c) =
    (pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))).app (op ⦋m⦌)
      (strictRawModuleTensorElementPinchedSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c))
```

`RawModuleTensorElementLinear.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementLinear {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    LinearSimplex A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))) n

lemma strictRawModuleTensorElementLinear_equation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    differential A ((strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk) =
      (strictRawModuleTensorElementLinear A X P Q c).val.rhs J k hk

lemma strictRawModuleTensorElementLinear_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    LinearSimplex.pullback θ.toOrderHom (strictRawModuleTensorElementLinear A X P Q c) =
    pinchedLinearSimplexMap
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementDiagram A X P Q).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))
      (strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c))

lemma strictRawModuleTensorElementLinear_component_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) =
    LinearData.component (pullback θ.toOrderHom
      (strictRawModuleTensorElementLinear A X P Q c).val) J k hJ hk

lemma strictRawModuleTensorElementLinear_component_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) =
    (strictRawModuleTensorElementLinear A X P Q c).val.component (J.image θ.toOrderHom) k
      (hJ.image θ.toOrderHom) (by rw [Finset.card_image_of_injOn hi]; exact hk)

lemma strictRawModuleTensorElementLinear_component_not_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : ¬ Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) = 0
```

`RawModuleTensorElementSelected.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

abbrev strictRawModuleTensorElementSelection {n : ℕ} (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) : ⦋J.card - 1⦌ ⟶ ⦋n⦌

lemma strictRawModuleTensorElementSelection_last {n : ℕ} (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) :
    (strictRawModuleTensorElementSelection J hJ).toOrderHom (Fin.last (J.card - 1)) =
      J.max' hJ

def strictRawModuleTensorElementSelectedCochain {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj
        (c.obj ((strictRawModuleTensorElementSelection J hJ).toOrderHom
          (Fin.last (J.card - 1)))))) k

lemma strictRawModuleTensorElementSelectedCochain_image {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last ((strictRawModuleTensorElementSelection J hJ).toOrderHom
          (Fin.last (J.card - 1)))))))).f k
      (strictRawModuleTensorElementSelectedCochain A X P Q c J k hJ hk) =
    (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk

def strictRawModuleTensorElementSelectedCochainAtMax {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (J.max' hJ)))) k
```

対象ビルド・小さい監査の結果と実測は §41.1 に記録した。
同じ全 cochain を元の dg nerve の cone/prism へ組み立てる全方程式、元の全評価屋根との
三角比較、同じ K の Hom 誘導射の同値性・完全忠実性はまだ完了としていない。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 41.1 検証と実測

TensorHomPinched・RawModuleTensorElementPinched・RawModuleTensorElementLinear・
RawModuleTensorElementSelected の通常の対象ビルドは成功した。
新しい公開宣言 24 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は四ファイル、それぞれ 126・134・124・97 行、計 481 行、公開宣言 24 本。
§40.1 の累計に加え、検証済み累計は 83 ファイル・8,500 行・明示宣言 445 本
（private 4 本）。200 行を超える証明はない。一次 ID は追加していない。
全係数の pinched Hom の同じ実評価、全再添字、線形成分・全微分方程式、
単射/非単射の成分式、選択した cochain と元の最大元への移送を検証した。

同じ全 cone/prism と元の屋根の比較、同じ K の実 Hom 射の同値性・完全忠実性、
指定 fiber・一般の native な辺と全族は未完。M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 42. 約 8,500 行の途中報告と残作業の見積り更新（11-14）

ユーザーの「約 8,500 行で止まらずに途中報告」に従う。
§41 の四ファイルは通常の対象ビルドが通過し、§40.1 の 8,019 行に 481 行を加えると
新設 Lean は 83 ファイル・8,500 行となる。既存の対象を変更した差分を別に隠す数え方はせず、
現作業木の M15 所有ソースも同じ合計になることを確認した。
小さい監査も成功し、確定結果は §41.1 に記録した。

M01–M09 と追加 N01 が完了。M19 の共通 IsThick の芯とその閉包の法則は作成済みだが、
同じ native 相対テンソルへの接続が残るため M19 完了には数えない。
M10 は全圏・通常の全評価・厳密制限と随伴・同じ局所化比較 K、実モデル構造、
frame 比較、元の dg Hom の全自然な同定を進めた段階である。
元の K の完全忠実性、指定 native fiber、一般の底の辺の輸送と全族の検収は未完。

段 0 の M06–M10 の 1,000〜1,800 行は、そのまま完成見込みに流用できない。
実際の projective モデル構造 N01、異なる模型の Hom 比較、同じ誘導射との全高次の
照合を個々に検収する費用が必要だった。以下は現時点の残りの**暫定作業見積り**であり、
未実装の定理の存在や上端以内の完成を保証するものではない。
M10 の幅は既存 FrameHom と一般の線形・方程式移送 API の再利用を前提とする。

| 残りの束 | 追加行数の下端 | 追加行数の上端 | 未完の主な検収 |
| --- | ---: | ---: | --- |
| M10 | 1,500 | 3,000 | 同じ全 cone/prism と K の Hom 射の照合、完全忠実性、fiber と一般輸送・全族 |
| M11–M15 | 1,800 | 2,800 | 同じ fiber の対称 operadic 相対テンソル、全構造・完全性・底変換 |
| M16–M20 | 450 | 850 | 指定単位辺と fiber・指数射、単位底比較、共通 thick との接続 |
| M21–M27 | 900 | 1,500 | 指数判定・底変換・合成・テンソル |
| M28–M30 | 600 | 1,000 | Amitsur 塔と同じ指定増大の降下 |
| M31–M35 | 500 | 800 | 同じ RHom 全関手・評価・指数二判定 |
| M36–M42 | 700 | 1,200 | 実際の完備反射・完備テンソルと同じ評価・利用側接続 |
| **残り合計** | **6,450** | **11,150** | |
| **8,500 行との合計** | **14,950** | **19,650** | |

したがって外枠 17,000 行以内の完成は、現時点では確証がない。
外枠を変更せず、既存構成の再利用と法則の共通化を進める。
Ho や離散な対象族への弱化、モデル構造・完備反射の仮定化、任意 E への範囲拡大はしない。
今回の途中報告点では停止せず、新しい一次構成・新しい定理・まとまりの外への拡張が必要に
なった時、または実際に外枠へ達した時に、共通規則どおり報告して止まる。
G12 は M15 完成後の元の段 0 と検収条件を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 43. M10 の同じ通常単体と高次 cochain の接合（11-14）

§42 の途中報告後も元の目標を継続する。
同じ全要素列の先端に元の probe を前置し、後続頂点は元の通常加群 frame 対象とする。
元の末尾単調写像は ComplexLimits の既存 `coneTailOrderHom` を再利用し、
その後の同じ通常図式を `closedNerveSimplex` で元の全通常 dg 加群の dg nerve へ送る。

この同じ通常単体と、§41 の選択した高次 cochain を接合した `SimplexData` を作った。
先端を含む成分には同じ次数の `k.negOnePow` と同じ最大元への型移送を適用する。
先端を含まない成分は元の通常単体の同じ成分とする。
`withoutFirst`・濃度・最大元の各有限集合補題は既存 ComplexLimits のものを再利用し、
それらのファイルは変更していない。

ここで得たものは元の全 cone の**データ**であり、HA の全方程式を持つ `Simplex` や
全 cone/prism とはまだ主張しない。方程式を引数の仮定に加えていない。
本節も M10 の同じ比較の係数移送・通常成分との貼り合わせと証明の分割で、一次 ID は追加しない。
全宣言の型は以下のとおり。

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeObj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Fin (n + 2) → RightModule A (dgAlgebraCategory A ((assocForget A).obj X))

lemma strictRawModuleTensorConeObj_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorConeObj A X P Q c 0 =
      ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)

lemma strictRawModuleTensorConeObj_succ {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    strictRawModuleTensorConeObj A X P Q c i.succ =
      ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i))

lemma strictRawModuleTensorConeObj_ne_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    strictRawModuleTensorConeObj A X P Q c i =
      ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (coneTailOrderHom n i)))

def strictRawModuleTensorConeOrdinarySimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1)

lemma strictRawModuleTensorConeOrdinarySimplex_obj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 2)) :
    (strictRawModuleTensorConeOrdinarySimplex A X P Q c).obj i =
      ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (coneTailOrderHom n i)))

def strictRawModuleTensorConeData {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1)
```

対象ビルドと小さい監査の結果は §43.1 に記録した。
元の全 HA 方程式・全作用素での自然性、元の全屋根と同じ K の Hom 射への照合は引き続き必要。
M10 の完全忠実性・指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 43.1 検証と実測

RawModuleTensorConeData の通常の対象ビルドは成功した。
新しい公開宣言 7 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は一ファイル 119 行、公開宣言 7 本。
§41.1 の累計に加え、検証済み累計は 84 ファイル・8,619 行・明示宣言 452 本
（private 4 本）。200 行を超える証明はない。一次 ID は追加していない。
§42 の 8,500 行の途中報告後も実装を継続した。

同じ全通常成分と符号つき高次 cochain の接合データ・元の端点の型の移送を検証した。
次は元の混合/通常成分の式、単射制限、全 HA 方程式と全作用素自然性を検証する。
完全な cone/prism、同じ屋根と K の実 Hom 射の照合、その同値性・完全忠実性、
指定 fiber・一般の native な辺と全族はまだ未完。
M11 以降と G12 の元の目標、17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 44. M10 の同じ cone の通常成分と全二点の HA 方程式（11-14）

§43 の同じ生データの通常成分・混合成分を、元の通常単体と符号つき選択 cochain へ戻す
異種等号を保持する。始点を除く面の全成分を同じ通常単体へ照合し、既存の一般の
`SimplexData.equation_image_of_pullback` によって、始点を含まない**任意の有限部分集合**の
全 HA 方程式を元のデータへ戻す。

一点を選ぶ元の最上位 cochain は、同じ線形単体の微分方程式から閉零元である。
元の最大元への型の移送は同じ微分と整合する。その閉性を元の混合辺へ移し、
通常の辺は元の面で検証することで、同じ cone データの**全ての二点集合**の HA 方程式を得る。
次数が零になることは元の濃度二の条件から導く。

これは M10 の同じ構成の成分式・通常成分との貼り合わせ・係数移送と証明の分割である。
一次 ID は追加しない。先端を含む三点以上の集合の方程式、全 cone/prism の全作用素自然性、
元の屋根と K の Hom 射の全高次比較はまだ未完。
全宣言の型は以下のとおり。

`RawModuleTensorConeComponents`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_ordinary {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeOrdinarySimplex A X P Q c).toSimplexData.hom I a b k hI ha hb hk)

lemma strictRawModuleTensorConeData_hom_mixed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk)
      (k.negOnePow • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c (withoutFirst I) k
        (withoutFirst_nonempty hI h0) (by have := card_withoutFirst I h0; omega))
```

`RawModuleTensorConeTail`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_tail {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeData A X P Q c).pullback (Fin.succOrderEmb (n + 1)).toOrderHom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (c ⋙ strictRawModuleTensorElementDiagram A X P Q)).toSimplexData
```

`RawModuleTensorConeTailEquation`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_equation_without_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (h0 : (0 : Fin (n + 2)) ∉ I) :
    (strictRawModuleTensorConeData A X P Q c).Equation I
```

`RawModuleTensorSelectedClosed`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochain_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (strictRawModuleTensorElementSelectedCochain A X P Q c J 0 hJ (by omega)) = 0

lemma strictRawModuleTensorElementSelectedCochainAtMax_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J 0 hJ (by omega)) =
      0
```

`RawModuleTensorConePairEquation`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_equation_pair {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (hc : I.card = 2) :
    (strictRawModuleTensorConeData A X P Q c).Equation I
```

対象ビルドと小さい監査の確定結果・実測は §44.1 に記録した。
M10 の完全忠実性・指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 44.1 検証と実測

RawModuleTensorConeComponents・RawModuleTensorConeTail・RawModuleTensorConeTailEquation・
RawModuleTensorSelectedClosed・RawModuleTensorConePairEquation の通常の対象ビルドは成功した。
新しい公開宣言 7 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は五ファイル、それぞれ 45・51・35・55・55 行、計 241 行、公開宣言 7 本。
§43.1 の累計に加え、検証済み累計は 89 ファイル・8,860 行・明示宣言 459 本
（private 4 本）。200 行を超える証明はない。一次 ID は追加していない。

元の接合データの両成分の式、始点を除く面の全成分一致、始点を含まない任意集合の方程式、
一点選択 cochain の閉性と元の型移送、全二点集合の方程式まで検証した。
残る正次混合成分・全 cone/prism・同じ屋根と K の Hom 射への照合、完全忠実性、
指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標は未完。

**一覧：済み 10／全体 43（うち追加 1）**。


## 45. M10 の選択 cochain の像と同じ全 cone データの単射制限（11-14）

§44 の通常成分と二点の方程式に続き、任意終端への制限で元の方程式を戻すため、
同じ全 cone データと始点つき単射 pullback の一致を検証する。

まず、元の選択 cochain を濃度の等式と明示次数で表し直し、元の表示に厳密に戻す。
既存の有限集合の列挙 `normalizedTensorElementSelectionOfCard` と、その終端・像の法則を
再利用する。同じ列の最上位 cochain であることから、順序埋め込みの像を選んだ成分と
制限列の元の成分を異種等号で照合し、元の次数符号の作用も保持する。
frame 射の後合成の単射性を仮定して逆推論するものではない。

同じ cone の全対象は、始点つき単射の制限と厳密に一致する。
通常零次成分を元の frame 射の閉零元へ戻し、高次の通常成分は元の閉 nerve の消滅式で零とする。
混合成分は同じ選択 cochain の像の式を使い、通常零次成分は同じ元の辺を、
高次通常成分は同じ零成分を比較する。これらの全成分を従属関数の外延性でまとめ、
全 `SimplexData` の単射 pullback と元の制限列のデータの一致を得る。

本節は M10 の同じ構成の係数移送・再添字・成分の貼り合わせと証明の分割であり、
一次 ID は追加しない。全作用素のうち非単射の全 cone データの整合性と、
始点を含む三点以上の集合の HA 方程式は引き続き別に検証する。
全宣言の型は以下のとおり。

`RawModuleTensorSelectedCard`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementSelectedCochainAtMaxOfCard {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (J.max' hJ)))) k

lemma strictRawModuleTensorElementSelectedCochainAtMax_eq_ofCard {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk =
      strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk (J.card - 1)
        (by have := Finset.card_pos.mpr hJ; omega)

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_congr {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r s : ℕ) (hrs : r = s) (hr : J.card = r + 1) (hs : J.card = s + 1) :
    strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk r hr =
      strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk s hs

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_raw {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk r hc)
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map
          (normalizedTensorElementSelectionOfCard J r hc)).toFunctor ⋙ c)).val.component
            Finset.univ k Finset.univ_nonempty
            (by simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk))
```

`RawModuleTensorSelectedCardImage`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_image {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c (J.image e) k (hJ.image e)
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hk) r
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hc))
      (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
        J k hJ hk r hc)
```

`RawModuleTensorSelectedImageReindex`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c (J.image e) k (hJ.image e)
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hk))
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
        J k hJ hk)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image_reindex_smul {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (r : ℤˣ) :
    HEq (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c (J.image e) k (hJ.image e)
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hk))
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
        J k hJ hk)
```

`RawModuleTensorConePrependObjects`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_obj_prepend {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (i : Fin (m + 2)) :
    (strictRawModuleTensorConeData A X P Q c).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom i) =
      (strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map
          (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).obj i
```

`RawModuleTensorConeOrdinaryClosed`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_ordinary_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) (hab : a ≤ b) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b 0 hI ha hb hk)
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementDiagram A X P Q).map
          (c.map (homOfLE ((coneTailOrderHom n).monotone hab))))).val
```

`RawModuleTensorConeOrdinaryZero`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_ordinary_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) (hc : I.card ≠ 2) :
    (strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk = 0
```

`RawModuleTensorConeOrdinaryPullbackZero`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_ordinary_zero {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)).hom I a b 0 hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).hom
          I a b 0 hI ha hb hk)
```

`RawModuleTensorConeMixedPullback`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_mixed {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).hom
          I a b k hI ha hb hk)
```

`RawModuleTensorConeOrdinaryPullback`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_ordinary {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).hom
          I a b k hI ha hb hk)
```

`RawModuleTensorConeInjectivePullback`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_injective {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (strictRawModuleTensorConeData A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) =
      strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
```

対象ビルド・小さい監査の結果と実測は §45.1 に記録した。
M10 の元の屋根と同じ K の実 Hom 射への全高次照合、同値性・完全忠実性、指定 fiber、
一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 45.1 検証と実測

RawModuleTensorSelectedCard・RawModuleTensorSelectedCardImage・RawModuleTensorSelectedImageReindex・
RawModuleTensorConePrependObjects・RawModuleTensorConeOrdinaryClosed・RawModuleTensorConeOrdinaryZero・
RawModuleTensorConeOrdinaryPullbackZero・RawModuleTensorConeMixedPullback・
RawModuleTensorConeOrdinaryPullback・RawModuleTensorConeInjectivePullback の通常の対象ビルドは成功した。
新しい公開宣言 14 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は十ファイル、それぞれ 66・61・69・35・35・46・69・77・64・60 行、
計 582 行、公開宣言 14 本。§44.1 の累計に加え、検証済み累計は
99 ファイル・9,442 行・明示宣言 473 本（private 4 本）。
200 行を超える証明はない。一次 ID は追加していない。

同じ選択 cochain の濃度による表示・元の表示との厳密一致・像の選択との異種等号・
元の次数符号の作用、全 cone データの対象と混合/通常成分の単射制限、
全データの単射 pullback 一致を検証した。
元の通常辺を閉零射へ戻す段でも、同じ加群射を保持している。
frame 射の作用の単射性は使っていない。

次は先端と終端を含む三点以上の集合の微分・全削除和・最後の切断合成を、
同じ全普遍線形 cochain の方程式へ照合する。一般の dg 閉後合成の全次数式
`dgClosedPostcomposition_f` は既存の `eHomWhiskerLeft` の成分式そのものであり、
複体専用の `homPostcompose` の再構成は不要と確認した。
その後、単射制限によって任意の終端の集合へ戻し、非単射作用素との全整合性を検証する。

全 HA 方程式・全 cone/prism・同じ屋根と K の実 Hom 射への照合、その同値性・完全忠実性、
指定 fiber・一般の native な辺と全族はまだ未完。
M11 以降と G12 の元の目標、17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 46. M10 の全 HA 方程式と元の実 cone 単体（11-14）

§45 の同じ接合データについて、先端と終端を含む任意の有限部分集合の HA 方程式を閉じる。
まず同じ選択 cochain を元の末尾射で送った像を回収し、終端まで届く選択は
同じ元の普遍 cochain の成分そのものであることを、同じ次数符号の作用まで照合する。
これにより混合成分とその微分を元の線形成分・同じ微分方程式の右辺へ戻す。

同じ通常側の切断集合が二点でないときは、元の通常高次成分が零なので切断合成は零になる。
元の全非線形和の支持を最後から二番目の内部点に絞り、最後の実切断合成を計算する。
閉零射の実合成は既存の一般 dg 閉後合成の全次数式 `dgClosedPostcomposition_f` により
同じ `eHomWhiskerLeft` の成分へ戻す。元の Hom end の後合成と符号作用を保ち、
同じ最後の削除成分を回収する。

全内部削除和へこの最後の切断成分を足すと、元の全普遍線形 cochain の右辺になる。
符号つき同じ微分の式と照合して、終端を含む全ての集合の方程式を得る。
任意終端の集合は、元の昇順選択列と §45 の同じ単射 pullback を使って戻す。
ここで一般の dg 単体データについて、指定集合の方程式だけを同じ単射に沿って移す証明を
私有補題に分割した。方程式を仮定した外部の Setup や追加公理は導入しない。

結果として元の `strictRawModuleTensorConeData` は**全有限部分集合・全次数の HA 方程式**を持つ。
同じデータとその方程式から `Simplex` を作り、元のデータとの厳密な一致、
全単射制限の一致、始点を除く面と元の全通常単体の一致を保持する。
非単射を含む全作用素への自然性と大域 cone/prism の束ねは次に検証する。

本節も M10 の同じ構成の微分・合成・符号・係数移送・成分の貼り合わせと証明の分割で、
一次 ID は追加しない。全宣言の型は以下のとおり。

`ClosedPostcomposition.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma modulePostcompose_graded (M : ModuleCategory A D) {P Q : ModuleCategory A D}
    (f : P ⟶ Q) (k : ℤ)
    (v : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) k) :
    compose A (closedHomEquiv A (RightModule A D) _ _ f).val v (add_zero k) =
      (eHomWhiskerLeft (Complex A) M f).f k v
```

`RawModuleTensorSelectedAtMaxImage.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementDiagram A X P Q).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) =
    (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk
```

`RawModuleTensorSelectedTerminal.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_terminal {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hm : J.max' hJ = Fin.last n) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk)
      ((strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk)

lemma strictRawModuleTensorElementSelectedCochainAtMax_terminal_smul {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hm : J.max' hJ = Fin.last n) (r : ℤˣ) :
    HEq (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk)
      (r • (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk)
```

`RawModuleTensorConeMixedLast.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk)
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        (withoutFirst I) k (withoutFirst_nonempty hI h0)
        (by have := card_withoutFirst I h0; omega))

lemma strictRawModuleTensorConeData_d_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq (differential A ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk))
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.rhs
        (withoutFirst I) k (by have := card_withoutFirst I h0; omega))
```

`RawModuleTensorConeErasedLast.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_erased_succ_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1))
    (h0 : 0 ∈ I) (j : Fin (n + 1)) (hj : j.succ ∈ I) (hjb : j.succ < b)
    (hJ : ((withoutFirst I).erase j).Nonempty)
    (hkJ : k + 1 = 1 - (((withoutFirst I).erase j).card : ℤ)) :
    HEq ((strictRawModuleTensorConeData A X P Q c).homOrZero (I.erase j.succ) a b (k + 1))
      ((k + 1).negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        ((withoutFirst I).erase j) (k + 1) hJ hkJ)
```

`RawModuleTensorConeLinearBoundary.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_linearBoundary_reindex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) :
    (strictRawModuleTensorConeData A X P Q c).linearBoundary I a b k =
      ∑ j : withoutFirst I, if j.val < Fin.last n then
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (withoutFirst I) j.val •
          (strictRawModuleTensorConeData A X P Q c).homOrZero (I.erase j.val.succ) a b (k + 1)
        else 0

lemma strictRawModuleTensorConeData_linearBoundary_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1))
    (h0 : 0 ∈ I) (hJ : 2 ≤ (withoutFirst I).card)
    (hkJ : k = 1 - ((withoutFirst I).card : ℤ)) :
    HEq ((strictRawModuleTensorConeData A X P Q c).linearBoundary I a b k)
      (∑ j : withoutFirst I, if j.val < Fin.last n then
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (withoutFirst I) j.val • ((k + 1).negOnePow •
          (strictRawModuleTensorElementLinear A X P Q c).val.component
            ((withoutFirst I).erase j.val) (k + 1)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ j.property)
            (by have := Finset.card_erase_add_one j.property; omega)) else 0)
```

`RawModuleTensorSelectedComposition.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_compose {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℤˣ) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).val
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) (add_zero k) =
    r • (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk
```

`RawModuleTensorConeTerminalComposition.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_terminal_compose_mixed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (L R : Finset (Fin (n + 2))) (a j b : Fin (n + 2)) (k : ℤ)
    (hL : 2 ≤ L.card) (ha : a = L.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hj : j = L.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)) (hk : k = 2 - (L.card : ℤ))
    (ha0 : a = 0) (h0 : 0 ∈ L) (hR : 2 ≤ R.card)
    (hjR : j = R.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR)) (hb : b = R.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR))
    (hkR : (0 : ℤ) = 2 - (R.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq (compose A ((strictRawModuleTensorConeData A X P Q c).hom R j b 0 hR hjR hb hkR)
      ((strictRawModuleTensorConeData A X P Q c).hom L a j k hL ha hj hk) (add_zero k))
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        (withoutFirst L) k (withoutFirst_nonempty hL h0)
        (by have := card_withoutFirst L h0; omega))
```

`RawModuleTensorConePenultimateValue.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_cutCompose_penultimate_value {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI))
      ((k + 1).negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        (withoutFirst (I.filter (· ≤ penultimate I hI))) (k + 1)
        (withoutFirst_nonempty
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two (a := a) (by rw [ha]; exact I.min'_mem _) (penultimate_mem I hI)
            (by rw [ha]; exact min_lt_penultimate I hI hc))
          (Finset.mem_filter.mpr ⟨h0, Fin.zero_le _⟩))
        (by have hsplit := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card (penultimate_mem I hI)
            have hr := (right_card_two_iff_penultimate I hI _ (penultimate_mem I hI)
              (penultimate_lt_max I hI)).mpr rfl
            have hw := card_withoutFirst (I.filter (· ≤ penultimate I hI))
              (Finset.mem_filter.mpr ⟨h0, Fin.zero_le _⟩)
            have hsZ := congrArg (fun t : ℕ => (t : ℤ)) hsplit
            have hwZ := congrArg (fun t : ℕ => (t : ℤ)) hw
            rw [hr] at hsZ
            push_cast at hsZ hwZ
            have harith : ∀ i l w t : ℤ, t = 2 - i → l + 2 = i + 1 →
                l = w + 1 → t + 1 = 1 - w := by intros; omega
            exact harith _ _ _ _ hk hsZ hwZ))
```

`RawModuleTensorConeTerminalCut.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_terminal_cut_component {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I)
    (hJ : ((withoutFirst I).erase (Fin.last n)).Nonempty)
    (hkJ : k + 1 = 1 - (((withoutFirst I).erase (Fin.last n)).card : ℤ)) :
    HEq ((strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI))
      ((k + 1).negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        ((withoutFirst I).erase (Fin.last n)) (k + 1) hJ hkJ)
```

`RawModuleTensorConeNonedgeCut.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_term_of_nonedge_cut {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 2)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hc : (I.filter (j ≤ ·)).card ≠ 2) :
    (strictRawModuleTensorConeData A X P Q c).term I a b k hI ha hb hk j hj haj hjb =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (strictRawModuleTensorConeData A X P Q c).homOrZero (I.erase j) a b (k + 1)
```

`RawModuleTensorConeCutSupport.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_cutCompose_of_nonedge {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 2)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hc : (I.filter (j ≤ ·)).card ≠ 2) :
    (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k j = 0

lemma strictRawModuleTensorConeData_cutCompose_of_ne_penultimate {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 2)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hne : j ≠ penultimate I hI) :
    (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k j = 0
```

`RawModuleTensorConeQuadratic.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_quadratic_single {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    (strictRawModuleTensorConeData A X P Q c).quadraticBoundary I a b k =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (penultimate I hI) •
      (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI)
```

`RawModuleTensorConeRhsReduction.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_rhs_reduced {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    (strictRawModuleTensorConeData A X P Q c).rhs I a b k hI ha hb hk =
    (strictRawModuleTensorConeData A X P Q c).linearBoundary I a b k +
      (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI)
```

`RawModuleTensorConeRhsMixedLast.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_rhs_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).rhs I a b k hI ha hb hk)
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.rhs
        (withoutFirst I) k (by have := card_withoutFirst I h0; omega))
```

`RawModuleTensorConeLastEquation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_equation_of_last_mem {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (hlast : Fin.last (n + 1) ∈ I) :
    (strictRawModuleTensorConeData A X P Q c).Equation I
```

`RawModuleTensorConeEquation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma rawModuleSimplexData_equation_image_of_pullback {m n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n) (α : Fin (m + 1) →o Fin (n + 1))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) m) (h : s.pullback α = t)
    (J : Finset (Fin (m + 1))) (hi : Set.InjOn α (J : Set (Fin (m + 1))))
    (ht : t.Equation J) : s.Equation (J.image α)

lemma strictRawModuleTensorConeData_equation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) : (strictRawModuleTensorConeData A X P Q c).Equation I
```

`RawModuleTensorConeSimplex.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1)

lemma strictRawModuleTensorConeSimplex_data {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeSimplex A X P Q c).toSimplexData = strictRawModuleTensorConeData A X P Q c

lemma strictRawModuleTensorConeSimplex_pullback_injective {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (strictRawModuleTensorConeSimplex A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) =
      strictRawModuleTensorConeSimplex A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)

lemma strictRawModuleTensorConeSimplex_tail {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeSimplex A X P Q c).pullback (Fin.succOrderEmb (n + 1)).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q)
```

通常の対象ビルドは成功した。小さい監査の確定結果と実測は §46.1 に記録した。
同じ屋根と K の実 Hom 射への全高次照合、その同値性・完全忠実性、指定 fiber、
一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 46.1 検証と実測

ClosedPostcomposition と RawModuleTensorSelectedAtMaxImage・SelectedTerminal・ConeMixedLast・
ConeErasedLast・ConeLinearBoundary・SelectedComposition・ConeTerminalComposition・
ConePenultimateValue・ConeTerminalCut・ConeNonedgeCut・ConeCutSupport・ConeQuadratic・
ConeRhsReduction・ConeRhsMixedLast・ConeLastEquation・ConeEquation・ConeSimplex
（省略した接頭辞はすべて RawModuleTensor）の通常の対象ビルドは成功した。
新しい公開宣言 25 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は十八ファイル。上記順で 35・45・59・67・61・84・42・75・93・48・45・52・44・38・
76・43・83・50 行、計 1,040 行、明示宣言 26 本（private 1 本）。
§45.1 の累計に加え、検証済み累計は 117 ファイル・10,482 行・明示宣言 499 本
（private 5 本）。現作業木の M15 所有ソースの合計も同じ 117 ファイル・10,482 行と確認した。
200 行を超える証明はない。一次 ID は追加していない。

元の実 cone の全 HA 方程式、同じデータを持つ実単体、全単射制限と元の全通常末尾面の一致を
検証した。非線形切断和の支持・次数・元の閉射との合成・全削除和の最後の成分と符号は、
同じ dg Hom end の線形成分へ戻して検証している。
先端・終端の型移送を明示し、比較射や方程式の存在を引数に仮定していない。

次は、非単射再添字での元の最上位 cochain の零と通常成分の元の制限を使い、
全 cone 単体の**全作用素**自然性を検証する。その後に同じ元の全 cone/prism を束ねる。
同じ屋根と K の実 Hom 射への全高次照合、その同値性・完全忠実性、指定 fiber、
一般の native な辺と全族はまだ未完。M11 以降と G12 の元の目標、17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 47. M10 の全作用素自然性と同じ大域 cone・prism（11-14）

§46 の同じ実 cone 単体について、選択集合上で単射な任意作用素の像と、
元の制限列の選択 cochain を明示濃度の列挙で照合する。
非単射のときは作用素の実 epi-mono 像分解を使う。全射部分は終端を保つため、
元の非単射成分式の後合成が恒等作用になり、同じ最上位 cochain の零を得る。
恒等作用以外の後合成を取り消すことや、その単射性の仮定は使わない。
元の選択 cochain と同じ混合 cone 成分の零へ、最大元の型の移送を保って戻す。

混合成分の単射/非単射分岐と、元の通常末尾面の全自然性をまとめる。
通常側では潰れた辺の単位分岐も元の閉 nerve の自然性で保持する。
従属関数の外延性により全 `SimplexData` の任意作用素の pullback を一致させ、
同じ実 `Simplex` の**非単射を含む全作用素**自然性を得る。

この同じ全単体族を、元の probe の指定点の下の coslice 写像へ束ねる。
点と nerve の join から元の全通常 dg 加群 nerve への大域 cone を構成し、
先端・全通常図式・任意の元の単体への制限を厳密に回収する。
通常図式の nerve には、元の局所化源と同じ ULiftHom 関手と同じ
`strictRawModuleDGSource` を使う。別の台の模型へ変えていない。

同じ join-cylinder 比較で大域 prism へ移し、両端を元の先端の定値図式と
同じ全通常図式に戻す。同じ区間因子の交換を私有の一般補題へ分け、
Lean の展開上限を増やさず元の全区間ホモトピーを構成する。
さらにその同じ全辺を全関手圏の射として保持する。パラメータを対象ごとの π₀ へ落とさない。

本節は M10 の同じ構成の全再添字・退化・係数移送・端点・貼り合わせの法則と証明の分割で、
一次 ID は追加しない。同じ源の解像度を後合成して §39 の屋根へ照合する段と、
同じ K の Hom 誘導射の同値性・完全忠実性は引き続き必要。
全宣言の型は以下のとおり。

`RawModuleTensorSelectedCardInjOn`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_image_of_injOn {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) (r : ℕ) (hc : J.card = r + 1) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk) r
      (by rw [Finset.card_image_of_injOn hi]; exact hc))
      (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        J k hJ hk r hc)
```

`RawModuleTensorSelectedInjOn`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image_reindex_of_injOn {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk))
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        J k hJ hk)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image_reindex_of_injOn_smul {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) (r : ℤˣ) :
    HEq (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk))
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        J k hJ hk)
```

`RawModuleTensorConeMixedInjOn`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_mixed_of_injOn {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hθ : Set.InjOn θ.toOrderHom ((withoutFirst I) : Set (Fin (m + 1)))) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom
          I a b k hI ha hb hk)
```

`RawModuleTensorSurjectiveTop`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementLinear_top_surjective_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hs : Function.Surjective θ.toOrderHom)
    (hn : ¬Function.Injective θ.toOrderHom) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (m + 1))).card : ℤ)) :
    (strictRawModuleTensorElementLinear A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component
        Finset.univ k Finset.univ_nonempty hk = 0
```

`RawModuleTensorNoninjectiveTop`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementLinear_top_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hn : ¬Function.Injective θ.toOrderHom) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (m + 1))).card : ℤ)) :
    (strictRawModuleTensorElementLinear A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component
        Finset.univ k Finset.univ_nonempty hk = 0
```

`RawModuleTensorSelectedNoninjective`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_reindex_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hn : ¬Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    strictRawModuleTensorElementSelectedCochainAtMax A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) J k hJ hk = 0
```

`RawModuleTensorConeDegenerateMixed`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_mixed_reindex_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hn : ¬Set.InjOn θ.toOrderHom ((withoutFirst I) : Set (Fin (m + 1)))) :
    (strictRawModuleTensorConeData A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom I a b k hI ha hb hk = 0
```

`RawModuleTensorConeDegeneratePullback`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_obj_prepend_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    (strictRawModuleTensorConeData A X P Q c).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i) =
      (strictRawModuleTensorConeData A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).obj i

lemma strictRawModuleTensorConeData_pullback_hom_mixed_not_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hn : ¬Set.InjOn θ.toOrderHom ((withoutFirst I) : Set (Fin (m + 1)))) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom
        I a b k hI ha hb hk)
```

`RawModuleTensorConeTailMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_tail_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ((strictRawModuleTensorConeData A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).pullback
      (Fin.succOrderEmb (m + 1)).toOrderHom =
      (strictRawModuleTensorConeData A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).pullback
        (Fin.succOrderEmb (m + 1)).toOrderHom
```

`RawModuleTensorConeOrdinaryMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_ordinary_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom
        I a b k hI ha hb hk)
```

`RawModuleTensorConeMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorConeData A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) =
      strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
```

`RawModuleTensorConeSimplexMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeSimplex_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorConeSimplex A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) =
      strictRawModuleTensorConeSimplex A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
```

`RawModuleTensorConeUnderSimplex`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConePoint : (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))

lemma strictRawModuleTensorConePoint_vertex :
    (strictRawModuleTensorConePoint A X P).app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))

lemma strictRawModuleTensorConeSimplex_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).map
      (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (strictRawModuleTensorConeSimplex A X P Q c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))

def strictRawModuleTensorConeUnderSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (strictRawModuleTensorConePoint A X P)) _⦋n⦌

lemma strictRawModuleTensorConeSimplex_naturality {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    strictRawModuleTensorConeSimplex A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).map (SimplexCategory.mkHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).op (strictRawModuleTensorConeSimplex A X P Q c)
```

`RawModuleTensorConeUnderMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeUnderMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (strictRawModuleTensorConePoint A X P)

lemma strictRawModuleTensorConeUnderMap_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeUnderMap A X P Q).app (Opposite.op ⦋n⦌) c =
      strictRawModuleTensorConeUnderSimplex A X P Q c
```

`RawModuleTensorConeProjection`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementNerveDiagram :
    nerve (strictRawModuleTensorElementIndex A X P Q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))

lemma strictRawModuleTensorElementNerveDiagram_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementNerveDiagram A X P Q).app (Opposite.op ⦋n⦌) c =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q)

lemma strictRawModuleTensorConeUnderMap_projection :
    strictRawModuleTensorConeUnderMap A X P Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (strictRawModuleTensorConePoint A X P) =
      strictRawModuleTensorElementNerveDiagram A X P Q
```

`RawModuleTensorConeJoin`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeJoin :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))

lemma strictRawModuleTensorConeJoin_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConeJoin A X P Q = strictRawModuleTensorConePoint A X P

lemma strictRawModuleTensorConeJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConeJoin A X P Q = strictRawModuleTensorElementNerveDiagram A X P Q

lemma strictRawModuleTensorConeJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c) ≫
      strictRawModuleTensorConeJoin A X P Q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
          (strictRawModuleTensorConeSimplex A X P Q c)
```

`RawModuleTensorConePrism`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConePrism : (Δ[1] : SSet.{u + 1}) ⊗
    nerve (strictRawModuleTensorElementIndex A X P Q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))

lemma strictRawModuleTensorConePrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConePrism A X P Q =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))

lemma strictRawModuleTensorConePrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConePrism A X P Q = strictRawModuleTensorElementNerveDiagram A X P Q
```

`RawModuleTensorConeFamily`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma conePrismEndpointZero {K T : SSet.{u + 1}}
    (p : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ T) :
    SSet.ι₀ (X := K) ≫ ((β_ K (Δ[1] : SSet.{u + 1})).hom ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ p

private lemma conePrismEndpointOne {K T : SSet.{u + 1}}
    (p : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ T) :
    SSet.ι₁ (X := K) ≫ ((β_ K (Δ[1] : SSet.{u + 1})).hom ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ p

def strictRawModuleTensorConeHomotopy :
    SSet.Homotopy (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))
      (strictRawModuleTensorElementNerveDiagram A X P Q)

def strictRawModuleTensorConeFamilyHom :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))
      (strictRawModuleTensorElementNerveDiagram A X P Q)
```

対象ビルド・小さい監査の結果と実測は §47.1 に記録した。
M10 の指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 47.1 検証と実測

RawModuleTensorSelectedCardInjOn・SelectedInjOn・ConeMixedInjOn・SurjectiveTop・NoninjectiveTop・
SelectedNoninjective・ConeDegenerateMixed・ConeDegeneratePullback・ConeTailMap・ConeOrdinaryMap・
ConeMap・ConeSimplexMap・ConeUnderSimplex・ConeUnderMap・ConeProjection・ConeJoin・ConePrism・ConeFamily
（省略した接頭辞はすべて RawModuleTensor）の通常の対象ビルドは成功した。
新しい公開宣言 33 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は十八ファイル。上記順で 63・74・79・50・57・82・53・62・42・86・67・31・67・49・
58・49・67・62 行、計 1,098 行、明示宣言 35 本（private 2 本）。
§46.1 の累計に加え、検証済み累計は 135 ファイル・11,580 行・明示宣言 534 本
（private 7 本）。現作業木の M15 所有ソースの合計も同じ 135 ファイル・11,580 行と確認した。
200 行を超える証明はない。一次 ID は追加していない。

元の全 cone 単体の全作用素自然性、同じ先端下の大域 coslice、同じ join cone、
同じ通常図式と任意単体への制限、両端を保つ大域 prism、同じ全区間ホモトピーと
全関手圏の射まで検証した。区間因子の交換は両端の等式補題へ分け、
200,000 heartbeat の上限を増やしていない。前節の実 cone 単体の同じ HA 方程式を使っている。

次は同じ `moduleResolution` の後合成で元の `strictRawModuleSource` へ送り、
同じ通常図式の全等式と指定端点を保って §39 の全実評価屋根へ比較する。
同じ augmentation の全逆と同じ評価の元の三角形、および元の K の実 Hom 誘導射との
全高次照合は引き続き必要。この段階を K の完全忠実性には数えない。
M10 の指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標、
17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。
