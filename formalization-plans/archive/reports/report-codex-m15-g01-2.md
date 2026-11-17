# BS-M15（⑤d）作業報告 — G01 後半（実親子の全単射まで）（§103〜§128、2026-11-15〜11-16）

元の報告：[report-codex-m15.md](../../bhatt-scholze/reports/report-codex-m15.md)

## §103 G01：二つの実射の指定辺への挿入と実全単体の原子性の保存（11-15）

### 103.1 検証済みの追加

約10,000行の途中報告§102の後も止めずに継続した。
追加は **2ファイル151行・明示宣言7**。累計 **83ファイル10,153行・明示宣言588**。
ComposableArrowRefinement.lean は79行・4宣言、WalkingAdjunctionAtomicRefinement.lean は72行・3宣言。
200行を超える個別の宣言・証明はない。新規Leanの行長は100文字以下。
G01の同じ原子の実細分・全鎖への挿入・端点の照合・係数移送とその証明の分割なので、
新しい一覧IDは足さない。

任意の実圏の有限の実鎖の指定した一辺に、中間対象と二つの実射を挿入した実関手を構成した。
先頭の辺なら元の尾部へ二回precompし、それ以外なら尾部で再帰して元の先頭を戻す。
再帰の出力と同時に両端の対象の実等式を構成し、全射を持つ実関手として取り出している。
鎖の実関手やその端点の一致の存在を引数に置いていない。

元の四Homの全単体について、この細分は原子性を保つことを証明した。
両端の対象の等式により、§101の有限端点による原子性の必要十分条件を戻している。
元の全射と実分解を含む原子性を結論としており、辺の存在だけの表示ではない。
§102の実併合・実残余射をこの構成へ挿入し、指定の併合条件を満たす辺の実細分として
一つ高次の元の実全単体を構成し、元が原子的なら新しい実全単体も原子的であることを得た。

### 103.2 型と残る境界

原典は[Riehl–Verity §4.1–§4.2](https://emilyriehl.github.io/files/adjunctions.pdf)、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
検証した型は以下。

```lean
def composableArrowRefinementData :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (_q : F.obj k.castSucc ⟶ B) (_g : B ⟶ F.obj k.succ),
      {G : ComposableArrows C (n + 2) //
        G.obj 0 = F.obj 0 ∧ G.obj (Fin.last (n + 2)) = F.obj (Fin.last (n + 1))}

def composableArrowRefinement {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ) :
    ComposableArrows C (n + 2)

lemma composableArrowRefinement_first {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ) :
    (composableArrowRefinement F k B q g).obj 0 = F.obj 0

lemma composableArrowRefinement_last {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ) :
    (composableArrowRefinement F k B q g).obj (Fin.last (n + 2)) = F.obj (Fin.last (n + 1))

lemma walkingAdjunctionRefinement_atomic {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (k : Fin (n + 1))
    (B : walkingAdjunctionHom X Y) (q : H.obj k.castSucc ⟶ B) (g : B ⟶ H.obj k.succ)
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      (composableArrowRefinement H k B q g)

def walkingAdjunctionBottomMergeRefinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)

lemma walkingAdjunctionBottomMergeRefinement_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionBottomMergeRefinement H k m hA h1)
```

今回の構成は、指定位置・中間対象・二つの実射から実全鎖を作る段階である。
指定した面が元の全鎖へ戻る等式、その他の面との両立、非退化性はまだ検証していない。
実併合を使う場合の位置と二番目の点の像0の条件は現在の入力であり、
全ての非fillableな原子に適切な最初の位置が実際に選べることはまだ未証明である。
従って原子のfillableな親の完成とは数えていない。
parental subcomputadのfiltration、元のQCatAdjunctionからの全coherentな延長、
原典の向きと現模型の水平反対の全比較、同じF≫U・単位・余単位・HAモデルの照合も未完。
G01の済みは0、G02以降も未完を維持する。

### 103.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大240秒の短いimpl枠。
セッション26798では基底のFin 1のSubsingletonが見つからなかったため終了1を確認した。
有限点の値の不等式で一意性を明記し、51014で実鎖の再帰と両端の等式が通った。
51014では指定辺の終点の型推論で失敗し、順序圏の射の始点・終点を明記した。
50991では有限点の後続の不等式の算術表示が一致しなかったため終了1を確認した。
既存のFin.castSucc_le_succの型を明記し、未使用束縛名の警告も整え、最終セッション62839で
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicRefinement:olean
と、続く追加7根だけの公理監査、外側の終了0を確認した。
最終対象ビルドは警告なし。
追加7根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・全出力・最終対象ビルドログは
[g12-atomic-refinement-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-atomic-refinement-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み10,153行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §104 G01：細分の指定面の全関手での回収と元のnerveの面との照合（11-15）

### 104.1 検証済みの追加

追加は **3ファイル296行・明示宣言17**。累計 **86ファイル10,449行・明示宣言605**。
ComposableArrowFaces.lean は106行・8宣言、ComposableArrowRefinementFaces.lean は117行・5宣言、
WalkingAdjunctionRefinementFaces.lean は73行・4宣言。
200行を超える個別の宣言・証明はない。新規Leanの行長は100文字以下。
G01の同じ原子の実細分・全鎖への挿入・面の全合成・係数移送・貼り合わせ・照合とその証明の分割なので、
新しい一覧IDは足さない。

一点を飛ばす実有限順序関手で全実鎖の面を構成した。
後続点でのsuccAboveの法則と薄い順序圏の全射の一意性から、尾部との全合成則を証明した。
これにより、面の尾部は元の尾部の対応する面であり、先頭を残す面の始点は元の始点である。
先頭へ一射を挿入して0番の面を取れば元の実鎖に戻り、先頭二点を残す面は先頭への挿入と可換となる。
先頭へ二射を挿入して中間点を除く面は、その二射の合成を先頭へ挿入したものと全関手として一致する。
対象だけで終えず、実precompのmapも展開して最初の射を検収した。

§103の細分の先頭・尾部での実定義を等式で取り出し、
元の尾部へ最初の実射を戻す等式と、先頭の対象の等式の輸送の法則を証明した。
これらの法則を使い、指定位置について再帰して、細分した実全鎖の中間点を除く指定面が
元の実全鎖に、全射を含む全関手の等式として一致することを証明した。
入力は元の指定辺が二つの実射の合成であるという等式だけである。

実面の順序関手は単体圏の実面δの順序関手そのものであることを照合した。
元のWalkingAdjunctionHomShapeのnerveの面が同じ実全鎖の面であることを実定義で証明し、
§102の元の実併合・実残余射の因子化を、§103の実全単体へ挿入した場合に適用した。
その指定面が元の実全単体に戻ることを、元のHomの単体集合の実際の面の作用として検収した。
別の面の模型上の等式だけではない。

### 104.2 型と残る境界

原典は[Riehl–Verity §4.1–§4.2](https://emilyriehl.github.io/files/adjunctions.pdf)、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
検証した型は以下。

```lean
def finiteChainFaceIndex {n : ℕ} (k : Fin (n + 2)) : Fin (n + 1) ⥤ Fin (n + 2)

lemma finiteChainFaceIndex_succ {n : ℕ} (k : Fin (n + 2)) :
    Fin.succFunctor (n + 1) ⋙ finiteChainFaceIndex k.succ =
      finiteChainFaceIndex k ⋙ Fin.succFunctor (n + 2)

def finiteChainFace {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 2)) :
    ComposableArrows C n

lemma finiteChainFace_first {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 1)) :
    (finiteChainFace F k.succ).obj 0 = F.obj 0

lemma finiteChainFace_tail {n : ℕ} (F : ComposableArrows C (n + 2)) (k : Fin (n + 2)) :
    (finiteChainFace F k.succ).δ₀ = finiteChainFace F.δ₀ k

lemma finiteChainFace_precomp_zero {n : ℕ} (F : ComposableArrows C n) {A : C}
    (f : A ⟶ F.left) : finiteChainFace (F.precomp f) 0 = F

lemma finiteChainFace_precomp_succ {n : ℕ} (F : ComposableArrows C (n + 1))
    {A : C} (f : A ⟶ F.left) (k : Fin (n + 1)) :
    finiteChainFace (F.precomp f) k.succ.succ =
      (finiteChainFace F k.succ).precomp (f ≫ eqToHom (finiteChainFace_first F k).symm)

lemma finiteChainFace_precomp_pair {n : ℕ} (F : ComposableArrows C n)
    {A B : C} (q : A ⟶ B) (g : B ⟶ F.left) :
    finiteChainFace ((F.precomp g).precomp q) (1 : Fin (n + 3)) = F.precomp (q ≫ g)

lemma composableArrowRefinement_zero {n : ℕ} (F : ComposableArrows C (n + 1))
    (B : C) (q : F.obj (0 : Fin (n + 1)).castSucc ⟶ B)
    (g : B ⟶ F.obj (0 : Fin (n + 1)).succ) :
    composableArrowRefinement F 0 B q g = (F.δ₀.precomp g).precomp q

lemma composableArrowRefinement_succ {n : ℕ} (F : ComposableArrows C (n + 2))
    (k : Fin (n + 1)) (B : C) (q : F.obj k.succ.castSucc ⟶ B)
    (g : B ⟶ F.obj k.succ.succ) :
    composableArrowRefinement F k.succ B q g =
      (composableArrowRefinement F.δ₀ k B q g).precomp
        (F.map' 0 1 ≫ eqToHom (composableArrowRefinement_first F.δ₀ k B q g).symm)

lemma composableArrowPrecomp_decompose {n : ℕ} (F : ComposableArrows C (n + 1)) :
    F.δ₀.precomp (F.map' 0 1) = F

lemma composableArrowPrecomp_transport {n : ℕ} {R S : ComposableArrows C n} (h : R = S)
    {A : C} (f : A ⟶ S.left) (h0 : R.left = S.left) :
    R.precomp (f ≫ eqToHom h0.symm) = S.precomp f

lemma composableArrowRefinement_face :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      q ≫ g = F.map (homOfLE (Fin.castSucc_le_succ k)) →
        finiteChainFace (composableArrowRefinement F k B q g) k.succ.castSucc = F

lemma finiteChainFaceIndex_simplex {n : ℕ} (k : Fin (n + 2)) :
    finiteChainFaceIndex k = walkingAdjunctionSimplexFunctor (SimplexCategory.δ k)

lemma walkingAdjunctionHomShape_face {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (k : Fin (n + 2)) (F : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    (((WalkingAdjunctionHomShape.{u} X Y).map (SimplexCategory.δ k).op) (ULift.up F)).down =
      finiteChainFace F k

lemma walkingAdjunctionBottomMergeRefinement_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    finiteChainFace (walkingAdjunctionBottomMergeRefinement H k m hA h1) k.succ.castSucc = H

lemma walkingAdjunctionBottomMergeRefinement_nerve_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    (((WalkingAdjunctionHomShape.{u} .minus Y).map
      (SimplexCategory.δ k.succ.castSucc).op)
        (ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1))).down = H
```

現在は、指定した位置と二番目の点の像0の条件を入力に、実全単体の細分・原子性・
元のnerveの指定面が元へ戻る等式までを構成している。
全ての対象の非fillableな原子に対する適切な最初の位置の実選択、
新しい全単体の非退化性、fillable条件、親の一意性、その他の面とのfiltrationの両立はまだ未完。
従って原子のfillableな親の完成とは数えていない。
parental subcomputadのfiltration、元のQCatAdjunctionからの全coherentな延長、
原典の向きと現模型の水平反対の全比較、同じF≫U・単位・余単位・HAモデルの照合も未完。
今回の元のnerveの指定面の回収を、coherentな延長の存在へ読み替えていない。
G01の済みは0、G02以降も未完を維持する。

### 104.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大240秒の短いimpl枠。
初期のセッション58328・5172・26873は、実全鎖の比較先の型推論、
実precompの最初のmapの展開・計算の未完による終了1をそれぞれ確認した。
セッション82561の最大240秒の一つの枠内で、比較する全関手・実mapを明記して面の合成則を検証した。
細分の再帰では、同じ有限点の値を明示し、尾部の半可約な型への書き換えの透明度を合わせた。
その後の最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementFaces:olean
は終了0、警告なし（1349 jobs）。続く追加17根だけの公理監査も終了0を確認し、
同じ枠を明示的に閉じて外側の終了0を確認した。
追加17根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・全出力・最終対象ビルドログは
[g12-refinement-faces-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-refinement-faces-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み10,449行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §105 G01：元の非退化な原子から最初の併合の位置を選んだ実細分（11-15）

### 105.1 検証済みの追加

追加は **4ファイル377行・明示宣言17**。累計 **90ファイル10,826行・明示宣言622**。
WalkingAdjunctionOnePointDegeneracy.lean は92行・3宣言、WalkingAdjunctionBottomMergePositions.lean は130行・6宣言、
WalkingAdjunctionFirstBottomMerge.lean は75行・4宣言、WalkingAdjunctionFirstRefinement.lean は80行・4宣言。
200行を超える個別の宣言・証明はない。新規Leanの行長は100文字以下。
G01の同じ原子の実表示・退化・最初の併合の実選択・実細分とその単位・係数移送・全合成・照合と
証明の分割なので、新しい一覧IDは足さない。

全頂点の共通表示が一点の実全単体は定値であることを、対象の重みの単射性と一点への全射の一意性で示した。
正の次元では、この定値な全単体を一つ低次の定値な単体の実退化の像として構成した。
従ってminusからの正の次元の元のnerveの非退化な全単体には、二点以上ある頂点が存在する。
元の単体集合のdegenerate・nonDegenerateを使っている。

元の隣接辺が二番目の実点を0へ送る条件を、値1の実点とその像の証人として定義した。
この証人から、始頂点に二点以上あることと、値1の全ての点の像0の条件が従う。
二番目の点を0へ送らない有限単調射は、0の逆像を反映する。
終頂点が一点でどの隣接辺にも併合がなければ、尾部の全射についてこの反映性を逆帰納し、
全頂点の二番目の点を排除できる。minusからの全頂点は非空なので、全頂点が一点となる。
元の非退化性と合わせ、併合する隣接辺の存在を証明した。

この実条件を満たす辺の非空な有限部分集合を構成し、その最小元を実際に取った。
選んだ位置が併合の条件を満たすことと、他の全ての併合の位置以下であることを検収した。
原子性から終頂点の一点を取り出し、この最小位置の始頂点の個数から一つ小さい実対象を作り、
実併合・実残余射を元の実全鎖へ挿入した。
これにより、元の正の次元の非退化な原子から、一つ高次の原子的な実全単体と、
元のnerveの指定面が元の全単体へ戻る等式までを構成した。
位置・併合の証人・原子性の保存・指定面の等式は、現在の構成の追加入力にはしていない。

### 105.2 型と残る境界

原典は[Riehl–Verity §4.1–§4.2](https://emilyriehl.github.io/files/adjunctions.pdf)、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
検証した型は以下。

```lean
lemma walkingAdjunctionConst_of_card_one {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hc : ∀ i, walkingAdjunctionOrdinalCard X Y (H.obj i) = 1) :
    H = (Functor.const _).obj (H.obj 0)

lemma walkingAdjunctionHomShape_degenerate_of_card_one {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : Fin (n + 2) ⥤ walkingAdjunctionHom X Y)
    (hc : ∀ i, walkingAdjunctionOrdinalCard X Y (H.obj i) = 1) :
    ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).degenerate (n + 1)

lemma walkingAdjunctionHomShape_exists_large_vertex {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (h : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    ∃ i, 2 ≤ walkingAdjunctionOrdinalCard .minus Y (H.obj i)

def WalkingAdjunctionBottomMergeAt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y) (k : Fin (n + 1)) : Prop

lemma ordinalReflectsZero_of_no_one {m n : ℕ} (f : Fin m →o Fin n)
    (h : ∀ j : Fin m, j.val = 1 → (f j).val ≠ 0) :
    ∀ i : Fin m, (f i).val = 0 → i.val = 0

lemma walkingAdjunctionCard_one_of_no_bottom_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hno : ∀ k, ¬ WalkingAdjunctionBottomMergeAt H k) :
    ∀ i, walkingAdjunctionOrdinalCard .minus Y (H.obj i) = 1

lemma walkingAdjunctionExists_bottom_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    ∃ k, WalkingAdjunctionBottomMergeAt H k

lemma WalkingAdjunctionBottomMergeAt.card_two_le {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y} {k : Fin (n + 1)}
    (h : WalkingAdjunctionBottomMergeAt H k) :
    2 ≤ walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)

lemma WalkingAdjunctionBottomMergeAt.one_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y} {k : Fin (n + 1)}
    (h : WalkingAdjunctionBottomMergeAt H k) :
    ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)), i.val = 1 →
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val = 0

def walkingAdjunctionFirstBottomMergeData {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    {k : Fin (n + 1) // WalkingAdjunctionBottomMergeAt H k ∧
      ∀ j, WalkingAdjunctionBottomMergeAt H j → k ≤ j}

def walkingAdjunctionFirstBottomMergeIndex {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    Fin (n + 1)

lemma walkingAdjunctionFirstBottomMergeIndex_spec {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    WalkingAdjunctionBottomMergeAt H (walkingAdjunctionFirstBottomMergeIndex H hlast hnd)

lemma walkingAdjunctionFirstBottomMergeIndex_minimal {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    {j : Fin (n + 1)} (hj : WalkingAdjunctionBottomMergeAt H j) :
    walkingAdjunctionFirstBottomMergeIndex H hlast hnd ≤ j

def walkingAdjunctionFirstRefinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)

lemma walkingAdjunctionFirstRefinement_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionFirstRefinement H ha hnd)

lemma walkingAdjunctionFirstRefinement_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    finiteChainFace (walkingAdjunctionFirstRefinement H ha hnd)
      (walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).succ.castSucc = H

lemma walkingAdjunctionFirstRefinement_nerve_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    (((WalkingAdjunctionHomShape.{u} .minus Y).map (SimplexCategory.δ
      (walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).succ.castSucc).op)
          (ULift.up (walkingAdjunctionFirstRefinement H ha hnd))).down = H
```

位置の実選択は今回で構成した。残る境界は、新しい実全単体自身の非退化性、
原典のfillable条件との照合とfillableな場合の除外、非fillableな場合の親の一意性、
その他の面とのfiltrationの両立である。
元が既にfillableな場合も今回の構成は定義されているため、新単体が常に非退化とは主張していない。
従って原子のfillableな親の完成とは数えていない。
始点plusの場合の別の親の構成、parental subcomputadのfiltration、
元のQCatAdjunctionからの全coherentな延長、原典の向きと現模型の水平反対の全比較、
同じF≫U・単位・余単位・HAモデルの照合も引き続き未完。
今回の元の非退化な原子からの実細分を、coherentな延長の存在へ読み替えていない。
G01の済みは0、G02以降も未完を維持する。

### 105.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大240秒の短いimpl枠。
初期のセッション87394は元の単体集合の非退化性の補題の明示引数が不足し、終了1を確認した。
不足する二つの引数を与え、局所の一意性の証明の警告を整えた。
セッション48371の最大240秒の一つの枠で、修正後の四つの対象を全て初回で検証した。
最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstRefinement:olean
は終了0、警告なし（1353 jobs）。続く追加17根だけの公理監査も終了0を確認し、
同じ枠を明示的に閉じて外側の終了0を確認した。
追加17根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・全出力・最終対象ビルドログは
[g12-first-refinement-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-first-refinement-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み10,826行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §106 G01：非退化な指定面の上の退化の限定と、厳密な併合条件による非退化性（11-15）

### 106.1 検証済みの追加

追加は **7ファイル556行・明示宣言17**。累計 **97ファイル11,382行・明示宣言639**。
NondegenerateFaceDegeneracy.lean は80行・2宣言、ComposableArrowRefinementPositions.lean は82行・2宣言、
NerveDegeneracyEdges.lean は54行・2宣言、ComposableArrowRefinementNondegenerate.lean は87行・1宣言、
WalkingAdjunctionIsomorphismProfiles.lean は63行・4宣言、WalkingAdjunctionBottomMergePurity.lean は120行・4宣言、
WalkingAdjunctionRefinementNondegenerate.lean は70行・2宣言。
200行を超える個別の宣言・証明はない。新規Leanの行長は100文字以下。
G01の同じ実細分・原子の実表示・面と退化の全合成・逆射・係数移送・照合とその証明の分割なので、
新しい一覧IDは足さない。

任意の単体集合について、非退化な指定面を持つ単体が退化している場合、
その退化の位置は指定面の両隣に限られ、退化を除いた低次の単体は指定面自身と一致することを示した。
指定面と退化の合成が非退化な単体を表示するため単射となり、有限全順序の自己単射は恒等写像となる。
面が飛ばす点以外の二点を退化で同じ点へ送れないことから、位置の限定を証明した。
これにより、両隣での退化に一致しないことから、元の単体集合の非退化性を得る法則を証明した。

実鎖の細分で挿入した対象を実等式で、右因子を異種等式で回収した。
元のnerveの退化で重なる辺の像は同型であり、両端の対象の等式と射の異種等式に沿って同型性を戻せる。
指定面が非退化な元の実鎖に戻る場合、左の退化は挿入対象の相違で、右の退化は右因子の非同型性で排除できる。
この証明を元のnerveの宇宙持ち上げの単体作用上で構成し、実併合による細分へ適用した。

残余射の非同型性を有限順序の明示条件へ移すため、元の実Homの同型から共通表示の実順序同型を構成した。
元の逆射と全合成・単位則を使っており、実同型は個数と各点の値を保つ。
実併合射の値はi↦i−1である。
実残余射が同型なら、元の射の終点の個数はm+1で、全ての点の値はi↦i−1となる。
逆にその個数と全点の条件が成り立つなら、終点を実併合後の対象と同一視し、
右因子の一意性により残余射はその等式による同型となる。
従って実残余射の同型性と、一つだけの最初の併合という個数・全点の条件の両方向を検証した。

これにより、元が非退化で、指定辺がこの一つだけの併合の条件に一致しない場合、
実併合で細分した全単体は元のHomの単体集合で非退化となる。
残余射の非同型性を仮定とする法則に加え、有限個数と全点の値の具体的条件による法則まで検証した。

### 106.2 型と残る境界

原典は[Riehl–Verity §4.1–§4.2](https://emilyriehl.github.io/files/adjunctions.pdf)、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
検証した型は以下。

```lean
lemma degeneracy_over_nondegenerate_face {X : SSet.{u}} {n : ℕ}
    (z : X _⦋n + 2⦌) (k : Fin (n + 3)) (j : Fin (n + 2)) (t : X _⦋n + 1⦌)
    (hdeg : X.σ j t = z) (hnd : X.δ k z ∈ X.nonDegenerate (n + 1)) :
    (k = j.castSucc ∨ k = j.succ) ∧ X.σ j (X.δ k z) = z

lemma nondegenerate_of_face_and_no_adjacent_degeneracy {X : SSet.{u}} {n : ℕ}
    (z : X _⦋n + 2⦌) (k : Fin (n + 3))
    (hnd : X.δ k z ∈ X.nonDegenerate (n + 1))
    (hno : ∀ j : Fin (n + 2), (k = j.castSucc ∨ k = j.succ) → X.σ j (X.δ k z) ≠ z) :
    z ∈ X.nonDegenerate (n + 2)

lemma composableArrowRefinement_middle :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      (composableArrowRefinement F k B q g).obj k.succ.castSucc = B

lemma composableArrowRefinement_right_edge :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      HEq ((composableArrowRefinement F k B q g).map
        (homOfLE (Fin.castSucc_le_succ k.succ))) g

lemma isIso_of_equal_objects_hom_heq {A B A' B' : C} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) [IsIso f] : IsIso g

lemma nerve_degeneracy_edge_isIso {n : ℕ} (F : ComposableArrows C n) (j : Fin (n + 1)) :
    IsIso (((nerve C).σ j F).map (homOfLE (Fin.castSucc_le_succ j)))

lemma composableArrowRefinement_nondegenerate {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ)
    (fac : q ≫ g = F.map (homOfLE (Fin.castSucc_le_succ k)))
    (hnd : ULift.up F ∈ (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).nonDegenerate (n + 1))
    (hq : F.obj k.castSucc ≠ B) (hg : ¬ IsIso g) :
    ULift.up (composableArrowRefinement F k B q g) ∈
      (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).nonDegenerate (n + 2)

lemma ordinalOrderIso_val {m n : ℕ} (e : Fin m ≃o Fin n) (i : Fin m) :
    (e i).val = i.val

def walkingAdjunctionOrderIsoOfIsIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f] :
    Fin (walkingAdjunctionOrdinalCard X Y A) ≃o Fin (walkingAdjunctionOrdinalCard X Y B)

lemma walkingAdjunctionCard_eq_of_isIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f] :
    walkingAdjunctionOrdinalCard X Y A = walkingAdjunctionOrdinalCard X Y B

lemma walkingAdjunctionOrderHom_val_of_isIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f]
    (i : Fin (walkingAdjunctionOrdinalCard X Y A)) :
    (walkingAdjunctionOrderHom f i).val = i.val

lemma walkingAdjunctionBottomMergeArrow_val {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (i : Fin (walkingAdjunctionOrdinalCard .minus Y A)) :
    (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA) i).val = i.val - 1

lemma walkingAdjunctionBottomMerge_pure_of_residual_isIso {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0)
    [IsIso (walkingAdjunctionBottomMergeResidual f m hA h1)] :
    walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1

lemma walkingAdjunctionBottomMerge_residual_isIso_of_pure {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0)
    (hp : walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1) :
    IsIso (walkingAdjunctionBottomMergeResidual f m hA h1)

lemma walkingAdjunctionBottomMerge_residual_isIso_iff_pure {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    IsIso (walkingAdjunctionBottomMergeResidual f m hA h1) ↔
      walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
        ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
          (walkingAdjunctionOrderHom f i).val = i.val - 1

lemma walkingAdjunctionBottomMergeRefinement_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hg : ¬ IsIso (walkingAdjunctionBottomMergeResidual
      (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)) :
    ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)

lemma walkingAdjunctionBottomMergeRefinement_nondegenerate_of_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hp : ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1)) :
    ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)
```

今回は、指定された併合の辺で一つだけの併合の条件が成り立たない場合の非退化性までである。
§105で選んだ最初の位置の実射にこの条件を適用できる。
ただし、この有限順序の具体的条件と原典のfillable条件の全照合、
細分後の最初の位置と厳密な併合条件の保存、親の一意性はまだ未完である。
元が既にfillableな場合を含む全ての原子の細分に対し、無条件で非退化とは主張していない。
従って原子のfillableな親の完成とは数えていない。
始点plusの場合の別の親の構成、その他の面とのfiltrationの両立、parental subcomputadのfiltration、
元のQCatAdjunctionからの全coherentな延長、原典の向きと現模型の水平反対の全比較、
同じF≫U・単位・余単位・HAモデルの照合も引き続き未完。
今回の条件つきの非退化性を、coherentな延長の存在へ読み替えていない。
G01の済みは0、G02以降も未完を維持する。

### 106.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大240秒の短いimpl枠。
セッション93163で任意の単体集合の退化の位置の限定の対象ビルドが最初に通った。
局所の単射性の束縛名の警告を整え、セッション79767の最大240秒の一つの枠で
残りの対象と追加した実同型・厳密な併合条件の照合までを検証した。
今回の数学の証明は全て各最初の対象ビルドで通過した。
最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementNondegenerate:olean
は終了0、警告なし（1356 jobs）。続く追加17根だけの公理監査も終了0を確認し、
同じ枠を明示的に閉じて外側の終了0を確認した。
追加17根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・全出力・最終対象ビルドログは
[g12-refinement-nondegenerate-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-refinement-nondegenerate-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み11,382行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §107 G01：最初の併合位置の保存と細分後の厳密な併合条件（11-15）

### 107.1 検証済みの追加

追加は **3ファイル372行・明示宣言13**。累計 **100ファイル11,754行・明示宣言652**。
ComposableArrowRefinementPrefix.lean は110行・3宣言、WalkingAdjunctionBottomMergeTransport.lean は57行・2宣言、
WalkingAdjunctionRefinementFirstMerge.lean は205行・8宣言。
200行を超える個別の宣言・証明はない。新規Leanの行長は100文字以下。
G01の同じ原子の実細分・実辺の回収・最初の位置の照合・係数移送・最小性とその証明の分割なので、
新しい一覧IDは足さない。

実全鎖の細分について、挿入した頂点までの実対象が元の対象であることを指定面から回収した。
挿入した左因子と、挿入位置より前の全実辺を実precompの再帰で異種等式として回収した。
先頭の射では対象の等式による右の輸送を取り除き、元の全射を保持している。
この射の照合を、両端の実対象の等式も使って、併合の実点の条件と一つだけの併合の全点条件へ両方向に移した。

実併合で細分した実全単体では、挿入した左辺に実際に併合の位置の証人がある。
その辺は終点の個数m+1、全点の値i↦i−1という一つだけの併合の条件を満たす。
細分の位置より前の辺の併合条件は元の辺の条件と同値である。
従って元の位置が最小なら、細分後もそれより前の併合の位置はなく、挿入した左辺の位置が最小である。
前の全ての新しい有限添字を元の添字に戻して検収している。

§105で実際に選んだ最小位置にこれらの法則を適用し、
構成した一つ高次の実全単体の最初の併合の所属・最小性と、一つだけの併合の全点条件を証明した。
位置の保存や最小性の証人を新しい入力に追加していない。
元の選択位置が一つだけの併合の条件に一致しない場合には、
§106の法則を適用し、この実際に選んだ細分が元のHomの単体集合で非退化となることも検証した。

### 107.2 型と残る境界

原典は[Riehl–Verity §3.1・§4.1–§4.2](https://emilyriehl.github.io/files/adjunctions.pdf)、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
原典の文字列の最初の折り返しとレベルの重複の条件を、現在は実有限順序の辺の個数・全点の値と比較している。
今回、細分後の実際の最初の位置と、その厳密な併合の条件を証明した。
検証した型は以下。

```lean
lemma composableArrowRefinement_before_obj {n : ℕ} (F : ComposableArrows C (n + 1))
    (k : Fin (n + 1)) (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ)
    (fac : q ≫ g = F.map (homOfLE (Fin.castSucc_le_succ k)))
    (i : Fin (n + 2)) (hi : i.val ≤ k.val) :
    (composableArrowRefinement F k B q g).obj i.castSucc = F.obj i

lemma composableArrowRefinement_left_edge :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      HEq ((composableArrowRefinement F k B q g).map
        (homOfLE (Fin.castSucc_le_succ k.castSucc))) q

lemma composableArrowRefinement_before_edge :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ)
      (j : Fin (n + 1)), j < k →
      HEq ((composableArrowRefinement F k B q g).map
        (homOfLE (Fin.castSucc_le_succ j.castSucc)))
          (F.map (homOfLE (Fin.castSucc_le_succ j)))

lemma walkingAdjunctionMergesBottom_heq {Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom .minus Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    (∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y A), i.val = 1 ∧
      (walkingAdjunctionOrderHom f i).val = 0) ↔
    (∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y A'), i.val = 1 ∧
      (walkingAdjunctionOrderHom g i).val = 0)

lemma walkingAdjunctionPureBottomMerge_heq {Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom .minus Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) (m : ℕ) :
    (walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1) ↔
    (walkingAdjunctionOrdinalCard .minus Y B' = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A'),
        (walkingAdjunctionOrderHom g i).val = i.val - 1)

lemma walkingAdjunctionBottomMergeRefinement_at {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    WalkingAdjunctionBottomMergeAt (walkingAdjunctionBottomMergeRefinement H k m hA h1)
      k.castSucc

lemma walkingAdjunctionBottomMergeRefinement_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionBottomMergeRefinement H k m hA h1).obj k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionBottomMergeRefinement H k m hA h1).obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom ((walkingAdjunctionBottomMergeRefinement H k m hA h1).map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1

lemma walkingAdjunctionBottomMergeRefinement_before_merge_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    {j : Fin (n + 1)} (hj : j < k) :
    WalkingAdjunctionBottomMergeAt (walkingAdjunctionBottomMergeRefinement H k m hA h1)
      j.castSucc ↔ WalkingAdjunctionBottomMergeAt H j

lemma walkingAdjunctionBottomMergeRefinement_no_earlier_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hmin : ∀ j, WalkingAdjunctionBottomMergeAt H j → k ≤ j)
    {r : Fin (n + 2)} (hr : r < k.castSucc) :
    ¬ WalkingAdjunctionBottomMergeAt (walkingAdjunctionBottomMergeRefinement H k m hA h1) r

lemma walkingAdjunctionBottomMergeRefinement_minimal {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hmin : ∀ j, WalkingAdjunctionBottomMergeAt H j → k ≤ j) :
    ∀ r, WalkingAdjunctionBottomMergeAt (walkingAdjunctionBottomMergeRefinement H k m hA h1) r →
      k.castSucc ≤ r

lemma walkingAdjunctionFirstRefinement_first_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    let k := walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
    WalkingAdjunctionBottomMergeAt (walkingAdjunctionFirstRefinement H ha hnd) k.castSucc ∧
      ∀ r, WalkingAdjunctionBottomMergeAt (walkingAdjunctionFirstRefinement H ha hnd) r →
        k.castSucc ≤ r

lemma walkingAdjunctionFirstRefinement_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    let k := walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
    let m := walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) - 2
    walkingAdjunctionOrdinalCard .minus Y ((walkingAdjunctionFirstRefinement H ha hnd).obj
      k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionFirstRefinement H ha hnd).obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom ((walkingAdjunctionFirstRefinement H ha hnd).map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1

lemma walkingAdjunctionFirstRefinement_nondegenerate_of_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint} (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hp :
      let k := walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
      let m := walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) - 2
      ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
        ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
          (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
            i.val - 1)) :
    ULift.up (walkingAdjunctionFirstRefinement H ha hnd) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)
```

実有限順序の模型で、選んだ非純粋な最初の併合の細分は、原子的・非退化で、
同じ位置が最小となり、そこで一つだけの併合の条件を満たすところまで構成した。
原典の文字列表示との全比較とfillable条件の表示の照合、親の一意性はまだ未完。
始点plusの場合の別の親、その他の面とのfiltrationの両立、parental subcomputadのfiltration、
元のQCatAdjunctionからの全coherentな延長、原典の向きと現模型の水平反対の全比較、
同じF≫U・単位・余単位・HAモデルの照合も引き続き未完である。
今回の最初の位置と厳密な併合条件の保存を、coherentな延長の存在へ読み替えていない。
G01の済みは0、G02以降も未完を維持する。

### 107.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大240秒の短いimpl枠。
セッション71217で実細分より前の対象・実辺・挿入左因子の回収の対象ビルドの終了0を確認した。
最終セッション58980の最大240秒の一つの枠で、
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementFirstMerge:olean
の終了0と、続く追加13根だけの公理監査の終了0を確認した。
最後の型に含めた複数のletのレイアウトと行長の警告を整えてから最終検証した。
先行する72907では対象ビルドと監査はともに終了0だったが、終了確認前に制御枠の期限で終了124となった。
最終枠はビルドと監査の後に自動で閉じる形で外側の終了0を確認した。最終対象ビルドは警告なし。
追加13根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・全出力・最終対象ビルドログは
[g12-first-merge-preservation-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-first-merge-preservation-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み11,754行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §108 G01：元のnerveの退化と、実細分の非退化性の必要十分条件（11-15）

### 108.1 検証済みの追加

追加は **3ファイル278行・明示宣言8**。累計 **103ファイル12,032行・明示宣言660**。
NerveCollapsedEdges.lean は93行・2宣言、WalkingAdjunctionIsoDegeneracy.lean は83行・3宣言、
WalkingAdjunctionRefinementNondegenerateIff.lean は102行・3宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ実細分・実辺・退化の照合と、既存の十分条件の逆方向、その証明の分割であり、一覧IDは追加しない。

任意の圏の実鎖で、一辺が対象の等式による恒等射なら、その辺の面を退化させて元の実関手を回収する。
一点だけを後続点へ動かす実順序関手への比較を構成し、全実射の自然性を使って関手の等式を示した。
従って元のnerveの宇宙持ち上げでも退化になる。
四つのwalking Homでは、実同型の点の個数と値の保存から、実同型が対象の等式による恒等射になることを示した。
これを使い、元の全単体が非退化であることと、全ての隣接実辺が非同型であることの同値を検証した。
退化側の逆方向では、実退化の像から同型な隣接辺を取り出している。

実併合の細分が非退化なら、挿入右辺との照合から実残余射が非同型であることを回収した。
残余射の同型性の既存の全点表示と合わせ、元の単体が非退化のもとで、
実細分の非退化性は、元の指定辺が一つだけの併合の全点条件でないことと同値になる。
実際に選んだ最初の併合にも適用し、最初の実細分について同じ必要十分条件を得た。
位置・同型性・非退化性の新しい証人を入力欄として仮定してはいない。

### 108.2 型と未完の境界

原典はRiehl–Verity §3.1・§4.1–§4.2、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma nerve_sigma_delta_of_eqToHom_edge {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C (n + 1)) (j : Fin (n + 1))
    (hobj : F.obj j.castSucc = F.obj j.succ)
    (hedge : F.map (homOfLE (Fin.castSucc_le_succ j)) = eqToHom hobj) :
    (nerve C).σ j ((nerve C).δ j.castSucc F) = F

lemma uliftNerve_degenerate_of_eqToHom_edge {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C (n + 1)) (j : Fin (n + 1))
    (hobj : F.obj j.castSucc = F.obj j.succ)
    (hedge : F.map (homOfLE (Fin.castSucc_le_succ j)) = eqToHom hobj) :
    ULift.up F ∈ (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).degenerate (n + 1)

lemma walkingAdjunctionIsIso_eqToHom {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f] :
    ∃ h : A = B, f = eqToHom h

lemma walkingAdjunctionHomShape_degenerate_of_isIso {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (j : Fin (n + 1))
    [IsIso (H.map (homOfLE (Fin.castSucc_le_succ j)))] :
    ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).degenerate (n + 1)

lemma walkingAdjunctionHomShape_nondegenerate_iff_no_isIso {n : ℕ}
    {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1) ↔
      ∀ j : Fin (n + 1), ¬ IsIso (H.map (homOfLE (Fin.castSucc_le_succ j)))

lemma walkingAdjunctionBottomMergeResidual_not_isIso_of_nondegenerate
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) :
    ¬ IsIso (walkingAdjunctionBottomMergeResidual
      (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)

lemma walkingAdjunctionBottomMergeRefinement_nondegenerate_iff_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    (ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) ↔
    ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1)

lemma walkingAdjunctionFirstRefinement_nondegenerate_iff_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint} (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    let k := walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
    let m := walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) - 2
    (ULift.up (walkingAdjunctionFirstRefinement H ha hnd) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) ↔
    ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1)
```

原典の文字列表示との全比較とfillable条件の照合、親の一意性、始点plusの親、
その他の面とのfiltrationの両立とparental subcomputadのfiltrationは未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。G01の済みは0、G02以降も未完を維持する。

### 108.3 検証と進み

指定のwith_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドを確認した。
追加8根の小さい公理監査も通り、入力名と出力名が一致し、依存はpropext・Classical.choice・Quot.soundのみ。
最終の固定コマンドは対象ビルドと監査を連続して実行し、外側の終了0も確認した。
最終対象：SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementNondegenerateIff:olean。
入力・根・監査全出力・対象ビルドログは
[g12-isomorphic-edges-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-isomorphic-edges-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み12,032行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §109 G01：指定面と実併合の全点条件からの親の一意性（11-15）

### 109.1 検証済みの追加

追加は **4ファイル361行・明示宣言10**。累計 **107ファイル12,393行・明示宣言670**。
ComposableArrowFaceRigidity.lean は92行・3宣言、ComposableArrowEpiFaceRigidity.lean は81行・2宣言、
WalkingAdjunctionBottomMergeRigidity.lean は125行・4宣言、
WalkingAdjunctionUniqueRefinementParent.lean は63行・1宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ実親・実細分の照合、全射の消去・合成・係数移送とその証明の分割であり、一覧IDは追加しない。

任意の圏の有限実鎖で、指定面の等式から、除いた頂点以外の全実対象と両端が除いた頂点でない全実射を回収した。
有限順序埋め込みの像の補集合が一点であることを使い、各射を同じ面の射に戻している。
従って指定面・挿入対象・その頂点に接する左右の二辺が一致すれば、元の実鎖は全関手として一致する。
さらに左辺がepiなら、指定面内の二辺の合成から右辺を消去で回収するため、右辺の一致を入力に置く必要がない。
epiはこの一般の消去則の仮定であり、次のwalking Homへの適用では実際に構成する。

四つのwalking Homのうち始点minusの二つでは、一つだけの併合の終点の個数と全点の値の条件から、
終点の一致と実左辺の一致を回収した。構成済みの実併合射の全射性と消去則からepiを構成し、
同じ全点条件を持つ任意の元の実辺もepiとなることを示した。
これにより、指定面がHであり、指定位置の左辺が終点の個数m+1・全点の値i↦i−1を持つ任意の実親Pは、
既に構成したwalkingAdjunctionBottomMergeRefinement H k m hA h1と全関手として一致する。
親の存在や右辺の等式・epiを新しい入力欄として仮定していない。

元の全単体Hが非退化なら、指定面とこの全点条件を持つ**非退化な実親が一意に存在すること**は、
元の指定辺が一つだけの併合の条件でないことと同値である。
存在は実細分を取り、一意性は上の全関手の等式、逆方向は§108の非退化性の必要十分条件から得た。
任意の指定位置での元のHomのnerveの実存在一意性であり、原典のfillable条件との全比較はまだ主張していない。

### 109.2 型と未完の境界

原典はRiehl–Verity §4.1–§4.2、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma finiteChainFace_obj_eq {n : ℕ} {F G : ComposableArrows C (n + 1)}
    (p : Fin (n + 2)) (h : finiteChainFace F p = finiteChainFace G p)
    (i : Fin (n + 2)) (hi : i ≠ p) : F.obj i = G.obj i

lemma finiteChainFace_map_heq {n : ℕ} {F G : ComposableArrows C (n + 1)}
    (p : Fin (n + 2)) (h : finiteChainFace F p = finiteChainFace G p)
    {a b : Fin (n + 2)} (hab : a ≤ b) (ha : a ≠ p) (hb : b ≠ p) :
    HEq (F.map (homOfLE hab)) (G.map (homOfLE hab))

lemma composableArrow_eq_of_face_and_incident_edges {n : ℕ}
    {F G : ComposableArrows C (n + 2)} (k : Fin (n + 1))
    (hface : finiteChainFace F k.succ.castSucc = finiteChainFace G k.succ.castSucc)
    (hmid : F.obj k.succ.castSucc = G.obj k.succ.castSucc)
    (hleft : HEq (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))
      (G.map (homOfLE (Fin.castSucc_le_succ k.castSucc))))
    (hright : HEq (F.map (homOfLE (Fin.castSucc_le_succ k.succ)))
      (G.map (homOfLE (Fin.castSucc_le_succ k.succ)))) : F = G

lemma rightFactor_heq_of_epi_comp_heq {A B D A' B' D' : C}
    (hA : A = A') (hB : B = B') (hD : D = D')
    (q : A ⟶ B) (q' : A' ⟶ B') (g : B ⟶ D) (g' : B' ⟶ D')
    [Epi q] (hq : HEq q q') (hc : HEq (q ≫ g) (q' ≫ g')) : HEq g g'

lemma composableArrow_eq_of_face_and_epi_left {n : ℕ}
    {F G : ComposableArrows C (n + 2)} (k : Fin (n + 1))
    (hface : finiteChainFace F k.succ.castSucc = finiteChainFace G k.succ.castSucc)
    (hmid : F.obj k.succ.castSucc = G.obj k.succ.castSucc)
    (hleft : HEq (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))
      (G.map (homOfLE (Fin.castSucc_le_succ k.castSucc))))
    [Epi (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))] : F = G

lemma walkingAdjunctionPureBottomMerge_rigidity {Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom .minus Y} (hA : A = A')
    (f : A ⟶ B) (g : A' ⟶ B') (m : ℕ)
    (hf : walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1)
    (hg : walkingAdjunctionOrdinalCard .minus Y B' = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A'),
        (walkingAdjunctionOrderHom g i).val = i.val - 1) :
    B = B' ∧ HEq f g

lemma walkingAdjunctionBottomMergeArrow_epi {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    Epi (walkingAdjunctionBottomMergeArrow A m hA)

lemma walkingAdjunctionPureBottomMerge_epi {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (hp : walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1) : Epi f

lemma walkingAdjunctionBottomMergeRefinement_unique {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (hface : finiteChainFace P k.succ.castSucc = H)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    P = walkingAdjunctionBottomMergeRefinement H k m hA h1

lemma walkingAdjunctionBottomMergeRefinement_existsUnique_nondegenerate_iff
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    (∃! P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2),
      ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2) ∧
      finiteChainFace P k.succ.castSucc = H ∧
      walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) ↔
    ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1)
```

厳密なルートの指定位置での親の全関手の一意性は今回検証した。
原典の文字列表示との全比較とfillable条件の照合、始点plusの親、
その他の面とのfiltrationの両立とparental subcomputadのfiltrationは未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。G01の済みは0、G02以降も未完を維持する。

### 109.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加10根だけの公理監査を確認した。
最終対象はSerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionUniqueRefinementParent:olean。
最終固定コマンドの対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
追加10根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-unique-refinement-parent-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-unique-refinement-parent-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み12,393行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §110 G01：終端への実射の挿入と始点plusの実親・指定面・原子性（11-15）

### 110.1 検証済みの追加

追加は **4ファイル339行・明示宣言16**。累計 **111ファイル12,732行・明示宣言686**。
ComposableArrowAppend.lean は84行・6宣言、ComposableArrowAppendFaces.lean は68行・1宣言、
ComposableArrowAppendPositions.lean は79行・3宣言、WalkingAdjunctionPlusParent.lean は108行・6宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ全随伴の実親の構成、全関手の面・係数移送・合成・照合とその証明の分割であり、一覧IDは追加しない。

任意の圏の有限実鎖の終端へ実射を挿入し、一つ高次の全実関手を構成した。
長さ0では一辺の関手を取り、正の長さでは尾部に再帰して元の先頭の実射を戻す。
元の始点を保つ等式と指定対象が新しい終点である等式を、実構成と同時に得る。
最後の面が元の全実関手を回収することを、尾部と先頭への挿入の面の合成則で証明した。
長さ0の基底では有限点を明示して全関手を比較している。
挿入した最後の実辺が指定射と異種等式で一致すること、
それより前の全実対象と全隣接実辺が元のものと一致することも検収した。

始点plusの原子的な実全単体Hには、minusからplusへの実生成射の定値関手を前置し、
元の実水平合成でminus始点の全実鎖Lを作った。各頂点の点の個数はHの個数に1を加えたものとなる。
原子のHの終点の個数1から、Lの終点の個数2を証明した。
その終点から個数1の構成済みの実対象への併合射を取り、終端挿入で実全単体の親候補を構成した。
この実親の最後の面はLに全関手として一致する。
両端の個数は原子性の端点判定を満たすので、この実親自体の原子性も検証した。
親の実関手・指定面・原子性の存在を仮定する欄は置いていない。

### 110.2 型と未完の境界

原典はRiehl–Verity Lemma 4.1.4・§4.2、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
def composableArrowAppendData :
    ∀ (n : ℕ) (F : ComposableArrows C n) (B : C) (_f : F.obj (Fin.last n) ⟶ B),
      {G : ComposableArrows C (n + 1) // G.obj 0 = F.obj 0 ∧
        G.obj (Fin.last (n + 1)) = B}

def composableArrowAppend {n : ℕ} (F : ComposableArrows C n) (B : C)
    (f : F.obj (Fin.last n) ⟶ B) : ComposableArrows C (n + 1)

lemma composableArrowAppend_first {n : ℕ} (F : ComposableArrows C n) (B : C)
    (f : F.obj (Fin.last n) ⟶ B) : (composableArrowAppend F B f).obj 0 = F.obj 0

lemma composableArrowAppend_last {n : ℕ} (F : ComposableArrows C n) (B : C)
    (f : F.obj (Fin.last n) ⟶ B) :
    (composableArrowAppend F B f).obj (Fin.last (n + 1)) = B

lemma composableArrowAppend_zero (F : ComposableArrows C 0) (B : C)
    (f : F.obj (Fin.last 0) ⟶ B) :
    composableArrowAppend F B f = ComposableArrows.mk₁ f

lemma composableArrowAppend_succ {n : ℕ} (F : ComposableArrows C (n + 1)) (B : C)
    (f : F.obj (Fin.last (n + 1)) ⟶ B) :
    composableArrowAppend F B f = (composableArrowAppend F.δ₀ B f).precomp
      (F.map' 0 1 ≫ eqToHom (composableArrowAppend_first F.δ₀ B f).symm)

lemma composableArrowAppend_face_last :
    ∀ (n : ℕ) (F : ComposableArrows C n) (B : C) (f : F.obj (Fin.last n) ⟶ B),
      finiteChainFace (composableArrowAppend F B f) (Fin.last (n + 1)) = F

lemma composableArrowAppend_last_edge :
    ∀ (n : ℕ) (F : ComposableArrows C n) (B : C) (f : F.obj (Fin.last n) ⟶ B),
      HEq ((composableArrowAppend F B f).map
        (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) f

lemma composableArrowAppend_before_obj {n : ℕ} (F : ComposableArrows C n) (B : C)
    (f : F.obj (Fin.last n) ⟶ B) (i : Fin (n + 1)) :
    (composableArrowAppend F B f).obj i.castSucc = F.obj i

lemma composableArrowAppend_before_edge {n : ℕ} (F : ComposableArrows C (n + 1)) (B : C)
    (f : F.obj (Fin.last (n + 1)) ⟶ B) (j : Fin (n + 1)) :
    HEq ((composableArrowAppend F B f).map
      (homOfLE (Fin.castSucc_le_succ j.castSucc)))
      (F.map (homOfLE (Fin.castSucc_le_succ j)))

def walkingAdjunctionPlusParentPrefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) :
    ComposableArrows (walkingAdjunctionHom .minus Y) n

lemma walkingAdjunctionPlusParentPrefix_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard .minus Y ((walkingAdjunctionPlusParentPrefix H).obj i) =
      1 + walkingAdjunctionOrdinalCard .plus Y (H.obj i)

lemma walkingAdjunctionPlusParentPrefix_last_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard .minus Y
      ((walkingAdjunctionPlusParentPrefix H).obj (Fin.last n)) = 0 + 2

def walkingAdjunctionPlusParent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)

lemma walkingAdjunctionPlusParent_face_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    finiteChainFace (walkingAdjunctionPlusParent H ha) (Fin.last (n + 1)) =
      walkingAdjunctionPlusParentPrefix H

lemma walkingAdjunctionPlusParent_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionPlusParent H ha)
```

始点plusの実親の全関手・指定面・原子性は今回構成したが、
元のHが非退化ならこの親も非退化であることはまだ今回の追加に含めていない。
原典の文字列表示とfillable条件との全比較、始点plusの実親の対応の検収、
その他の面とのfiltrationの両立とparental subcomputadのfiltrationは未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。G01の済みは0、G02以降も未完を維持する。

### 110.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加16根だけの公理監査を確認した。
最終対象はSerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParent:olean。
最終固定コマンドの対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
追加16根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-plus-parent-construction-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-plus-parent-construction-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み12,732行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §111 G01：始点plusの実親の非退化性・純粋な終端辺・最初の位置（11-15）

### 111.1 検証済みの追加

追加は **4ファイル328行・明示宣言8**。累計 **115ファイル13,060行・明示宣言694**。
WalkingAdjunctionPrefixIsomorphisms.lean は78行・2宣言、
WalkingAdjunctionPlusParentNondegenerate.lean は79行・1宣言、
WalkingAdjunctionPrefixBottomMerge.lean は50行・1宣言、
WalkingAdjunctionPlusParentPositions.lean は121行・4宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ実親の構成、同型性の反映・実辺の係数移送・全合成・最初の位置の照合と
その証明の分割であり、一覧IDは追加しない。

minusからplusへの固定した任意の実対象の前置について、実水平合成が同型になるなら元の射が同型となることを示した。
点の個数の加法則から元の両対象を同一視し、同型の剛性と実水平合成の忠実性で元の射を恒等射へ戻す。
元の全鎖が非退化なら、生成射を前置した全鎖も非退化である。
前置した実辺の型を明示し、同型性を反映する実射に型クラス推論を渡している。

始点plusの原子的な全鎖Hが非退化なら、§110で実際に構成した親も元のHomのnerveで非退化となることを示した。
挿入した最後の辺の両端の個数は2と1なので同型ではない。
それより前の辺は終端挿入の法則で前置した元の辺に戻し、同型性の反映で否定した。
長さ0のHも含み、親の非退化性や全隣接辺の非同型性を新しい入力に置いていない。

生成射を前置した全隣接辺では、順序和の右区間に入る点の像は正となる。
この実順序和の計算から、前置した全鎖に底の二点の併合の辺がないことを示した。
終端挿入の実辺の照合を使い、親の最後より前の全位置でも併合が起きないことを検証した。
最後の実辺は終点の個数1・全点の値i↦i−1という一つだけの併合の条件を満たし、
個数2の始点の値1の点から実併合の位置の証人を構成した。
元の有限最小元で選んだ最初の併合の位置は、この親では最後の辺に一致する。
最後の位置を新しい仮定とせず、元の実最小元との等式を示した。

### 111.2 型と未完の境界

原典はRiehl–Verity Lemma 4.1.4・§4.2、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma walkingAdjunctionPrefix_reflectsIsIso {Y : WalkingAdjunctionPoint}
    (U : walkingAdjunctionHom .minus .plus) {A B : walkingAdjunctionHom .plus Y} (f : A ⟶ B)
    [IsIso ((walkingAdjunctionHorizontal .minus .plus Y).map
      (X := (U, A)) (Y := (U, B)) (𝟙 U, f))] : IsIso f

lemma walkingAdjunctionPlusParentPrefix_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate (n + 1)) :
    ULift.up (walkingAdjunctionPlusParentPrefix H) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)

lemma walkingAdjunctionPlusParent_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n) :
    ULift.up (walkingAdjunctionPlusParent H ha) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)

lemma walkingAdjunctionPlusParentPrefix_no_bottom_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) (n + 1)) (j : Fin (n + 1)) :
    ¬ WalkingAdjunctionBottomMergeAt (walkingAdjunctionPlusParentPrefix H) j

lemma walkingAdjunctionPlusParent_no_before_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) (j : Fin n) :
    ¬ WalkingAdjunctionBottomMergeAt (walkingAdjunctionPlusParent H ha) j.castSucc

lemma walkingAdjunctionPlusParent_last_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).succ) = 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom ((walkingAdjunctionPlusParent H ha).map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1

lemma walkingAdjunctionPlusParent_last_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionBottomMergeAt (walkingAdjunctionPlusParent H ha) (Fin.last n)

lemma walkingAdjunctionPlusParent_first_index {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n) :
    walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionPlusParent H ha)
      (walkingAdjunctionAtomic_endpoint_cards _ (walkingAdjunctionPlusParent_atomic H ha)).2
      (walkingAdjunctionPlusParent_nondegenerate H ha hnd) = Fin.last n
```

始点plusの実親は、今回、原子性・非退化性・指定面・最初の位置とそこでの全点の純粋性まで検証した。
原典の文字列表示とfillable条件との全比較、実親の対応の逆方向の全検収、
その他の面とのfiltrationの両立とparental subcomputadのfiltrationは未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。G01の済みは0、G02以降も未完を維持する。

### 111.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加8根だけの公理監査を確認した。
最終対象はSerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParentPositions:olean。
最終固定コマンドの対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
追加8根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-plus-parent-nondegenerate-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-plus-parent-nondegenerate-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み13,060行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §112 G01：一点の実前置因子の回収・元の全関手への合成・往復（11-15）

### 112.1 検証済みの追加

追加は **3ファイル337行・明示宣言14**。累計 **118ファイル13,397行・明示宣言708**。
WalkingAdjunctionZeroReflection.lean は75行・2宣言、
WalkingAdjunctionBottomPointCut.lean は106行・4宣言、
WalkingAdjunctionRemoveBottomPrefix.lean は156行・8宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ実親・水平分解の構成、全実射の合成・切れ目の自然性・係数移送・往復の照合と
その証明の分割であり、一覧IDは追加しない。

minus始点の全実鎖で、全隣接辺が二番目の点を0へ送らなければ、
終点への全実射が0の逆像を反映することを逆帰納で示した。
一般の二頂点間の実射も、終点まで合成し、その後半の実射の最小元保存を使うことで同じ反映を満たす。
長さ0の鎖も含む。従来の終点が一点の場合に限った計算を、終点の個数を仮定しない全射の法則に広げた。

全実頂点で座標1のplusの切れ目を構成した。
全実射の最小元保存と0の逆像の反映から、実区間表示がこの切れ目を保つことを証明した。
終点の個数が2なら、この実切れ目は両外端の間にあるので、
既存の実区間関手の全水平分解を適用して左右の全実関手と合成の等式を構成できる。
切れ目・因子・自然性・全合成の等式の存在を仮定する入力欄は設けていない。

左因子は全頂点で一点を持つことを、切れ目の座標1と左外端の座標0から示した。
一点の終点への元の実射は一意であることを実順序表示の忠実性から検証し、
左因子全体がminusからplusへの実生成射の定値関手に一致することを示した。
右因子を始点plusの全実関手として回収し、それへ実生成射を前置すると元の全実鎖へ戻ることを証明した。
この実右因子の各頂点の点の個数に1を加えると元の個数となる。

さらに生成射の前置は全実関手を区別することを、対象の個数と実水平合成の忠実性から示した。
前置した任意の長さの全鎖には、隣接辺が値1の点を0へ送らないことも明示した。
従って、元から始点plusの実原子を前置していた場合には、その一点を取り除く操作が、
元の同じ実全関手へ戻ることを検証した。逆の証人を入力に置いた往復ではない。

### 112.2 型と未完の境界

原典はRiehl–Verity Proposition 3.1.10・Lemma 4.1.4・§4.2、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma walkingAdjunctionReflectsZeroToLast_of_no_bottom_merge {n : ℕ}
    {Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0) :
    ∀ (i : Fin (n + 1)) (a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj i))),
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.le_last i))) a).val = 0 → a.val = 0

lemma walkingAdjunctionReflectsZeroMap_of_no_bottom_merge {n : ℕ}
    {Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    {i j : Fin (n + 1)} (hij : i ≤ j)
    (a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj i)))
    (ha : (walkingAdjunctionOrderHom (H.map (homOfLE hij)) a).val = 0) : a.val = 0

def walkingAdjunctionBottomPointCut {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0) : WalkingAdjunctionPlusCut H

lemma walkingAdjunctionBottomPointCut_val {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0) (i : Fin (n + 1)) :
    ((walkingAdjunctionBottomPointCut H hno).value i).val = 1

def walkingAdjunctionBottomPointFactorization {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) :
    WalkingAdjunctionFactorization H

lemma walkingAdjunctionBottomPointFactorization_left_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2)
    (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard .minus .plus
      ((walkingAdjunctionBottomPointFactorization H hno hlast).left.obj i) = 1

lemma walkingAdjunctionHom_ext_of_card_one_target {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f g : A ⟶ B)
    (hc : walkingAdjunctionOrdinalCard X Y B = 1) : f = g

lemma walkingAdjunctionBottomPointFactorization_left {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) :
    (walkingAdjunctionBottomPointFactorization H hno hlast).left =
      (CategoryTheory.Functor.const (Fin (n + 1))).obj
        (walkingAdjunctionGeneratorVertex .minus)

def walkingAdjunctionRemoveBottomPrefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) :
    ComposableArrows (walkingAdjunctionHom .plus Y) n

lemma walkingAdjunctionRemoveBottomPrefix_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) :
    walkingAdjunctionPlusParentPrefix (walkingAdjunctionRemoveBottomPrefix H hno hlast) = H

lemma walkingAdjunctionRemoveBottomPrefix_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) (i : Fin (n + 1)) :
    1 + walkingAdjunctionOrdinalCard .plus Y
      ((walkingAdjunctionRemoveBottomPrefix H hno hlast).obj i) =
        walkingAdjunctionOrdinalCard .minus Y (H.obj i)

lemma walkingAdjunctionPlusParentPrefix_injective {n : ℕ} {Y : WalkingAdjunctionPoint} :
    Function.Injective (walkingAdjunctionPlusParentPrefix (n := n) (Y := Y))

lemma walkingAdjunctionPlusParentPrefix_no_one {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) :
    ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y
      ((walkingAdjunctionPlusParentPrefix H).obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        ((walkingAdjunctionPlusParentPrefix H).map
          (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0

lemma walkingAdjunctionRemoveBottomPrefix_roundtrip {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionRemoveBottomPrefix (walkingAdjunctionPlusParentPrefix H)
      (walkingAdjunctionPlusParentPrefix_no_one H)
      (walkingAdjunctionPlusParentPrefix_last_card H ha) = H
```

今回は、終点が二点・全隣接辺に併合がない実鎖から始点plusの実因子を回収し、全合成と前置の往復まで検証した。
任意の最後の深さの純粋な実親から、その最後の面をこの回収へ渡すための条件を自動で供給し、
回収した因子の原子性・非退化性を含む実親の対応の逆方向を全て検収する部分はまだ未完。
原典の文字列表示とfillable条件との全比較、その他の面とのfiltrationの両立、
parental subcomputadのfiltration、元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。G01の済みは0、G02以降も未完を維持する。

### 112.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加14根だけの公理監査を確認した。
最終対象はSerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRemoveBottomPrefix:olean。
最終固定コマンドの対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
追加14根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-remove-bottom-prefix-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-remove-bottom-prefix-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み13,397行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §113 G01：最後の純粋な実親からの原子的・非退化な実子と両方向の往復（11-15）

### 113.1 検証済みの追加

追加は **5ファイル463行・明示宣言15**。累計 **123ファイル13,860行・明示宣言723**。
ComposableArrowLastFace.lean は55行・3宣言、
WalkingAdjunctionLastParentUniqueness.lean は59行・1宣言、
WalkingAdjunctionLastFaceData.lean は94行・3宣言、
WalkingAdjunctionPlusChild.lean は180行・5宣言、
WalkingAdjunctionPlusParentChildRoundtrip.lean は75行・3宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ実親・水平分解の構成、最初の実位置・全射の合成・実同型・係数移送・往復の照合と
その証明の分割であり、一覧IDは追加しない。

最後の実面の添字関手をcastSuccの実関手に同一視し、最後以前の全実対象・隣接実辺を回収した。
同じ最後の実面を持ち、両方の実終点の個数が1である二つの実全鎖は、全関手として一致する。
最後以外の対象・辺は面から回収し、最後の実対象は個数の単射性、最後の実辺は一点の終点への射の一意性で比較する。
最後の実辺の等式は入力に置いていない。

minus始点の原子的で非退化な実全単体Pについて、構成済みの最初の実併合の位置が最後の辺であり、
その辺が元の始点の個数から定まる一つだけの併合の全点条件を満たす場合を扱った。
実最小元の最小性から最後より前の全実辺で併合がないことを示し、最後の実面の全辺へ移した。
最初の併合の証人は二点以上を与え、原子の終点の個数1と純粋性の個数の条件から、
その最後の実面の終点の個数が2となることを得た。
これらは一点の前置を除く構成の入力を実際に供給する法則であり、
実面の条件を別の存在・反映・選択の仮定として増やしていない。

最後の実面に§112の一点の前置の回収を適用し、始点plusの実全関手である子を構成した。
回収した子の原子性は、個数の加法則・元の親の両端・元の端点判定から証明した。
非退化性は、子の同型な辺からIso.prodで積の実同型を作り、実水平合成で前置した辺へ送り、
元の最後の実面と親の辺へ戻して親の非退化性に反することから示した。長さ0も含む。
子の存在・原子性・非退化性を新しい入力にしていない。

この子に生成射を前置すると、元の親の最後の実面へ全関手として戻る。
構成した子から再び実親を作ると、同じ最後の実面と個数1の終点による一意性で、元の同じ実親へ戻る。
逆に、始点plusの非退化な実原子Hから実親を構成し、そこからこの実子を回収しても、
前置の単射性と指定面の等式から、元の同じHへ全関手として戻ることを示した。
両方向とも同型類に落とす前の実全関手の等式である。

### 113.2 型と未完の境界

原典はRiehl–Verity Lemma 4.1.4・§4.2、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma finiteChainFaceIndex_last (n : ℕ) :
    finiteChainFaceIndex (Fin.last (n + 1)) = Fin.castSuccFunctor (n + 1)

lemma finiteChainFace_last_obj {n : ℕ} (F : ComposableArrows C (n + 1)) (i : Fin (n + 1)) :
    (finiteChainFace F (Fin.last (n + 1))).obj i = F.obj i.castSucc

lemma finiteChainFace_last_edge {n : ℕ} (F : ComposableArrows C (n + 2)) (j : Fin (n + 1)) :
    HEq ((finiteChainFace F (Fin.last (n + 2))).map
      (homOfLE (Fin.castSucc_le_succ j)))
      (F.map (homOfLE (Fin.castSucc_le_succ j.castSucc)))

lemma walkingAdjunction_eq_of_last_face_and_card_one {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F G : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (hface : finiteChainFace F (Fin.last (n + 1)) = finiteChainFace G (Fin.last (n + 1)))
    (hf : walkingAdjunctionOrdinalCard X Y (F.obj (Fin.last (n + 1))) = 1)
    (hg : walkingAdjunctionOrdinalCard X Y (G.obj (Fin.last (n + 1))) = 1) : F = G

lemma walkingAdjunctionNoMerge_before_last_of_first_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n) (j : Fin n) :
    ¬ WalkingAdjunctionBottomMergeAt P j.castSucc

lemma walkingAdjunctionLastFace_no_one_of_first_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n) :
    ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y
      ((finiteChainFace P (Fin.last (n + 1))).obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        ((finiteChainFace P (Fin.last (n + 1))).map
          (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0

lemma walkingAdjunctionLastFace_card_two_of_first_last_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    walkingAdjunctionOrdinalCard .minus Y
      ((finiteChainFace P (Fin.last (n + 1))).obj (Fin.last n)) = 2

def walkingAdjunctionPlusChild {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    ComposableArrows (walkingAdjunctionHom .plus Y) n

lemma walkingAdjunctionPlusChild_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    walkingAdjunctionPlusParentPrefix (walkingAdjunctionPlusChild P ha hnd hidx hp) =
      finiteChainFace P (Fin.last (n + 1))

lemma walkingAdjunctionPlusChild_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionPlusChild P ha hnd hidx hp)

lemma walkingAdjunctionPlusChild_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    ULift.up (walkingAdjunctionPlusChild P ha hnd hidx hp) ∈
      (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n

lemma walkingAdjunctionPlusChild_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    walkingAdjunctionPlusParent (walkingAdjunctionPlusChild P ha hnd hidx hp)
      (walkingAdjunctionPlusChild_atomic P ha hnd hidx hp) = P

lemma walkingAdjunctionPlusParent_before_last_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard .minus Y
      ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc) = 2

lemma walkingAdjunctionPlusParent_last_pure_with_source {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).succ) =
      walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom ((walkingAdjunctionPlusParent H ha).map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1

lemma walkingAdjunctionPlusParent_child {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n) :
    walkingAdjunctionPlusChild (walkingAdjunctionPlusParent H ha)
      (walkingAdjunctionPlusParent_atomic H ha) (walkingAdjunctionPlusParent_nondegenerate H ha hnd)
      (walkingAdjunctionPlusParent_first_index H ha hnd)
      (walkingAdjunctionPlusParent_last_pure_with_source H ha) = H
```

実有限順序の模型の最後の深さの条件については、実親と始点plusの原子的・非退化な子の両方向の実構成と往復を検証した。
原典の文字列表示とfillable条件との全比較、内側の深さの実親の逆方向の全照合、
その他の面とのfiltrationの両立、parental subcomputadのfiltration、
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合はまだ未完である。G01の済みは0、G02以降も未完を維持する。

### 113.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加15根だけの公理監査を確認した。
最終対象はSerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParentChildRoundtrip:olean。
最終固定コマンドの対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
回収した子の終点の型を明示し、積の実辺の同型をIso.prodから構成してから最終検証した。
追加15根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-plus-parent-child-roundtrip-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-plus-parent-child-roundtrip-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み13,860行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §114 G01：内側の実面の非退化性・最初の位置・元の純粋な実親の全関手の復元（11-15）

### 114.1 検証済みの追加

追加は **4ファイル435行・明示宣言18**。累計 **127ファイル14,295行・明示宣言741**。
ComposableArrowInnerFace.lean は118行・7宣言、
WalkingAdjunctionInnerFaceNondegenerate.lean は105行・4宣言、
WalkingAdjunctionInnerFaceFirstMerge.lean は97行・3宣言、
WalkingAdjunctionInnerParentReconstruction.lean は115行・4宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ実親・実細分の構成、元の実辺の全合成・実最小元・実同型・係数移送・往復の照合と
その証明の分割であり、一覧IDは追加しない。

任意の圏の実全鎖について、内側の実面の全対象と隣接辺を元の実鎖へ照合した。
指定位置までの対象とそれより前の辺は元の同じ位置、それより後は元の一つ後の位置となる。
指定辺は元の二つの隣接実辺の合成に異種等式で一致する。内側の面は実終点も保つ。
両端の実有限添字を同一視すれば全実射も一致することを使い、全射を保持している。

原子的な実親の内側の指定面は、両端の対象が変わらないので原子的となる。
左の元の実辺に底の二点の実併合があれば、右の実射の最小元保存により合成辺も実際に併合する。
実併合の証人の値1と実同型の全点の値の保存から、併合する実辺は同型でないことを示した。
親が非退化なら、子の指定辺はこの実併合で非同型となり、他の全実辺も親の非同型辺へ戻るので、
子は元のHomのnerveで非退化となる。子の原子性・非退化性を新しい入力に置いていない。

親の実際に選んだ最初の併合の位置が内側の指定した辺である場合には、
実最小元の所属から左の実辺の併合の証人を供給した。
指定辺より前の子の実辺で併合があれば、元の親にも同じ位置で併合があり、実最小元の最小性に反する。
指定合成辺の実併合と合わせ、子の実際に選んだ最初の位置が指定位置に一致することを示した。

親の指定した左の実辺が一つだけの併合の全点条件を満たす場合、
子の始点の個数と実併合の証人を供給し、子の指定辺を実際に細分した実全関手が、元の親と一致することを証明した。
使った一意性は、指定面と純粋な左の実辺から全実関手を回収する§109の法則である。
さらに親の非退化性と、実細分の非退化性の必要十分条件から、子の指定辺は非純粋となることを回収した。
親が最初の実位置で純粋に併合している場合には、子の実最小元と始点の実個数を照合し、
元のwalkingAdjunctionFirstRefinementで親を選び直しても、元の同じ実親へ全関手として戻ることを示した。
最後の個数の書き換えは実面の対象の型で明示している。

### 114.2 型と未完の境界

原典はRiehl–Verity Lemma 4.1.3・§4.2、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma finiteChainFace_map_heq_of_indices {n : ℕ} (F : ComposableArrows C (n + 1))
    (p : Fin (n + 2)) {a b : Fin (n + 1)} {a' b' : Fin (n + 2)}
    (ha : p.succAbove a = a') (hb : p.succAbove b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
    HEq ((finiteChainFace F p).map (homOfLE hab)) (F.map (homOfLE hab'))

lemma finiteChainFace_inner_before_obj {n : ℕ} (F : ComposableArrows C (n + 2))
    (k : Fin (n + 1)) (i : Fin (n + 2)) (hi : i.val ≤ k.val) :
    (finiteChainFace F k.succ.castSucc).obj i = F.obj i.castSucc

lemma finiteChainFace_inner_after_obj {n : ℕ} (F : ComposableArrows C (n + 2))
    (k : Fin (n + 1)) (i : Fin (n + 2)) (hi : k.val < i.val) :
    (finiteChainFace F k.succ.castSucc).obj i = F.obj i.succ

lemma finiteChainFace_inner_before_edge {n : ℕ} (F : ComposableArrows C (n + 2))
    (k j : Fin (n + 1)) (hj : j < k) :
    HEq ((finiteChainFace F k.succ.castSucc).map (homOfLE (Fin.castSucc_le_succ j)))
      (F.map (homOfLE (Fin.castSucc_le_succ j.castSucc)))

lemma finiteChainFace_inner_after_edge {n : ℕ} (F : ComposableArrows C (n + 2))
    (k j : Fin (n + 1)) (hj : k < j) :
    HEq ((finiteChainFace F k.succ.castSucc).map (homOfLE (Fin.castSucc_le_succ j)))
      (F.map (homOfLE (Fin.castSucc_le_succ j.succ)))

lemma finiteChainFace_inner_merged_edge {n : ℕ} (F : ComposableArrows C (n + 2))
    (k : Fin (n + 1)) :
    HEq ((finiteChainFace F k.succ.castSucc).map (homOfLE (Fin.castSucc_le_succ k)))
      (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
        F.map (homOfLE (Fin.castSucc_le_succ k.succ)))

lemma finiteChainFace_inner_last {n : ℕ} (F : ComposableArrows C (n + 2)) (k : Fin (n + 1)) :
    (finiteChainFace F k.succ.castSucc).obj (Fin.last (n + 1)) = F.obj (Fin.last (n + 2))

lemma WalkingAdjunctionBottomMergeAt.not_isIso {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)} {k : Fin (n + 1)}
    (h : WalkingAdjunctionBottomMergeAt H k) :
    ¬ IsIso (H.map (homOfLE (Fin.castSucc_le_succ k)))

lemma walkingAdjunctionInnerFace_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (finiteChainFace P k.succ.castSucc)

lemma walkingAdjunctionInnerFace_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc) :
    WalkingAdjunctionBottomMergeAt (finiteChainFace P k.succ.castSucc) k

lemma walkingAdjunctionInnerFace_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc) :
    ULift.up (finiteChainFace P k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)

lemma walkingAdjunctionInnerFace_first_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc) :
    WalkingAdjunctionBottomMergeAt P k.castSucc

lemma walkingAdjunctionInnerFace_no_before_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc)
    (j : Fin (n + 1)) (hj : j < k) :
    ¬ WalkingAdjunctionBottomMergeAt (finiteChainFace P k.succ.castSucc) j

lemma walkingAdjunctionInnerFace_first_index {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc) :
    walkingAdjunctionFirstBottomMergeIndex (finiteChainFace P k.succ.castSucc)
      (walkingAdjunctionAtomic_endpoint_cards _ (walkingAdjunctionInnerFace_atomic P k ha)).2
      (walkingAdjunctionInnerFace_nondegenerate P k hnd
        (walkingAdjunctionInnerFace_first_merge P k ha hnd hidx)) = k

lemma walkingAdjunctionInnerFace_source_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc) :
    walkingAdjunctionOrdinalCard .minus Y
      ((finiteChainFace P k.succ.castSucc).obj k.castSucc) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 2

lemma walkingAdjunctionInnerFace_refinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    P = walkingAdjunctionBottomMergeRefinement (finiteChainFace P k.succ.castSucc) k
      (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2)
      (walkingAdjunctionInnerFace_source_card P k hm)
      (walkingAdjunctionInnerFace_merge P k hm).one_zero

lemma walkingAdjunctionInnerFace_not_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    ¬ (walkingAdjunctionOrdinalCard .minus Y
        ((finiteChainFace P k.succ.castSucc).obj k.succ) =
          walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((finiteChainFace P k.succ.castSucc).obj k.castSucc)),
        (walkingAdjunctionOrderHom ((finiteChainFace P k.succ.castSucc).map
          (homOfLE (Fin.castSucc_le_succ k))) i).val = i.val - 1)

lemma walkingAdjunctionInnerFace_firstRefinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    walkingAdjunctionFirstRefinement (finiteChainFace P k.succ.castSucc)
      (walkingAdjunctionInnerFace_atomic P k ha)
      (walkingAdjunctionInnerFace_nondegenerate P k hnd
        (walkingAdjunctionInnerFace_first_merge P k ha hnd hidx)) = P
```

実有限順序の模型では、内側の純粋な最初の親からの指定面について、
原子性・非退化性・最初の位置・非純粋性・元の実親への再構成を検証した。
順方向の選択した実細分の指定面が元の子へ戻る等式は既存の実指定面の法則である。
ただし原典の文字列表示とfillable条件との全比較、その他の面とのfiltrationの両立、
parental subcomputadのfiltration、元のQCatAdjunctionからの全coherentな延長、
水平反対の向きの全比較、同じF≫U・単位・余単位・HAモデルとの照合はまだ未完である。
G01の済みは0、G02以降も未完を維持する。

### 114.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加18根だけの公理監査を確認した。
最終対象はSerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionInnerParentReconstruction:olean。
最終固定コマンドの対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
追加18根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-inner-parent-reconstruction-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-inner-parent-reconstruction-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み14,295行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §115 G01：実像の個数・実辺の変化量・非退化原子の次元境界・実親の幅の保存（11-15）

### 115.1 検証済みの追加

追加は **5ファイル554行・明示宣言28**。累計 **132ファイル14,849行・明示宣言769**。
OrdinalImageCard.lean は104行・7宣言、OrdinalMapVariation.lean は103行・8宣言、
WalkingAdjunctionOrdinalWidth.lean は117行・5宣言、
WalkingAdjunctionOrdinalWidthPrecomp.lean は100行・4宣言、
WalkingAdjunctionOrdinalWidthRefinement.lean は130行・4宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ実全随伴・実親の構成とその実filtrationに必要な個数の表示、
既存の実射の全合成・係数移送・実同型・全射・幅の照合とその証明の分割であり、一覧IDは追加しない。

原典の[Riehl–Verity Proposition 4.2.15](https://emilyriehl.github.io/files/adjunctions.pdf)を再確認した。
原典のfiltrationは幅・深さ・次元の辞書式順序と、幅に対する次元の境界を使う。
今回の追加は現在の実有限順序模型でそのための個数と幅の表示を検収するものであり、
文字列の幅との全比較やfiltrationの存在を仮定してはいない。

実有限単調射の像の個数を構成し、始点・終点の個数以下であること、
始点の個数に等しいことが単射性、終点の個数に等しいことが全射性に同値であることを検証した。
合成の実像の個数について、中間集合を前半の像とその補集合に分けることで下限を得た。
前半が全射なら、合成の実像の個数は後半の実像の個数と一致する。

実辺の変化量を「始点の個数＋終点の個数−実像の個数の2倍」として自然数で定めた。
変化量0では両端の個数が等しく、有限単調射の全点の値が保たれることを示した。
四つのwalking Homでは、変化量0は元の実射の同型性と同値となる。
従って非同型な実辺では変化量は正である。
二辺の合成の変化量は元の変化量の和以下であり、前半が全射なら等しい。
両端の個数の差も変化量で押さえられる。

実全鎖の両端の個数から両端の補正を除き、全隣接実辺の変化量を加えた有限順序の幅を定めた。
原子的な実全単体では、この幅は1と全実辺の変化量の和に等しい。
元のHomのnerveで非退化な原子では全隣接辺が非同型なので各変化量は1以上となり、
その次元はこの有限順序の幅より小さいことを証明した。長さ0も含む。

両端と実射の等式による係数移送が変化量を保つこと、先頭への実射の挿入による
全実辺の変化量の和と幅の変化を示した。補正の減算が実個数以下であることも検収した。
元の一辺と同じ変化量の和を持つ二辺への実細分は、任意の実位置で有限順序の幅を保つ。
先頭の場合は二回の挿入と元の分解の幅の式、それ以外は尾部の再帰と対象の輸送を使った。
実底併合の全射性と元の射への因子化からこの条件を自動で供給し、
実底併合による実細分と、実最小元で選んだ最初の実親は、この幅を保つことを検証した。
親の幅の保存を新しい入力にしていない。

### 115.2 型と未完の境界

HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）への全coherentな延長の前の実法則。
追加の型は以下。

```lean
def ordinalImageCard {m n : ℕ} (f : Fin m →o Fin n) : ℕ := (Finset.univ.image f).card

/-- 概要：実像の個数は実始点の個数以下。
方針：有限像の個数の上限。規約：空も含む。
使われ方：Riehl–Verity Proposition 4.2.15の実辺の変化量。 -/
lemma ordinalImageCard_le_source {m n : ℕ} (f : Fin m →o Fin n) : ordinalImageCard f ≤ m

lemma ordinalImageCard_le_source {m n : ℕ} (f : Fin m →o Fin n) : ordinalImageCard f ≤ m

lemma ordinalImageCard_le_target {m n : ℕ} (f : Fin m →o Fin n) : ordinalImageCard f ≤ n

lemma ordinalImageCard_eq_source_iff {m n : ℕ} (f : Fin m →o Fin n) :
    ordinalImageCard f = m ↔ Function.Injective f

lemma ordinalImageCard_eq_target_iff {m n : ℕ} (f : Fin m →o Fin n) :
    ordinalImageCard f = n ↔ Function.Surjective f

lemma ordinalImageCard_comp_lower_bound {a b c : ℕ} (f : Fin a →o Fin b) (g : Fin b →o Fin c) :
    ordinalImageCard f + ordinalImageCard g ≤ b + ordinalImageCard (g.comp f)

lemma ordinalImageCard_comp_of_surjective {a b c : ℕ} (f : Fin a →o Fin b)
    (g : Fin b →o Fin c) (hf : Function.Surjective f) :
    ordinalImageCard (g.comp f) = ordinalImageCard g

def ordinalMapVariation {m n : ℕ} (f : Fin m →o Fin n) : ℕ := m + n - 2 * ordinalImageCard f

/-- 概要：変化量0の実辺は両端の個数を保つ。
方針：像の個数の両方の上限を使う。規約：空も含む。
使われ方：Riehl–Verity §4.2の実非退化辺の変化量の正値。 -/
lemma ordinalMapVariation_zero_card {m n : ℕ} (f : Fin m →o Fin n)
    (h : ordinalMapVariation f = 0) : m = n

lemma ordinalMapVariation_zero_card {m n : ℕ} (f : Fin m →o Fin n)
    (h : ordinalMapVariation f = 0) : m = n

lemma ordinalMapVariation_zero_val {m n : ℕ} (f : Fin m →o Fin n)
    (h : ordinalMapVariation f = 0) (i : Fin m) : (f i).val = i.val

lemma ordinalMapVariation_id (m : ℕ) : ordinalMapVariation (OrderHom.id (α := Fin m)) = 0

lemma ordinalMapVariation_comp_le {a b c : ℕ} (f : Fin a →o Fin b) (g : Fin b →o Fin c) :
    ordinalMapVariation (g.comp f) ≤ ordinalMapVariation f + ordinalMapVariation g

lemma ordinalMapVariation_comp_of_surjective {a b c : ℕ} (f : Fin a →o Fin b)
    (g : Fin b →o Fin c) (hf : Function.Surjective f) :
    ordinalMapVariation (g.comp f) = ordinalMapVariation f + ordinalMapVariation g

lemma ordinalMapVariation_source_le {m n : ℕ} (f : Fin m →o Fin n) :
    m ≤ n + ordinalMapVariation f

lemma ordinalMapVariation_target_le {m n : ℕ} (f : Fin m →o Fin n) :
    n ≤ m + ordinalMapVariation f

lemma walkingAdjunctionMapVariation_zero_iff_isIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) :
    ordinalMapVariation (walkingAdjunctionOrderHom f) = 0 ↔ IsIso f

lemma walkingAdjunctionMapVariation_pos_of_not_isIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) (h : ¬ IsIso f) :
    0 < ordinalMapVariation (walkingAdjunctionOrderHom f)

def walkingAdjunctionOrdinalWidth {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) : ℕ

lemma walkingAdjunctionOrdinalWidth_atomic {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalWidth H = 1 + ∑ j : Fin n, ordinalMapVariation
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))

lemma walkingAdjunctionOrdinalWidth_dimension_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate n) :
    n < walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionMapVariation_heq {X Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom X Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    ordinalMapVariation (walkingAdjunctionOrderHom f) =
      ordinalMapVariation (walkingAdjunctionOrderHom g)

lemma walkingAdjunctionCard_pair_corrections_le (X Y : WalkingAdjunctionPoint)
    (A B : walkingAdjunctionHom X Y) :
    walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ≤
      walkingAdjunctionOrdinalCard X Y A + walkingAdjunctionOrdinalCard X Y B

lemma walkingAdjunctionPrecomp_variation_sum {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) {A : walkingAdjunctionHom X Y}
    (f : A ⟶ H.left) :
    (∑ j : Fin (n + 1), ordinalMapVariation
      (walkingAdjunctionOrderHom ((H.precomp f).map (homOfLE (Fin.castSucc_le_succ j))))) =
    ordinalMapVariation (walkingAdjunctionOrderHom f) +
      ∑ j : Fin n, ordinalMapVariation
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))

lemma walkingAdjunctionOrdinalWidth_precomp {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) {A : walkingAdjunctionHom X Y}
    (f : A ⟶ H.left) :
    walkingAdjunctionOrdinalWidth (H.precomp f) + walkingAdjunctionOrdinalCard X Y H.left =
      walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y A +
        ordinalMapVariation (walkingAdjunctionOrderHom f)

lemma walkingAdjunctionOrdinalWidth_refinement_zero {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (B : walkingAdjunctionHom X Y)
    (q : H.obj (0 : Fin (n + 1)).castSucc ⟶ B)
    (g : B ⟶ H.obj (0 : Fin (n + 1)).succ)
    (hv : ordinalMapVariation (walkingAdjunctionOrderHom q) +
      ordinalMapVariation (walkingAdjunctionOrderHom g) =
        ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1))) :
    walkingAdjunctionOrdinalWidth (composableArrowRefinement H 0 B q g) =
      walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionOrdinalWidth_refinement {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (k : Fin (n + 1))
      (B : walkingAdjunctionHom X Y) (q : H.obj k.castSucc ⟶ B) (g : B ⟶ H.obj k.succ),
      ordinalMapVariation (walkingAdjunctionOrderHom q) +
        ordinalMapVariation (walkingAdjunctionOrderHom g) =
          ordinalMapVariation (walkingAdjunctionOrderHom
            (H.map (homOfLE (Fin.castSucc_le_succ k)))) →
      walkingAdjunctionOrdinalWidth (composableArrowRefinement H k B q g) =
        walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionBottomMergeRefinement_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionBottomMergeRefinement H k m hA h1) =
      walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionFirstRefinement_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement H ha hnd) =
      walkingAdjunctionOrdinalWidth H
```

今回の有限順序の幅と原典の文字列の幅との全比較はまだ未完。
始点plusの前置と最後の親の幅の計算、幅で実頂点の個数を押さえる全法則、
指定以外の面と原子分解についての幅・深さの比較、各幅での有限性、
fillable条件との全比較、parental subcomputadのfiltrationと全付着の構成は引き続き未完である。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。G01の済みは0、G02以降も未完を維持する。

### 115.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加28根だけの公理監査を確認した。
最終対象はSerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthRefinement:olean。
最終固定コマンドの対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
先頭のH.leftとH.obj 0、有限添字の同じ実先頭の表示を揃え、行長と正規importも整えてから最終検証した。
追加28根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-ordinal-width-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-ordinal-width-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み14,849行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §116 G01：幅による全実頂点の境界と、全次数・四Homでの有限性（11-15）

### 116.1 検証済みの追加

追加は **4ファイル326行・明示宣言12**。累計 **136ファイル15,175行・明示宣言781**。
WalkingAdjunctionOrdinalWidthVertices.lean は81行・3宣言、
FiniteFunctorObjects.lean は54行・1宣言、
WalkingAdjunctionBoundedChains.lean は64行・3宣言、
WalkingAdjunctionOrdinalWidthFinite.lean は127行・5宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ実全随伴と実filtrationに必要な実個数・全関手の有限表示、
元の実辺の全合成・既存の原子・幅・次元の法則とその証明の分割であり、一覧IDは追加しない。

任意の実全鎖で、各実頂点の点の個数は、始点の個数と全実辺の変化量の和以下となることを示した。
尾部に帰納し、先頭の辺の個数の差の上限と全辺の変化量の和の分解を合わせている。
原子の始点の個数と幅の式を適用すると、全実頂点の個数は幅と両端の補正の和より小さく、
全実頂点の重みは有限順序の幅以下となる。元の全関手の全頂点についての境界である。

一般の補題として、有限な対象・射を持つ圏から、対象が有限な範囲にあり各Homが有限な圏への実関手は有限個であることを示した。
対象の関数と全射の作用の関数を依存和へ符号化し、その単射性を実関手の構造と証明非依存性で証明した。
全射の作用の暗黙の両端引数を明示し、関手の実作用を失わずに比較している。
仮定した有限性は一般の補題の型に明示し、walking Homへの適用では以下のように実際に証明する。

四つのwalking Homの任意の二対象間の実射は、忠実な有限単調射の表示から有限関数型へ単射で入り、有限個となる。
重みが指定値以下の実対象も、重みの単射性で有限個となる。
従って全頂点の重みを制限した固定次数の実全関手は、一般の関手の有限性から有限個となる。
これに全実頂点の幅の境界を適用し、固定次数・固定幅の実原子は有限個であることを示した。

非退化な原子の次元は有限順序の幅より小さいという§115の法則から、
固定幅の全次数の非退化実原子を、有限個の次数と有限個の実関手の依存和の像に入れた。
さらに二つの実対象の有限性を明示し、四Hom・全次数を合わせても、固定幅の非退化な実原子は有限集合となることを示した。
幅が指定値以下の全非退化実原子も、有限個の各幅の集合の有限和へ入るので有限である。
いずれも元の実全関手そのものの有限性であり、同型類だけの有限性へ置き換えていない。

### 116.2 型と未完の境界

原典はRiehl–Verity Proposition 4.2.15、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma walkingAdjunctionVertexCard_le_first_add_variation {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) n) (i : Fin (n + 1)),
      walkingAdjunctionOrdinalCard X Y (H.obj i) ≤
        walkingAdjunctionOrdinalCard X Y (H.obj 0) +
          ∑ j : Fin n, ordinalMapVariation
            (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))

lemma walkingAdjunctionOrdinalWidth_vertex_card_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard X Y (H.obj i) < walkingAdjunctionOrdinalWidth H +
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y

lemma walkingAdjunctionOrdinalWidth_vertex_weight_le {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) (i : Fin (n + 1)) :
    walkingAdjunctionWeight X Y (H.obj i) ≤ walkingAdjunctionOrdinalWidth H

lemma finite_functors_of_objectwise_finite {I : Type u₁} {D : Type u₂}
    [Category.{v₁} I] [Category.{v₂} D] [Finite I]
    [∀ i j : I, Finite (i ⟶ j)] [∀ A B : D, Finite (A ⟶ B)]
    (P : D → Prop) [Finite {A : D // P A}] :
    Finite {F : I ⥤ D // ∀ i, P (F.obj i)}

lemma walkingAdjunctionHom_finite (X Y : WalkingAdjunctionPoint) (A B : walkingAdjunctionHom X Y) :
    Finite (A ⟶ B)

lemma walkingAdjunctionBoundedObjects_finite (X Y : WalkingAdjunctionPoint) (w : ℕ) :
    Finite {A : walkingAdjunctionHom X Y // walkingAdjunctionWeight X Y A ≤ w}

lemma walkingAdjunctionBoundedChains_finite (n : ℕ) (X Y : WalkingAdjunctionPoint) (w : ℕ) :
    Finite {H : ComposableArrows (walkingAdjunctionHom X Y) n //
      ∀ i, walkingAdjunctionWeight X Y (H.obj i) ≤ w}

lemma walkingAdjunctionAtomicWidth_finite (n : ℕ) (X Y : WalkingAdjunctionPoint) (w : ℕ) :
    Finite {H : ComposableArrows (walkingAdjunctionHom X Y) n //
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ∧
        walkingAdjunctionOrdinalWidth H = w}

lemma walkingAdjunctionAtomicWidth_set_finite (X Y : WalkingAdjunctionPoint) (w : ℕ) :
    {p : Σ n : ℕ, ComposableArrows (walkingAdjunctionHom X Y) n |
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) p.2 ∧
        ULift.up p.2 ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate p.1 ∧
          walkingAdjunctionOrdinalWidth p.2 = w}.Finite

lemma walkingAdjunctionPoint_finite : Finite WalkingAdjunctionPoint

lemma walkingAdjunctionAllAtomicWidth_set_finite (w : ℕ) :
    {p : Σ X : WalkingAdjunctionPoint, Σ Y : WalkingAdjunctionPoint,
        Σ n : ℕ, ComposableArrows (walkingAdjunctionHom X Y) n |
      WalkingAdjunctionLevelIsAtomic (X := ⟨p.1⟩) (Y := ⟨p.2.1⟩) p.2.2.2 ∧
        ULift.up p.2.2.2 ∈
          (WalkingAdjunctionHomShape.{u} p.1 p.2.1).nonDegenerate p.2.2.1 ∧
            walkingAdjunctionOrdinalWidth p.2.2.2 = w}.Finite

lemma walkingAdjunctionAllAtomicWidth_le_set_finite (w : ℕ) :
    {p : Σ X : WalkingAdjunctionPoint, Σ Y : WalkingAdjunctionPoint,
        Σ n : ℕ, ComposableArrows (walkingAdjunctionHom X Y) n |
      WalkingAdjunctionLevelIsAtomic (X := ⟨p.1⟩) (Y := ⟨p.2.1⟩) p.2.2.2 ∧
        ULift.up p.2.2.2 ∈
          (WalkingAdjunctionHomShape.{u} p.1 p.2.1).nonDegenerate p.2.2.1 ∧
            walkingAdjunctionOrdinalWidth p.2.2.2 ≤ w}.Finite
```

現在の実有限順序の幅では、実非退化原子の次元と全実頂点の境界、固定幅と指定幅以下での全体の有限性を検証した。
原典の文字列の幅・fillable条件との全比較、始点plusの前置と最後の親の幅の計算、
指定以外の面と原子分解の幅・深さの比較、parental subcomputadのfiltrationと全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。G01の済みは0、G02以降も未完を維持する。

### 116.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加12根だけの公理監査を確認した。
最終対象はSerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthFinite:olean。
最終固定コマンドの対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
Finiteの積・依存和、有限像・有限和の正規import、集合の所属の現行名、符号化先の部分型を整えて最終検証した。
追加12根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-ordinal-width-finite-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-ordinal-width-finite-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み15,175行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §117 G01：全実面の幅の非増加・実順序和の加法性・始点plusの実親の幅の増分（11-15）

### 117.1 検証済みの追加

追加は **4ファイル453行・明示宣言16**。累計 **140ファイル15,628行・明示宣言797**。
WalkingAdjunctionOrdinalWidthFaces.lean は159行・5宣言、
OrdinalAppendVariation.lean は88行・3宣言、
WalkingAdjunctionOrdinalWidthAppend.lean は87行・4宣言、
WalkingAdjunctionPlusParentWidth.lean は119行・4宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
G01の同じ実全随伴・実親・実filtrationの構成に必要な、全実面・実順序和・実挿入の合成、
実射の像の個数・係数移送・幅の照合とその証明の分割であり、一覧IDは追加しない。

一点と一辺の実全鎖の有限順序の幅を、実頂点の個数と実辺の変化量で表示した。
先頭の実頂点を除く面の幅は、一辺の個数の差の上限と先頭挿入の幅の式から元の幅以下となる。
最初の二辺を合成する内側の面も、元の二回の実挿入と合成辺の実挿入を比較し、
変化量が合成で増えないことから、元の幅以下となる。
それ以外の面は尾部の面へ帰納し、先頭の実射の対象の輸送が変化量を保つことを使った。
これにより、任意の実全単体の全ての境界面を含む実面について、有限順序の幅は増えないことを証明した。
先頭の実対象と有限添字の表示は同じ実頂点へ明示的に揃えている。

有限順序の実順序和について、実像を左右の区間の像へ分け、
左右が交わらないことと両包含の単射性から、実像の個数が加法的であることを示した。
従って実順序和の変化量も加法的となる。実単調射の両端の個数と異種等式での変化量の移送も示した。

実終端挿入では、挿入より前の各実辺の変化量と最後の実射の変化量を回収した。
全実辺の有限和を最後の点で分けることで、終端挿入の幅の変化を、元の実終点・新しい終点・実射の変化量で表示した。
空の実対象や長さ0の鎖も含む式である。

始点plusの実鎖にminusからの実生成射を前置すると、各実辺の変化量は元の変化量に一致する。
全実辺の変化量の和は変わらず、両端の個数と始点の補正を計算すると、有限順序の幅は1増える。
構成した実底併合射の変化量は、全射性から像の個数を実終点へ戻すことで1と計算した。
始点plusの実原子の実親では、前置した鎖の終点が二点、新しい終点が一点なので、
終端の実底併合の挿入はその鎖の幅を保つ。
従って構成済みの始点plusの実親の有限順序の幅は、元の子の幅より1大きい。
親の幅の条件を新しい入力に置いていない。

### 117.2 型と未完の境界

原典はRiehl–Verity Lemma 4.1.4・Proposition 4.2.15、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma walkingAdjunctionOrdinalWidth_zero {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) 0) :
    walkingAdjunctionOrdinalWidth H =
      walkingAdjunctionOrdinalCard X Y (H.obj 0) + walkingAdjunctionOrdinalCard X Y (H.obj 0) -
        (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y)

lemma walkingAdjunctionOrdinalWidth_one {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) 1) :
    walkingAdjunctionOrdinalWidth H = walkingAdjunctionOrdinalCard X Y (H.obj 0) +
      walkingAdjunctionOrdinalCard X Y (H.obj 1) -
        (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y) +
          ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1))

lemma walkingAdjunctionOrdinalWidth_tail_le {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    walkingAdjunctionOrdinalWidth H.δ₀ ≤ walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionOrdinalWidth_first_inner_face_le {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H (1 : Fin (n + 3))) ≤
      walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionOrdinalWidth_face_le {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (p : Fin (n + 2)),
      walkingAdjunctionOrdinalWidth (finiteChainFace H p) ≤ walkingAdjunctionOrdinalWidth H

lemma ordinalMapVariation_heq {a b c d : ℕ} (ha : a = c) (hb : b = d)
    (f : Fin a →o Fin b) (g : Fin c →o Fin d) (h : HEq f g) :
    ordinalMapVariation f = ordinalMapVariation g

lemma ordinalImageCard_append {m n p q : ℕ} (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalImageCard (ordinalAppend f g) = ordinalImageCard f + ordinalImageCard g

lemma ordinalMapVariation_append {m n p q : ℕ} (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalMapVariation (ordinalAppend f g) = ordinalMapVariation f + ordinalMapVariation g

lemma walkingAdjunctionAppend_before_variation {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) (j : Fin n) :
    ordinalMapVariation (walkingAdjunctionOrderHom ((composableArrowAppend H B f).map
      (homOfLE (Fin.castSucc_le_succ j.castSucc)))) =
    ordinalMapVariation (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))

lemma walkingAdjunctionAppend_last_variation {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) :
    ordinalMapVariation (walkingAdjunctionOrderHom ((composableArrowAppend H B f).map
      (homOfLE (Fin.castSucc_le_succ (Fin.last n))))) =
      ordinalMapVariation (walkingAdjunctionOrderHom f)

lemma walkingAdjunctionAppend_variation_sum {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) :
    (∑ j : Fin (n + 1), ordinalMapVariation
      (walkingAdjunctionOrderHom ((composableArrowAppend H B f).map
        (homOfLE (Fin.castSucc_le_succ j))))) =
      (∑ j : Fin n, ordinalMapVariation
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))) +
          ordinalMapVariation (walkingAdjunctionOrderHom f)

lemma walkingAdjunctionOrdinalWidth_append {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) :
    walkingAdjunctionOrdinalWidth (composableArrowAppend H B f) +
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) =
    walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y B +
      ordinalMapVariation (walkingAdjunctionOrderHom f)

lemma walkingAdjunctionPlusParentPrefix_variation {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) (j : Fin n) :
    ordinalMapVariation (walkingAdjunctionOrderHom ((walkingAdjunctionPlusParentPrefix H).map
      (homOfLE (Fin.castSucc_le_succ j)))) =
      ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ j))))

lemma walkingAdjunctionPlusParentPrefix_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParentPrefix H) =
      walkingAdjunctionOrdinalWidth H + 1

lemma walkingAdjunctionBottomMergeArrow_variation {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    ordinalMapVariation (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA)) =
      1

lemma walkingAdjunctionPlusParent_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent H ha) =
      walkingAdjunctionOrdinalWidth H + 1
```

現在の有限順序の幅では、内側の実親の幅の保存（§115）、最後の深さの実親の増分1、
全実面の幅の非増加まで検証した。
実水平分解と原子分解の幅の加法性、原典の文字列の幅・fillable条件との全比較、
指定以外の面と原子分解についての深さの比較、parental subcomputadのfiltrationと全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。G01の済みは0、G02以降も未完を維持する。

### 117.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルド二つと追加16根だけの公理監査を確認した。
対象はSerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthFaces:oleanと
SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParentWidth:olean。
最終固定コマンドの対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
実面の先頭の対象の輸送・同じ実有限添字・実関手の表示・補正の0からの加算を揃え、行長も整えて最終検証した。
追加16根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-width-faces-plus-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-width-faces-plus-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み15,628行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §118 G01：実水平合成・実原子分解の幅の加法性、全実退化の保存、非自明な因子の厳密な境界（11-15）

### 118.1 検証済みの追加

追加は **5ファイル555行・明示宣言24**。累計 **145ファイル16,183行・明示宣言821**。
OrdinalGlueVariation.lean は126行・2宣言、
WalkingAdjunctionOrdinalWidthHorizontal.lean は134行・5宣言、
WalkingAdjunctionAtomicWordWidth.lean は95行・7宣言、
WalkingAdjunctionOrdinalWidthDegeneracy.lean は109行・5宣言、
WalkingAdjunctionOrdinalWidthPositive.lean は91行・5宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の実全随伴・実filtrationの構成に必要な、既存の実貼り合わせ・水平合成・原子分解・
退化の法則、実単位・実射の係数移送、幅の照合とその証明の分割であり、一覧IDは追加しない。

端点を共有する実順序の貼り合わせの像は、左右の区間の像の和集合となる。
単調性と端点の保存から、その交わりが共有する一点であることを示した。
従って貼り合わせの像の個数に1を足すと左右の像の個数の和になり、実辺の変化量は加法的となる。
空の部分を許す実順序和の法則（§117）と合わせ、元の八つの水平合成の実順序表示へ輸送した。
中点の補正を含む実頂点の個数と全隣接実辺の変化量を計算して、
全次数の実水平合成の有限順序の幅が左右の幅の和と等しいことを証明した。
構成済みの実水平分解にも、その全実関手の合成の等式に沿って同じ等式を戻した。

実単位の幅は全次数で0となる。
実原子的な語の葉の幅の和を定義し、実語への帰納法により、
任意の実原子分解の葉の幅の和が元の全実鎖の幅に一致することを検証した。
この和は実原子分解や括弧の選び方によらない。
任意の実水平分解の左右の因子の幅は元の幅以下となる。

元のnerveの実退化について、重なる一辺を除く有限添字が、元の隣接二点へ戻ることを
有限順序の前後の場合分けで明示した。
重なる実辺は同型なので変化量が0、残りの実辺は元の対応する実辺へ輸送できる。
有限和を重なる辺と残りへ分けることで、全実辺の変化量の和が保たれる。
両端の実対象も変わらないので、全次数・全位置の実退化は有限順序の幅を保つ。

実原子の幅は1以上であり、実原子分解の合成で幅が加法的であるため、
幅0の全実鎖の実長さは0となる。逆向きは実長さ0から元の実単位そのものへ戻すことで得た。
従って幅が正であることと実長さが正であることが同値となる。
右の実因子が非自明なら左の幅は元の幅より真に小さく、左が非自明なら右が真に小さい。
因子の幅の正値を新しい仮定として置かず、構成済みの実長さと原子分解から回収している。

### 118.2 型と未完の境界

原典はRiehl–Verity Lemma 4.1.4・Proposition 4.2.15、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma ordinalImageCard_glue {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0) :
    ordinalImageCard (ordinalGlue f g) + 1 = ordinalImageCard f + ordinalImageCard g

lemma ordinalMapVariation_glue {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0) :
    ordinalMapVariation (ordinalGlue f g) = ordinalMapVariation f + ordinalMapVariation g

lemma walkingAdjunctionOrdinalCard_comp_correction (X M Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom M Y) :
    walkingAdjunctionOrdinalCard X Y ((walkingAdjunctionHorizontal X M Y).obj (A, B)) +
      walkingAdjunctionTargetCorrection M =
    walkingAdjunctionOrdinalCard X M A + walkingAdjunctionOrdinalCard M Y B

lemma walkingAdjunctionHorizontal_variation (X M Y : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X M} {B B' : walkingAdjunctionHom M Y}
    (f : A ⟶ A') (g : B ⟶ B') :
    ordinalMapVariation (walkingAdjunctionOrderHom ((walkingAdjunctionHorizontal X M Y).map
      (X := (A, B)) (Y := (A', B')) (f, g))) =
    ordinalMapVariation (walkingAdjunctionOrderHom f) +
      ordinalMapVariation (walkingAdjunctionOrderHom g)

lemma walkingAdjunctionHorizontal_variation_sum {n : ℕ} (X M Y : WalkingAdjunctionPoint)
    (F : ComposableArrows (walkingAdjunctionHom X M) n)
    (G : ComposableArrows (walkingAdjunctionHom M Y) n) :
    (∑ j : Fin n, ordinalMapVariation (walkingAdjunctionOrderHom
      ((F.prod' G ⋙ walkingAdjunctionHorizontal X M Y).map
        (homOfLE (Fin.castSucc_le_succ j))))) =
      (∑ j : Fin n, ordinalMapVariation
        (walkingAdjunctionOrderHom (F.map (homOfLE (Fin.castSucc_le_succ j))))) +
      ∑ j : Fin n, ordinalMapVariation
        (walkingAdjunctionOrderHom (G.map (homOfLE (Fin.castSucc_le_succ j))))

lemma walkingAdjunctionOrdinalWidth_horizontal {n : ℕ} (X M Y : WalkingAdjunctionPoint)
    (F : ComposableArrows (walkingAdjunctionHom X M) n)
    (G : ComposableArrows (walkingAdjunctionHom M Y) n) :
    walkingAdjunctionOrdinalWidth (F.prod' G ⋙ walkingAdjunctionHorizontal X M Y) =
      walkingAdjunctionOrdinalWidth F + walkingAdjunctionOrdinalWidth G

lemma WalkingAdjunctionFactorization.ordinalWidth {n : ℕ} {X Y : WalkingAdjunctionPoint}
    {H : ComposableArrows (walkingAdjunctionHom X Y) n} (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionOrdinalWidth H =
      walkingAdjunctionOrdinalWidth a.left + walkingAdjunctionOrdinalWidth a.right

lemma walkingAdjunctionIdentity_card (X : WalkingAdjunctionPoint) :
    walkingAdjunctionOrdinalCard X X (walkingAdjunctionIdentity X) =
      walkingAdjunctionTargetCorrection X

lemma walkingAdjunctionOrdinalWidth_id (n : ℕ) (X : WalkingAdjunctionLevel n) :
    walkingAdjunctionOrdinalWidth (𝟙 X : X ⟶ X) = 0

def WalkingAdjunctionAtomicWord.ordinalWidth {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F) : ℕ

lemma WalkingAdjunctionAtomicWord.ordinalWidth_eq {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F) :
    a.ordinalWidth = walkingAdjunctionOrdinalWidth F

lemma WalkingAdjunctionAtomicWord.ordinalWidth_independent {n : ℕ}
    {X Y : WalkingAdjunctionLevel n} {F : X ⟶ Y}
    (a b : WalkingAdjunctionAtomicWord n F) : a.ordinalWidth = b.ordinalWidth

lemma WalkingAdjunctionFactorization.left_ordinalWidth_le {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionOrdinalWidth a.left ≤ walkingAdjunctionOrdinalWidth H

lemma WalkingAdjunctionFactorization.right_ordinalWidth_le {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionOrdinalWidth a.right ≤ walkingAdjunctionOrdinalWidth H

lemma finPredAbove_other_edge {n : ℕ} (j : Fin (n + 1)) (i : Fin n) :
    j.predAbove (j.succAbove i).castSucc = i.castSucc ∧
      j.predAbove (j.succAbove i).succ = i.succ

lemma walkingAdjunctionDegeneracy_other_variation {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (j : Fin (n + 1)) (i : Fin n) :
    ordinalMapVariation (walkingAdjunctionOrderHom (((nerve (walkingAdjunctionHom X Y)).σ j H).map
      (homOfLE (Fin.castSucc_le_succ (j.succAbove i))))) =
    ordinalMapVariation (walkingAdjunctionOrderHom (H.map
      (homOfLE (Fin.castSucc_le_succ i))))

lemma walkingAdjunctionDegeneracy_collapsed_variation {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (j : Fin (n + 1)) :
    ordinalMapVariation (walkingAdjunctionOrderHom (((nerve (walkingAdjunctionHom X Y)).σ j H).map
      (homOfLE (Fin.castSucc_le_succ j)))) = 0

lemma walkingAdjunctionDegeneracy_variation_sum {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (j : Fin (n + 1)) :
    (∑ i : Fin (n + 1), ordinalMapVariation (walkingAdjunctionOrderHom
      (((nerve (walkingAdjunctionHom X Y)).σ j H).map
        (homOfLE (Fin.castSucc_le_succ i))))) =
    ∑ i : Fin n, ordinalMapVariation (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ i))))

lemma walkingAdjunctionOrdinalWidth_degeneracy {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (j : Fin (n + 1)) :
    walkingAdjunctionOrdinalWidth ((nerve (walkingAdjunctionHom X Y)).σ j H) =
      walkingAdjunctionOrdinalWidth H

lemma WalkingAdjunctionAtomicWord.size_zero_of_ordinalWidth_zero {n : ℕ}
    {X Y : WalkingAdjunctionLevel n} {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F)
    (h : walkingAdjunctionOrdinalWidth F = 0) : walkingAdjunctionLevelSize F = 0

lemma walkingAdjunctionOrdinalWidth_zero_iff_size_zero {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) n) :
    walkingAdjunctionOrdinalWidth H = 0 ↔ walkingAdjunctionLevelSize H = 0

lemma walkingAdjunctionOrdinalWidth_pos_iff_size_pos {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) n) :
    0 < walkingAdjunctionOrdinalWidth H ↔ 0 < walkingAdjunctionLevelSize H

lemma WalkingAdjunctionFactorization.left_ordinalWidth_lt {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) (h : 0 < walkingAdjunctionLevelSize a.right) :
    walkingAdjunctionOrdinalWidth a.left < walkingAdjunctionOrdinalWidth H

lemma WalkingAdjunctionFactorization.right_ordinalWidth_lt {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) (h : 0 < walkingAdjunctionLevelSize a.left) :
    walkingAdjunctionOrdinalWidth a.right < walkingAdjunctionOrdinalWidth H
```

有限順序の幅について、全実面の非増加（§117）、全実退化での保存、
水平合成と実原子分解の加法性、非自明な実因子の厳密な境界まで検証した。
原典の文字列の幅・fillable条件との全比較、指定以外の面の深さの比較、
parental subcomputadのfiltrationと全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。

### 118.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加24根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionOrdinalWidthPositive:oleanと
WalkingAdjunctionOrdinalWidthDegeneracy:oleanで、今回の他の3ファイルを前者から取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
有限添字の前後の表示は既存のpredAbove・succAboveの補題で揃え、元の圏の合成も実水平合成へ明示して最終検証した。
追加24根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-width-horizontal-atomic-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-width-horizontal-atomic-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み16,183行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §119 G01：内側の実面での最初の併合位置・純粋性の輸送・退化面と欠損2の厳密な幅の減少（11-15）

### 119.1 検証済みの追加

追加は **7ファイル642行・明示宣言19**。累計 **152ファイル16,825行・明示宣言840**。
WalkingAdjunctionFaceMergeEdges.lean は83行・4宣言、
WalkingAdjunctionFaceFirstIndex.lean は125行・3宣言、
WalkingAdjunctionFaceMergePurity.lean は62行・2宣言、
WalkingAdjunctionOrdinalWidthInnerFace.lean は148行・3宣言、
WalkingAdjunctionDegenerateInnerWidth.lean は90行・2宣言、
OrdinalBottomMergeVariation.lean は76行・3宣言、
WalkingAdjunctionFaceWidthGap.lean は58行・2宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationの構成に必要な、実面・実合成・実射の係数移送・純粋性の
保存・幅と深さの照合とその証明の分割であり、新しい一覧IDは加えない。

有限単調射が底の二点を併合しない場合、0の逆像を反映すること（既存）を使い、
そのような実二辺の合成でも底の二点の併合が生じないことを示した。
内側の実面の前の辺・後の辺の併合条件は元の対応する実辺の条件と同値となり、
合成辺では元の二辺のどちらにも併合がなければ新しい併合はない。
これらは元の全実関手に対する法則であり、原子性を要求しない。

最初の実併合に触れない内側面では、面も非退化なら、元の実最小元そのものと面の実最小元を比較した。
最初の併合の二辺より後で面を取る場合には最初の辺の添字は不変、
その前の二辺を合成する場合には、元の後続添字j.succが面のjとなる。
後者の先行する全辺を前・合成・後へ分け、合成辺にも新しい早い併合がないことを証明した。
残る前後の実辺について、終点の個数と全点の値i↦i−1という純粋性の条件も両方向に輸送した。
位置の存在・所属・最小性は、構成済みの元の有限最小元から回収している。

任意の内側の実面について、面の幅と元の二辺の変化量の和は、
元の幅と合成辺の変化量の和に等しいことを証明した。
先頭の二回の実挿入で基底の等式を作り、尾部で再帰して先頭の実対象・実射の補正を相殺した。
従って合成で変化量が真に減れば、元の内側面の幅も真に減る。
さらに、元の鎖が非退化なら、内側面が非退化であることと、指定する合成辺が非同型であることが同値となる。
残る全ての実辺は元の非同型な実辺へ戻るため、退化は指定する合成辺に限られる。
面が退化する場合はその合成辺の変化量が0、元の辺の変化量が正なので、面の幅は元より真に小さい。
四つのHom・全実位置を扱い、元や面の原子性を仮定していない。

純粋な底併合は、値1を欠く部分集合に制限すれば単射となる。
これを先行辺の実像に適用し、先行辺の像が値1を欠くなら、底併合との合成で像の個数が保たれることを示した。
両端の個数の差が1なので、合成辺の変化量は先行辺の変化量より1小さい。
純粋な底併合自身の変化量は、実全射性を全点の値から構成して1と計算した。
この実二辺を合成する内側面では、幅がちょうど2減る。
0を保ち二番目の点の像が1より大きい場合には、像が値1を欠くことも元の実単調性から示した。

### 119.2 型と未完の境界

原典はRiehl–Verity Proposition 4.2.15（特に指定面の前後と指定直前の面の区別）、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma ordinalNoOneZero_comp {a b c : ℕ} (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (hf : ∀ i : Fin a, i.val = 1 → (f i).val ≠ 0)
    (hg : ∀ i : Fin b, i.val = 1 → (g i).val ≠ 0) :
    ∀ i : Fin a, i.val = 1 → (g.comp f i).val ≠ 0

lemma walkingAdjunctionInnerFace_before_merge_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : j < k) :
    WalkingAdjunctionBottomMergeAt (finiteChainFace H k.succ.castSucc) j ↔
      WalkingAdjunctionBottomMergeAt H j.castSucc

lemma walkingAdjunctionInnerFace_after_merge_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : k < j) :
    WalkingAdjunctionBottomMergeAt (finiteChainFace H k.succ.castSucc) j ↔
      WalkingAdjunctionBottomMergeAt H j.succ

lemma walkingAdjunctionInnerFace_no_merged_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hf : ¬ WalkingAdjunctionBottomMergeAt H k.castSucc)
    (hg : ¬ WalkingAdjunctionBottomMergeAt H k.succ) :
    ¬ WalkingAdjunctionBottomMergeAt (finiteChainFace H k.succ.castSucc) k

lemma walkingAdjunctionInnerFace_first_index_after {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hjk : j < k)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 2))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H hlast hnd = j.castSucc)
    (hface : ULift.up (finiteChainFace H k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    walkingAdjunctionFirstBottomMergeIndex (finiteChainFace H k.succ.castSucc)
      (by rw [finiteChainFace_inner_last]; exact hlast) hface = j

lemma walkingAdjunctionInnerFace_no_earlier_merge_before {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hkj : k < j)
    (hmin : ∀ r, WalkingAdjunctionBottomMergeAt H r → j.succ ≤ r)
    (r : Fin (n + 1)) (hrj : r < j) :
    ¬ WalkingAdjunctionBottomMergeAt (finiteChainFace H k.succ.castSucc) r

lemma walkingAdjunctionInnerFace_first_index_before {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hkj : k < j)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 2))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H hlast hnd = j.succ)
    (hface : ULift.up (finiteChainFace H k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    walkingAdjunctionFirstBottomMergeIndex (finiteChainFace H k.succ.castSucc)
      (by rw [finiteChainFace_inner_last]; exact hlast) hface = j

lemma walkingAdjunctionInnerFace_before_pure_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : j < k) (m : ℕ) :
    let F := finiteChainFace H k.succ.castSucc
    (walkingAdjunctionOrdinalCard .minus Y (F.obj j.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (F.obj j.castSucc)),
        (walkingAdjunctionOrderHom (F.map (homOfLE (Fin.castSucc_le_succ j))) i).val = i.val - 1) ↔
    (walkingAdjunctionOrdinalCard .minus Y (H.obj j.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj j.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (H.map
          (homOfLE (Fin.castSucc_le_succ j.castSucc))) i).val = i.val - 1)

lemma walkingAdjunctionInnerFace_after_pure_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : k < j) (m : ℕ) :
    let F := finiteChainFace H k.succ.castSucc
    (walkingAdjunctionOrdinalCard .minus Y (F.obj j.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (F.obj j.castSucc)),
        (walkingAdjunctionOrderHom (F.map (homOfLE (Fin.castSucc_le_succ j))) i).val = i.val - 1) ↔
    (walkingAdjunctionOrdinalCard .minus Y (H.obj j.succ.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj j.succ.castSucc)),
        (walkingAdjunctionOrderHom (H.map
          (homOfLE (Fin.castSucc_le_succ j.succ))) i).val = i.val - 1)

lemma walkingAdjunctionOrdinalWidth_first_inner_defect {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H (1 : Fin (n + 3))) +
      ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1)) +
      ordinalMapVariation (walkingAdjunctionOrderHom (H.δ₀.map' 0 1)) =
    walkingAdjunctionOrdinalWidth H + ordinalMapVariation
      (walkingAdjunctionOrderHom (H.map' 0 1 ≫ H.δ₀.map' 0 1))

lemma walkingAdjunctionOrdinalWidth_inner_defect {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) (k : Fin (n + 1)),
      walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) +
        ordinalMapVariation (walkingAdjunctionOrderHom
          (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))) +
        ordinalMapVariation (walkingAdjunctionOrderHom
          (H.map (homOfLE (Fin.castSucc_le_succ k.succ)))) =
      walkingAdjunctionOrdinalWidth H + ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
          H.map (homOfLE (Fin.castSucc_le_succ k.succ))))

lemma walkingAdjunctionOrdinalWidth_inner_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) (k : Fin (n + 1))
    (hv : ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
          H.map (homOfLE (Fin.castSucc_le_succ k.succ)))) <
      ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))) +
      ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.succ))))) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) <
      walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionInnerFace_nondegenerate_iff_not_isIso {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2))
    (k : Fin (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 2)) :
    (ULift.up (finiteChainFace H k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1)) ↔
    ¬ IsIso (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
      H.map (homOfLE (Fin.castSucc_le_succ k.succ)))

lemma walkingAdjunctionOrdinalWidth_inner_lt_of_not_nondegenerate {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2))
    (k : Fin (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 2))
    (hf : ULift.up (finiteChainFace H k.succ.castSucc) ∉
      (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) <
      walkingAdjunctionOrdinalWidth H

lemma ordinalImageCard_comp_bottomMerge_of_no_one {a b c : ℕ}
    (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (hf : ∀ i, (f i).val ≠ 1) (hg : ∀ i, (g i).val = i.val - 1) :
    ordinalImageCard (g.comp f) = ordinalImageCard f

lemma ordinalMapVariation_bottomMerge {b c : ℕ} (g : Fin b →o Fin c)
    (hbc : c + 1 = b) (hg : ∀ i, (g i).val = i.val - 1) :
    ordinalMapVariation g = 1

lemma ordinalMapVariation_comp_bottomMerge_of_no_one {a b c : ℕ}
    (f : Fin a →o Fin b) (g : Fin b →o Fin c) (hbc : c + 1 = b)
    (hf : ∀ i, (f i).val ≠ 1) (hg : ∀ i, (g i).val = i.val - 1) :
    ordinalMapVariation (g.comp f) + 1 = ordinalMapVariation f

lemma ordinalNoOneImage_of_bottom_and_gt_one {a b : ℕ} (f : Fin a →o Fin b)
    (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (h1 : ∀ i, i.val = 1 → 1 < (f i).val) : ∀ i, (f i).val ≠ 1

lemma walkingAdjunctionOrdinalWidth_inner_gap_two {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) (k : Fin (n + 1))
    (hcard : walkingAdjunctionOrdinalCard X Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard X Y (H.obj k.succ.castSucc))
    (hmiss : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val ≠ 1)
    (hpure : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) + 2 =
      walkingAdjunctionOrdinalWidth H
```

今回の最初の位置の比較は、指定する併合の二辺から離れた内側面で、面が非退化の場合の法則である。
退化する内側面は幅の厳密な減少で扱える。
指定直前の面では、先行辺の像が値1を欠く場合の幅の欠損2まで証明した。
値1が像に入る場合の新しい非純粋性・実親の深さの比較、
境界面と全原子分解を含む全ての順位の比較、原典の文字列の幅・fillable条件との全比較、
parental subcomputadのfiltrationと全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。G01の済みは0、G02以降も未完を維持する。

### 119.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加19根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionFaceFirstIndex:olean、WalkingAdjunctionFaceMergePurity:olean、
WalkingAdjunctionDegenerateInnerWidth:olean、WalkingAdjunctionFaceWidthGap:olean。
今回の他の3ファイルもこれらから取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
有限添字のcastSuccとsucc、実挿入・実射の局所表示を揃えて最終検証した。
追加19根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-face-depth-width-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-face-depth-width-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み16,825行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §120 G01：指定直前の実面の非純粋性・実親の深さの減少と、実像の二つの場合の結合（11-15）

### 120.1 検証済みの追加

追加は **5ファイル387行・明示宣言7**。累計 **157ファイル17,212行・明示宣言847**。
WalkingAdjunctionPureMergeCancellation.lean は70行・2宣言、
WalkingAdjunctionPreviousFace.lean は105行・1宣言、
WalkingAdjunctionFirstRefinementIndex.lean は44行・1宣言、
WalkingAdjunctionPreviousFaceParent.lean は80行・1宣言、
WalkingAdjunctionPreviousFaceDichotomy.lean は88行・2宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationの構成に必要な、実面・実親の実構成の法則、
実合成の消去・実最小元の輸送・幅と深さの照合とその証明の分割であり、一覧IDは追加しない。

先行辺が底の二点を併合せず、純粋な底併合との合成が再び純粋なら、
0の保存・反映と全点での1減算の等式から、先行辺が全点の値を保つことを証明した。
元の個数も等しくなるため、実像の個数から変化量0を得て、先行辺が元の実Homで同型になる。
元の鎖が非退化ならその先行辺は非同型なので、この消去の補題から合成の非純粋性を得られる。

最初の純粋な併合の直前の辺が二番目の点を二番目へ送る場合、
その二辺を合成する実面では二番目の点が0へ送られる。
残る全実辺と合成辺の検収から面の非退化性を回収した。
合成位置より前の辺は元の先行辺なので併合せず、面の実最小元は合成位置そのものとなる。
この面の原子性・非退化性・非純粋性から、構成済みの実最初の細分により実親を作った。
その親の幅は面の幅に等しく、元の鎖の幅以下となる。
新しい実親の実最小元の添字は面の実最小元のcastSuccであり、元の実最小元k.succより真に小さい。
面や親の非退化性、実最小元、幅や深さの証人を新しい入力として置いていない。

0を保ち底の二点を併合しない先行辺では、その像が値1を欠くか、
二番目の点が二番目に送られるかの二つに分かれることも実単調性から示した。
像に値1があれば、その原像の下の二番目の点で単調性と非併合を使い、像が値1であることを得る。
先行辺の非併合は元の最初の併合の最小性から回収した。
従って指定直前の実面は、幅がちょうど2減る場合（§119）か、
幅が元以下で深さが真に小さい、上で実際に構成した親を持つ場合に分かれる。
結論には元の実有限最小元で定義した実親の全関手を保持している。

### 120.2 型と未完の境界

原典はRiehl–Verity Proposition 4.2.15の指定直前の面の二つの場合、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma ordinalVal_eq_of_bottomMerge_comp_pure {a b c : ℕ}
    (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (hf : ∀ i, i.val = 1 → (f i).val ≠ 0)
    (hg : ∀ i, (g i).val = i.val - 1)
    (hcomp : ∀ i, (g.comp f i).val = i.val - 1) : ∀ i, (f i).val = i.val

lemma walkingAdjunctionIsIso_of_pure_bottomMerge_comp {Y : WalkingAdjunctionPoint}
    {A B C : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (g : B ⟶ C)
    (ha : 2 ≤ walkingAdjunctionOrdinalCard .minus Y A)
    (hbc : walkingAdjunctionOrdinalCard .minus Y C + 1 =
      walkingAdjunctionOrdinalCard .minus Y B)
    (hf : ∀ i, i.val = 1 → (walkingAdjunctionOrderHom f i).val ≠ 0)
    (hg : ∀ i, (walkingAdjunctionOrderHom g i).val = i.val - 1)
    (hp : walkingAdjunctionOrdinalCard .minus Y C =
        walkingAdjunctionOrdinalCard .minus Y A - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (f ≫ g) i).val = i.val - 1) : IsIso f

lemma walkingAdjunctionPreviousFace_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 2))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H hlast hnd = k.succ)
    (hbc : walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.castSucc))
    (hg : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1)
    (hthrough : ∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc.castSucc)),
      i.val = 1 ∧ (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = 1) :
    let F := finiteChainFace H k.succ.castSucc
    ∃ hface : ULift.up F ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1),
      walkingAdjunctionFirstBottomMergeIndex F
        (by rw [finiteChainFace_inner_last]; exact hlast) hface = k ∧
      ¬ (walkingAdjunctionOrdinalCard .minus Y (F.obj k.succ) =
          walkingAdjunctionOrdinalCard .minus Y (F.obj k.castSucc) - 2 + 1 ∧
        ∀ i, (walkingAdjunctionOrderHom
          (F.map (homOfLE (Fin.castSucc_le_succ k))) i).val = i.val - 1)

lemma walkingAdjunctionFirstRefinement_first_index {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hp : ULift.up (walkingAdjunctionFirstRefinement H ha hnd) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) :
    walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionFirstRefinement H ha hnd)
      (walkingAdjunctionAtomic_endpoint_cards _
        (walkingAdjunctionFirstRefinement_atomic H ha hnd)).2
      hp = (walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).castSucc

lemma walkingAdjunctionPreviousFace_parent_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = k.succ)
    (hbc : walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.castSucc))
    (hg : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1)
    (hthrough : ∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc.castSucc)),
      i.val = 1 ∧ (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = 1) :
    let F := finiteChainFace H k.succ.castSucc
    let fa := walkingAdjunctionInnerFace_atomic H k ha
    ∃ hf : ULift.up F ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1),
      ∃ hp : ULift.up (walkingAdjunctionFirstRefinement F fa hf) ∈
          (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2),
        walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement F fa hf) ≤
          walkingAdjunctionOrdinalWidth H ∧
        (walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionFirstRefinement F fa hf)
          (walkingAdjunctionAtomic_endpoint_cards _
            (walkingAdjunctionFirstRefinement_atomic F fa hf)).2 hp).val <
          (walkingAdjunctionFirstBottomMergeIndex H
            (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).val

lemma ordinalNoOneImage_or_through_one {a b : ℕ} (f : Fin a →o Fin b)
    (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (hf : ∀ i, i.val = 1 → (f i).val ≠ 0) :
    (∀ i, (f i).val ≠ 1) ∨ ∃ i, i.val = 1 ∧ (f i).val = 1

lemma walkingAdjunctionPreviousFace_dichotomy {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = k.succ)
    (hbc : walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.castSucc))
    (hg : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1) :
    let F := finiteChainFace H k.succ.castSucc
    let fa := walkingAdjunctionInnerFace_atomic H k ha
    (walkingAdjunctionOrdinalWidth F + 2 = walkingAdjunctionOrdinalWidth H) ∨
      ∃ hf : ULift.up F ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1),
        ∃ hp : ULift.up (walkingAdjunctionFirstRefinement F fa hf) ∈
            (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2),
          walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement F fa hf) ≤
            walkingAdjunctionOrdinalWidth H ∧
          (walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionFirstRefinement F fa hf)
            (walkingAdjunctionAtomic_endpoint_cards _
              (walkingAdjunctionFirstRefinement_atomic F fa hf)).2 hp).val <
            (walkingAdjunctionFirstBottomMergeIndex H
              (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).val
```

指定直前の内側面について、実最初の位置、原子性・非退化性・純粋な併合の具体的条件の下で、
実像の二つの場合と、その面または構成した実親の幅・深さの比較まで検証した。
境界面と全原子分解を含む全ての順位の比較、原典の文字列の幅・fillable条件との全比較、
parental subcomputadのfiltrationと全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。

### 120.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加7根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionPreviousFaceDichotomy:oleanで、今回の他の4ファイルを取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
実合成辺の評価を直接の式へ移し、有限添字と実最小元の表示・行長を揃えて最終検証した。
追加7根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-previous-parent-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-previous-parent-audit-2026-11-15/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み17,212行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §121 G01：先頭の実境界面の幅の欠損・保存と、先頭・最後の実境界面の非原子性（11-16）

### 121.1 検証済みの追加

追加は **3ファイル214行・明示宣言6**。累計 **160ファイル17,426行・明示宣言853**。
OrdinalSmallSourceInjective.lean は42行・1宣言、
WalkingAdjunctionFirstFaceWidth.lean は109行・3宣言、
WalkingAdjunctionLastFaceAtomicity.lean は63行・2宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationの構成に必要な、実境界面・実挿入・実単位の法則、
実像の個数・実同型・原子性の照合とその証明の分割であり、一覧IDは追加しない。

先頭の実射の挿入の幅の式から、元の幅と先頭面の幅の差は、
先頭辺の「始点の個数から実像の個数を除いたもの」の2倍となることを示した。
先頭辺が単射なら、先頭面の幅は元の幅に一致する。
二点以下からの実単調射が0を保ち底の二点を併合しなければ、単射であることも全実点で証明した。
始点minusの実原子の実始点の個数は1または2であり、最初の併合が先頭でなければ、
元の実最小元の最小性から先頭辺の非併合が従う。従って先頭面の幅は元と等しい。
先頭面が原子的だと、その実始点の個数も元の実始点と同じ補正の和となる。
先頭辺の単射性と同じ個数から変化量0を得ると、先頭辺が実同型となり元の非退化性に反する。
この場合の先頭面の非原子性を、元の全実関手について回収した。

最後の境界面についても、元の実全鎖が非退化な原子なら、その面は原子的でないことを示した。
最後の面が原子的だと、元の最後の二つの実対象はどちらも一点となる。
一点から一点への実射の全射性と実像の個数から変化量0を回収し、元の実Homで同型と示した。
元の最後の実辺の非同型性に反するため、最後の面は原子的ではない。
こちらは全四Hom・全正の次数を扱い、最後の面そのものの非退化性を仮定しない。

先頭面の欠損を検討する途中では、終点と実像の差で幅が減る案を調べたが、
実挿入の等式を解くと、正しくは始点と実像の差となる。
未検証の減少の主張は採用せず、上記の実単射性による幅の保存と非原子性へ修正して最終検証した。
既にコミット済みの幅の法則に変更はない。

### 121.2 型と未完の境界

原典はRiehl–Verity Proposition 4.2.15の境界面と原子分解、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma ordinalInjective_of_le_two_bottom_no_one {a b : ℕ} (f : Fin a →o Fin b)
    (ha : a ≤ 2) (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (hno : ∀ i, i.val = 1 → (f i).val ≠ 0) : Function.Injective f

lemma walkingAdjunctionOrdinalWidth_first_face_defect {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    walkingAdjunctionOrdinalWidth H = walkingAdjunctionOrdinalWidth H.δ₀ +
      2 * (walkingAdjunctionOrdinalCard X Y (H.obj 0) -
        ordinalImageCard (walkingAdjunctionOrderHom (H.map' 0 1)))

lemma walkingAdjunctionOrdinalWidth_first_face_of_injective {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (hf : Function.Injective (walkingAdjunctionOrderHom (H.map' 0 1))) :
    walkingAdjunctionOrdinalWidth H.δ₀ = walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionFirstFace_width_and_not_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0) :
    walkingAdjunctionOrdinalWidth H.δ₀ = walkingAdjunctionOrdinalWidth H ∧
      ¬ WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H.δ₀

lemma walkingAdjunctionHom_isIso_of_card_one {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B)
    (ha : walkingAdjunctionOrdinalCard X Y A = 1)
    (hb : walkingAdjunctionOrdinalCard X Y B = 1) : IsIso f

lemma walkingAdjunctionLastFace_not_atomic {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1)) :
    ¬ WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      (finiteChainFace H (Fin.last (n + 1)))
```

先頭面の幅の欠損と単射の場合の保存、最初の併合が先頭でない場合の先頭面の非原子性、
全四Homでの最後の面の非原子性まで検証した。
境界面の全原子分解とそれぞれの親を含む全ての順位の比較、
最初の併合が先頭にある場合の境界面の全検収、原典の文字列の幅・fillable条件との全比較、
parental subcomputadのfiltrationと全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。

### 121.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加6根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionFirstFaceWidth:oleanとWalkingAdjunctionLastFaceAtomicity:olean。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
先頭辺の実始点・実終点・像の個数、実点の型、依存する式の簡約を揃えて最終検証した。
追加6根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-boundary-faces-audit-2026-11-16/](../../../evidence/bhatt-scholze/g12/g12-boundary-faces-audit-2026-11-16/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み17,426行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §122 G01：非原子的な実境界面の全原子因子の幅の厳密な境界（11-16）

### 122.1 検証済みの追加

追加は **2ファイル158行・明示宣言5**。累計 **162ファイル17,584行・明示宣言858**。
WalkingAdjunctionAtomicFactorWidth.lean は91行・3宣言、
WalkingAdjunctionBoundaryFactorWidth.lean は67行・2宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationの構成に必要な、実原子分解・実道の単位と合成の法則、
実水平合成・幅の加法性・非原子性の照合とその証明の分割であり、一覧IDは追加しない。

構成済みの実原子的な自由な道の比較関手について、長さ1の道の実像が原子的となることを示した。
道を最初の実生成射と長さ0の残りへ分け、残りを空の道へ戻して元の実生成射を回収した。
任意の実生成射eを、前の道qと後の道rの間へ置いた実道について、
その実像の幅が、前の実像・e・後の実像の三つの幅の和となることを示した。
これは元の実関手の合成の等式と実水平合成の加法性を、同じ実対象の上で二度使う法則である。

全実像が非原子的であれば道の長さは1でない。
この道は指定した原子eを含むので、前後の道の少なくとも一方は長さが正となる。
その実像の元の実長さが正であることを既存の実比較関手から回収し、
幅の正値へ移すと、eの幅は全実像の幅より真に小さくなる。
指定する原子を先頭や末尾に限定せず、全位置の実因子に証明した。

最後の実境界面では、元が非退化な実原子なら面は非原子的である（§121）。
その面の実道への分解の任意の実原子因子に上の厳密な境界を使い、
全実面の幅の非増加（§117）へ合成すると、その因子の幅は元の実鎖より真に小さい。
こちらは全四Hom・全正の次数を扱う。
始点minusの実鎖の先頭面については、最初の併合が先頭でない場合に、
面の非原子性と元との幅の等式（§121）を使い、任意の実原子因子の幅が元より真に小さいことを示した。
結論は元の全実関手との等式で指定した実分解に対するものである。

### 122.2 型と未完の境界

原典はRiehl–Verity Proposition 4.2.15の境界面の原子分解、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma walkingAdjunctionAtomicPath_atomic_of_length_one {n : ℕ}
    {A B : WalkingAdjunctionAtomicVertex n} (p : Quiver.Path A B) (hp : p.length = 1) :
    WalkingAdjunctionLevelIsAtomic ((walkingAdjunctionAtomicPathFunctor n).map p)

lemma walkingAdjunctionAtomicFactor_width_sum {n : ℕ}
    {A B C D : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path A B) (e : B ⟶ C) (r : Quiver.Path C D) :
    walkingAdjunctionOrdinalWidth
      ((walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r))) =
      walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map q) +
        (walkingAdjunctionOrdinalWidth e.val +
          walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map r))

lemma walkingAdjunctionAtomicFactor_width_lt {n : ℕ}
    {A B C D : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path A B) (e : B ⟶ C) (r : Quiver.Path C D)
    (ha : ¬ WalkingAdjunctionLevelIsAtomic
      ((walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)))) :
    walkingAdjunctionOrdinalWidth e.val < walkingAdjunctionOrdinalWidth
      ((walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)))

lemma walkingAdjunctionLastFace_atomicFactor_width_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1))
    {B C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨X⟩⟩ : WalkingAdjunctionAtomicVertex n) B) (e : B ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) =
      finiteChainFace H (Fin.last (n + 1))) :
    walkingAdjunctionOrdinalWidth e.val < walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionFirstFace_atomicFactor_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0)
    {B C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) B) (e : B ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) = H.δ₀) :
    walkingAdjunctionOrdinalWidth e.val < walkingAdjunctionOrdinalWidth H
```

境界面の任意の位置の実原子因子について、元より幅が真に小さいことまで検証した。
各因子の実親の幅・深さを含む全ての順位の比較は未完。
特に、始点plusの因子の実親では幅が1増えるので、この厳密な不等式だけから
親の幅が元より真に小さいと主張はしない。
最初の併合が先頭にある場合の境界面の全検収、原典の文字列の幅・fillable条件との全比較、
parental subcomputadのfiltrationと全付着の構成も未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。

### 122.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加5根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionBoundaryFactorWidth:oleanで、今回のもう一方のファイルも取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
実道の型とその実像の元の対象を保つため、幅の加法性は同じ実対象を明示した等式の合成で輸送して最終検証した。
追加5根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-boundary-factor-audit-2026-11-16/](../../../evidence/bhatt-scholze/g12/g12-boundary-factor-audit-2026-11-16/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み17,584行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §123 G01：幅1の実生成射の回収と、生成射を前置した実境界面の例外の識別（11-16）

### 123.1 検証済みの追加

追加は **3ファイル218行・明示宣言5**。累計 **165ファイル17,802行・明示宣言863**。
WalkingAdjunctionWidthOneGenerator.lean は52行・1宣言、
WalkingAdjunctionPrefixBoundaryRecognition.lean は64行・2宣言、
WalkingAdjunctionWidthOneBoundary.lean は102行・2宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationの構成に必要な、実境界面・実親・実生成射の実構成の法則、
実最小元と幅の照合・係数移送とその証明の分割であり、一覧IDは追加しない。

minusからplusへの幅1の実全鎖について、両端の実対象の非空性と幅の式から、
始点の実個数が1で、全辺の変化量の和が0であることを示した。
全実頂点の個数の上限（§116）と各頂点の非空性から、全頂点の個数は1となる。
構成済みの定値関手の回収と実個数の単射性で、元の全実関手が実生成射の定値関手そのものであることを得た。
この結論には原子性・非退化性の仮定を使わない。

最後の実面が実生成射を始点plusの実原子Eへ前置した鎖なら、
一点の実終点と指定面による全実関手の一意性から、元の鎖は構成済みの実親PlusParent Eと一致する。
さらに、元の鎖が非退化で実終点が一点なら、最後より前の全辺で実併合がないことを
元の最後の面と前置した実辺へ輸送できる。
元の実最小元の所属から、その最初の併合位置は最後の辺に限られることを示した。
こちらは前置される鎖Eの原子性・非退化性を仮定しない。

最後の実面が幅1のminusからplusの実因子Qと始点plusの実原子Eの実水平合成である場合、
Qを上の実生成射へ戻すことで、元の実親そのものと最後の実最小元の等式を回収した。
QやEの非退化性を新しい入力に置いていない。

先頭の実面が同じ幅1の因子Qと実原子Eの水平合成である場合、元の最初の実併合は先頭になる。
先頭でないと仮定すると、その面の幅は元と等しい（§121）。
Eの実原子性と実前置の個数の式から、先頭の二つの実対象の個数も等しい。
先頭面の幅の欠損の等式で実像の個数を始点へ戻すと、先頭辺の変化量は0となる。
その実辺の同型性は元の非退化性に反するため、元の実最小元は0に限られる。

### 123.2 型と未完の境界

原典はRiehl–Verity Proposition 4.2.15の境界面と親の幅が一致し得る場合、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma walkingAdjunctionWidthOne_minus_plus_generator {n : ℕ}
    (H : ComposableArrows (walkingAdjunctionHom .minus .plus) n)
    (hw : walkingAdjunctionOrdinalWidth H = 1) :
    H = (Functor.const (Fin (n + 1))).obj (walkingAdjunctionGeneratorVertex .minus)

lemma walkingAdjunction_eq_plusParent_of_last_face_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hface : finiteChainFace H (Fin.last (n + 1)) = walkingAdjunctionPlusParentPrefix E) :
    H = walkingAdjunctionPlusParent E ha

lemma walkingAdjunctionFirstIndex_last_of_last_face_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hface : finiteChainFace H (Fin.last (n + 1)) = walkingAdjunctionPlusParentPrefix E) :
    walkingAdjunctionFirstBottomMergeIndex H hlast hnd = Fin.last n

lemma walkingAdjunctionLastFace_widthOne_prefix_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (Q : ComposableArrows (walkingAdjunctionHom .minus .plus) n)
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E)
    (hq : walkingAdjunctionOrdinalWidth Q = 1)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hface : finiteChainFace H (Fin.last (n + 1)) =
      Q.prod' E ⋙ walkingAdjunctionHorizontal .minus .plus Y) :
    H = walkingAdjunctionPlusParent E ha ∧
      walkingAdjunctionFirstBottomMergeIndex H hlast hnd = Fin.last n

lemma walkingAdjunctionFirstIndex_zero_of_first_face_widthOne_prefix {n : ℕ}
    {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (Q : ComposableArrows (walkingAdjunctionHom .minus .plus) n)
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hea : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E)
    (hq : walkingAdjunctionOrdinalWidth Q = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hface : H.δ₀ = Q.prod' E ⋙ walkingAdjunctionHorizontal .minus .plus Y) :
    walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = 0
```

幅1のminusからplusの前置因子があり、残りが始点plusの実原子である実境界面について、
最後では元の実親と最後の実最小元、先頭では実最小元0へ戻すことまで検証した。
全ての実原子因子と前後の残余へ適用するための分解の整理、各因子の実親の幅・深さを含む
全ての順位の比較は未完。
最初の併合が先頭にある場合の境界面の全検収、原典の文字列の幅・fillable条件との全比較、
parental subcomputadのfiltrationと全付着の構成も未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。

### 123.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加5根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionWidthOneBoundary:oleanで、今回の他の2ファイルも取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
実前置の定義と同じ実全関手の等式へ輸送し、行長を揃えて最終検証した。
追加5根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-width-one-boundary-audit-2026-11-16/](../../../evidence/bhatt-scholze/g12/g12-width-one-boundary-audit-2026-11-16/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み17,802行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §124 G01：指定面以外の実境界面の全原子因子について、実親の幅の厳密な境界（11-16）

### 124.1 検証済みの追加

追加は **3ファイル225行・明示宣言5**。累計 **168ファイル18,027行・明示宣言868**。
WalkingAdjunctionPlusFactorParentWidth.lean は79行・1宣言、
WalkingAdjunctionBoundaryPlusParentWidth.lean は78行・2宣言、
WalkingAdjunctionBoundaryMinusParentWidth.lean は68行・2宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationの構成に必要な、実親・実境界面・実道の実構成の法則、
実幅の加法性・単位・原子分解の照合とその証明の分割であり、一覧IDは追加しない。

始点minusの実鎖の原子分解で、指定する原子eの始点がplusの場合を扱った。
その前の実道はminusからplusなので、幅0なら実長さ0となり始点・終点が一致することに反する。
従って前の実幅は正となる。
前後の実幅の和が2未満なら、前の実幅は1で、後の実幅は0に限られる。
実長さ0の検出と道の長さの正値の回収から、後の実道は空となる。
前の実像は幅1なので元の実生成射の定値関手へ戻り（§123）、
全体は単独の実原子eに生成射を前置した実全関手となる。
この形を排除できる実鎖では、前後の実幅の和は2以上となるため、
eの実親の幅がeの幅より1増えること（§117）を含めても、全体の実幅より真に小さい。
共通の補題では、この排除を実関手の等式の否定として述べている。

具体的な実境界面では、その排除を元の実最小元の条件から実際に導いた。
最後の実面については、元の最初の併合が最後でない場合、
生成射の前置の形から実最小元が最後になること（§123）との矛盾で排除できる。
先頭の実面については、元の最初の併合が先頭でない場合、
同じ形から実最小元が0となること（§123）との矛盾で排除できる。
従って指定面以外のこれらの実境界面では、始点plusの任意の実原子因子について、
構成した実親の幅も元の実鎖より真に小さい。
前後の道を空に限定せず、任意の位置の実原子因子を扱っている。

minus始点の正の次数の非退化な実原子因子についても、
その実最小元から構成した実細分の幅が因子と等しいこと（§115）を使った。
先頭・最後の実面の全原子因子の幅の厳密な境界（§122）へ移し、
実細分の幅も元の実鎖より真に小さいことを得た。
先頭については最初の併合が先頭でない場合、最後は全四Homの元の実鎖を扱う。
実細分の非退化性はこの幅の等式に不要なので、新しい入力欄には置いていない。

### 124.2 型と未完の境界

原典はRiehl–Verity Proposition 4.2.15の境界因子の親の比較、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma walkingAdjunctionPlusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (F : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    {C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟨⟨.plus⟩⟩)
    (e : (⟨⟨.plus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) = F)
    (hno : ∀ E : ComposableArrows (walkingAdjunctionHom .plus Y) n,
      WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E →
        F ≠ walkingAdjunctionPlusParentPrefix E) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent e.val e.property) <
      walkingAdjunctionOrdinalWidth F

lemma walkingAdjunctionLastFace_plusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ Fin.last n)
    {C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟨⟨.plus⟩⟩)
    (e : (⟨⟨.plus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) =
      finiteChainFace H (Fin.last (n + 1))) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent e.val e.property) <
      walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionFirstFace_plusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0)
    {C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟨⟨.plus⟩⟩)
    (e : (⟨⟨.plus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) = H.δ₀) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent e.val e.property) <
      walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionLastFace_minusFactor_parent_width_lt {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 2))
    {C : WalkingAdjunctionAtomicVertex (n + 1)}
    (q : Quiver.Path (⟨⟨X⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟨⟨.minus⟩⟩)
    (e : (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)))
    (hfac : (walkingAdjunctionAtomicPathFunctor (n + 1)).map (q.comp (e.toPath.comp r)) =
      finiteChainFace H (Fin.last (n + 2)))
    (he : ULift.up e.val ∈
      (WalkingAdjunctionHomShape.{u} .minus C.level.point).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement e.val e.property he) <
      walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionFirstFace_minusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0)
    {C : WalkingAdjunctionAtomicVertex (n + 1)}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟨⟨.minus⟩⟩)
    (e : (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)))
    (hfac : (walkingAdjunctionAtomicPathFunctor (n + 1)).map (q.comp (e.toPath.comp r)) = H.δ₀)
    (he : ULift.up e.val ∈
      (WalkingAdjunctionHomShape.{u} .minus C.level.point).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement e.val e.property he) <
      walkingAdjunctionOrdinalWidth H
```

今回の境界因子の実親の幅の比較は、構成済みの実道の分解と同じ実生成射の上で検証した。
退化した原子因子から非退化な元へ戻す全輸送とその順位の整理、
最初の併合が先頭にある場合の境界面の全検収、原典の文字列の幅・fillable条件との全比較、
parental subcomputadのfiltrationと全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。

### 124.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加5根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionBoundaryMinusParentWidth:oleanと
WalkingAdjunctionBoundaryPlusParentWidth:oleanで、今回のもう一方の共通ファイルも取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
行長を整え、元の実道と実幅・実関手の等式の輸送を明示して最終検証した。
追加5根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-boundary-parent-audit-2026-11-16/](../../../evidence/bhatt-scholze/g12/g12-boundary-parent-audit-2026-11-16/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み18,027行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §125 G01：最初の純粋な併合が先頭の場合の、実単位の境界と次数1の検収（11-16）

### 125.1 検証済みの追加

追加は **2ファイル141行・明示宣言5**。累計 **170ファイル18,168行・明示宣言873**。
WalkingAdjunctionOnePointSource.lean は69行・3宣言、
WalkingAdjunctionInitialPureBoundary.lean は72行・2宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationの構成に必要な、実原子・実最小元・実単位と境界の法則、
実対象の個数・実射の端点・元の非退化性の照合とその証明の分割であり、一覧IDは追加しない。

minus自己Homで実始点が一点の実射は、終点も一点になることを示した。
唯一の実点が最小元かつ最大元なので、共通表示がその両方を保つことを比較すると、終点の個数は1となる。
従ってminus自己Homで実鎖の始点が一点なら、始点から全頂点への実射を通して、全頂点が一点となる。
構成済みの定値関手の回収と実個数の単射性により、その全実鎖は同じ実単位の定値関手に等しい。
正の次数の元の鎖の二番目の実頂点が一点で、さらにその次の辺があれば、
その実辺は一点から一点となるので同型である。元の非退化性に反するため、元の次数は1に限られる。

始点minusの非退化な実原子で、実際に選んだ最初の併合位置が0である場合も検収した。
実最小元の所属から、元の始点に二番目の実点が存在する。
実原子の初期個数の式は1と終点側の補正の和なので、終点側がplusの場合の一点とは両立しない。
従って終点側はminusとなる。
その先頭の併合が純粋な場合の実個数の条件では、始点の個数2から次の個数1を得る。
上記の実単位と非退化性の検収を使い、元の次数が1で、先頭の実面の元の実長さは0と示した。
実単位の回収自体は全関手の等式であり、次数と単位を新しい入力に置いていない。
この最後の結論は純粋な併合の終点の個数の条件だけで得られ、全点の値の追加仮定を必要としない。

### 125.2 型と未完の境界

原典はRiehl–Verity Proposition 4.2.15の幅2の余単位の場合の単位の境界、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma walkingAdjunctionMinusHom_target_card_one
    {A B : walkingAdjunctionHom .minus .minus} (f : A ⟶ B)
    (ha : walkingAdjunctionOrdinalCard .minus .minus A = 1) :
    walkingAdjunctionOrdinalCard .minus .minus B = 1

lemma walkingAdjunctionMinusChain_eq_identity_of_first_card_one {n : ℕ}
    (H : ComposableArrows (walkingAdjunctionHom .minus .minus) n)
    (hc : walkingAdjunctionOrdinalCard .minus .minus (H.obj 0) = 1) :
    H = (Functor.const (Fin (n + 1))).obj (walkingAdjunctionIdentity .minus)

lemma walkingAdjunctionMinusChain_dimension_zero_of_second_card_one {n : ℕ}
    (H : ComposableArrows (walkingAdjunctionHom .minus .minus) (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus .minus).nonDegenerate (n + 1))
    (hc : walkingAdjunctionOrdinalCard .minus .minus (H.obj 1) = 1) : n = 0

lemma walkingAdjunctionTarget_minus_of_first_index_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = 0) : Y = .minus

lemma walkingAdjunctionInitialPureBoundary_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = 0)
    (hp : walkingAdjunctionOrdinalCard .minus Y (H.obj 1) =
      walkingAdjunctionOrdinalCard .minus Y (H.obj 0) - 2 + 1) :
    Y = .minus ∧ n = 0 ∧ walkingAdjunctionLevelSize H.δ₀ = 0
```

最初の純粋な実併合が先頭にある場合、元の終点側の符号・次数1・実単位の先頭面まで検証した。
退化した原子因子から非退化な元へ戻す全輸送とその順位の整理、
原典の文字列の幅・fillable条件との全比較、parental subcomputadのfiltrationと全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。

### 125.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加5根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionInitialPureBoundary:oleanで、今回のもう一方のファイルも取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
元の実点の最小元・最大元の条件を同じ点へ揃え、実単位の全関手の等式へ輸送して最終検証した。
追加5根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-initial-pure-audit-2026-11-16/](../../../evidence/bhatt-scholze/g12/g12-initial-pure-audit-2026-11-16/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み18,168行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §126 G01：任意の実全射での幅・原子性の輸送と、同じ幅の非退化な実原子への還元（11-16）

### 126.1 検証済みの追加

追加は **3ファイル170行・明示宣言4**。累計 **173ファイル18,338行・明示宣言877**。
WalkingAdjunctionEpiWidth.lean は57行・1宣言、
WalkingAdjunctionEpiAtomicity.lean は60行・2宣言、
WalkingAdjunctionAtomicNondegenerateCore.lean は53行・1宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationの構成に必要な、元の単体圏・実全射・実退化の合成の法則、
実幅・端点・原子性・非退化性の照合とその証明の分割であり、一覧IDは追加しない。

一つの実退化の幅の保存（§118）を、任意の単体圏の実全射の作用へ広げた。
始点次数に帰納し、単射でもある実全射は同じ次数の恒等射へ戻す。
非単射の場合はmathlibの単体圏の実退化一つと残りの全射への分解を取り、
実順序関手の合成の等式を通して、実退化の幅の保存と帰納法を合わせた。
全て元の有限順序関手と全実関手の作用であり、合成の保存を新しい入力に置いていない。

単体圏の実全射は、最小元と最大元の実原像を選ぶことで、その両端を保つことも示した。
実最初・最後の頂点の保存を、端点による実原子性の必要十分条件へ適用し、
全射による再添字付けで原子性が同値となることを得た。
切断の証人を入力に置かず、元の全射性から直接検収した。

元のHomのnerveの宇宙持ち上げにmathlibの非退化単体への分解を適用した。
任意の実原子Hから、元以下の次数m、単体圏の実全射f、非退化な実全関手Kを回収し、
元の全実関手がfの再添字付けによるKの像そのものであることを示した。
全射による実原子性の反映からKも原子的となり、全射による幅の保存からKとHの実幅は等しい。
実原子性・元の単体集合での非退化性・同じ幅・全関手の等式・元以下の次数を同時に結論に保持する。
非退化な元や全射の存在を、新しい仮定として置いていない。

### 126.2 型と未完の境界

原典はRiehl–Verity Proposition 4.2.15の退化した原子因子から非退化な元への処理、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma walkingAdjunctionOrdinalWidth_epi {X Y : WalkingAdjunctionPoint} :
    ∀ (m n : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f]
      (H : ComposableArrows (walkingAdjunctionHom X Y) n),
      walkingAdjunctionOrdinalWidth (walkingAdjunctionSimplexFunctor f ⋙ H) =
        walkingAdjunctionOrdinalWidth H

lemma walkingAdjunctionSimplexFunctor_epi_endpoints {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f] :
    (walkingAdjunctionSimplexFunctor f).obj 0 = 0 ∧
      (walkingAdjunctionSimplexFunctor f).obj (Fin.last m) = Fin.last n

lemma walkingAdjunctionLevelIsAtomic_epi_iff {m n : ℕ} {X Y : WalkingAdjunctionPoint}
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f] (H : ComposableArrows (walkingAdjunctionHom X Y) n) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionSimplexFunctor f ⋙ H) ↔
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H

lemma walkingAdjunctionAtomic_nondegenerate_core {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (K : ComposableArrows (walkingAdjunctionHom X Y) m),
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) K ∧
      ULift.up K ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate m ∧
      walkingAdjunctionOrdinalWidth K = walkingAdjunctionOrdinalWidth H ∧
      H = walkingAdjunctionSimplexFunctor f ⋙ K ∧ m ≤ n
```

退化した実原子因子は、元の全射作用と全関手の等式を保持したまま、同じ幅の非退化な実原子へ戻せる。
この還元と全ての面・実親の順位を一つの生成集合とfiltrationへまとめる構成、
原典の文字列の幅・fillable条件との全比較、parental subcomputadの全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。

### 126.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加4根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionAtomicNondegenerateCore:oleanで、今回の他の2ファイルも取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
元の実単体作用・宇宙持ち上げの分解・同じ全関手の等式と幅へ輸送して最終検証した。
追加4根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-epi-nondegenerate-audit-2026-11-16/](../../../evidence/bhatt-scholze/g12/g12-epi-nondegenerate-audit-2026-11-16/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み18,338行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §127 G01：非退化な実原子の生成元の型と、模型の純粋性・実親・指定面の一体化（11-16）

### 127.1 検証済みの追加

追加は **3ファイル276行・明示宣言10**。累計 **176ファイル18,614行・明示宣言887**。
WalkingAdjunctionAtomicCells.lean は128行・4宣言、
WalkingAdjunctionAtomicCellParentLaws.lean は80行・4宣言、
WalkingAdjunctionAtomicCellParentPositions.lean は68行・2宣言。
明示宣言には生成元のstructureの型を1根として含める。自動生成される欄・コンストラクタは別根に数えない。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationに使う、構成済みの実生成元・実親・純粋性・指定面の
実データの一体化と、その幅・面・有限添字の法則であり、一覧IDは追加しない。

非退化な実原子を、元の全実関手chain、原子性atomic、元の単体集合での非退化性nondegenerateを
保持する生成元の型WalkingAdjunctionAtomicCellへまとめた。
次数と両端は型に置く。
有限順序模型のNativeFillableは、plus始点では偽、minus始点の次数0では真、
minus始点の正の次数では元の実最小元の辺が純粋な底併合であるという、検証済みの具体的条件を使う。
この定義は現在の有限順序模型の条件であり、原典の文字列の条件と一致するとの全比較を済みにはしない。

NativeFillableでない生成元から、一つ高次のminus始点の実生成元parentを実際に構成した。
plus始点には既存の実終端の親、minus始点の正の次数には既存の実最初の細分を使う。
minus始点の次数0ではNativeFillableが真なので、非純粋性との矛盾でその場合を排除する。
元の実構成の原子性・非退化性の定理を適用し、実親の存在や非退化性を引数の欄に置いていない。
実親の実最小元を回収し、挿入した実辺の個数と全点の値を元へ揃えることで、
構成した実親がNativeFillableを満たすことも証明した。

まとめた実親の幅は、plus始点では元より1大きく、minus始点では元の幅に等しい。
実親の指定面の添字parentFaceIndexも元の実構成から取り出した。
plus始点では親の最後、minus始点では元の実最小元の直後である。
元の生成元を親のHomへ移すparentChildImageは、plus始点で実生成射の前置、minus始点で元の実全関手となる。
親の指定面がこのparentChildImageそのものと等しいことを、元の全実関手の等式で検収した。

指定面の実添字は常に0でないことも証明した。
その添字が親の最後より小さいことは、元の生成元の始点がminusであることと同値となる。
従って内側と最後の二つの実付着に必要な位置の制約を、元の実添字から結論として回収できる。
これらの法則は親の型の新しい証人を入力にせず、既存の実構成から得ている。

### 127.2 型と未完の境界

原典はRiehl–Verity Definition 4.1.1・4.2.1、Lemma 4.2.10、Proposition 4.2.15、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
structure WalkingAdjunctionAtomicCell (n : ℕ) (X Y : WalkingAdjunctionPoint) where
  chain : ComposableArrows (walkingAdjunctionHom X Y) n
  atomic : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) chain
  nondegenerate : ULift.up chain ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate n

def WalkingAdjunctionAtomicCell.NativeFillable {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) : Prop

def WalkingAdjunctionAtomicCell.parent {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y

lemma WalkingAdjunctionAtomicCell.parent_nativeFillable {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    (a.parent hnf).NativeFillable

lemma WalkingAdjunctionAtomicCell.parent_width {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    walkingAdjunctionOrdinalWidth (a.parent hnf).chain = walkingAdjunctionOrdinalWidth a.chain +
      (match X with | .plus => 1 | .minus => 0)

def WalkingAdjunctionAtomicCell.parentFaceIndex {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) : Fin (n + 2)

def WalkingAdjunctionAtomicCell.parentChildImage {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) :
    ComposableArrows (walkingAdjunctionHom .minus Y) n

lemma WalkingAdjunctionAtomicCell.parent_face {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    finiteChainFace (a.parent hnf).chain (a.parentFaceIndex hnf) = a.parentChildImage

lemma WalkingAdjunctionAtomicCell.parentFaceIndex_ne_zero {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (a : WalkingAdjunctionAtomicCell.{u} n X Y)
    (hnf : ¬ a.NativeFillable) : a.parentFaceIndex hnf ≠ 0

lemma WalkingAdjunctionAtomicCell.parentFaceIndex_lt_last_iff {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (a : WalkingAdjunctionAtomicCell.{u} n X Y)
    (hnf : ¬ a.NativeFillable) : a.parentFaceIndex hnf < Fin.last (n + 1) ↔ X = .minus
```

現在の有限順序模型で、実生成元・純粋性条件・非純粋な元からの実親・実親の純粋性、
幅・指定面の実全関手の等式・付着の実位置までを一つの型の上で検証した。
原典の文字列の幅・fillable条件との全比較、親と子の往復をこの型へまとめた全単射、
全ての順位をまとめたfiltrationとparental subcomputadの全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。

### 127.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加10根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionAtomicCellParentPositions:oleanで、今回の他の2ファイルも取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
実最小元の選択に元の非退化性の引数を明示し、実面の両端の同じ実対象と実個数へ揃えて最終検証した。
追加10根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-atomic-cells-audit-2026-11-16/](../../../evidence/bhatt-scholze/g12/g12-atomic-cells-audit-2026-11-16/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み18,614行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §128 G01：有限順序模型の実子の回収と、実親子の両方向の往復・全単射（11-16）

### 128.1 検証済みの追加

追加は **3ファイル345行・明示宣言12**。累計 **179ファイル18,959行・明示宣言899**。
WalkingAdjunctionAtomicCellChildren.lean は104行・3宣言、
WalkingAdjunctionAtomicCellChild.lean は142行・7宣言、
WalkingAdjunctionAtomicCellPairing.lean は99行・2宣言。
個々の宣言・証明は200行以下、新規Leanの行長は100文字以下。
同じG01の全実随伴・実filtrationに使う、構成済みの実親と実子のデータの一体化、
実最小元・係数移送・原子性・非退化性・非純粋性と両方向の合成の照合であり、一覧IDは追加しない。

模型の純粋性NativeFillableを、指定する同じ実最小元の添字へ移す補題を作った。
添字を先に同一視することで、全点の条件の依存する有限点の型も同じ実添字に揃えている。
純粋な実親で最初の併合が最後なら、元の最後の面から実前置を除く実子を回収し、
その原子性・非退化性を同じ生成元の型へ戻した。始点plusなのでNativeFillableではない。
最初の併合が内側なら、元の指定面からminus始点の実子を取り、
原子性・非退化性・実最小元の保存と、純粋な実親の逆の非純粋性の法則を同じ型へ戻した。
子の存在・原子性・非退化性・非純粋性を新しい入力に置いていない。

正の次数の全ての純粋な実生成元からのchildを、一つの関数にまとめた。
子の次数0では最小添字が唯一の最後の点なのでplus始点の子を取る。
それ以外では、元の実最小元が最後かを判定し、最後の実子または内側の実子を取る。
子の始点を依存和に保持し、その中に元の実全関手と非純粋性を保持している。
実分岐は依存和の値そのものの等式として回収し、親の関数へその等式を移した。
子から実親を作り直すと元の純粋な実生成元に戻ることを検証した。

逆向きにも、非純粋な実生成元から親を作り、その子を回収すると、元の始点と実生成元へ戻る。
plus始点では元の実最後の親子の往復を使う。
minus始点の正の次数では、親の実最小元は元の最小元のcastSuccなので最後ではなく、
実指定面を回収すると元の全実関手となる。
実関手の等式と証明の一意性から、生成元そのものの等式へ戻した。
二つの実関数と両方向の往復を使い、現在の有限順序模型の非純粋な生成元と
一つ高次のminus始点の純粋な実生成元の全単射を構成した。
この全単射は原典の文字列の模型との全比較を済みにするものではない。

### 128.2 型と未完の境界

原典はRiehl–Verity Definition 4.2.1の親子の全単射、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。追加の型は以下。

```lean
lemma WalkingAdjunctionAtomicCell.pure_at_of_nativeFillable {n : ℕ}
    {Y : WalkingAdjunctionPoint} (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y)
    (k : Fin (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = k)
    (hfill : p.NativeFillable) :
    walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.succ) =
        walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.castSucc) - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (p.chain.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = i.val - 1

def WalkingAdjunctionAtomicCell.lastChild {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y)
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = Fin.last n)
    (hfill : p.NativeFillable) :
    {a : WalkingAdjunctionAtomicCell.{u} n .plus Y // ¬ a.NativeFillable}

def WalkingAdjunctionAtomicCell.innerChild {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 2) .minus Y) (k : Fin (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = k.castSucc)
    (hfill : p.NativeFillable) :
    {a : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y // ¬ a.NativeFillable}

lemma WalkingAdjunctionAtomicCell.ext_chain {n : ℕ} {X Y : WalkingAdjunctionPoint}
    {a b : WalkingAdjunctionAtomicCell.{u} n X Y} (h : a.chain = b.chain) : a = b

def WalkingAdjunctionAtomicCell.child {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y) (hfill : p.NativeFillable) :
    Σ X : WalkingAdjunctionPoint,
      {a : WalkingAdjunctionAtomicCell.{u} n X Y // ¬ a.NativeFillable}

lemma WalkingAdjunctionAtomicCell.child_of_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 2) .minus Y) (hfill : p.NativeFillable)
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate =
      Fin.last (n + 1)) : p.child hfill = ⟨.plus, p.lastChild hk hfill⟩

lemma WalkingAdjunctionAtomicCell.child_of_not_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 2) .minus Y) (hfill : p.NativeFillable)
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate ≠
      Fin.last (n + 1)) : p.child hfill =
      ⟨.minus, p.innerChild ((walkingAdjunctionFirstBottomMergeIndex p.chain
        (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate).castPred hk)
        (Fin.castSucc_castPred _ hk).symm hfill⟩

lemma WalkingAdjunctionAtomicCell.lastChild_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y)
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = Fin.last n)
    (hfill : p.NativeFillable) :
    ((p.lastChild hk hfill).val.parent (p.lastChild hk hfill).property) = p

lemma WalkingAdjunctionAtomicCell.innerChild_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 2) .minus Y) (k : Fin (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = k.castSucc)
    (hfill : p.NativeFillable) :
    ((p.innerChild k hk hfill).val.parent (p.innerChild k hk hfill).property) = p

lemma WalkingAdjunctionAtomicCell.child_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y) (hfill : p.NativeFillable) :
    ((p.child hfill).2.val.parent (p.child hfill).2.property) = p

lemma WalkingAdjunctionAtomicCell.parent_child {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    (a.parent hnf).child (a.parent_nativeFillable hnf) = ⟨X, ⟨a, hnf⟩⟩

def walkingAdjunctionAtomicCellParentEquiv (n : ℕ) (Y : WalkingAdjunctionPoint) :
    (Σ X : WalkingAdjunctionPoint,
      {a : WalkingAdjunctionAtomicCell.{u} n X Y // ¬ a.NativeFillable}) ≃
    {p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y // p.NativeFillable}
```

現在の有限順序模型で、実親と実子、生成元そのものの両方向の往復と全単射まで検証した。
原典の文字列の幅・fillable条件との全比較、全ての順位をまとめたfiltrationと
parental subcomputadの全付着の構成は未完。
元のQCatAdjunctionからの全coherentな延長、水平反対の向きの全比較、
同じF≫U・単位・余単位・HAモデルとの照合も未完である。
G01の済みは0、G02以降も未完を維持する。外枠20,000行まで残りは1,041行。

### 128.3 検証と進み

with_build_lock.sh --class impl --wait 3600、最大240秒の短い枠で対象ビルドと追加12根だけの公理監査を確認した。
最終固定コマンドの対象はWalkingAdjunctionAtomicCellPairing:oleanで、今回の他の2ファイルも取り込む。
対象ビルド・監査と外側の終了は0、最終対象ビルドは警告なし。
最小添字の等式を依存和の値の等式として回収し、同じ親の実関手とcastPredの証明も揃えて最終検証した。
追加12根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・監査全出力・対象ビルドログは
[g12-cell-pairing-audit-2026-11-16/](../../../evidence/bhatt-scholze/g12/g12-cell-pairing-audit-2026-11-16/)に保存した。
M15・drafts・main・⑤aの既存ファイル・Interfaceは変更せず、全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み18,959行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


