module
public import SerrePositivity.KST.SConstruction.ArCofiberInputs
public import SerrePositivity.KST.SConstruction.DegeneratePushouts

/-! # 零対角の枠の中の cofiber 四角形
概要：第一行または対角に対応する標準 cofiber 四角形は枠の中に留まる。
方針：第一行では垂直辺が、対角では水平辺が恒等となる。
規約：枠の元の図式を厳密に使用する。使われ方：枠上の cofiber 補完の固定。
原典：HTT §1.2.12・§4.3.2、BGT Lemma 7.3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：枠の区間の cofiber 四角形の全ての角も枠に属する。
方針：縦座標零の場合と、第一行・対角の二つの場合を分ける。
規約：対角条件は端点の等号。使われ方：枠内の順序写像の定義。 -/
lemma arCofiberSquareOrder_mem_frame {n : ℕ} (a : FrameAr.{u} n)
    (q : ULift.{u} (Fin 2 × Fin 2)) :
    (arCofiberSquareOrder n (a.val, q)).down.val.1 = 0 ∨
      IsDiagonal (arCofiberSquareOrder n (a.val, q)) := by
  change (if q.down.2 = 0 then 0 else a.val.down.val.1) = 0 ∨
    (if q.down.2 = 0 then 0 else a.val.down.val.1) =
      (if q.down.1 = 0 then a.val.down.val.1 else a.val.down.val.2)
  by_cases hq : q.down.2 = 0
  · exact Or.inl (if_pos hq)
  · rcases a.property with ha | ha
    · exact Or.inl (by simp only [hq, ↓reduceIte, ha])
    · right
      change a.val.down.val.1 = a.val.down.val.2 at ha
      simp only [hq, ↓reduceIte, ← ha, ite_self]

/-- 概要：枠と正方形の積から枠への cofiber の角の順序写像。
方針：Ar[n] の順序写像を枠に制限する。
規約：元の Ar の写像と厳密に同じ値。使われ方：枠の cofiber 族の形状。 -/
def frameCofiberSquareOrder (n : ℕ) :
    FrameAr.{u} n × ULift.{u} (Fin 2 × Fin 2) →o FrameAr.{u} n where
  toFun p := ⟨arCofiberSquareOrder n (p.1.val, p.2), arCofiberSquareOrder_mem_frame p.1 p.2⟩
  monotone' _ _ h := (arCofiberSquareOrder n).monotone h

/-- 概要：枠の全区間に対応する cofiber 四角形を同時に表す射。
方針：鎖の各頂点で枠内の順序写像を適用する。
規約：枠が第一因子。使われ方：補完の既存部分の構成。 -/
def frameCofiberSquareMap (n : ℕ) :
    frameNerve.{u} n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ frameNerve n where
  app d := ↾fun s ↦ (show Monotone (fun r : Fin (d.unop.len + 1) ↦
    frameCofiberSquareOrder n
      (s.1.obj r, ULift.up (prodStdSimplex.objEquiv s.2 r))) from by
        intro r t h
        exact (frameCofiberSquareOrder n).monotone
          ⟨s.1.monotone h, (prodStdSimplex.objEquiv s.2).monotone h⟩).functor
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    rfl

/-- 概要：枠の四角形を Ar[n] に含めると元の全区間の四角形に一致する。
方針：鎖の各頂点で包含と順序写像の値を比べる。
規約：厳密な等号。使われ方：既存の gapped 境界との一致。 -/
lemma frameCofiberSquareMap_inclusion (n : ℕ) :
    frameCofiberSquareMap n ≫ frameInclusion n =
      (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ arCofiberSquareMap n := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  rfl

/-- 概要：枠の一つの区間に付随する四角形。
方針：枠のパラメーターを指定した頂点に固定する。
規約：四角形の値は全て枠に属する。使われ方：点ごとの押し出し性。 -/
def frameCofiberSquareAt {n : ℕ} (a : FrameAr.{u} n) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ frameNerve n :=
  CartesianMonoidalCategory.lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 _) ≫
    frameCofiberSquareMap n

/-- 概要：第一行の区間では cofiber 四角形は下辺を垂直に定値に延ばしたもの。
方針：左端零なので縦座標の選択に依存しない。
規約：第一行の (0,0) も含む。使われ方：恒等垂直辺の押し出し性。 -/
lemma frameCofiberSquareAt_firstRow {n : ℕ} (a : FrameAr.{u} n)
    (ha : a.val.down.val.1 = 0) :
    frameCofiberSquareAt a = CartesianMonoidalCategory.fst _ _ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ frameCofiberSquareAt a := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change (if _ = 0 then 0 else a.val.down.val.1) = _
    simp only [ha, ite_self]
    rfl
  · rfl

/-- 概要：対角の区間では cofiber 四角形は左辺を水平に定値に延ばしたもの。
方針：両端が等しいので横座標の選択に依存しない。
規約：対角の全ての頂点を扱う。使われ方：恒等水平辺の押し出し性。 -/
lemma frameCofiberSquareAt_diagonal {n : ℕ} (a : FrameAr.{u} n)
    (ha : IsDiagonal a.val) :
    frameCofiberSquareAt a = CartesianMonoidalCategory.snd _ _ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ frameCofiberSquareAt a := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change a.val.down.val.1 = a.val.down.val.2 at ha
    change (if _ = 0 then a.val.down.val.1 else a.val.down.val.2) = _
    simp only [← ha, ite_self]
    rfl

/-- 概要：枠の任意の図式の標準 cofiber 四角形は押し出し。
方針：第一行と対角でそれぞれ一対の辺が恒等となることを使う。
規約：値域は quasicategory、零対角の仮定はこの主張には不要。
使われ方：枠上の cofiber 族の普遍性。 -/
lemma frameCofiberSquareAt_isPushout {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : frameNerve n ⟶ C) (a : FrameAr.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (frameCofiberSquareAt a ≫ F) := by
  rcases a.property with ha | ha
  · have he := congrArg (fun f => f ≫ F) (frameCofiberSquareAt_firstRow a ha)
    rw [Category.assoc] at he
    rw [he]
    exact isPushoutSquare_fst _
  · have he := congrArg (fun f => f ≫ F) (frameCofiberSquareAt_diagonal a ha)
    rw [Category.assoc] at he
    rw [he]
    exact isPushoutSquare_snd _


/-- 概要：枠の図式から標準 cofiber 正方形の族を取り出す。
方針：枠内の形状で前合成して内部 curry を取る。
規約：零条件はまだ要求しない。使われ方：枠で固定する cofiber 族。 -/
def frameCofiberFamily {n : ℕ} {C : SSet.{u}} (F : frameNerve n ⟶ C) :
    frameNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
  curry ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (frameNerve n)).hom ≫ frameCofiberSquareMap n ≫ F)

/-- 概要：枠の cofiber 族を一点で評価すると対応する標準正方形を得る。
方針：curry の頂点評価と積の対称性を使う。
規約：厳密な頂点の等号。使われ方：全部分複体への持ち上げ。 -/
lemma frameCofiberFamily_vertex {n : ℕ} {C : SSet.{u}}
    (F : frameNerve n ⟶ C) (a : FrameAr.{u} n) :
    (frameCofiberFamily F).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (frameCofiberSquareAt a ≫ F) := by
  rw [frameCofiberFamily, curry_vertex_value]
  apply congrArg (fun f : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  rfl

/-- 概要：枠の cofiber 正方形の零角は元の枠の対角である。
方針：角 (0,1) で端点選択を計算する。
規約：零対象の性質を仮定せず頂点を同定する。使われ方：零角条件の移送。 -/
lemma frameCofiberSquareAt_zero_corner {n : ℕ} {C : SSet.{u}}
    (F : frameNerve n ⟶ C) (a : FrameAr.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (frameCofiberSquareAt a ≫ F) 0 1 =
      F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀
        (⟨arObj a.val.down.val.1 a.val.down.val.1 le_rfl, Or.inr rfl⟩ : FrameAr n)) := by
  apply congrArg (F.app (Opposite.op ⦋0⦌))
  apply ComposableArrows.ext₀
  apply Subtype.ext
  rfl

/-- 概要：零対角の枠の標準正方形は自然な cofiber 族をなす。
方針：零角の同定と恒等辺による押し出し性から全部分複体に持ち上げる。
規約：値域は quasicategory、安定性は要求しない。
使われ方：第一行と対角を変更せず補完する際の既存データ。 -/
def zeroFrameCofiberFamily {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : frameNerve n ⟶ C) (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    frameNerve n ⟶ cofiberDiagrams C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (frameCofiberFamily F) (by
    intro v
    obtain ⟨a, rfl⟩ := nerveEquiv.symm.surjective v
    change IsCofiberDiagramVertex
      ((frameCofiberFamily F).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a))
    rw [frameCofiberFamily_vertex]
    constructor
    · rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex, frameCofiberSquareAt_zero_corner]
      have hz := hF (ComposableArrows.mk₀
        (⟨arObj a.val.down.val.1 a.val.down.val.1 le_rfl, Or.inr rfl⟩ : FrameAr n)) rfl
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hz
      exact hz
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C (frameCofiberSquareAt a ≫ F)))
      rw [Equiv.symm_apply_apply]
      exact frameCofiberSquareAt_isPushout F a)

/-- 概要：枠の cofiber 族の条件を忘れると元の正方形の族。
方針：全部分複体の持ち上げの定義を展開する。
規約：全次数での厳密等号。使われ方：相対境界の一致。 -/
lemma zeroFrameCofiberFamily_ι {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : frameNerve n ⟶ C) (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    zeroFrameCofiberFamily F hF ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      frameCofiberFamily F := rfl

/-- 概要：cofiber 四角形の族の右上角は元の 枠 の区間。
方針：端点の選択で横・縦とも時刻一を取る。
規約：図式を入れる前の添字の厳密等号。使われ方：元の図式の回収。 -/
lemma frameCofiberSquareMap_apex (n : ℕ) :
    CartesianMonoidalCategory.lift (𝟙 (frameNerve.{u} n))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ frameCofiberSquareMap n = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> rfl

/-- 概要：自然な cofiber 四角形の族の右上角を取ると元の図式に戻る。
方針：curry の評価と添字の右上角の恒等式を合わせる。
規約：零対角条件は不要。使われ方：復元した cofiber 族の境界の厳密化。 -/
lemma frameCofiberFamily_apex {n : ℕ} {C : SSet.{u}} (F : frameNerve n ⟶ C) :
    frameCofiberFamily F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = F := by
  rw [frameCofiberFamily, curry_evaluate_vertex]
  have he : CartesianMonoidalCategory.lift
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (𝟙 (frameNerve n)) ≫ (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (frameNerve n)).hom =
      CartesianMonoidalCategory.lift (𝟙 (frameNerve n))
        (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
          stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := rfl
  rw [← Category.assoc, ← Category.assoc, he, frameCofiberSquareMap_apex, Category.id_comp]


/-- 概要：枠上の実際の cofiber 族は右上角で元の枠を厳密に回収する。
方針：全部分複体への包含後に右上角の評価式を使う。
規約：quasicategory 性だけを要求し、安定性は不要。
使われ方：補完後の図式の第一行を指定入力と厳密に一致させる。 -/
lemma zeroFrameCofiberFamily_apex {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : frameNerve n ⟶ C) (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    zeroFrameCofiberFamily F hF ≫ cofiberApex C = F := by
  change (zeroFrameCofiberFamily F hF ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = F
  rw [zeroFrameCofiberFamily_ι]
  exact frameCofiberFamily_apex F

end SerrePositivity.KST.SConstruction
