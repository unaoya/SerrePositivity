module

public import SerrePositivity.InfinityCategories.F1.Coherent.HomReindex

/-!
概要：豊穣 Hom の比較の単体的な自然性。
方針：最後の頂点固定延長による前合成と豊穣 Hom の単体の引き戻しを比較する。
規約：Mathlib の包含順序に合わせて右 pinched 模型を用いる。
使われ方：Kerodon Construction 4.6.7.3、Remark 4.6.7.9、比較射の単体的構造。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：比較の Hom の添字の等号による移送を計算する。
方針：添字の等号を消去し、始域と終域の Hom の移送の式を比べる。
規約：右端の対象 A と B への正規化を含めて述べる。
使われ方：Kerodon Construction 4.6.7.3、比較の単体的な自然性。 -/
lemma coherentHomComparisonHom_transport {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y A B : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) {i j i' j' : Fin (n + 2)}
    (hi : i = i') (hj : j = j')
    (hA : coherentHomComparisonObj X Y i' = A)
    (hB : coherentHomComparisonObj X Y j' = B) :
    coherentHomComparisonHom σ i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (coherentHomComparisonObj X Y) hi).trans hA)
      ((congrArg (coherentHomComparisonObj X Y) hj).trans hB)) =
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩) hi hj) ≫
        coherentHomComparisonHom σ i' j' ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) := by
  subst i'
  subst j'
  simp

/-- 概要：thickening の Hom の端点を等号で移しても path の集合は変わらない。
方針：二つの端点の等号を消去する。
規約：各次数の単体を構成する path の各頂点で述べる。
使われ方：Kerodon Construction 4.6.7.3、添字変換した Hom の作用の座標比較。 -/
lemma thickeningHom_transport_I {J : Type u} [LinearOrder J]
    {i j i' j' : SimplicialThickening J} (hi : i = i') (hj : j = j')
    {d : SimplexCategoryᵒᵖ} (P : (SimplicialCategory.sHom i j).obj d)
    (k : Fin (d.unop.len + 1)) :
    (((eqToHom (congrArg₂ SimplicialCategory.sHom hi hj)).app d P).obj k).I =
      (P.obj k).I := by
  subst i'
  subst j'
  rfl

/-- 概要：最後の頂点固定延長の豊穣 Hom 上の作用は path の像の nerve と一致する。
方針：端点を標準の castSucc と last に移した後、各 path の部分集合の像を比較する。
規約：移送を消さずに明示しておく。
使われ方：Kerodon Construction 4.6.7.3、最大元の自然性を豊穣関手へ適用する段階。 -/
lemma thickeningExtend_map_cast_last {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (SimplicialThickening.functor (PinchedHom.extend α).toOrderHom.uliftMap).map
      (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (m + 2))))
      ⟨ULift.up (Fin.last (m + 1))⟩ ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
        (PinchedHom.extendOrderHom_castSucc α.toOrderHom i)
        (PinchedHom.extendOrderHom_last α.toOrderHom)) =
      nerveMap (pathLastReindexFunctor α i) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun k ↦ ?_)
  apply SimplicialThickening.Path.ext
  have h := thickeningHom_transport_I
    (congrArg (fun a : Fin (n + 2) ↦
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
        (PinchedHom.extendOrderHom_castSucc α.toOrderHom i))
    (congrArg (fun a : Fin (n + 2) ↦
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
        (PinchedHom.extendOrderHom_last α.toOrderHom))
    (((SimplicialThickening.functor (PinchedHom.extend α).toOrderHom.uliftMap).map
      (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (m + 2))))
      ⟨ULift.up (Fin.last (m + 1))⟩).app d P) k
  exact h

/-- 概要：比較の添字延長が誘導する豊穣 Hom 上の射。
方針：最後の頂点固定延長の豊穣関手の map を取る。
規約：両端点を Fin の添字で明示する。
使われ方：Kerodon Construction 4.6.7.3、比較の自然性の正規化。 -/
def thickeningExtendHom {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i j : Fin (m + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (m + 2)))) ⟨ULift.up j⟩ ⟶
      SimplicialCategory.sHom
        (⟨ULift.up (PinchedHom.extendOrderHom α.toOrderHom i)⟩ :
          SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up (PinchedHom.extendOrderHom α.toOrderHom j)⟩ :=
  (SimplicialThickening.functor (PinchedHom.extend α).toOrderHom.uliftMap).map _ _

/-- 概要：二端点を同じ対象に正規化した Hom の自然性から元の自然性が従う。
方針：正規化の同型を右から合成し、等号の射の合成をまとめる。
規約：正規化後の二対象 A と B は各場合に指定する。
使われ方：Kerodon Construction 4.6.7.3、比較の型の移送を含む自然性。 -/
lemma coherentHomComparisonHom_naturality_of_normalized
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y A B : C} {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (i j : Fin (m + 2))
    (hA : coherentHomComparisonObj X Y i = A) (hB : coherentHomComparisonObj X Y j = B)
    (hA' : coherentHomComparisonObj X Y (PinchedHom.extendOrderHom α.toOrderHom i) = A)
    (hB' : coherentHomComparisonObj X Y (PinchedHom.extendOrderHom α.toOrderHom j) = B)
    (h : thickeningExtendHom α i j ≫ coherentHomComparisonHom σ
      (PinchedHom.extendOrderHom α.toOrderHom i)
      (PinchedHom.extendOrderHom α.toOrderHom j) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA' hB') =
          coherentHomComparisonHom ((SimplicialCategory.sHom X Y).map α.op σ) i j ≫
            eqToHom (congrArg₂ SimplicialCategory.sHom hA hB)) :
    (thickeningExtendHom α i j ≫ coherentHomComparisonHom σ
      (PinchedHom.extendOrderHom α.toOrderHom i)
      (PinchedHom.extendOrderHom α.toOrderHom j)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentHomComparisonObj_extend X Y α i)
          (coherentHomComparisonObj_extend X Y α j)) =
            coherentHomComparisonHom ((SimplicialCategory.sHom X Y).map α.op σ) i j := by
  apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom hA hB))).1
  simpa only [Category.assoc, eqToHom_trans] using h

/-- 概要：比較の coherent な単体は豊穣 Hom の単体の引き戻しに自然。
方針：対象を延長の計算で比較し、Hom は端点を正規化して最大元の自然性を適用する。
規約：任意の面と退化を一つの式で扱う。
使われ方：Kerodon Construction 4.6.7.3、比較の単体集合の射。 -/
lemma coherentHomComparisonSimplex_naturality {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    (SimplicialNerve C).map (PinchedHom.extend α).op (coherentHomComparisonSimplex σ) =
      coherentHomComparisonSimplex ((SimplicialCategory.sHom X Y).map α.op σ) := by
  apply EnrichedFunctor.ext SSet
    (fun i ↦ coherentHomComparisonObj_extend X Y α i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change (thickeningExtendHom α i j ≫ coherentHomComparisonHom σ
    (PinchedHom.extendOrderHom α.toOrderHom i)
    (PinchedHom.extendOrderHom α.toOrderHom j)) ≫ eqToHom _ =
      coherentHomComparisonHom ((SimplicialCategory.sHom X Y).map α.op σ) i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    let hi := PinchedHom.extendOrderHom_last α.toOrderHom
    let hN := coherentHomComparisonObj_last X Y n
    let hM := coherentHomComparisonObj_last X Y m
    apply coherentHomComparisonHom_naturality_of_normalized α σ _ _ hM hM
      ((congrArg (coherentHomComparisonObj X Y) hi).trans hN)
      ((congrArg (coherentHomComparisonObj X Y) hi).trans hN)
    rw [coherentHomComparisonHom_transport σ hi hi hN hN]
    simp only [coherentHomComparisonHom_last_last, comp_toUnit_assoc]
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := SimplicialThickening.Path.le (P.obj 0)
    change m + 1 ≤ j.val at h
    have : j.val < m + 1 := j.isLt
    omega
  case cast.last i =>
    let hi := PinchedHom.extendOrderHom_castSucc α.toOrderHom i
    let hj := PinchedHom.extendOrderHom_last α.toOrderHom
    let hNi := coherentHomComparisonObj_cast X Y (α.toOrderHom i)
    let hNj := coherentHomComparisonObj_last X Y n
    let hMi := coherentHomComparisonObj_cast X Y i
    let hMj := coherentHomComparisonObj_last X Y m
    apply coherentHomComparisonHom_naturality_of_normalized α σ _ _ hMi hMj
      ((congrArg (coherentHomComparisonObj X Y) hi).trans hNi)
      ((congrArg (coherentHomComparisonObj X Y) hj).trans hNj)
    rw [coherentHomComparisonHom_transport σ hi hj hNi hNj]
    simp only [coherentHomComparisonHom_cast_last]
    rw [← Category.assoc]
    dsimp only [thickeningExtendHom]
    rw [thickeningExtend_map_cast_last, ← Category.assoc,
      pathLastMaximumMap_naturality, Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
  case cast.cast i j =>
    let hi := PinchedHom.extendOrderHom_castSucc α.toOrderHom i
    let hj := PinchedHom.extendOrderHom_castSucc α.toOrderHom j
    let hNi := coherentHomComparisonObj_cast X Y (α.toOrderHom i)
    let hNj := coherentHomComparisonObj_cast X Y (α.toOrderHom j)
    let hMi := coherentHomComparisonObj_cast X Y i
    let hMj := coherentHomComparisonObj_cast X Y j
    apply coherentHomComparisonHom_naturality_of_normalized α σ _ _ hMi hMj
      ((congrArg (coherentHomComparisonObj X Y) hi).trans hNi)
      ((congrArg (coherentHomComparisonObj X Y) hj).trans hNj)
    rw [coherentHomComparisonHom_transport σ hi hj hNi hNj]
    simp only [coherentHomComparisonHom_cast_cast, comp_toUnit_assoc]

/-- 概要：豊穣 Hom から coherent nerve の右 pinched 写像空間への比較射。
方針：各 Hom の単体を固定面・固定終点のある coherent 単体へ送り、自然性で貼り合わせる。
規約：値域の単体の宇宙 max(u,v) に合わせて始域を ULift する。
使われ方：Kerodon Construction 4.6.7.3、Remark 4.6.7.9、fiber と豊穣 Hom の比較。 -/
noncomputable def coherentHomComparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⟶
      pinchedHom (coherentNerveVertex X) (coherentNerveVertex Y) where
  app d := ↾fun σ ↦ coherentHomComparisonPinchedSimplex σ.down
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro σ
    apply PinchedHom.Simplex.ext
    exact (coherentHomComparisonSimplex_naturality α.unop σ.down).symm

/-- 概要：比較射の各単体の元の coherent な単体を計算する。
方針：ULift を戻した単体の比較の定義を展開する。
規約：固定面・固定終点の証明は部分型の証明として保持する。
使われ方：Kerodon Construction 4.6.7.3、比較射と辺・高次単体の対応の検査。 -/
lemma coherentHomComparison_app_val {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    ((coherentHomComparison X Y).app (Opposite.op ⦋n⦌) (ULift.up σ)).val =
      coherentHomComparisonSimplex σ := rfl

end SerrePositivity.InfinityCategories
