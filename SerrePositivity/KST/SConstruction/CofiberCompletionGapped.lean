module
public import SerrePositivity.KST.SConstruction.CofiberComparisonIsos

/-! # 固定 span の cofiber 補完の gapped 性
概要：枠と span を厳密に保つ cofiber の族の右上角は gapped 図式になる。
方針：三つの比較 prism で標準正方形へ普遍性を移し、第一行からの判定を使う。
規約：gapped 性を出力の仮定に含めない。
使われ方：BGT Lemma 7.3 の第一行復元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：積上の族の右上角を取る図式。
方針：正方形の右上角に制限する。
規約：普遍性を含まない。使われ方：補完から得る実際の Ar[n] 図式。 -/
def arSquareFamilyApex {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) : arNerve n ⟶ C :=
  lift (𝟙 (arNerve n)) (SSet.const
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ E

/-- 概要：枠を保つ族の右上角も元の枠を厳密に保つ。
方針：枠の等号を右上角で制限し、枠の標準正方形の頂点評価を使う。
規約：全単体での等号。使われ方：零対角条件の回収。 -/
lemma arSquareFamilyApex_frame {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F) :
    frameInclusion n ≫ arSquareFamilyApex E = F := by
  have he := congrArg (fun p : frameNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C =>
    lift (𝟙 (frameNerve n)) (SSet.const
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ p) h
  simp only [← Category.assoc] at he
  erw [frameCofiberSquareMap_apex, Category.id_comp] at he
  exact he

/-- 概要：固定 span と枠を持つ押し出し正方形の族の右上角は gapped。
方針：対角を枠から回収し、比較同型で標準 cofiber 正方形へ押し出し性を移す。
規約：C は quasicategory。安定性は族の存在に使い、この含意では不要。
使われ方：相対 cofiber 補完から実際の第一行復元を得る。 -/
lemma isGapped_arSquareFamilyApex {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
    (hframe : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (hleft : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (hbottom : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (hpushout : ∀ a : Ar.{u} n, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E)) :
    IsGapped (arSquareFamilyApex E) := by
  apply (isGapped_iff_originSquares _).2
  constructor
  · intro i
    let v : (frameNerve n) _⦋0⦌ := ComposableArrows.mk₀
      (⟨arObj i i le_rfl, Or.inr rfl⟩ : FrameAr n)
    have he := ConcreteCategory.congr_hom
      (NatTrans.congr_app (arSquareFamilyApex_frame E F hframe) (Opposite.op ⦋0⦌)) v
    have hz := hF v rfl
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hz
    exact he.symm ▸ hz
  · intro i j hij
    have e := arCofiberCanonicalSquareComparisonIso E F hframe hleft hbottom (arObj i j hij)
    exact IsPushoutSquare.of_functorIso (hpushout (arObj i j hij)) e.symm

end SerrePositivity.KST.SConstruction
