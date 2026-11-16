module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowBoundaryComponents

/-!
概要：元の係数の持ち上げを、指定された退化境界を保つ行全体の射へ束ねる。
方針：元の各余積成分の射を降下させ、包含による検出で両脚と退化境界の一致を示す。
規約：元の行の射と指定境界を厳密に保持する。
使われ方：IS-W2 R03f.2の元の相対latching射のleft anodyne性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
  (hη : ∀ i, leftAnodyneExtensions (η.app i)) (n : ℕ)
  {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (a : simplicialReplacementRow F n ⟶ E) (b : simplicialReplacementRow G n ⟶ B)
  (d : (simplicialReplacementDegenerateRow G n : SSet.{u}) ⟶ E)
  (sq : CommSq a (simplicialReplacementRowMap η n) p b)
  (hd : d ≫ p = (simplicialReplacementDegenerateRow G n).ι ≫ b)
  (ha : simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫ d =
    (simplicialReplacementDegenerateRow F n).ι ≫ a)

include hη sq hd ha

/-- 元の退化境界を固定した係数ごとの持ち上げは、同じ行全体の持ち上げとなる。 -/
theorem simplicialReplacementRowBoundary_lift :
    ∃ l : simplicialReplacementRow G n ⟶ E,
      simplicialReplacementRowMap η n ≫ l = a ∧ l ≫ p = b ∧
      (simplicialReplacementDegenerateRow G n).ι ≫ l = d := by
  classical
  let h := fun σ => simplicialReplacementRowBoundary_component η hη n p a b d sq hd ha σ
  let v := fun σ => (h σ).choose
  let c : Cofan (fun σ : ComposableArrows I n => G.obj (σ.obj 0)) := Cofan.mk E v
  let l := simplicialReplacementRowDesc G n c
  have hl (σ) : simplicialReplacementRowInclusion G n σ ≫ l = v σ :=
    simplicialReplacementRowDesc_inclusion n c σ
  have hs (σ) : η.app (σ.obj 0) ≫ v σ = simplicialReplacementRowInclusion F n σ ≫ a :=
    (h σ).choose_spec.1
  have hp (σ) : v σ ≫ p = simplicialReplacementRowInclusion G n σ ≫ b :=
    (h σ).choose_spec.2.1
  have hv (σ) (hσ : σ ∈ (nerve I).degenerate n) :
      v σ = simplicialReplacementRowPartInclusion n G ((nerve I).degenerate n) σ hσ ≫ d :=
    (h σ).choose_spec.2.2 hσ
  refine ⟨l, ?_, ?_, ?_⟩
  · apply simplicialReplacementRow_hom_ext n
    intro σ
    rw [← Category.assoc, simplicialReplacementRowInclusion_map, Category.assoc, hl, hs]
  · apply simplicialReplacementRow_hom_ext n
    intro σ
    rw [← Category.assoc, hl, hp]
  · apply simplicialReplacementRowPart_hom_ext n ((nerve I).degenerate n)
    intro σ hσ
    rw [← Category.assoc, simplicialReplacementRowPartInclusion_inclusion, hl]
    exact hv σ hσ

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
