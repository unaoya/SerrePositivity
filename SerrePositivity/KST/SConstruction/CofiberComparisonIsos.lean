module
public import SerrePositivity.KST.SConstruction.CofiberComparisonEdges

/-! # 固定 span に沿う比較の関手同型
概要：三つの prism の全縦辺が恒等となることから正方形間の関手同型を得る。
方針：枠、固定零射、固定入力射をそれぞれ対応する prism に適用する。
規約：標的の quasicategory 性以外に普遍性は仮定しない。
使われ方：BGT Lemma 7.3 の補完の cofiber 性を実際の図式へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：正方形の四頂点で縦辺が定値となるホモトピーの両端は関手同型。
方針：四頂点の表示から任意の頂点へ移し、点ごとの同値ホモトピーを適用する。
規約：C は quasicategory。使われ方：三つの比較 prism の共通処理。 -/
def functorIsoOfSquareConstantPrism {C : SSet.{u}} [Quasicategory C]
    (P : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C)
    (h : ∀ x y : Fin 2, ∃ z : C _⦋0⦌, squareVertexLine x y ≫ P = SSet.const z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ P) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfEquivalenceHomotopy
  intro v
  obtain ⟨x, hx⟩ := stdSimplex.obj₀Equiv.symm.surjective v.1
  obtain ⟨y, hy⟩ := stdSimplex.obj₀Equiv.symm.surjective v.2
  have hv : v = (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) :=
    Prod.ext hx.symm hy.symm
  obtain ⟨z, hz⟩ := h x y
  have he := congrArg SSet.yonedaEquiv hz
  change P.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) 1) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 1 at he
  rw [hv, he]
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const z
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hi
  exact hi

/-- 概要：内部横座標の比較では枠の指定により各縦辺が恒等。
方針：左側を対角の枠へ送り、右側の定値性と合わせる。
規約：E の正方形の普遍性は不要。使われ方：T→U の比較同型。 -/
lemma arCofiberHorizontalPrism_constant {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (a : Ar.{u} n) (x y : Fin 2) :
    ∃ z : C _⦋0⦌, squareVertexLine x y ≫ (arCofiberHorizontalPrism a ≫ E) = SSet.const z := by
  by_cases hx : x = 0
  · subst x
    simp only [← Category.assoc]
    erw [arCofiberHorizontalPrism_left, Category.assoc, h, ← Category.assoc,
      frameCofiberSquareMap_diagonal_horizontal, SSet.const_comp]
    exact ⟨_, rfl⟩
  · have hx1 : x = 1 := by fin_cases x <;> simp_all
    subst x
    simp only [← Category.assoc]
    erw [arCofiberHorizontalPrism_right, SSet.const_comp]
    exact ⟨_, rfl⟩

/-- 概要：第二端点の比較では固定零射により各縦辺が恒等。
方針：左側を固定 span の左辺へ送り、右側の定値性と合わせる。
規約：E の正方形の普遍性は不要。使われ方：T→H(a) の比較同型。 -/
lemma arCofiberTargetPrism_constant {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (a : Ar.{u} n) (x y : Fin 2) :
    ∃ z : C _⦋0⦌, squareVertexLine x y ≫ (arCofiberTargetPrism a ≫ E) = SSet.const z := by
  by_cases hx : x = 0
  · subst x
    simp only [← Category.assoc]
    erw [arCofiberTargetPrism_left, Category.assoc, h, ← Category.assoc,
      arCofiberZeroInputMap_fixedStart, SSet.const_comp]
    exact ⟨_, rfl⟩
  · have hx1 : x = 1 := by fin_cases x <;> simp_all
    subst x
    simp only [← Category.assoc]
    erw [arCofiberTargetPrism_right, SSet.const_comp]
    exact ⟨_, rfl⟩

/-- 概要：第一端点の比較では固定入力射により各縦辺が恒等。
方針：下側を固定 span の下辺の終点へ送り、上側の定値性と合わせる。
規約：E の正方形の普遍性は不要。使われ方：D→U の比較同型。 -/
lemma arCofiberSourcePrism_constant {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (a : Ar.{u} n) (x y : Fin 2) :
    ∃ z : C _⦋0⦌, squareVertexLine x y ≫ (arCofiberSourcePrism a ≫ E) = SSet.const z := by
  by_cases hy : y = 0
  · subst y
    simp only [← Category.assoc]
    erw [arCofiberSourcePrism_lower, Category.assoc, h, ← Category.assoc,
      arCofiberInputMap_fixedTarget, SSet.const_comp]
    exact ⟨_, rfl⟩
  · have hy1 : y = 1 := by fin_cases y <;> simp_all
    subst y
    simp only [← Category.assoc]
    erw [arCofiberSourcePrism_upper, SSet.const_comp]
    exact ⟨_, rfl⟩

/-- 概要：枠の指定から T と U の関手同型が得られる。
方針：内部横座標の prism の全縦辺の恒等性を使う。
規約：C は quasicategory。使われ方：単位の中間正方形との比較。 -/
def arCofiberHorizontalComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (arCofiberComparisonSquare a ≫ E) (arCofiberComparisonUnitSquare a ≫ E) := by
  have e := functorIsoOfSquareConstantPrism (arCofiberHorizontalPrism a ≫ E)
    (arCofiberHorizontalPrism_constant E F h a)
  simp only [← Category.assoc, arCofiberHorizontalPrism_zero, arCofiberHorizontalPrism_one] at e
  exact e

/-- 概要：固定零射から T と元の区間の四角形の関手同型が得られる。
方針：第二端点の prism の全縦辺の恒等性を使う。
規約：C は quasicategory。使われ方：選んだ cofiber 正方形との比較。 -/
def arCofiberTargetComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (arCofiberComparisonSquare a ≫ E)
      (lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E) := by
  have e := functorIsoOfSquareConstantPrism (arCofiberTargetPrism a ≫ E)
    (arCofiberTargetPrism_constant E F h a)
  simp only [← Category.assoc, arCofiberTargetPrism_zero, arCofiberTargetPrism_one] at e
  exact e

/-- 概要：固定入力射から D と U の関手同型が得られる。
方針：第一端点の prism の全縦辺の恒等性を使う。
規約：C は quasicategory。使われ方：単位正方形の普遍性の移送。 -/
def arCofiberSourceComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (arCofiberUnitSquare a ≫ E) (arCofiberComparisonUnitSquare a ≫ E) := by
  have e := functorIsoOfSquareConstantPrism (arCofiberSourcePrism a ≫ E)
    (arCofiberSourcePrism_constant E F h a)
  simp only [← Category.assoc, arCofiberSourcePrism_zero, arCofiberSourcePrism_one] at e
  exact e

/-- 概要：枠と span を保つ図式では単位の中間正方形と元の四角形が関手同型。
方針：D→U、T→U、T→H(a) の三つの比較を合成する。
規約：押し出し性は仮定しない。使われ方：cofiber 普遍性を中間正方形へ移す。 -/
def arCofiberSelectedSquareComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (hframe : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (hleft : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (hbottom : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (arCofiberUnitSquare a ≫ E)
      (lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E) :=
  arCofiberSourceComparisonIso E F hbottom a ≪≫
    (arCofiberHorizontalComparisonIso E F hframe a).symm ≪≫
      arCofiberTargetComparisonIso E F hleft a

/-- 概要：枠と span を保つ図式の標準抽出は選んだ元の四角形と関手同型。
方針：標準抽出と D の比較に、三つの prism による D と元の四角形の比較を合成する。
規約：C は quasicategory、押し出し性は不要。
使われ方：補完された実際の図式の標準正方形の普遍性。 -/
def arCofiberCanonicalSquareComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (hframe : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (hleft : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) ≫ E = arCofiberZeroInputMap n ≫ F)
    (hbottom : (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ≫ E = arCofiberInputMap n ≫ F)
    (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property ≫
        lift (𝟙 (arNerve n)) (SSet.const
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ E)
      (lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E) :=
  (arCofiberUnitComparisonIso E F hframe a).symm ≪≫
    arCofiberSelectedSquareComparisonIso E F hframe hleft hbottom a

end SerrePositivity.KST.SConstruction
