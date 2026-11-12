module
public import SerrePositivity.KST.SConstruction.CofiberUnitPrism

/-! # 単位 prism の頂点での恒等性
概要：枠で指定された cofiber 族では、単位 prism の全ての縦辺が恒等辺になる。
方針：下側の角は第一行の枠内で計算し、上側の角は形状自体が定値になることを使う。
規約：正方形の普遍性はこの比較に要求しない。
使われ方：補完後の標準抽出との関手同型の構成。
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

/-- 概要：単位 prism の下側の角は第一行の枠の右辺を通る。
方針：時刻を変える二つの頂点で max(t,0)=t を計算する。
規約：x は正方形の横の端点。使われ方：枠の厳密な指定の適用。 -/
lemma arCofiberUnitPrism_lower {n : ℕ} (a : Ar.{u} n) (x : Fin 2) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const
      (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        arCofiberUnitPrism a =
      lift (SSet.const (ComposableArrows.mk₀
        (⟨arObj 0 (intervalStep a.down.val.1 a.down.val.2 a.down.property x) (Fin.zero_le _),
          Or.inl rfl⟩ : FrameAr n))) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫
        (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  · refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    rfl
  · apply Prod.ext
    · rfl
    · apply ULift.ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext r
      fin_cases r <;> rfl

/-- 概要：単位 prism の上側の角は時刻に依存しない。
方針：時刻を変える二つの頂点で max(t,1)=1 を計算する。
規約：パラメーターは (i,k) に固定。使われ方：上側の角の恒等辺。 -/
lemma arCofiberUnitPrism_upper {n : ℕ} (a : Ar.{u} n) (x : Fin 2) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const
      (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        arCofiberUnitPrism a =
      SSet.const (ComposableArrows.mk₀
        (arObj a.down.val.1 (intervalStep a.down.val.1 a.down.val.2 a.down.property x)
          (le_intervalStep _ _ _ _)),
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  · refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    rfl
  · apply Prod.ext
    · rfl
    · apply ULift.ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext r
      fin_cases r <;> rfl

/-- 概要：第一行の cofiber 正方形の右辺は元の第一行の頂点で定値。
方針：枠内の順序写像を二つの端点で計算する。
規約：全ての第一行の区間を含む。使われ方：prism の下側の角の恒等性。 -/
lemma frameCofiberSquareMap_row_right {n : ℕ} (k : Fin (n + 1)) :
    lift (SSet.const (ComposableArrows.mk₀
      (⟨arObj 0 k (Fin.zero_le _), Or.inl rfl⟩ : FrameAr.{u} n))) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫
        frameCofiberSquareMap n =
      SSet.const (ComposableArrows.mk₀ (⟨arObj 0 k (Fin.zero_le _), Or.inl rfl⟩ : FrameAr n)) := by
  apply SSet.yonedaEquiv.injective
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  fin_cases r <;> rfl

/-- 概要：枠を保つ四角形の族に単位 prism を適用すると、各縦辺は定値。
方針：各角を上下に分け、下側では枠の指定、上側では定値形状を使う。
規約：E が押し出しの族であることは不要。使われ方：点ごとの同値ホモトピー。 -/
lemma arCofiberUnitPrism_vertex_constant {n : ℕ} {C : SSet.{u}}
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (a : Ar.{u} n) (v : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    ∃ z : C _⦋0⦌, lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const v) ≫
      (arCofiberUnitPrism a ≫ E) = SSet.const z := by
  obtain ⟨x, hx⟩ := stdSimplex.obj₀Equiv.symm.surjective v.1
  obtain ⟨y, hy⟩ := stdSimplex.obj₀Equiv.symm.surjective v.2
  have hv : v = (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) :=
    Prod.ext hx.symm hy.symm
  rw [hv]
  by_cases hy0 : y = 0
  · subst y
    simp only [← Category.assoc]
    erw [arCofiberUnitPrism_lower, Category.assoc, h,
      ← Category.assoc, frameCofiberSquareMap_row_right, SSet.const_comp]
    exact ⟨_, rfl⟩
  · have hy1 : y = 1 := by
      fin_cases y <;> simp_all
    subst y
    simp only [← Category.assoc]
    erw [arCofiberUnitPrism_upper, SSet.const_comp]
    exact ⟨_, rfl⟩

/-- 概要：枠を保つ族の単位正方形と右上角の図式の標準抽出は関手同型。
方針：単位 prism の各縦辺が恒等なので点ごとの同値ホモトピーから同型を作る。
規約：C は quasicategory。E の正方形が押し出しであることは不要。
使われ方：標準抽出の普遍性を単位正方形の普遍性へ還元する。 -/
def arCofiberUnitComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (E : arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C) (F : frameNerve n ⟶ C)
    (h : (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ E = frameCofiberSquareMap n ≫ F)
    (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (arCofiberUnitSquare a ≫ E)
      (arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property ≫
        lift (𝟙 (arNerve n)) (SSet.const
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ E) := by
  have hv (v : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((arCofiberUnitPrism a ≫ E).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1))) := by
    obtain ⟨z, hz⟩ := arCofiberUnitPrism_vertex_constant E F h a v
    have he := congrArg SSet.yonedaEquiv hz
    change (arCofiberUnitPrism a ≫ E).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 1 at he
    rw [he]
    have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const z
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hi
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hi
    exact hi
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfEquivalenceHomotopy (arCofiberUnitPrism a ≫ E) hv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberUnitPrism a ≫ E)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberUnitPrism a) ≫ E) at e
  simp only [← Category.assoc, arCofiberUnitPrism_zero, arCofiberUnitPrism_one] at e
  exact e

/-- 概要：正方形の族を Ar[n] と正方形の積上の図式に戻す。
方針：uncurry の後で二因子を交換する。
規約：押し出し条件をまだ課さない。使われ方：cofiber 補完への単位比較の適用。 -/
def arSquareFamilyDiagram {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) :
    arNerve n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C :=
  (β_ (arNerve n) (Δ[1] ⊗ Δ[1] : SSet.{u})).hom ≫ uncurry H

/-- 概要：積上に戻した正方形の族の一つの角は元の族の評価。
方針：uncurry と評価の各次数の定義を計算する。
規約：全ての角の頂点を許す。使われ方：右上角の図式の同定。 -/
lemma arSquareFamilyDiagram_evaluate {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)
    (v : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    lift (𝟙 (arNerve n)) (SSet.const v) ≫ arSquareFamilyDiagram H =
      H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：族の枠への制限が標準抽出なら、積上の図式も枠の形状と厳密に一致。
方針：uncurry の自然性と枠の curry の逆律を使う。
規約：全単体の厳密等号。使われ方：単位比較の枠条件の検証。 -/
lemma arSquareFamilyDiagram_frame {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)
    (F : frameNerve n ⟶ C) (h : frameInclusion n ≫ H = frameCofiberFamily F) :
    (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ arSquareFamilyDiagram H =
      frameCofiberSquareMap n ≫ F := by
  dsimp only [arSquareFamilyDiagram]
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left,
    Category.assoc, ← uncurry_natural_left, h, frameCofiberFamily, uncurry_curry]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：枠を標準形に保つ正方形の族にも単位比較を適用できる。
方針：族を積上の図式に戻し、枠の厳密な一致を確認して既存の比較同型を使う。
規約：C は quasicategory。使われ方：cofiber 補完の右上角の標準正方形への接続。 -/
def arSquareFamilyUnitComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)
    (F : frameNerve n ⟶ C) (h : frameInclusion n ≫ H = frameCofiberFamily F)
    (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (arCofiberUnitSquare a ≫ arSquareFamilyDiagram H)
      (arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property ≫
        H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := (Δ[1] ⊗ Δ[1] : SSet.{u})) (Y := C)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  have e := arCofiberUnitComparisonIso (arSquareFamilyDiagram H) F
    (arSquareFamilyDiagram_frame H F h) a
  have he := congrArg (fun q : arNerve n ⟶ C =>
    arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property ≫ q)
      (arSquareFamilyDiagram_evaluate H
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  exact Eq.mp (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (arCofiberUnitSquare a ≫ arSquareFamilyDiagram H) q) he) e

/-- 概要：枠を保つ実際の cofiber 補完では、単位の中間正方形と右上角の標準抽出が同型。
方針：cofiber 条件を忘れた族の枠の等号を確認し、単位比較の同型を適用する。
規約：安定性は補完の存在に使い、この比較そのものには不要。
使われ方：第一行復元で残る中間正方形の普遍性の切り分け。 -/
def cofiberFamilyUnitComparisonIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (H : arNerve n ⟶ cofiberDiagrams C) (F : frameNerve n ⟶ C)
    (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
    (h : frameInclusion n ≫ H = zeroFrameCofiberFamily F hF) (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (arCofiberUnitSquare a ≫ arSquareFamilyDiagram
        (H ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι))
      (arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property ≫
        H ≫ cofiberApex C) := by
  have hraw : frameInclusion n ≫
      (H ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) = frameCofiberFamily F := by
    rw [← Category.assoc, h, zeroFrameCofiberFamily_ι]
  have e := arSquareFamilyUnitComparisonIso
    (H ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) F hraw a
  exact e

end SerrePositivity.KST.SConstruction
