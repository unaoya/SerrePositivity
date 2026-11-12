module
public import SerrePositivity.KST.SConstruction.PointwisePushoutApex
public import SerrePositivity.KST.SConstruction.CofiberEvaluations
public import SerrePositivity.KST.SConstruction.ColimitComparison
public import SerrePositivity.CategoryTheory.Monoidal.Braided

/-! # 元の標的で選んだ図式の押し出しの普遍性
概要：C 内の同じ押し出し選択が二重関手圏でも普遍四角形を与える。
方針：座標を交換し、二回の点ごとの判定を使う。
規約：選択を図式圏の選択に置換しない。使われ方：raw ρ の cofiber・gapped 性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：C 内で選んだ押し出しを二重関手圏の正方形として表す。
方針：span と図式の座標を戻してパラメーターを curry する。
規約：C 内の同じ正規化した選択。使われ方：raw ρ を押し出し頂点として扱う。 -/
def pointwiseDiagramPushout {B K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ (ihom B).obj C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom K).obj ((ihom B).obj C) :=
  chosenDiagramPushout (exchangeDiagramFamily F) ≫ (ihomCurryIso B K C).hom

/-- 概要：内部 currying 後の二点評価は積の頂点での評価。
方針：内部 Hom の成分と恒等射での自然性を計算する。
規約：単体集合は任意。使われ方：二重関手圏の点ごとの判定。 -/
lemma ihomCurry_evaluate_pair (B K C : SSet.{u}) (k : K _⦋0⦌) (b : B _⦋0⦌) :
    (ihomCurryIso B K C).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (b, k) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  change v.app n ((𝟙 n) ≫ (𝟙 n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b n.unop.len, K.map (𝟙 n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k n.unop.len)) =
    v.app n (𝟙 n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (b, k) n.unop.len)
  simp only [Category.id_comp, CategoryTheory.Functor.map_id_apply]
  rfl

/-- 概要：二重関手圏での四角形の二点評価は C 内の選んだ四角形の評価。
方針：curry と座標交換を各単体で計算する。
規約：任意の二頂点での厳密等号。使われ方：点ごとの普遍性の判定。 -/
lemma pointwiseDiagramPushout_evaluate {B K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ (ihom B).obj C)
    (k : K _⦋0⦌) (b : B _⦋0⦌) :
    pointwiseDiagramPushout F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b =
      chosenDiagramPushout (exchangeDiagramFamily F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (b, k) := by
  unfold pointwiseDiagramPushout
  simp only [Category.assoc, ihomCurry_evaluate_pair]

/-- 概要：C 内の点ごとの選択は二重関手圏でも押し出し。
方針：二回の点ごとの判定で選んだ C 内の普遍四角形に帰着する。
規約：追加の普遍性仮定は不要。使われ方：同じ span の押し出しとの比較。 -/
lemma pointwiseDiagramPushout_isPushout {B K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ (ihom B).obj C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (pointwiseDiagramPushout F) := by
  refine (functor_pushout_iff_pointwise (A := K) (C := (ihom B).obj C)
    (pointwiseDiagramPushout F)).2 ?_
  intro k
  refine (functor_pushout_iff_pointwise (A := B) (C := C)
    (pointwiseDiagramPushout F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)).2 ?_
  intro b
  rw [Category.assoc, pointwiseDiagramPushout_evaluate]
  exact (functor_pushout_iff_pointwise (chosenDiagramPushout (exchangeDiagramFamily F))).1
    (chosenDiagramPushout_isPushout _) (b, k)

/-- 概要：二重関手圏の四角形は元の span を保持する。
方針：選んだ四角形の span の式と内部 currying の計算。
規約：全単体の等号。使われ方：他の押し出しとの比較。 -/
lemma pointwiseDiagramPushout_span {B K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ (ihom B).obj C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (pointwiseDiagramPushout F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K (horn 2 0) ((ihom B).obj C) (curry F) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ chosenDiagramPushout (exchangeDiagramFamily F) ≫
    (ihomCurryIso B K C).hom = _
  rw [← Category.assoc, chosenDiagramPushout_span]
  apply uncurry_injective
  apply uncurry_injective
  change uncurry (uncurry (_ ≫ ihomCurry B K C)) = _
  rw [SerrePositivity.InternalHomExchange.doubleUncurry_comp_ihomCurry]
  change (α_ B K (horn 2 0 : SSet.{u})).inv ≫
    uncurry (curry ((β_ (B ⊗ K) (horn 2 0 : SSet.{u})).hom ≫
      uncurry (curry (exchangeFirstTwo (horn 2 0 : SSet.{u}) B K ≫ uncurry F)))) =
    uncurry (uncurry (curry ((β_ K (horn 2 0 : SSet.{u})).hom ≫ uncurry (curry F))))
  simp only [uncurry_curry, uncurry_natural_left, ← Category.assoc]
  congr 1

/-- 概要：二重関手圏の押し出し頂点は元の点ごとの apex。
方針：内部 Hom の零単体を全成分で計算する。
規約：同型でなく厳密等号。使われ方：raw ρ への条件の輸送。 -/
lemma pointwiseDiagramPushout_apex {B K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ (ihom B).obj C) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (pointwiseDiagramPushout F) 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (pointwiseDiagramPushoutApex F) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro k
  apply CategoryTheory.Functor.functorHom_ext
  intro t β
  apply ConcreteCategory.hom_ext
  intro b
  rfl

/-- 概要：選んだ図式圏の押し出しの頂点は点ごとの apex の族。
方針：内部 Hom の頂点の成分を計算する。
規約：選択した同じ四角形の等号。使われ方：比較同型の apex。 -/
lemma chosenDiagramPushout_apex {K D : SSet.{u}} [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj D) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (chosenDiagramPushout d) 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (pointwisePushoutApex d) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro k
  rfl

/-- 概要：完全関手による押し出しと C 内の点ごとの押し出しの apex は関手として同型。
方針：二重関手圏の同じ span の普遍四角形を比較して apex で評価する。
規約：厳密な apex の保存は要求しない。使われ方：raw ρ の条件の輸送。 -/
def pointwiseDiagramPushoutApex_postcompIso {B K C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ D) (f : D ⟶ (ihom B).obj C)
    (hf : PreservesSConstructionData f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pointwisePushoutApex (curry F) ≫ f)
      (pointwiseDiagramPushoutApex (F ≫ f)) := by
  let P := chosenDiagramPushout (curry F)
  have hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (P ≫ (ihom K).map f) := by
    refine (functor_pushout_iff_pointwise (A := K) (C := (ihom B).obj C)
      (P ≫ (ihom K).map f)).2 ?_
    intro k
    rw [Category.assoc, ihom_postcomp_evaluate, ← Category.assoc]
    exact hf.2 _ ((functor_pushout_iff_pointwise P).1 (chosenDiagramPushout_isPushout _) k)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (P ≫ (ihom K).map f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (pointwiseDiagramPushout (F ≫ f)) := by
    rw [pointwiseDiagramPushout_span]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ chosenDiagramPushout (curry F)) ≫ (ihom K).map f = _
    rw [chosenDiagramPushout_span]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro v
    apply CategoryTheory.Functor.functorHom_ext
    intro e α
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  let e := pushoutSquareIsoOfSpanIso (P ≫ (ihom K).map f)
    (pointwiseDiagramPushout (F ≫ f)) hP (pointwiseDiagramPushout_isPushout _)
      (by rw [hs])
  have ea := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at ea
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (((ihom K).map f).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (chosenDiagramPushout (curry F)) 1 1))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (pointwiseDiagramPushout (F ≫ f)) 1 1) at ea
  rw [chosenDiagramPushout_apex, pointwiseDiagramPushout_apex] at ea
  exact ea

end SerrePositivity.KST.SConstruction
