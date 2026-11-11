module
public import SerrePositivity.KST.Fibration.Relative.ClosedKernelContraction
public import SerrePositivity.KST.Fibration.WeakStringZeroRow
public import SerrePositivity.KST.Comparison.HomotopyPullbackThreeInputs

/-!
概要：有限旗の明示条件から、元の定数旗射の実現四角形を導く。
方針：Segal 実現を零段に適用し、元の定数旗と零段の評価を照合する。
規約：条件は Prop 値の引数。使われ方：商比較前の fiber 同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：P 全旗の元の定数包含。
方針：零圏への全旗模型の定数包含を消費。
規約：同じ入力 F(P)。使われ方：実現四角形の上辺。 -/
def closedKernelConstant {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    coreSRealizationFunctor.obj (closedStableModel P) ⟶ closedKernelRealization P :=
  weakStringRealizationConstantDiagonal coreSRealizationFunctor (closedKernelZeroMap P)

/-- 概要：P 全旗から W 全旗への元の対角包含。
方針：同じ自然変換の対角。規約：実 SSet 射。
使われ方：可縮な底からの射。 -/
def closedKernelRealizationPost {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedKernelRealization P ⟶ closedRelativeRealization P :=
  simplicialDiagonalFunctor.map (closedStableFlagPost P)

/-- 概要：定数旗の包含は元の完全包含と厳密に可換。
方針：全関手圏の定数関手の後合成を評価する。
規約：局所化前の等式。使われ方：fiber 射影の元の左辺。 -/
lemma closedKernel_constant_post {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) :
    weakStringConstantExact (closedKernelZeroMap P) n ≫ closedKernelFlagPost P n =
      closedStableInclusion P ≫ closedFlagConstant P n := by
  apply Subtype.ext
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    ((ihom (stdSimplex.obj n)).obj B.carrier) (closedFlagStablePredicate P n).predicate).ι).1
  have h₀ := closedKernelFlagPost_inclusion P n
  have h₁ := weakStringConstantExact_ι (closedKernelZeroMap P) n
  have h₂ := closedFlagConstant_ι P n
  have he : curry (snd (stdSimplex.obj n) (closedStableModel P).carrier) ≫
      (ihom (stdSimplex.obj n)).map (closedStableInclusion P).val =
      (closedStableInclusion P).val ≫ curry (snd (stdSimplex.obj n) B.carrier) := by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, uncurry_natural_left, uncurry_curry,
      whiskerLeft_snd]
  calc
    _ = (weakStringConstantExact (closedKernelZeroMap P) n).val ≫
        ((closedKernelFlagPost P n).val ≫
          (closedStableInclusion (closedFlagStablePredicate P n)).val) := Category.assoc _ _ _
    _ = _ := congrArg ((weakStringConstantExact (closedKernelZeroMap P) n).val ≫ ·) h₀
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ (ihom (stdSimplex.obj n)).map (closedStableInclusion P).val) h₁
    _ = _ := he
    _ = _ := congrArg ((closedStableInclusion P).val ≫ ·) h₂.symm
    _ = _ := (Category.assoc _ _ _).symm

/-- 概要：元の定数旗と包含の対角可換四角形。
方針：全段の可換条件を同じ対角で評価。
規約：四辺を全て指定。使われ方：homotopy pullback と実 fiber。 -/
theorem closedRelativeSquare {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    CommSq (closedKernelConstant P)
      (coreSRealizationFunctor.map (closedStableInclusion P))
      (closedKernelRealizationPost P) (closedRelativeConstant P) := by
  constructor
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  have h := congrArg coreSRealizationFunctor.map (closedKernel_constant_post P n.unop)
  rw [coreSRealizationFunctor.map_comp, coreSRealizationFunctor.map_comp] at h
  exact congrArg (fun f => f.app n x) h

/-- 概要：底の厳密同型を安定模型の厳密同型へ持ち上げる。
方針：同型の完全性を消費。規約：底の二射を変更しない。
使われ方：零長旗の評価同型。 -/
def stableIsoOfCarrierIso {X Y : StableModel.{u}} (e : X.carrier ≅ Y.carrier) : X ≅ Y := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence
  have k := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).symm.isQCatEquivalence
  exact {
    hom := ⟨e.hom, h.preservesZero, h.preservesCofiber⟩
    inv := ⟨e.inv, k.preservesZero, k.preservesCofiber⟩
    hom_inv_id := Subtype.ext e.hom_inv_id
    inv_hom_id := Subtype.ext e.inv_hom_id }

/-- 概要：零長 W 旗は元の B と厳密に同型。
方針：一点関手圏の同型を全頂点条件へ制限。
規約：順射は元の頂点評価。使われ方：Segal 零行の同定。 -/
def closedFlagZeroIso {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedFlagModel P ⦋0⦌ ≅ B :=
  stableIsoOfCarrierIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (SConstruction.pointFunctorEvaluationIso B.carrier)
      (closedFlagStablePredicate P ⦋0⦌).predicate (ClosedStablePredicate.top B).predicate
      (fun v => ⟨fun _ => trivial,
        fun _ => coreFlag_mem P ⦋0⦌ v (weakStringPredicate_zero (𝟙 (flagAmbient B)) v)⟩) ≪≫
      stableModelForget.mapIso (topClosedStableIso B))

/-- 概要：零長同型は元の頂点評価。
方針：全部分圏の包含の計算。規約：厳密等号。
使われ方：元の射への同定。 -/
lemma closedFlagZeroIso_hom {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    (closedFlagZeroIso P).hom = closedFlagVertex P ⦋0⦌ 0 := Subtype.ext rfl

/-- 概要：零長同型の逆は元の定数旗。
方針：周囲の一点関手への包含の単射性。
規約：指定した元の射。使われ方：実現の零行評価。 -/
lemma closedFlagZeroIso_inv {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    (closedFlagZeroIso P).inv = closedFlagConstant P ⦋0⦌ := by
  apply Subtype.ext
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    ((ihom (Δ[0] : SSet.{u})).obj B.carrier)
    (closedFlagStablePredicate P ⦋0⦌).predicate).ι).1
  have h : (closedFlagZeroIso P).inv.val ≫
      (closedStableInclusion (closedFlagStablePredicate P ⦋0⦌)).val =
      (SConstruction.pointFunctorEvaluationIso B.carrier).inv := rfl
  exact h.trans (closedFlagConstant_ι P ⦋0⦌).symm

/-- 概要：零行と標準零単体を元の F(B) へ戻す同型。
方針：零長同型に F を適用。規約：元の頂点評価。
使われ方：Segal 実現からの四角形の輸送。 -/
def closedFlagZeroRowIso {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    coreSRealizationFunctor.obj (closedFlagModel P ⦋0⦌) ⊗ (Δ[0] : SSet.{u}) ≅
      coreSRealizationFunctor.obj B :=
  simplexZeroTensorIso _ ≪≫ coreSRealizationFunctor.mapIso (closedFlagZeroIso P)

/-- 概要：零行評価は元の定数旗の対角包含。
方針：定数旗の自然性を一点の唯一の単体作用素で評価。
規約：厳密等号。使われ方：元の c_B の保持。 -/
lemma closedFlagZeroRow_evaluation {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    diagonalRowEvaluation (closedFlagRealizationDiagram P) 0 =
      (closedFlagZeroRowIso P).hom ≫ closedRelativeConstant P := by
  have he (n : SimplexCategory) : (closedFlagZeroIso P).hom ≫ closedFlagConstant P n =
      closedFlagMap P (SimplexCategory.const n ⦋0⦌ 0) := by
    apply (cancel_epi (closedFlagZeroIso P).inv).1
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, closedFlagZeroIso_inv]
    exact (closedFlagConstant_reindex P _).symm
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  change (coreSRealizationFunctor.map (closedFlagMap P (stdSimplex.objEquiv t))).app n x =
    (coreSRealizationFunctor.map (closedFlagConstant P n.unop)).app n
      ((coreSRealizationFunctor.map (closedFlagZeroIso P).hom).app n x)
  have ht : stdSimplex.objEquiv t = SimplexCategory.const n.unop ⦋0⦌ 0 := Subsingleton.elim _ _
  rw [ht]
  have h := congrArg coreSRealizationFunctor.map (he n.unop)
  rw [coreSRealizationFunctor.map_comp] at h
  exact (congrArg (fun f => f.app n x) h).symm

/-- 概要：零行の包含は元の P 包含の頂点評価と可換。
方針：全関手圏の後合成と評価の自然性。
規約：元の頂点を保持。使われ方：左辺の射影公式。 -/
lemma closedKernelFlagPost_zero {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedKernelFlagPost P ⦋0⦌ ≫ (closedFlagZeroIso P).hom =
      (weakStringZeroAmbientIso (closedKernelZeroMap P)).hom ≫ closedStableInclusion P := by
  apply Subtype.ext
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：有限旗の明示仮定から元の定数旗四角形は homotopy pullback。
方針：Segal 実現と四頂点の同型不変性。
規約：仮定は Prop 値の引数のみ。使われ方：S1 の条件付き fiber 本体。 -/
theorem closedRelativeSquare_homotopyPullback {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (h : ClosedStableFlagPostPullback P) :
    IsHomotopyPullback (closedRelativeSquare P) := by
  let e := weakStringRealizationZeroRowIso coreSRealizationFunctor (closedKernelZeroMap P)
  apply (isHomotopyPullback_iff_of_localized_isIso
    (CommSq.mk (diagonalRowEvaluation_naturality (closedStableFlagPost P) 0).symm)
    (closedRelativeSquare P) e.hom (𝟙 _) (closedFlagZeroRowIso P).hom (𝟙 _)
    ?_ ?_ ?_ ?_ (by infer_instance) (by infer_instance)
    (by infer_instance) (by infer_instance)).mp
  · exact segalRealization_homotopyPullback (closedStableFlagPost P)
      (fun _ _ θ _ => h θ) 0
  · rw [Category.comp_id]
    exact weakStringRealizationZeroRow_evaluation _ _
  · change (_ ▷ (Δ[0] : SSet.{u})) ≫
      (fst _ _ ≫ coreSRealizationFunctor.map (closedFlagZeroIso P).hom) =
      (fst _ _ ≫ coreSRealizationFunctor.map
        (weakStringZeroAmbientIso (closedKernelZeroMap P)).hom) ≫ _
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]
    have he := congrArg coreSRealizationFunctor.map (closedKernelFlagPost_zero P)
    rw [coreSRealizationFunctor.map_comp, coreSRealizationFunctor.map_comp] at he
    exact (congrArg (fst (coreSRealizationFunctor.obj
      (weakStringModel (closedKernelZeroMap P) ⦋0⦌)) (Δ[0] : SSet.{u}) ≫ ·) he).trans
        (Category.assoc _ _ _).symm
  · simp only [Category.comp_id, Category.id_comp]
    rfl
  · rw [Category.comp_id]
    exact closedFlagZeroRow_evaluation P

end SerrePositivity.KST.Fibration.Relative
