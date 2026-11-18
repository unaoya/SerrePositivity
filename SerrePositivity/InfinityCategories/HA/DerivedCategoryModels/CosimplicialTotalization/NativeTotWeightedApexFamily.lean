module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellFamily
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellIdentification
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexEvaluationAtParameter

/-!
概要：元のweighted Totセルの全図式射・全高次単体の評価族。
方針：既存StrictSimplexCategoryと全評価を、元の指定セルと厳密写像へ適用。
規約：IS-W2 D01の既存構成の組み立て・表示則。同じ元の全joinセルへ戻す。
使われ方：HA 1.2.4、全錐族の局所セルの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の閉零複体を、同じHA零セルとして読む通常関手。 -/
def nativeTotClosedVertexFunctor :
    ClosedCategory A (Complex A) ⥤ StrictSimplexCategory A (Complex A) 0 where
  obj M := ⟨closedNerveSimplex ((Functor.const (Fin 1)).obj M)⟩
  map f := strictClosedSimplexMap ((Functor.const (Fin 1)).map f)
  map_id M := by
    apply StrictSimplexMap.ext
    intro i
    exact closedHom_id M
  map_comp f g := by
    apply StrictSimplexMap.ext
    intro i
    apply Subtype.ext
    exact closedHom_comp f g

/-- 同じweightedセルの初点は、元のTotの同じ零セル。 -/
theorem nativeTotWeightedCellFunctor_apex {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFunctor A σ ⋙ strictSimplexPullbackFunctor A (Complex A)
        (SimplexCategory.const ⦋0⦌ ⦋n+1⦌ 0).toOrderHom =
      productTotalFunctor A ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A ⋙ nativeTotClosedVertexFunctor A := by
  have hs (X : CosimplicialObject (Complex A)) :
      ((nativeTotWeightedCellFunctor A σ).obj X).val.pullback
          (SimplexCategory.const ⦋0⦌ ⦋n+1⦌ 0).toOrderHom =
        (((productTotalFunctor A ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A ⋙ nativeTotClosedVertexFunctor A).obj X).val) := by
    apply Simplex.vertexEquiv.injective
    rfl
  apply CategoryTheory.Functor.hext
  · intro X
    exact congrArg StrictSimplexCategory.mk (hs X)
  · intro X Y f
    apply StrictSimplexMap.hext
    · exact congrArg Simplex.toSimplexData (hs X)
    · exact congrArg Simplex.toSimplexData (hs Y)
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl

/-- 元のTot頂点関手の全パラメータ評価。 -/
def nativeTotApexFamily :
    nerve (CosimplicialObject (Complex A)) ⊗ (Δ[0] : SSet.{u+1}) ⟶
      dgNerve A (Complex A) :=
  strictSimplexFunctorEvaluation A (Complex A)
    (productTotalFunctor A ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A ⋙ nativeTotClosedVertexFunctor A)

/-- セル族を初点へ制限すると、同じ全Tot頂点族になる。 -/
theorem nativeTotWeightedCellFamily_apex {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInl (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1})) ≫
        nativeTotWeightedCellFamily A σ = nativeTotApexFamily A := by
  unfold nativeTotWeightedCellFamily
  rw [← Category.assoc, ← whiskerLeft_comp, joinStdSimplexIso_leftPoint_inl]
  have hp := strictSimplexFunctorEvaluation_pullback A (Complex A)
    (nativeTotWeightedCellFunctor A σ)
    (SimplexCategory.const ⦋0⦌ ⦋n+1⦌ 0).toOrderHom
  rw [nativeTotWeightedCellFunctor_apex] at hp
  exact hp.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
