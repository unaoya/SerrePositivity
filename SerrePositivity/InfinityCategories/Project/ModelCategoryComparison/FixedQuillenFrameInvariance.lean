module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeBoundaryTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
概要：一般モデル圏の frame の弱比較は、固定 Quillen 類だけで実際の Hom のホモトピー同値。
方針：相対 latching の境界持ち上げと Reedy Brown 分解を、trivial Kan 制限と二対三則へ移す。
規約：SSet のモデル構造の存在は仮定しない。使われ方：導来 Hom 随伴の frame 選択の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits HomotopicalAlgebra SSet
open scoped SSet.modelCategoryQuillen
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [ModelCategory C]

/-- Reedy trivial cofibration の Hom は、固定 Quillen 類の trivial Kan fibration である。 -/
lemma frameHomMap_trivialKanFibration {A B : SimplexCategory ⥤ C} (a : A ⟶ B)
    (ha : reedyLeft simplex (trivialCofibrations C) a) (Y : C) [IsFibrant Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app Y) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  have : HasLiftingProperty (relativeLatchingMap simplex (SimplexCategory.mk n) a)
      (terminal.from Y) :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (ha _) (mem_fibrations _)
  exact boundary_source_lifting a n

/-- Reedy cofibrant な実際の frame の弱比較は、元の Hom 写像そのものでホモトピー同値。 -/
lemma frameHomMap_homotopyEquivalence {A B : SimplexCategory ⥤ C} (a : A ⟶ B)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (hcA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hcB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (ha : ∀ n, weakEquivalences C (a.app n)) (Y : C) [IsFibrant Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app Y) := by
  let := simplexModelCategory C
  have : IsCofibrant A := ⟨hA⟩
  have : IsCofibrant B := ⟨hB⟩
  have : WeakEquivalence a := ⟨ha⟩
  let h := Classical.choice (inferInstance : Nonempty (CofibrantBrownFactorization a))
  have : Cofibration h.i := (cofibration_iff _).mpr h.hi
  have hi : reedyLeft simplex (trivialCofibrations C) h.i :=
    (reedyLeft_trivialCofibrations_iff simplex h.i).mpr ⟨h.hi, mem_weakEquivalences h.i⟩
  have hs : reedyLeft simplex (trivialCofibrations C) h.s :=
    (reedyLeft_trivialCofibrations_iff simplex h.s).mpr
      ⟨mem_cofibrations h.s, mem_weakEquivalences h.s⟩
  let F := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (evaluation C SSet.{u}).obj Y
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (F.map (Quiver.Hom.op h.i)) :=
    frameHomMap_trivialKanFibration h.i hi Y
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (F.map (Quiver.Hom.op h.s)) :=
    frameHomMap_trivialKanFibration h.s hs Y
  have : KanComplex (F.obj (Opposite.op A)) := cosimplicialHom_kanComplex A hA hcA Y
  have : KanComplex (F.obj (Opposite.op B)) := cosimplicialHom_kanComplex B hB hcB Y
  have : Fibration (F.map (Quiver.Hom.op h.i)) := by
    apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
    intro X Z i hi
    have : Mono i := SSet.modelCategoryQuillen.J_le_monomorphisms i hi
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := F.map (Quiver.Hom.op h.i)) i inferInstance
  have : KanComplex (F.obj (Opposite.op h.Z)) :=
    isFibrant_of_fibration (F.map (Quiver.Hom.op h.i))
  have hi' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (F.map (Quiver.Hom.op h.i))).isSimplicialHomotopyEquivalence
  have hs' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (F.map (Quiver.Hom.op h.s))).isSimplicialHomotopyEquivalence
  have he : F.map (Quiver.Hom.op h.p) ≫ F.map (Quiver.Hom.op h.s) = 𝟙 _ := by
    rw [← F.map_comp]
    change F.map (Quiver.Hom.op (h.s ≫ h.p)) = _
    rw [h.s_p]
    exact F.map_id _
  have hp := hs'.cancel_right (he.symm ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _)
  have hf : F.map (Quiver.Hom.op h.p) ≫ F.map (Quiver.Hom.op h.i) =
      F.map (Quiver.Hom.op a) := by
    rw [← F.map_comp]
    exact congrArg F.map (congrArg Quiver.Hom.op h.fac)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (F.map (Quiver.Hom.op a))
  rw [← hf]
  exact hp.comp hi'

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
