module
public import SerrePositivity.KST.SConstruction.McCarthySpan
public import SerrePositivity.KST.SConstruction.CofiberGappedPushout

/-! # McCarthy の span の gapped な三頂点
概要：span の三頂点は λ・μ・元の E であり、全て gapped。
方針：内部 Hom の頂点を実際の Ar 図式に戻して両枝の端点を使う。
規約：中間の図式に gapped 性を追加仮定しない。使われ方：ρ の gapped 性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：span の族の転置の頂点は指定頂点での制限。
方針：内部 Hom の交換と curry の頂点公式。
規約：全形状に共通。使われ方：McCarthy の三つの入力図式の同定。 -/
lemma transposeFamily_vertex {A K D : SSet.{u}} (F : A ⊗ K ⟶ D) (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K D).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K A D (curry F)).app (Opposite.op ⦋0⦌) a) =
      lift (SSet.const a) (𝟙 K) ≫ F := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K D).symm
    ((curry ((β_ K A).hom ≫ uncurry (curry F))).app (Opposite.op ⦋0⦌) a) = _
  rw [uncurry_curry, curry_vertex_value]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K D).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K D)
    (lift (𝟙 K) (SSet.const a) ≫ (β_ K A).hom ≫ F)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- 概要：転置した span の族の区間からの頂点制限は prism の端点。
方針：頂点の制限公式で積の二つの座標を計算する。
規約：区間から span への射は任意。使われ方：λ・μ・ν の端点の回収。 -/
lemma transposeFamily_interval_vertex {A K D : SSet.{u}} (F : A ⊗ K ⟶ D)
    (i : (Δ[1] : SSet.{u}) ⟶ A) (j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K D).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K A D (curry F)).app (Opposite.op ⦋0⦌)
        (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint j K ≫ (i ▷ K) ≫ F := by
  rw [transposeFamily_vertex]
  rw [← Category.assoc]
  congr 1
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro k
  apply Prod.ext
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)) d.unop.len =
      i.app d (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm j) d.unop.len)
    exact (ConcreteCategory.congr_hom (i.naturality
      (SimplexCategory.const d.unop ⦋0⦌ 0).op) (stdSimplex.obj₀Equiv.symm j)).symm
  · rfl

/-- 概要：McCarthy の span の三つの入力図式は gapped。
方針：ホーンの全頂点を二枝の端点で表し、λ・μ・E を回収する。
規約：A と E の gapped 性だけを使う。使われ方：ρ の gapped 性の無条件な供給。 -/
lemma mcCarthySpan_isGapped_vertex {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (hA : IsGapped A)
    (α : Fin (n + 1) →o Fin (m + 1)) (τ : Fin (n + 1) →o Fin 2)
    (E : arNerve n ⟶ cofiberDiagrams C) (hE : IsGapped E)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) (a : (horn 2 0 : SSet.{u}) _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (horn 2 0) (cofiberDiagrams C)
        (curry (mcCarthySpan z A α τ E h))).app (Opposite.op ⦋0⦌) a)) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
  fin_cases i <;> dsimp only at *
  · have he : (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 3), ha⟩ :
        (horn 2 0 : SSet.{u}) _⦋0⦌) =
        horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
      apply Subtype.ext
      rfl
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (horn 2 0) (cofiberDiagrams C)
        (curry (mcCarthySpan z A α τ E h))).app (Opposite.op ⦋0⦌)
          (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 3), ha⟩)))
    rw [he, transposeFamily_interval_vertex, mcCarthySpan_upper,
      mcCarthyLambdaMu_zero]
    exact mcCarthyLambda_isGapped z A hA α
  · have he : (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 3), ha⟩ :
        (horn 2 0 : SSet.{u}) _⦋0⦌) =
        horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      apply Subtype.ext
      rfl
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (horn 2 0) (cofiberDiagrams C)
        (curry (mcCarthySpan z A α τ E h))).app (Opposite.op ⦋0⦌)
          (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 3), ha⟩)))
    rw [he, transposeFamily_interval_vertex, mcCarthySpan_upper,
      mcCarthyLambdaMu_one]
    exact mcCarthyMu_isGapped z A hA α τ
  · have he : (⟨stdSimplex.obj₀Equiv.symm (2 : Fin 3), ha⟩ :
        (horn 2 0 : SSet.{u}) _⦋0⦌) =
        horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      apply Subtype.ext
      rfl
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (horn 2 0) (cofiberDiagrams C)
        (curry (mcCarthySpan z A α τ E h))).app (Opposite.op ⦋0⦌)
          (⟨stdSimplex.obj₀Equiv.symm (2 : Fin 3), ha⟩)))
    rw [he, transposeFamily_interval_vertex, mcCarthySpan_left,
      mcCarthyLambdaNu_one]
    exact hE

end SerrePositivity.KST.SConstruction
