module
public import SerrePositivity.KST.SConstruction.McCarthySpan
public import SerrePositivity.KST.SConstruction.SpanIdentityBranches

/-! # McCarthy の span の subobject と quotient
概要：二つの角の span は、それぞれ左枝・上枝が厳密に恒等となる。
方針：各枝の射影の式から恒等 span の標準形状を認識する。
規約：元の C 内の選択に使える厳密な等号。使われ方：ρ の各角の回収。
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

/-- 概要：cofiber の入力の始点評価は正方形の (0,0) の評価。
方針：下辺の制限と評価の合成則。
規約：全単体での等号。使われ方：subobject の二つの表示の照合。 -/
lemma cofiberProjection_source (C : SSet.{u}) :
    cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [cofiberProjection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 概要：McCarthy の span の subobject は左枝が恒等な標準 span。
方針：上枝は Ar の motion、左枝は元の subobject で一定。
規約：時刻単体に条件を課さない。使われ方：ρ の subobject の厳密回収。 -/
lemma mcCarthySpan_source {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    mcCarthySpan z A α τ E h ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (identitySpanShape true ▷ arNerve n) ≫ mcCarthyArMotion α τ ≫ A := by
  apply spanFamily_constant_right _ (mcCarthyArMotion α τ ≫ A) (arNerveMap α ≫ A)
  · rw [← Category.assoc, ← Category.assoc, mcCarthySpan_upper,
      Category.assoc, mcCarthyLambdaMu_source]
  · rw [← Category.assoc, ← Category.assoc, mcCarthySpan_left,
      Category.assoc, mcCarthyLambdaNu_source, h]
  · rw [← Category.assoc, mcCarthyArMotion_zero]

/-- 概要：上枝の quotient は指定零対象で厳密に一定。
方針：標準恒等 cofiber の quotient の式を後合成する。
規約：全高次単体の等号。使われ方：quotient span の恒等な上枝の認識。 -/
lemma mcCarthyLambdaMu_quotient {n m : ℕ} {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) :
    mcCarthyLambdaMu z A α τ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1) =
      SSet.const z.vertex := by
  simp only [mcCarthyLambdaMu, Category.assoc]
  rw [zeroCofiberFunctor_quotient]
  simp

/-- 概要：McCarthy の span の quotient は上枝が恒等な標準 span。
方針：上枝の一定性と左枝の始点の quotient を照合する。
規約：元の左枝の全高次単体を保持する。使われ方：ρ の quotient の厳密回収。 -/
lemma mcCarthySpan_quotient {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    mcCarthySpan z A α τ E h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1) =
      (identitySpanShape false ▷ arNerve n) ≫ mcCarthyLambdaNu z E ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1) := by
  apply spanFamily_constant_left _
    (mcCarthyLambdaNu z E ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1))
    (SSet.const z.vertex)
  · rw [← Category.assoc, ← Category.assoc, mcCarthySpan_upper,
      Category.assoc, mcCarthyLambdaMu_quotient,
      SSet.comp_const]
  · rw [← Category.assoc, ← Category.assoc, mcCarthySpan_left, Category.assoc]
  · rw [← Category.assoc, ← Category.assoc, mcCarthyLambdaNu_zero]
    simp only [Category.assoc]
    rw [zeroCofiberFunctor_quotient]
    simp

end SerrePositivity.KST.SConstruction
