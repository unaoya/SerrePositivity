module
public import SerrePositivity.KST.SConstruction.ArCutFamily
public import SerrePositivity.KST.SConstruction.EquivalenceDiagramExactness
public import SerrePositivity.KST.SConstruction.FullSubcomplexGappedReflection

/-! # 切断 cofiber 族の各角の厳密な評価
概要：各角の評価を端点の min・恒等・定数・max による制限と同定する。
方針：任意の角の添字の等号を全単体で計算する。
規約：切断 cofiber 族自身の gapped 性まで示す。使われ方：S_n の内部の切断四角形。
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

/-- 切断四角形の任意の角の端点への作用は単調。 -/
def cutCornerOrder {n : ℕ} (k : Fin (n + 1)) (x y : Fin 2) :
    Fin (n + 1) →o Fin (n + 1) where
  toFun i := cutEndpoint k i x y
  monotone' _i _j h := cutEndpoint_mono k h le_rfl le_rfl

/-- 添字の切断四角形の各角は同じ端点写像による Ar の射。 -/
lemma arCutSquareMap_corner {n : ℕ} (k : Fin (n + 1)) (x y : Fin 2) :
    CartesianMonoidalCategory.lift (𝟙 (arNerve.{u} n))
        (SSet.const (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y)) ≫
      arCutSquareMap n k = arNerveMap (cutCornerOrder k x y) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun _ => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  rfl

/-- 切断の族の角の評価は元の図式の端点写像による制限に厳密に一致する。 -/
lemma arCutFamily_evaluation {n : ℕ} {C : SSet.{u}} (k : Fin (n + 1))
    (F : arNerve n ⟶ C) (x y : Fin 2) :
    arCutFamily k F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) =
      arNerveMap (cutCornerOrder k x y) ≫ F := by
  rw [arCutFamily, curry_evaluate_vertex]
  have h : CartesianMonoidalCategory.lift
      (SSet.const (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y)) (𝟙 (arNerve n)) ≫
      (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom =
    CartesianMonoidalCategory.lift (𝟙 (arNerve n))
      (SSet.const (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y)) := rfl
  rw [← Category.assoc, ← Category.assoc, h, arCutSquareMap_corner]

/-- 切断 cofiber 族の各角は元の図式の端点制限として厳密に回収される。 -/
lemma gappedCutCofiberFamily_evaluation {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (k : Fin (n + 1)) {F : arNerve n ⟶ C} (hF : IsGapped F) (x y : Fin 2) :
    gappedCutCofiberFamily k hF ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) =
      arNerveMap (cutCornerOrder k x y) ≫ F := by
  rw [← Category.assoc, gappedCutCofiberFamily_ι, arCutFamily_evaluation]

/-- 切断四角形の族は全 cofiber 図式の圏の中で実際に gapped。 -/
lemma gappedCutCofiberFamily_isGapped {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (k : Fin (n + 1)) {F : arNerve n ⟶ C} (hF : IsGapped F) :
    IsGapped (gappedCutCofiberFamily k hF) := by
  apply IsGapped.of_fullSubcomplex IsCofiberDiagramVertex
  apply (isGapped_functor_iff_pointwise _).2
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  rw [Category.assoc, gappedCutCofiberFamily_evaluation]
  exact hF.precomp (cutCornerOrder k i j)

end SerrePositivity.KST.SConstruction
