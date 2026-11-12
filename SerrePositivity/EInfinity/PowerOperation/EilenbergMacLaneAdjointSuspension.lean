module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSuspensionNaturality
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSuspensionUnit

/-!
# Γ の随伴構造射の全自然変換

DAG XIII §2.2 の Ω 比較への前段。全複体上の指定構造射を loop の全関手へ移し、
同じ基本円の単位上の計算も元の随伴で保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 一つシフトした同じ Γ の、円からの基点付き内部 Hom の全関手。 -/
def gammaLoopFunctor : Complex A ⥤ PointedSimplicialSet.{u} :=
  shiftFunctor (Complex A) (1 : ℤ) ⋙ gammaPointedFunctor A ⋙
    PointedSimplicialSet.internalHomFunctor PointedSimplicialSet.circle.{u}

/-- 指定 suspension 射の随伴は、複体全体で自然な比較である。 -/
def gammaAdjointSuspension : gammaPointedFunctor A ⟶ gammaLoopFunctor A where
  app M := (PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}).homEquiv
    (gammaPointed A M) (gammaPointed A (M⟦(1 : ℤ)⟧)) (gammaSuspension A M)
  naturality {M N} f := by
    let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
    have h := congrArg (adj.homEquiv (gammaPointed A M) (gammaPointed A (N⟦(1 : ℤ)⟧)))
      (gammaSuspension_naturality A f)
    change adj.homEquiv _ _
      ((PointedObject.smashFunctor.obj PointedSimplicialSet.circle.{u}).map
        ((gammaPointedFunctor A).map f) ≫ gammaSuspension A N) =
      adj.homEquiv _ _ (gammaSuspension A M ≫ (gammaPointedFunctor A).map (f⟦(1 : ℤ)⟧')) at h
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at h
    exact h

/-- 単位の点における随伴比較も、同じ基本円と実際の自己同型で計算する。 -/
lemma gammaAdjointSuspension_on_unit :
    gammaUnitBasedPoint A ≫ (gammaAdjointSuspension A).app (𝟙_ (Complex A)) =
    (PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}).homEquiv
      (𝟙_ PointedSimplicialSet.{u})
      (gammaPointed A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧))
      ((ρ_ PointedSimplicialSet.circle.{u}).hom ≫ unitCircle A ≫
        (gammaPointedFunctor A).map (unitShiftAutomorphism A).hom) := by
  let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
  have h := congrArg (adj.homEquiv (𝟙_ PointedSimplicialSet.{u})
    (gammaPointed A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧))) (gammaSuspension_on_unit A)
  change adj.homEquiv _ _
    ((PointedObject.smashFunctor.obj PointedSimplicialSet.circle.{u}).map
      (gammaUnitBasedPoint A) ≫ gammaSuspension A (𝟙_ (Complex A))) = _ at h
  rw [Adjunction.homEquiv_naturality_left] at h
  exact h

end SerrePositivity.EInfinity.PowerOperation
