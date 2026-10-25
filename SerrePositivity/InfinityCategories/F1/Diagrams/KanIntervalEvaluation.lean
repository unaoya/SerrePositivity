module

public import SerrePositivity.InfinityCategories.Core.EquivalencePathFinalLifting
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.F1.Diagrams.TrianglePathInterval

/-!
概要：Kan 標的への区間族の終点評価と、その固定終点全族の可縮性。
方針：Kan 複体の全辺が可逆であることから可逆 path の評価へ同定する。
規約：固定する終点は任意のパラメーター上の全族。
使われ方：Ind-S (9) の合成端を固定した長い Hom 族の読出し。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- Kan 標的への全区間族は可逆 path の全空間と厳密に同型。 -/
def kanIntervalEquivalencePathIso (H : SSet.{u}) [KanComplex H] :
    (ihom (Δ[1] : SSet.{u})).obj H ≅ equivalencePath H where
  hom := fullSubcomplexLift IsEquivalencePathVertex (𝟙 _) (fun _ =>
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _))
  inv := equivalencePathι H
  hom_inv_id := rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 可逆 path との比較を忘れると、元の全区間族そのもの。 -/
lemma kanIntervalEquivalencePathIso_hom_ι (H : SSet.{u}) [KanComplex H] :
    (kanIntervalEquivalencePathIso H).hom ≫ equivalencePathι H = 𝟙 _ := rfl

/-- Kan 標的への区間族の終点評価は trivial Kan fibration。 -/
lemma kanIntervalEvaluation_trivialKanFibration (H : SSet.{u}) [KanComplex H] :
    TrivialKanFibration (evaluateFunctorAt (Y := H) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  have : (kanIntervalEquivalencePathIso H).hom ≫ equivalencePathEndpoint H 1 =
      evaluateFunctorAt (Y := H) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    rw [equivalencePathEndpoint, ← Category.assoc,
      kanIntervalEquivalencePathIso_hom_ι, Category.id_comp]
  rw [← this]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (TrivialKanFibration.mem (p := (kanIntervalEquivalencePathIso H).hom))
    (TrivialKanFibration.mem (p := equivalencePathEndpoint H 1))⟩

/-- 合成端を全入力で固定した区間族の空間は可縮 Kan。 -/
lemma kanIntervalFamilyFiber_isContractibleKan (H K : SSet.{u}) [KanComplex H]
    (c : K ⟶ H) :
    IsContractibleKan (vertexFiber ((ihom K).map
      (evaluateFunctorAt (Y := H) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) (functorVertex c)) := by
  letI := kanIntervalEvaluation_trivialKanFibration H
  exact vertexFiber_isContractibleKan _ _

/-- 始域の同型による前合成と頂点評価は厳密に可換。 -/
lemma evaluateFunctorAt_pre {A B H : SSet.{u}} (f : A ⟶ B) (a : A _⦋0⦌) :
    (pre f).app H ≫ evaluateFunctorAt a = evaluateFunctorAt (Y := H) (f.app _ a) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  change F.app d (𝟙 d) (f.app d (PinchedHom.constant a d.unop.len)) =
    F.app d (𝟙 d) (PinchedHom.constant (f.app (Opposite.op ⦋0⦌) a) d.unop.len)
  rw [pinchedConstant_map]

/-- 標準区間と同型な始域の終点評価も trivial Kan fibration。 -/
lemma kanIntervalEvaluation_trivialKanFibration_of_iso {A H : SSet.{u}} [KanComplex H]
    (e : A ≅ (Δ[1] : SSet.{u})) (a : A _⦋0⦌)
    (ha : e.inv.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = a) :
    TrivialKanFibration (evaluateFunctorAt (Y := H) a) := by
  have h := evaluateFunctorAt_pre (H := H) e.inv (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  rw [ha] at h
  rw [← h]
  have : IsIso ((pre e.inv).app H) := by
    change IsIso (((internalHom.mapIso e.symm.op).app H).hom)
    infer_instance
  have := kanIntervalEvaluation_trivialKanFibration H
  exact ⟨trivialKanFibrations.comp_mem _ _
    (TrivialKanFibration.mem (p := (pre e.inv).app H)) (TrivialKanFibration.mem (p := _))⟩

/-- 要求正本の持ち上げた native Hom の合成端評価。 -/
lemma triangleLongHomEvaluation_trivialKanFibration (H : SSet.{max u v}) [KanComplex H] :
    TrivialKanFibration (evaluateFunctorAt
      (X := (SSet.uliftFunctor.{v, u}).obj (nerve TriangleNativePath.{u})) (Y := H)
      (ULift.up (ComposableArrows.mk₀ triangleFullPath.{u}) :
        ((SSet.uliftFunctor.{v, u}).obj (nerve TriangleNativePath.{u})) _⦋0⦌)) :=
  kanIntervalEvaluation_trivialKanFibration_of_iso uliftTriangleNativePathIntervalIso _
    uliftTriangleNativePathIntervalIso_inv_last

/-- 要求正本の合成端を全入力で固定した全長 Hom 族の可縮 Kan 性。 -/
lemma triangleLongHomFamilyFiber_isContractibleKan
    (H K : SSet.{max u v}) [KanComplex H] (c : K ⟶ H) :
    IsContractibleKan (vertexFiber ((ihom K).map
      (evaluateFunctorAt
        (X := (SSet.uliftFunctor.{v, u}).obj (nerve TriangleNativePath.{u}))
        (Y := H) (ULift.up (ComposableArrows.mk₀ triangleFullPath.{u}) :
        ((SSet.uliftFunctor.{v, u}).obj (nerve TriangleNativePath.{u})) _⦋0⦌)))
      (functorVertex c)) := by
  have := triangleLongHomEvaluation_trivialKanFibration.{u, v} H
  exact vertexFiber_isContractibleKan _ _

end SerrePositivity.InfinityCategories
