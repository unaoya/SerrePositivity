module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedComposition

/-!
概要：中間対象を通る合成で、長 Hom の全座標を分離した二短辺へ戻す。
方針：区間座標は一、第一・補助座標は前半、第二座標は後半から回収する。
規約：K・L の全次数の座標を厳密に保持する。
使われ方：全族二胞体の内部合成条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma triangleLiftedIntervalConstant (A : SSet.{u}) (i : Fin 2) :
    (SSet.uliftFunctor.{v, u}).map
        (SSet.const (stdSimplex.obj₀Equiv.symm i) : A ⟶ (Δ[1] : SSet.{u})) ≫
      (HomotopyLimits.uliftStdSimplexIso.{u, v} 1).hom =
      SSet.const (stdSimplex.obj₀Equiv.symm i) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

def triangleSeparatedCoordinateMap {K L : SSet.{max u v}}
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    (SSet.uliftFunctor.{v, u}).obj
        (nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))) ⟶
      (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) :=
  lift ((SSet.uliftFunctor.{v, u}).map (trianglePathMiddleMap t i j) ≫
      (HomotopyLimits.uliftStdSimplexIso.{u, v} 1).hom)
    (lift
      (lift (triangleLiftedCoordinate
          (pathCutLastZeroMap (triangleZeroLabel t) (triangleZeroLabel_zero t hi) j) s)
        (triangleLiftedCoordinate
          (pathCutLastZeroMap (triangleUpperLabel t) (triangleUpperLabel_zero t hi) j) s))
      (triangleLiftedCoordinate
        (pathCutLastZeroMap (triangleZeroLabel t) (triangleZeroLabel_zero t hi) j) r))

lemma controlledTriangleMiddleMap_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i j k : Fin (n + 1)} (hj : t j = 1) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ trianglePathMiddleMap t i k =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply stdSimplex.ext
  intro l
  exact trianglePathMiddle_comp_one t (P.obj l) (Q.obj l) hj

lemma triangleSeparatedCoordinateMap_comp_middle
    {K L : SSet.{max u v}} {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) {i j k : Fin (n + 1)}
    (hi : t i = 0) (hj : t j = 1) :
    (SSet.uliftFunctor.{v, u}).map
      (eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩) ≫ triangleSeparatedCoordinateMap s r t hi k =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
        (lift
          (lift ((SSet.uliftFunctor.{v, u}).map (fst _ _) ≫ triangleLiftedCoordinate
              (pathCutLastZeroMap (triangleZeroLabel t) (triangleZeroLabel_zero t hi) j) s)
            ((SSet.uliftFunctor.{v, u}).map (snd _ _) ≫ triangleLiftedCoordinate
              (pathCutLastZeroMap (triangleUpperLabel t)
                (triangleUpperLabel_zero_of_ne t (by omega)) k) s))
          ((SSet.uliftFunctor.{v, u}).map (fst _ _) ≫ triangleLiftedCoordinate
            (pathCutLastZeroMap (triangleZeroLabel t) (triangleZeroLabel_zero t hi) j) r)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [triangleSeparatedCoordinateMap, Category.assoc, lift_fst]
    have h := congrArg (fun f => (SSet.uliftFunctor.{v, u}).map f ≫
      (HomotopyLimits.uliftStdSimplexIso.{u, v} 1).hom)
      (controlledTriangleMiddleMap_comp_one t hj (i := i) (k := k))
    simpa only [Functor.map_comp, Category.assoc] using
      h.trans (triangleLiftedIntervalConstant _ 1)
  · apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [triangleSeparatedCoordinateMap, Category.assoc, lift_fst]
        exact triangleLiftedCoordinate_eq_of_comp_eq _ _ _ _
          (controlledTriangleCutMap_comp_one (triangleZeroLabel t)
            (triangleZeroLabel_zero t hi) (triangleZeroLabel_one t (by omega))) s
      · simp only [triangleSeparatedCoordinateMap, Category.assoc, lift_snd, lift_fst]
        exact triangleLiftedCoordinate_eq_of_comp_eq _ _ _ _
          (controlledTriangleCutMap_comp_zero (triangleUpperLabel t)
            (triangleUpperLabel_zero t hi) (triangleUpperLabel_zero_of_ne t (by omega))) s
    · simp only [triangleSeparatedCoordinateMap, Category.assoc, lift_snd]
      exact triangleLiftedCoordinate_eq_of_comp_eq _ _ _ _
        (controlledTriangleCutMap_comp_one (triangleZeroLabel t)
          (triangleZeroLabel_zero t hi) (triangleZeroLabel_one t (by omega))) r

end SerrePositivity.InfinityCategories
