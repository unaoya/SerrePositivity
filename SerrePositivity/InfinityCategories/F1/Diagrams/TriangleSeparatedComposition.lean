module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLabelPathComposition
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleCutMapComposition
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLiftedCoordinateIdentities
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLabelBaseline

/-!
概要：二切断から作った小さい長 Hom は、零対象側での前合成を無視する。
方針：持ち上げた Hom で各座標を比較し、ulift の忠実性で元の宇宙へ戻す。
規約：K・L の全パラメーターを保持する。
使われ方：制御二胞体の全次数の豊穣合成則の単位側。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma controlledTriangleMiddleMap_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i j k : Fin (n + 1)} (hj : t j = 0) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ trianglePathMiddleMap t i k =
      snd _ _ ≫ trianglePathMiddleMap t j k := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply stdSimplex.ext
  intro l
  exact trianglePathMiddle_comp_zero t (P.obj l) (Q.obj l) hj

lemma triangleSeparatedLongHom_comp_zero
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj H)
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 0) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ triangleSeparatedLongHom M s r t hi k =
      snd _ _ ≫ triangleSeparatedLongHom M s r t hj k := by
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [Functor.map_comp, Functor.map_comp, triangleSeparatedLongHom_map,
    triangleSeparatedLongHom_map, ← Category.assoc, ← Category.assoc]
  apply congrArg (fun f => f ≫ M)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
    exact (congrArg (fun f => (SSet.uliftFunctor.{v, u}).map f ≫
      (HomotopyLimits.uliftStdSimplexIso.{u, v} 1).hom)
      (controlledTriangleMiddleMap_comp_zero t hj)).trans (by
        simp only [Functor.map_comp, Category.assoc])
  · apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, lift_fst]
        exact triangleLiftedCoordinate_eq_of_comp_eq _ _ _ _
          (controlledTriangleCutMap_comp_zero (triangleZeroLabel t)
            (triangleZeroLabel_zero t hi) (triangleZeroLabel_zero t hj)) s
      · simp only [Category.assoc, lift_snd, lift_fst]
        exact triangleLiftedCoordinate_eq_of_comp_eq _ _ _ _
          (controlledTriangleCutMap_comp_zero (triangleUpperLabel t)
            (triangleUpperLabel_zero t hi) (triangleUpperLabel_zero t hj)) s
    · simp only [Category.assoc, lift_snd]
      exact triangleLiftedCoordinate_eq_of_comp_eq _ _ _ _
        (controlledTriangleCutMap_comp_zero (triangleZeroLabel t)
          (triangleZeroLabel_zero t hi) (triangleZeroLabel_zero t hj)) r

lemma controlledTriangleMiddleMap_comp_two {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i j k : Fin (n + 1)} (hj : t j = 2) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ trianglePathMiddleMap t i k =
      fst _ _ ≫ trianglePathMiddleMap t i j := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply stdSimplex.ext
  intro l
  exact trianglePathMiddle_comp_two t (P.obj l) (Q.obj l) hj

lemma triangleSeparatedLongHom_comp_two
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj H)
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 2) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ triangleSeparatedLongHom M s r t hi k =
      fst _ _ ≫ triangleSeparatedLongHom M s r t hi j := by
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [Functor.map_comp, Functor.map_comp, triangleSeparatedLongHom_map,
    triangleSeparatedLongHom_map, ← Category.assoc, ← Category.assoc]
  apply congrArg (fun f => f ≫ M)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
    exact (congrArg (fun f => (SSet.uliftFunctor.{v, u}).map f ≫
      (HomotopyLimits.uliftStdSimplexIso.{u, v} 1).hom)
      (controlledTriangleMiddleMap_comp_two t hj)).trans (by
        simp only [Functor.map_comp, Category.assoc])
  · apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, lift_fst]
        exact triangleLiftedCoordinate_eq_of_comp_eq _ _ _ _
          (controlledTriangleCutMap_comp_one (triangleZeroLabel t)
            (triangleZeroLabel_zero t hi) (triangleZeroLabel_one t (by omega))) s
      · simp only [Category.assoc, lift_snd, lift_fst]
        exact triangleLiftedCoordinate_eq_of_comp_eq _ _ _ _
          (controlledTriangleCutMap_comp_one (triangleUpperLabel t)
            (triangleUpperLabel_zero t hi) (triangleUpperLabel_one t hj)) s
    · simp only [Category.assoc, lift_snd]
      exact triangleLiftedCoordinate_eq_of_comp_eq _ _ _ _
        (controlledTriangleCutMap_comp_one (triangleZeroLabel t)
          (triangleZeroLabel_zero t hi) (triangleZeroLabel_one t (by omega))) r

end SerrePositivity.InfinityCategories
