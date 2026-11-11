module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedMiddleCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLiftedHom

/-!
概要：新しい長 Hom の内部合成は、分離した二短辺の元の合成を厳密に回収する。
方針：中間対象を通る全座標を終点へ戻し、Kan 延長に指定した合成端の式を使う。
規約：全次数・全パラメーターの射の等式。
使われ方：全族の制御二胞体の唯一の非単位の豊穣合成則。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma triangleSeparatedLongHom_map_coordinates
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj H)
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M s r t hi j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedCoordinateMap s r t hi j ≫ M :=
  (SSet.uliftFunctor.{v, u}).map_preimage _

lemma triangleSeparatedLongHom_comp_middle
    {K L A B : SSet.{max u v}} {H : SSet.{u}}
    (f : K ⟶ A) (g : K ⟶ B) (μ : A ⊗ B ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj H)
    (hM : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
      lift (fst (K ⊗ K) L ≫ fst K K ≫ f)
        (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫ μ)
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    (SSet.uliftFunctor.{v, u}).map
      (eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M s r t hi k) =
      lift ((SSet.uliftFunctor.{v, u}).map (fst _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) s ≫ f)
        ((SSet.uliftFunctor.{v, u}).map (snd _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel t)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel_zero_of_ne t (i := j) (by omega)) k) s ≫ g) ≫ μ := by
  rw [Functor.map_comp, triangleSeparatedLongHom_map_coordinates, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedCoordinateMap_comp_middle s r t hi hj]
  let b := lift
    (lift ((SSet.uliftFunctor.{v, u}).map (fst _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) s)
      ((SSet.uliftFunctor.{v, u}).map (snd _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel t)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel_zero_of_ne t (i := j) (by omega)) k) s))
    ((SSet.uliftFunctor.{v, u}).map (fst _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) r)
  have hb : lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) b =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((K ⊗ K) ⊗ L) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    rfl
  change lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) b ≫ M = _
  rw [hb, Category.assoc, hM]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
