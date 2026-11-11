module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.BoundaryPrismOpposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialHornProductBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornDuality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-! # 最後の外側ホーンと境界の積の充填

概要：最後の外側ホーン上の図式と境界上の族を、指定辺の可逆性によって延長する。
方針：両因子を反転し、最初の外側ホーンの積の充填を用いて戻す。
規約：右因子の最後の頂点上の辺に可逆性を課す。使われ方：余錐の cartesian な辺の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

private def fullReverse (p n : ℕ) :
    (Δ[p] : SSet.{u}) ⊗ Δ[n] ≅ ((Δ[p] : SSet.{u}) ⊗ Δ[n]).op :=
  tensorIso (stdSimplex.opIso ⦋p⦌).symm (stdSimplex.opIso ⦋n⦌).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso Δ[p] Δ[n]

private def boundaryProductReverse (p n : ℕ) :
    (Δ[p] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ≅
      ((Δ[p] : SSet.{u}) ⊗ (boundary n : SSet.{u})).op :=
  tensorIso (stdSimplex.opIso ⦋p⦌).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso n) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso Δ[p] (boundary n)

private def lastHornReverse (m : ℕ) :
    (horn (m + 2) 0 : SSet.{u}) ≅ (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}).op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornReverseIndexIso m ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso (m + 2) (Fin.last (m + 2))

private def hornProductReverse (m n : ℕ) :
    (horn (m + 2) 0 : SSet.{u}) ⊗ Δ[n] ≅
      ((horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⊗ Δ[n]).op :=
  tensorIso (lastHornReverse m) (stdSimplex.opIso ⦋n⦌).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso _ _

private def cornerReverse (m n : ℕ) :
    (horn (m + 2) 0 : SSet.{u}) ⊗ (boundary n : SSet.{u}) ≅
      ((horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⊗ (boundary n : SSet.{u})).op :=
  tensorIso (lastHornReverse m) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso n) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso _ _

private lemma reverse_full_boundary (p n : ℕ) :
    (Δ[p] ◁ (boundary n).ι) ≫ (fullReverse.{u} p n).hom =
      (boundaryProductReverse p n).hom ≫ SSet.opFunctor.map (Δ[p] ◁ (boundary n).ι) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext <;> rfl

private lemma reverse_full_horn (m n : ℕ) :
    ((horn (m + 2) 0).ι ▷ Δ[n]) ≫ (fullReverse.{u} (m + 2) n).hom =
      (hornProductReverse m n).hom ≫
        SSet.opFunctor.map ((horn (m + 2) (Fin.last (m + 2))).ι ▷ Δ[n]) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext <;> rfl

private lemma reverse_corner_left (m n : ℕ) :
    ((horn (m + 2) 0).ι ▷ (boundary n : SSet.{u})) ≫
      (boundaryProductReverse.{u} (m + 2) n).hom =
      (cornerReverse m n).hom ≫
        SSet.opFunctor.map ((horn (m + 2) (Fin.last (m + 2))).ι ▷ (boundary n : SSet.{u})) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext <;> rfl

private lemma reverse_corner_right (m n : ℕ) :
    ((horn (m + 2) 0 : SSet.{u}) ◁ (boundary n).ι) ≫ (hornProductReverse.{u} m n).hom =
      (cornerReverse m n).hom ≫ SSet.opFunctor.map
        ((horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ◁ (boundary n).ι) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext <;> rfl

private def reverseProductMap {X : SSet.{u}} (p n : ℕ)
    (F : (Δ[p] : SSet.{u}) ⊗ Δ[n] ⟶ X) : (Δ[p] : SSet.{u}) ⊗ Δ[n] ⟶ X.op :=
  (fullReverse p n).hom ≫ SSet.opFunctor.map F

private lemma reverseProductMap_comp {X Y : SSet.{u}} (p n : ℕ)
    (F : (Δ[p] : SSet.{u}) ⊗ Δ[n] ⟶ X) (q : X ⟶ Y) :
    reverseProductMap p n (F ≫ q) = reverseProductMap p n F ≫ SSet.opFunctor.map q := by
  simp only [reverseProductMap, CategoryTheory.Functor.map_comp, Category.assoc]

private lemma reverseProductMap_double {X : SSet.{u}} (p n : ℕ)
    (F : (Δ[p] : SSet.{u}) ⊗ Δ[n] ⟶ X) :
    reverseProductMap p n (reverseProductMap p n F) ≫
      (SSet.opFunctorCompOpFunctorIso.app X).hom = F := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  change F.app (Opposite.op ⦋d⦌) (_, _) = F.app (Opposite.op ⦋d⦌) (s, t)
  congr 1
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i
  · change ((s i.rev.rev).rev).rev = s i
    simp
  · change ((t i.rev.rev).rev).rev = t i
    simp

private lemma reverseProductMap_back {X : SSet.{u}} (p n : ℕ)
    (F : (Δ[p] : SSet.{u}) ⊗ Δ[n] ⟶ X.op) :
    reverseProductMap p n (reverseProductMap p n F ≫
      (SSet.opFunctorCompOpFunctorIso.app X).hom) = F := by
  rw [reverseProductMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.opFunctorCompOpFunctorIso_coherence, reverseProductMap_double]

/-- 概要：最後の外側ホーン上の図式と境界上の族は指定辺が可逆なら同時に延長できる。
方針：両因子を反転し、最初の外側ホーンの積の充填を適用して反転を戻す。
規約：値域は quasicategory、右因子の最後の頂点上の辺に可逆性を課す。
使われ方：余錐の制限射に対する cartesian な辺の証明。 -/
lemma finalHornProduct_fill_boundary {X : SSet.{u}} [Quasicategory X] (m n : ℕ)
    (G : (Δ[m + 2] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ X)
    (H : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⊗ Δ[n] ⟶ X)
    (hw : ((horn (m + 2) (Fin.last (m + 2))).ι ▷ (boundary n : SSet.{u})) ≫ G =
      ((horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ◁ (boundary n).ι) ≫ H)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last n)) 1)))) :
    ∃ F : (Δ[m + 2] : SSet.{u}) ⊗ Δ[n] ⟶ X,
      (Δ[m + 2] ◁ (boundary n).ι) ≫ F = G ∧
      ((horn (m + 2) (Fin.last (m + 2))).ι ▷ Δ[n]) ≫ F = H := by
  let G' := (boundaryProductReverse (m + 2) n).hom ≫ SSet.opFunctor.map G
  let H' := (hornProductReverse m n).hom ≫ SSet.opFunctor.map H
  have hw' : ((horn (m + 2) 0).ι ▷ (boundary n : SSet.{u})) ≫ G' =
      ((horn (m + 2) 0 : SSet.{u}) ◁ (boundary n).ι) ≫ H' := by
    dsimp only [G', H']
    rw [← Category.assoc, reverse_corner_left, Category.assoc, ← CategoryTheory.Functor.map_comp,
      hw, CategoryTheory.Functor.map_comp, ← Category.assoc, ← reverse_corner_right, Category.assoc]
  have hi' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H'.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) 1))) := by
    have he := hi.op
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last n)) 1)))) ?_).2 he
    change SSet.opObjEquiv.symm (H.app (Opposite.op ⦋1⦌) (_, _)) =
      SSet.opObjEquiv.symm (H.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last n)) 1))
    congr 2
    apply Prod.ext
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseFinalHornMap_edge m (𝟙 _)
    · apply stdSimplex.ext
      intro i
      change (0 : Fin (n + 1)).rev = Fin.last n
      exact Fin.rev_zero n
  obtain ⟨F', hF'₁, hF'₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProduct_fill_boundary m n G' H' hw' hi'
  let F := reverseProductMap (m + 2) n F' ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  have hback : reverseProductMap (m + 2) n F = F' := reverseProductMap_back _ _ _
  have : SSet.opFunctor.{u}.Faithful := SSet.opEquivalence.faithful_functor
  refine ⟨F, ?_, ?_⟩
  · apply SSet.opFunctor.map_injective
    apply (cancel_epi (boundaryProductReverse.{u} (m + 2) n).hom).1
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← reverse_full_boundary, Category.assoc]
    change (Δ[m + 2] ◁ (boundary n).ι) ≫ reverseProductMap (m + 2) n F = G'
    rw [hback]
    exact hF'₁
  · apply SSet.opFunctor.map_injective
    apply (cancel_epi (hornProductReverse.{u} m n).hom).1
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← reverse_full_horn, Category.assoc]
    change ((horn (m + 2) 0).ι ▷ Δ[n]) ≫ reverseProductMap (m + 2) n F = H'
    rw [hback]
    exact hF'₂

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
