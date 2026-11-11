module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleCoherentEncoderNative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FamilyParameterEquality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedLongFaithfulness
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedPrismRecovery

/-!
概要：実 encoder の等号から、K の固定頂点上の全高次区間族を回収する。
方針：等しい curry 単体を全パラメーターへ戻し、native Hom と有限切断を評価する。
規約：K の高次単体全体での単射性は別途必要。
使われ方：厳密切断に残る全 K 方向の回収条件を明示する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable (X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
  (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
  (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
    (Δ[1] ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y))
  (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
    (Δ[1] ◁ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z))

lemma controlledTriangleCoherentEncoder_parameter_eq
    {n : ℕ}
    (l l' : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)) _⦋n⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋n⦌) l =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋n⦌) l') :
    (((Δ[2] : SSet.{u + 1}) ⊗ K) ◁ SSet.yonedaEquiv.symm l) ≫
        (α_ Δ[2] K _).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentFamily X Y Z K f g =
      (((Δ[2] : SSet.{u + 1}) ⊗ K) ◁ SSet.yonedaEquiv.symm l') ≫
        (α_ Δ[2] K _).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentFamily X Y Z K f g := by
  have hh := congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
    ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)).app
      (Opposite.op ⦋n⦌) t) h
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoderRaw X Y Z K f g).app _ l =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoderRaw X Y Z K f g).app _ l' at hh
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.curry_app_eq_parameter _ l l' hh

lemma controlledTriangleCoherentEncoder_simplex_eq
    {n m : ℕ}
    (l l' : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)) _⦋n⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋n⦌) l =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋n⦌) l')
    (β : ⦋m⦌ ⟶ ⦋n⦌) (s : K _⦋m⦌) (t : Fin (m + 1) →o Fin 3) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleSeparatedExtension X Y Z K f g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleSeparatedExtension_comp X Y Z K f g) s
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)).map β.op l) t =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleSeparatedExtension X Y Z K f g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleSeparatedExtension_comp X Y Z K f g) s
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)).map β.op l') t := by
  have hh := controlledTriangleCoherentEncoder_parameter_eq X Y Z K f g a hf hg l l' h
  let w : (((Δ[2] : SSet.{u + 1}) ⊗ K) ⊗ Δ[n]) _⦋m⦌ :=
    ((stdSimplex.objEquiv.symm (SimplexCategory.mkHom t), s), stdSimplex.objEquiv.symm β)
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app hh (Opposite.op ⦋m⦌)) w
  exact he

/-- 同じ encoder 像から、各 K 頂点上の全区間・全高次パラメーターを回収する。 -/
lemma controlledTriangleCoherentEncoder_interval_at_vertex_eq
    {n : ℕ}
    (l l' : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)) _⦋n⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋n⦌) l =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋n⦌) l')
    (k : K _⦋0⦌) :
    lift (fst (Δ[1] : SSet.{u + 1}) Δ[n])
        (lift (SSet.const k) (snd Δ[1] Δ[n] ≫ SSet.yonedaEquiv.symm l)) ≫
        uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalInterval X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)) =
      lift (fst (Δ[1] : SSet.{u + 1}) Δ[n])
        (lift (SSet.const k) (snd Δ[1] Δ[n] ≫ SSet.yonedaEquiv.symm l')) ≫
        uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleUniversalInterval X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)) := by
  have hs := controlledTriangleCoherentEncoder_simplex_eq X Y Z K f g a hf hg l l' h
    (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismRetraction n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k (n + 2))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n)
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex_longHom_eq_of_eq f g
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleSeparatedExtension X Y Z K f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleSeparatedExtension_comp X Y Z K f g) _ _ _ _ hs
    0 (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel_zero n) (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel])
  have hu := congrArg (fun m => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLiftedSection.{u, u + 1} n ≫
    (SSet.uliftFunctor.{u + 1, u}).map m) hm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_prism_recovery _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleSeparatedExtension_diagonal X Y Z K f g),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_prism_recovery _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleSeparatedExtension_diagonal X Y Z K f g)] at hu
  exact hu

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
