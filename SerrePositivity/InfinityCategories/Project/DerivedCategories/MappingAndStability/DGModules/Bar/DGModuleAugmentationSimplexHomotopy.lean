module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationBoundaryHomotopy
/-!
概要：元の同じ実単体の HA 方程式を、augmentation の実比較成分の全微分式へ代入する。
方針：実線形・二次境界への比較 cochain の作用を、同じ削除・左右切断和へ展開する。
規約：混合候補全体の HA 方程式は別工程。使われ方：全 prism の補正和の一般微分計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ実単体の線形・二次境界を代入した、全比較成分の微分式。 -/
lemma dgModuleAugmentationHomotopyAt_simplex_equation
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d (k - 1) k
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) k (k - 1) rfl
          (s.hom I a b k hI ha hb hk)) +
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
          (s.toSimplexData.linearBoundary I a b k) -
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
          (s.toSimplexData.quadraticBoundary I a b k)) +
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk) = 0 := by
  have hs := s.equation I a b k hI ha hb hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic] at hs
  change (_root_.SerrePositivity.DifferentialGraded.homObject R _ (s.obj a) (s.obj b)).d k (k + 1)
    (s.hom I a b k hI ha hb hk) = _ at hs
  have hc : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b)
        (k + 1) k (by omega)
        ((_root_.SerrePositivity.DifferentialGraded.homObject R _ (s.obj a) (s.obj b)).d k (k + 1) (s.hom I a b k hI ha hb hk)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
          (s.toSimplexData.linearBoundary I a b k) -
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
          (s.toSimplexData.quadraticBoundary I a b k) := by
    have he := congrArg (fun x ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F
      (s.obj a) (s.obj b) (k + 1) k (by omega) x) hs
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt, map_sub] using! he
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt_differential R C E F
    (s.obj a) (s.obj b) k (k - 1) rfl (s.hom I a b k hI ha hb hk)
  rw [hc] at he
  exact he
/-- 同じ実単体の比較微分式を、削除係数と左右の実切断補正の全有限和へ展開する。 -/
lemma dgModuleAugmentationHomotopyAt_simplex_expansion
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d (k - 1) k
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) k (k - 1) rfl
          (s.hom I a b k hI ha hb hk)) +
      ((∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
            (s.toSimplexData.homOrZero (I.erase j) a b (k + 1))) -
        ∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
          ((2 - ((I.filter (j ≤ ·)).card : ℤ)).negOnePow •
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationImageCut R C E F s.toSimplexData I a b k j +
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s.toSimplexData I a b k j)) +
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk) = 0 := by
  have he := dgModuleAugmentationHomotopyAt_simplex_equation R C E F s I a b k hI ha hb hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt_linearBoundary,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt_quadraticBoundary R C E F s.toSimplexData I a b k hk] at he
  exact he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
