module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AugmentationCombinatorics
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationSimplexHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationCutDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationHomotopyNaturality
/-!
概要：同じ実切断補正の微分の中間次数を正規化し、左右に元の HA 方程式を代入する。
方針：生の次数を指定する Leibniz 則と実 Hom 射影の chain map の可換性を使う。
規約：比較 cochain・元の単体・切断係数を選び直さない。
使われ方：全候補の HA 方程式に残る削除・二重切断和の相殺。
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
/-- 指定出力次数で、同じ比較成分の微分を元の微分と比較差で解く。 -/
lemma dgModuleAugmentationHomotopyAt_differential_eq
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) (p q : ℤ) (h : p - 1 = q)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y p) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val (F.obj Y.source)).d q p
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F X Y p q h a) =
      -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F X Y (p + 1) p (by omega)
        ((_root_.SerrePositivity.DifferentialGraded.homObject R _ X Y).d p (p + 1) a) +
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F X Y).f p a) := by
  apply eq_neg_of_add_eq_zero_left
  simpa only [add_assoc] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt_differential R C E F X Y p q h a
variable {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 右比較成分の出力次数を正規化し、左微分を同じ入力 Hom 射影へ戻す。 -/
lemma dgModuleAugmentationHomotopyCut_differential_normalized
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k) :
    let p := 2 - ((I.filter (· ≤ j)).card : ℤ)
    let q := 2 - ((I.filter (j ≤ ·)).card : ℤ)
    let l := s.homOrZero (I.filter (· ≤ j)) a j p
    let r := s.homOrZero (I.filter (j ≤ ·)) j b q
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s I a b k j) =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj j).replacement.val (F.obj (s.obj b).source)).d (q - 1) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) q r))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f p l)
      (by dsimp [p, q] at *; omega) +
    (q - 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
      (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) q r)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f (p + 1)
        ((_root_.SerrePositivity.DifferentialGraded.homObject R _ (s.obj a) (s.obj j)).d p (p + 1) l))
      (by dsimp [p, q] at *; omega) := by
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut, dite_eq_left hsum]
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgDifferential_compose_of_indices R _ _ k
    (2 - ((I.filter (· ≤ j)).card : ℤ) + 1) (2 - ((I.filter (j ≤ ·)).card : ℤ))
    (k + 1) hsum rfl
    (by omega) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) _
      (s.homOrZero (I.filter (j ≤ ·)) j b _))
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
      (s.homOrZero (I.filter (· ≤ j)) a j _))
  have hl := ConcreteCategory.congr_hom
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).comm
      (2 - ((I.filter (· ≤ j)).card : ℤ)) (2 - ((I.filter (· ≤ j)).card : ℤ) + 1))
    (s.homOrZero (I.filter (· ≤ j)) a j _)
  change (_root_.SerrePositivity.DifferentialGraded.homObject R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).obj (s.obj a))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).obj (s.obj j))).d
      (2 - ((I.filter (· ≤ j)).card : ℤ)) (2 - ((I.filter (· ≤ j)).card : ℤ) + 1)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j _)) = _ at hl
  rw [hl] at hd
  exact hd
/-- 同じ実切断の微分を、元の左右微分と実比較差へ展開する。 -/
lemma dgModuleAugmentationHomotopyCut_differential_boundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k) :
    let p := 2 - ((I.filter (· ≤ j)).card : ℤ)
    let q := 2 - ((I.filter (j ≤ ·)).card : ℤ)
    let l := s.homOrZero (I.filter (· ≤ j)) a j p
    let r := s.homOrZero (I.filter (j ≤ ·)) j b q
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s I a b k j) =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (-(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj j) (s.obj b) (q + 1) q (by omega)
          ((_root_.SerrePositivity.DifferentialGraded.homObject R _ (s.obj j) (s.obj b)).d q (q + 1) r) +
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F (s.obj j) (s.obj b)).f q r))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f p l)
      (by dsimp [p, q] at *; omega) +
    (q - 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
      (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) q r)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f (p + 1)
        ((_root_.SerrePositivity.DifferentialGraded.homObject R _ (s.obj a) (s.obj j)).d p (p + 1) l))
      (by dsimp [p, q] at *; omega) := by
  dsimp only
  rw [dgModuleAugmentationHomotopyCut_differential_normalized R C E F s I a b k j hsum]
  have he := dgModuleAugmentationHomotopyAt_differential_eq R C E F
    (s.obj j) (s.obj b) (2 - ((I.filter (j ≤ ·)).card : ℤ)) _ rfl
    (s.homOrZero (I.filter (j ≤ ·)) j b _)
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj j).replacement.val (F.obj (s.obj b).source)).d _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) _
      (s.homOrZero (I.filter (j ≤ ·)) j b _)) = _ at he
  rw [he]
/-- 正しい元の実係数の微分は、全域表示でも同じ線形・二次境界の差。 -/
lemma dgModuleAugmentationSource_homOrZero_differential
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.DifferentialGraded.homObject R _ (s.obj a) (s.obj b)).d k (k + 1)
      (s.toSimplexData.homOrZero I a b k) =
      s.toSimplexData.linearBoundary I a b k - s.toSimplexData.quadraticBoundary I a b k := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s.toSimplexData I a b k hI ha hb hk]
  exact (s.equation I a b k hI ha hb hk).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic s.toSimplexData I a b k hI ha hb hk)
/-- 内部の同じ実切断の左右に、元の実単体の HA 方程式を代入する。 -/
lemma dgModuleAugmentationHomotopyCut_simplex_boundary
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    let p := 2 - ((I.filter (· ≤ j)).card : ℤ)
    let q := 2 - ((I.filter (j ≤ ·)).card : ℤ)
    let l := s.toSimplexData.homOrZero (I.filter (· ≤ j)) a j p
    let r := s.toSimplexData.homOrZero (I.filter (j ≤ ·)) j b q
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s.toSimplexData I a b k j) =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (-(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj j) (s.obj b) (q + 1) q (by omega)
          (s.toSimplexData.linearBoundary (I.filter (j ≤ ·)) j b q -
            s.toSimplexData.quadraticBoundary (I.filter (j ≤ ·)) j b q) +
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F (s.obj j) (s.obj b)).f q r))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f p l)
      (by dsimp [p, q]; have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega) +
    (q - 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
      (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) q r)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f (p + 1)
        (s.toSimplexData.linearBoundary (I.filter (· ≤ j)) a j p -
          s.toSimplexData.quadraticBoundary (I.filter (· ≤ j)) a j p))
      (by dsimp [p, q]; have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega) := by
  dsimp only
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hamin.1 hj haj
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjb
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  have hl := dgModuleAugmentationSource_homOrZero_differential R C E F s
    (I.filter (· ≤ j)) a j _ hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl
  have hr := dgModuleAugmentationSource_homOrZero_differential R C E F s
    (I.filter (j ≤ ·)) j b _ hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjb.le _) rfl
  have he := dgModuleAugmentationHomotopyCut_differential_boundary R C E F
    s.toSimplexData I a b k j hsum
  dsimp only at he
  rw [hl, hr] at he
  exact he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
