module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorHomotopy
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerLinearizationDesc
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.Algebra.Algebra.Bilinear
import SerrePositivity.EInfinity.NatTensor.Symmetry

/-!
# コホモロジー上の cup 積の次数付き可換性

## 概要
余単体的可換環の Alexander–Whitney 積はコホモロジー上で次数付き可換。

## 方針
非正規化 AW 対角と符号付き交換後の対角の差を、標準単体の鎖テンソルの収縮で
再帰的に埋める。普遍鎖を余輪体の対に評価し、交換差が余境界になることを示す。

## 規約
鎖テンソルの符号は KST の全複体の規約に従う。評価は整数線形である。

## 使われ方
Hodge–Tate 比較のコホモロジー積（BS 著者版 Construction 4.9）。
-/

public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology HomologicalComplex
open scoped Simplicial TensorProduct MonoidalCategory

namespace SerrePositivity.Cosimplicial

set_option backward.isDefEq.respectTransparency false

attribute [local instance] SerrePositivity.EInfinity.NatTensor.shapeSymmetry

local notation "F" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor
local notation "Tens" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor
local notation "tm" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap
local notation "C" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace
local notation "L" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization
local notation "gen" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator

private abbrev chains (X : SSet.{u}) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (alternatingFaceMapComplex _).obj (C X)

private abbrev chainsMap {X Y : SSet.{u}} (f : X ⟶ Y) : chains X ⟶ chains Y :=
  (alternatingFaceMapComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f)

private def swapTensor (M N : ModuleCat.{u} ℤ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M N ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor N M :=
  by
  letI : Module ℤ M := M.isModule
  letI : Module ℤ N := N.isModule
  exact ModuleCat.ofHom (TensorProduct.comm ℤ M N).toAddMonoidHom.toIntLinearMap

private lemma swapTensor_natural {M M' N N' : ModuleCat.{u} ℤ} (f : M ⟶ M') (g : N ⟶ N') :
    tm f g ≫ swapTensor M' N' = swapTensor M N ≫ tm g f := by
  let : Module ℤ M := M.isModule
  let : Module ℤ N := N.isModule
  let : Module ℤ M' := M'.isModule
  let : Module ℤ N' := N'.isModule
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y => ?_) (fun x y hx hy => ?_)
  · change (TensorProduct.comm ℤ M' N') (TensorProduct.map f.hom g.hom (x ⊗ₜ[ℤ] y)) =
      TensorProduct.map g.hom f.hom ((TensorProduct.comm ℤ M N) (x ⊗ₜ[ℤ] y))
    simp only [TensorProduct.map_tmul, TensorProduct.comm_tmul]
  · simp only [map_add, hx, hy]

private def swapBicomplex (K J : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    (((F).mapBifunctorHomologicalComplex (.down ℕ) (.down ℕ)).obj K).obj J ⟶
      (((F).flip.mapBifunctorHomologicalComplex (.down ℕ) (.down ℕ)).obj K).obj J :=
  HomologicalComplex₂.homMk (fun i => swapTensor (K.X i.1) (J.X i.2))
    (fun p p' q _ => by
      change swapTensor _ _ ≫ tm (𝟙 _) (K.d p p') = tm (K.d p p') (𝟙 _) ≫ swapTensor _ _
      exact (swapTensor_natural (K.d p p') (𝟙 (J.X q))).symm)
    (fun p q q' _ => by
      change swapTensor _ _ ≫ tm (J.d q q') (𝟙 _) = tm (𝟙 _) (J.d q q') ≫ swapTensor _ _
      exact (swapTensor_natural (𝟙 (K.X p)) (J.d q q')).symm)

private def swapChains (K J : ChainComplex (ModuleCat.{u} ℤ) ℕ) : Tens K J ⟶ Tens J K :=
  HomologicalComplex₂.total.map (swapBicomplex K J) (.down ℕ) ≫
    (mapBifunctorFlipIso J K F (.down ℕ)).hom

private lemma ι_swapChains (K J : ChainComplex (ModuleCat.{u} ℤ) ℕ) (p q n : ℕ)
    (h : p + q = n) :
    ιMapBifunctor K J F (.down ℕ) p q n h ≫ (swapChains K J).f n =
      (-1 : ℤ) ^ (p*q) •
      (swapTensor (K.X p) (J.X q) ≫
        ιMapBifunctor J K F (.down ℕ) q p n (by change q+p=n; omega)) := by
  rw [swapChains, comp_f, HomologicalComplex₂.ιTotal_map_assoc,
    ι_mapBifunctorFlipIso_hom, Linear.comp_units_smul]
  have hs : ComplexShape.σ (.down ℕ) (.down ℕ) (.down ℕ) q p =
      (-1 : ℤˣ) ^ (p*q) := by
    rw [Nat.mul_comm p q]
    rfl
  rw [hs, Units.smul_def]
  simp only [Units.val_pow_eq_pow_val, Units.coe_neg_one]
  rfl

private lemma swapChains_natural {K J K' J' : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ K') (g : J ⟶ J') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap f g ≫ swapChains K' J' =
      swapChains K J ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap g f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q h
  rw [comp_f, comp_f, ← Category.assoc, ← Category.assoc, ι_swapChains,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap, Category.assoc, ι_swapChains,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap]
  simp only [← Category.assoc]
  rw [swapTensor_natural]

private def diagonalAt (Y : Type u) :
    (L).obj Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor ((L).obj Y) ((L).obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun x => gen x ⊗ₜ[ℤ] gen x)

private lemma diagonalAt_gen (Y : Type u) (x : Y) :
    diagonalAt Y (gen x) = gen x ⊗ₜ[ℤ] gen x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator _ x

private lemma diagonalAt_natural {Y Z : Type u} (f : Y ⟶ Z) :
    (L).map f ≫ diagonalAt Z = diagonalAt Y ≫ tm ((L).map f) ((L).map f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change diagonalAt Z ((L).map f (gen x)) = tm ((L).map f) ((L).map f) (diagonalAt Y (gen x))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, diagonalAt_gen, diagonalAt_gen]
  change _ = TensorProduct.map ((L).map f).hom ((L).map f).hom _
  simp only [TensorProduct.map_tmul, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]

private def linearDiagonal (X : SSet.{u}) :
    C X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (C X) (C X) where
  app n := diagonalAt (X.obj n)
  naturality _ _ f := diagonalAt_natural (X.map f)

private lemma linearDiagonal_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f ≫ linearDiagonal Y =
      linearDiagonal X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f) := by
  ext i : 1
  exact diagonalAt_natural (f.app i)

private def awDiagonal (X : SSet.{u}) : chains X ⟶ Tens (chains X) (chains X) :=
  (alternatingFaceMapComplex _).map (linearDiagonal X) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney (C X) (C X)

private lemma awDiagonal_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    chainsMap f ≫ awDiagonal Y =
      awDiagonal X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap (chainsMap f) (chainsMap f) := by
  rw [awDiagonal, awDiagonal, ← Category.assoc, ← Functor.map_comp, linearDiagonal_natural,
    Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_naturality,
    Category.assoc]

private def awDifference (X : SSet.{u}) : chains X ⟶ Tens (chains X) (chains X) :=
  awDiagonal X - awDiagonal X ≫ swapChains (chains X) (chains X)

private lemma awDifference_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    chainsMap f ≫ awDifference Y =
      awDifference X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap (chainsMap f) (chainsMap f) := by
  rw [awDifference, awDifference, Preadditive.comp_sub, Preadditive.sub_comp,
    awDiagonal_natural, ← Category.assoc, awDiagonal_natural, Category.assoc,
    swapChains_natural, ← Category.assoc]

private abbrev simplexChains (N : ℕ) : ChainComplex (ModuleCat.{u} ℤ) ℕ := chains Δ[N]

private def tensorPush {N M : ℕ} (f : ⦋N⦌ ⟶ ⦋M⦌) :
    Tens (simplexChains.{u} N) (simplexChains N) ⟶
      Tens (simplexChains M) (simplexChains M) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap
    (chainsMap (SSet.stdSimplex.map f)) (chainsMap (SSet.stdSimplex.map f))

private abbrev simplexContraction (N : ℕ) :=
  ((SSet.Augmented.StandardSimplex.extraDegeneracy (⦋N⦌ : SimplexCategory)).map
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.{u}).homotopyEquiv

private abbrev tensorVertex (N : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap
    ((simplexContraction.{u} N).hom ≫ (simplexContraction N).inv)
    ((simplexContraction N).hom ≫ (simplexContraction N).inv)

private def tensorContraction (N : ℕ) :
    Homotopy (𝟙 (Tens (simplexChains.{u} N) (simplexChains N))) (tensorVertex N) :=
  (Homotopy.ofEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_id _ _).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorHomotopy
      (simplexContraction N).homotopyHomInvId.symm
      (simplexContraction N).homotopyHomInvId.symm)

private lemma hzRight {A B D E : ModuleCat.{u} ℤ} (f : A ⟶ B) :
    tm f (0 : D ⟶ E) = (0 : _ ⟶ _) := by
  have h' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_add_right f (0 : D ⟶ E) 0
  rw [zero_add] at h'
  exact add_left_cancel (h'.symm.trans (add_zero _).symm)
private lemma hzLeft {A B D E : ModuleCat.{u} ℤ} (f : D ⟶ E) :
    tm (0 : A ⟶ B) f = (0 : _ ⟶ _) := by
  have h' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_add_left (0 : A ⟶ B) 0 f
  rw [zero_add] at h'
  exact add_left_cancel (h'.symm.trans (add_zero _).symm)

private lemma tensorVertex_positive (N n : ℕ) : (tensorVertex.{u} N).f (n + 1) = 0 := by
  apply mapBifunctor.hom_ext
  intro p q h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap, comp_zero]
  change p + q = n + 1 at h
  have hz (i : ℕ) (hi : i ≠ 0) :
      ((simplexContraction.{u} N).hom ≫ (simplexContraction N).inv).f i = 0 := by
    have hzero := HomologicalComplex.isZero_single_obj_X (.down ℕ) 0
      (SimplicialObject.Augmented.point.obj
        (((SimplicialObject.Augmented.whiskering _ _).obj (L)).obj
          ((SSet.Augmented.stdSimplex : SimplexCategory ⥤ SSet.Augmented.{u}).obj ⦋N⦌))) i hi
    have hh : (simplexContraction.{u} N).hom.f i = 0 := hzero.eq_of_tgt _ _
    rw [comp_f, hh, zero_comp]
  by_cases hp : p = 0
  · rw [hz q (by omega), hzRight, zero_comp]
  · rw [hz p hp, hzLeft, zero_comp]

private lemma tensor_fill (N n : ℕ)
    (x : (Tens (simplexChains.{u} N) (simplexChains N)).X (n + 1))
    (hx : (Tens (simplexChains N) (simplexChains N)).d (n + 1) n x = 0) :
    (Tens (simplexChains N) (simplexChains N)).d (n + 2) (n + 1)
      ((tensorContraction N).hom (n + 1) (n + 2) x) = x := by
  have h := (tensorContraction.{u} N).comm (n + 1)
  rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex,
    tensorVertex_positive, add_zero] at h
  have e := congrArg (fun f => f x) h
  change x = (tensorContraction N).hom n (n + 1)
    ((Tens (simplexChains N) (simplexChains N)).d (n + 1) n x) +
    (Tens (simplexChains N) (simplexChains N)).d (n + 2) (n + 1)
      ((tensorContraction N).hom (n + 1) (n + 2) x) at e
  rwa [hx, map_zero, zero_add, eq_comm] at e

private def tensorModels (k : ℕ) : CosimplicialObject (ModuleCat.{u} ℤ) where
  obj N := (Tens (simplexChains N.len) (simplexChains N.len)).X k
  map f := (tensorPush f).f k
  map_id N := by
    change (tensorPush (𝟙 ⦋N.len⦌)).f k = _
    simp [tensorPush, chainsMap, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_id]
  map_comp f g := by
    change (tensorPush (f ≫ g)).f k = _
    simp only [tensorPush, chainsMap, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap, Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_comp, comp_f]

private def tensorFaceSum {N k : ℕ}
    (x : (Tens (simplexChains.{u} N) (simplexChains N)).X k) :
    (Tens (simplexChains (N + 1)) (simplexChains (N + 1))).X k :=
  AlternatingCofaceMapComplex.objD (tensorModels k) N x

private lemma tensorFaceSum_eq {N k : ℕ}
    (x : (Tens (simplexChains.{u} N) (simplexChains N)).X k) :
    tensorFaceSum x = ∑ i : Fin (N + 2), (-1 : ℤ)^i.val •
      (tensorPush (SimplexCategory.δ i)).f k x := by
  simp only [tensorFaceSum, AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul]
  rfl

private lemma tensorFaceSum_sub {N k : ℕ}
    (x y : (Tens (simplexChains.{u} N) (simplexChains N)).X k) :
    tensorFaceSum (x - y) = tensorFaceSum x - tensorFaceSum y := by
  let x' : (tensorModels k).obj ⦋N⦌ := x
  let y' : (tensorModels k).obj ⦋N⦌ := y
  exact map_sub (AlternatingCofaceMapComplex.objD (tensorModels k) N).hom x' y'

private lemma tensorFaceSum_sq {N k : ℕ}
    (x : (Tens (simplexChains.{u} N) (simplexChains N)).X k) :
    tensorFaceSum (tensorFaceSum x) = 0 := by
  let x' : (tensorModels k).obj ⦋N⦌ := x
  have h := congrArg (fun (f : (tensorModels k).obj ⦋N⦌ ⟶ (tensorModels k).obj ⦋N + 2⦌) => f x')
    (AlternatingCofaceMapComplex.d_squared (tensorModels k) N)
  exact h

private lemma tensorFaceSum_boundary {N k : ℕ}
    (x : (Tens (simplexChains.{u} N) (simplexChains N)).X (k + 1)) :
    (Tens (simplexChains (N + 1)) (simplexChains (N + 1))).d (k + 1) k
      (tensorFaceSum x) = tensorFaceSum ((Tens (simplexChains N) (simplexChains N)).d (k + 1) k x) := by
  simp only [tensorFaceSum_eq, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg (fun f => f x) ((tensorPush (SimplexCategory.δ i)).comm (k + 1) k)

private def fundamental (N : ℕ) : (simplexChains.{u} N).X N :=
  gen (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋N⦌))

private lemma fundamental_boundary (N : ℕ) :
    (simplexChains.{u} (N + 1)).d (N + 1) N (fundamental (N + 1)) =
      ∑ i : Fin (N + 2), (-1 : ℤ)^i.val •
        (chainsMap (SSet.stdSimplex.map (SimplexCategory.δ i))).f N (fundamental N) := by
  rw [alternatingFaceMapComplex_obj_d]
  simp only [AlternatingFaceMapComplex.objD, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (L).map ((SSet.stdSimplex.obj ⦋N + 1⦌).map (SimplexCategory.δ i).op)
      (gen (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋N + 1⦌))) =
    (L).map ((SSet.stdSimplex.map (SimplexCategory.δ i)).app _)
      (gen (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋N⦌)))
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  rw [← SSet.stdSimplex.objEquiv_symm_comp, Category.id_comp]
  rfl

private def differenceChain (N : ℕ) :
    (Tens (simplexChains.{u} N) (simplexChains N)).X N :=
  (awDifference Δ[N]).f N (fundamental N)

private lemma differenceChain_boundary (N : ℕ) :
    (Tens (simplexChains.{u} (N + 1)) (simplexChains (N + 1))).d (N + 1) N
      (differenceChain (N + 1)) = tensorFaceSum (differenceChain N) := by
  have h := congrArg (fun f => f (fundamental (N + 1)))
    ((awDifference (Δ[N+1] : SSet.{u})).comm (N + 1) N)
  change (Tens (simplexChains (N + 1)) (simplexChains (N + 1))).d (N + 1) N
      (differenceChain (N + 1)) = (awDifference Δ[N+1]).f N
      ((simplexChains (N + 1)).d (N + 1) N (fundamental (N + 1))) at h
  rw [h, fundamental_boundary, tensorFaceSum_eq, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  exact congrArg (fun f => f.f N (fundamental N))
    (awDifference_natural (SSet.stdSimplex.map (SimplexCategory.δ i)))

private lemma differenceChain_zero : differenceChain.{u} 0 = 0 := by
  unfold differenceChain awDifference
  change (awDiagonal (Δ[0] : SSet.{u})).f 0 (fundamental 0) -
    (swapChains (simplexChains 0) (simplexChains 0)).f 0
      ((awDiagonal Δ[0]).f 0 (fundamental 0)) = 0
  apply sub_eq_zero.mpr
  unfold awDiagonal
  simp only [comp_f, ModuleCat.comp_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp (C (Δ[0] : SSet.{u})) (C Δ[0]) 0
      (diagonalAt _ (fundamental 0)) = _
  have hh : (awDiagonal (Δ[0] : SSet.{u})).f 0 (fundamental 0) =
      ιMapBifunctor (simplexChains 0) (simplexChains 0) F (.down ℕ) 0 0 0 rfl
        (fundamental 0 ⊗ₜ[ℤ] fundamental 0) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp
        (C (Δ[0] : SSet.{u})) (C Δ[0]) 0 (diagonalAt _ (fundamental 0)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp, Fin.sum_univ_one]
    have hzero (f : ⦋0⦌ ⟶ ⦋0⦌) : f = 𝟙 _ := Subsingleton.elim _ _
    change (tm ((C (Δ[0] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront 0 0).op)
      ((C (Δ[0] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack 0 0).op) ≫
      ιMapBifunctor (simplexChains 0) (simplexChains 0) F (.down ℕ) 0 0 0 rfl)
        (diagonalAt _ (fundamental 0)) = _
    rw [hzero (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront 0 0),
      hzero (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack 0 0)]
    change (tm ((C (Δ[0] : SSet.{u})).map (𝟙 _))
      ((C (Δ[0] : SSet.{u})).map (𝟙 _)) ≫
      ιMapBifunctor (simplexChains 0) (simplexChains 0) F (.down ℕ) 0 0 0 rfl)
        (diagonalAt _ (fundamental 0)) = _
    have hi := CategoryTheory.Functor.map_id (C (Δ[0] : SSet.{u})) (op ⦋0⦌)
    erw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_id, Category.id_comp]
    exact congrArg (fun z => (ιMapBifunctor (simplexChains 0) (simplexChains 0) F
      (.down ℕ) 0 0 0 rfl) z) (diagonalAt_gen _ _)
  change (awDiagonal (Δ[0] : SSet.{u})).f 0 (fundamental 0) =
    (swapChains (simplexChains 0) (simplexChains 0)).f 0
      ((awDiagonal Δ[0]).f 0 (fundamental 0))
  rw [hh]
  have h := congrArg (fun f => f (gen (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) ⊗ₜ[ℤ]
      gen (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))))
    (ι_swapChains (simplexChains.{u} 0) (simplexChains 0) 0 0 0 rfl)
  simp only [Nat.mul_zero, pow_zero, one_smul, ModuleCat.comp_apply] at h
  exact h.symm

private def commutativityChain : (N : ℕ) →
    (Tens (simplexChains.{u} N) (simplexChains N)).X (N + 1)
  | 0 => 0
  | N + 1 => (tensorContraction (N + 1)).hom (N + 1) (N + 2)
      (differenceChain (N + 1) - tensorFaceSum (commutativityChain N))

private lemma commutativityChain_boundary_zero :
    (Tens (simplexChains.{u} 0) (simplexChains 0)).d 1 0 (commutativityChain 0) =
      differenceChain 0 := by
  rw [commutativityChain, map_zero, differenceChain_zero]

private lemma commutativityChain_boundary (N : ℕ) :
    (Tens (simplexChains.{u} (N + 1)) (simplexChains (N + 1))).d (N + 2) (N + 1)
      (commutativityChain (N + 1)) =
    differenceChain (N + 1) - tensorFaceSum (commutativityChain N) := by
  induction N with
  | zero =>
    rw [commutativityChain]
    apply tensor_fill
    rw [map_sub, differenceChain_boundary, tensorFaceSum_boundary,
      commutativityChain_boundary_zero, sub_self]
  | succ N ih =>
    rw [commutativityChain]
    apply tensor_fill
    rw [map_sub, differenceChain_boundary, tensorFaceSum_boundary, ih,
      tensorFaceSum_sub, tensorFaceSum_sq, sub_zero, sub_self]

section Evaluation

variable (X : CosimplicialObject CommRingCat.{u})

private abbrev coeffs (N : ℕ) := ModuleCat.of ℤ (X.obj ⦋N⦌)

private def coeffMap {N M : ℕ} (f : ⦋N⦌ ⟶ ⦋M⦌) : coeffs X N ⟶ coeffs X M :=
  ModuleCat.ofHom (X.map f).hom.toAddMonoidHom.toIntLinearMap

private def evalCochain {m : ℕ} (a : X.obj ⦋m⦌) (N : ℕ) :
    (simplexChains.{u} N).X m ⟶ coeffs X N :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc
    (fun s => X.map (SSet.stdSimplex.objEquiv s) a)

private lemma evalCochain_gen {m N : ℕ} (a : X.obj ⦋m⦌) (f : ⦋m⦌ ⟶ ⦋N⦌) :
    evalCochain X a N (gen (SSet.stdSimplex.objEquiv.symm f)) = X.map f a := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator
    (M := coeffs X N) (fun s => X.map (SSet.stdSimplex.objEquiv s) a)
    (SSet.stdSimplex.objEquiv.symm f)).trans (by rw [Equiv.apply_symm_apply])

private lemma evalCochain_natural {m N M : ℕ} (a : X.obj ⦋m⦌) (f : ⦋N⦌ ⟶ ⦋M⦌) :
    (chainsMap (SSet.stdSimplex.map f)).f m ≫ evalCochain X a M =
      evalCochain X a N ≫ coeffMap X f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro s
  obtain ⟨g, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective s
  change evalCochain X a M ((L).map ((SSet.stdSimplex.map f).app _)
      (gen (SSet.stdSimplex.objEquiv.symm g))) =
    X.map f (evalCochain X a N (gen (SSet.stdSimplex.objEquiv.symm g)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator,
    ← SSet.stdSimplex.objEquiv_symm_comp, evalCochain_gen, evalCochain_gen, X.map_comp]
  rfl

private lemma evalCochain_boundary {m : ℕ} (a : X.obj ⦋m⦌)
    (ha : cochainDifferential X m a = 0) (N : ℕ) :
    (simplexChains.{u} N).d (m + 1) m ≫ evalCochain X a N = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro s
  obtain ⟨g, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective s
  have h := congrArg (fun z => X.map g z) ha
  rw [cochainDifferential_apply, map_zero, map_sum] at h
  change evalCochain X a N ((simplexChains.{u} N).d (m + 1) m
    (gen (SSet.stdSimplex.objEquiv.symm g))) = 0
  rw [alternatingFaceMapComplex_obj_d]
  simp only [AlternatingFaceMapComplex.objD, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_zsmul]
  rw [map_sum]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans h
  change evalCochain X a N ((-1 : ℤ)^i.val •
    (L).map ((SSet.stdSimplex.obj ⦋N⦌).map (SimplexCategory.δ i).op)
      (gen (SSet.stdSimplex.objEquiv.symm g))) = _
  rw [map_zsmul, map_zsmul]
  congr 1
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  change evalCochain X a N (gen (SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i ≫ g))) = _
  rw [evalCochain_gen, X.map_comp]
  rfl

private def multiplication (N : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor (coeffs X N) (coeffs X N) ⟶ coeffs X N :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.mul ℤ (X.obj ⦋N⦌))).toAddMonoidHom.toIntLinearMap

private lemma multiplication_tmul (N : ℕ) (x y : coeffs X N) :
    multiplication X N (x ⊗ₜ[ℤ] y) = x * y := by
  change (TensorProduct.lift (LinearMap.mul ℤ (X.obj ⦋N⦌))) (x ⊗ₜ[ℤ] y) = _
  exact TensorProduct.lift.tmul _ _

private def evalPair {m n : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (N : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor ((simplexChains.{u} N).X m)
      ((simplexChains N).X n) ⟶ coeffs X N :=
  tm (evalCochain X a N) (evalCochain X b N) ≫ multiplication X N

private lemma evalPair_gen {m n N : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌)
    (f : ⦋m⦌ ⟶ ⦋N⦌) (g : ⦋n⦌ ⟶ ⦋N⦌) :
    evalPair X a b N (gen (SSet.stdSimplex.objEquiv.symm f) ⊗ₜ[ℤ]
      gen (SSet.stdSimplex.objEquiv.symm g)) = X.map f a * X.map g b := by
  change multiplication X N
    (TensorProduct.map (evalCochain X a N).hom (evalCochain X b N).hom
      (gen (SSet.stdSimplex.objEquiv.symm f) ⊗ₜ[ℤ] gen (SSet.stdSimplex.objEquiv.symm g))) = _
  rw [TensorProduct.map_tmul, multiplication_tmul]
  change evalCochain X a N (gen (SSet.stdSimplex.objEquiv.symm f)) *
    evalCochain X b N (gen (SSet.stdSimplex.objEquiv.symm g)) = _
  rw [evalCochain_gen, evalCochain_gen]

private def evalSummand {m n : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (N p q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor ((simplexChains.{u} N).X p)
      ((simplexChains N).X q) ⟶ coeffs X N := by
  by_cases hp : p = m
  · subst p
    by_cases hq : q = n
    · subst q
      exact evalPair X a b N
    · exact 0
  · exact 0

private lemma evalSummand_same {m n : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (N : ℕ) :
    evalSummand X a b N m n = evalPair X a b N := by
  simp [evalSummand]

private lemma evalSummand_zero_left {m n N p q : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌)
    (hp : p ≠ m) : evalSummand X a b N p q = 0 := by
  simp [evalSummand, hp]

private lemma evalSummand_zero_right {m n N p q : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌)
    (hq : q ≠ n) : evalSummand X a b N p q = 0 := by
  by_cases hp : p = m
  · subst p
    simp [evalSummand, hq]
  · exact evalSummand_zero_left X a b hp

private def evaluateAt {m n : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (N k : ℕ) :
    (Tens (simplexChains.{u} N) (simplexChains N)).X k ⟶ coeffs X N :=
  mapBifunctorDesc (fun p q _ => evalSummand X a b N p q)

private abbrev evaluate {m n : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (N : ℕ) :=
  evaluateAt X a b N (m + n)

@[reassoc]
private lemma ι_evaluate {m n : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (N p q k : ℕ)
    (h : p + q = k) :
    ιMapBifunctor (simplexChains N) (simplexChains N) F (.down ℕ) p q k h ≫
      evaluateAt X a b N k = evalSummand X a b N p q :=
  ι_mapBifunctorDesc _ _ _ _

private lemma evalSummand_gen {m n N p q : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌)
    (hp : p = m) (hq : q = n) (f : ⦋p⦌ ⟶ ⦋N⦌) (g : ⦋q⦌ ⟶ ⦋N⦌) :
    evalSummand X a b N p q (gen (SSet.stdSimplex.objEquiv.symm f) ⊗ₜ[ℤ]
      gen (SSet.stdSimplex.objEquiv.symm g)) =
        X.map (eqToHom (congrArg SimplexCategory.mk hp.symm) ≫ f) a *
        X.map (eqToHom (congrArg SimplexCategory.mk hq.symm) ≫ g) b := by
  subst p
  subst q
  rw [evalSummand_same]
  simpa using evalPair_gen X a b f g

private lemma evalPair_natural {m n N M : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌)
    (f : ⦋N⦌ ⟶ ⦋M⦌) :
    tm ((chainsMap (SSet.stdSimplex.map f)).f m) ((chainsMap (SSet.stdSimplex.map f)).f n) ≫
      evalPair X a b M = evalPair X a b N ≫ coeffMap X f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_hom_ext
  intro s t
  obtain ⟨g, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective s
  obtain ⟨h, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective t
  let v := gen (SSet.stdSimplex.objEquiv.symm g)
  let w := gen (SSet.stdSimplex.objEquiv.symm h)
  change evalPair X a b M (TensorProduct.map ((chainsMap (SSet.stdSimplex.map f)).f m).hom
    ((chainsMap (SSet.stdSimplex.map f)).f n).hom (v ⊗ₜ[ℤ] w)) =
      X.map f (evalPair X a b N (v ⊗ₜ[ℤ] w))
  rw [TensorProduct.map_tmul]
  change evalPair X a b M (((L).map ((SSet.stdSimplex.map f).app _) v) ⊗ₜ[ℤ]
    ((L).map ((SSet.stdSimplex.map f).app _) w)) = _
  dsimp only [v, w]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator,
    ← SSet.stdSimplex.objEquiv_symm_comp, ← SSet.stdSimplex.objEquiv_symm_comp,
    evalPair_gen, evalPair_gen, map_mul, X.map_comp, X.map_comp]
  rfl

private lemma evaluate_natural {m n N M : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌)
    (f : ⦋N⦌ ⟶ ⦋M⦌) :
    (tensorPush f).f (m + n) ≫ evaluate X a b M = evaluate X a b N ≫ coeffMap X f := by
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = m + n at h
  rw [← Category.assoc, tensorPush, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap,
    Category.assoc, ι_evaluate, ← Category.assoc, ι_evaluate]
  by_cases hp : p = m
  · subst p
    have hq : q = n := Nat.add_left_cancel h
    subst q
    rw [evalSummand_same, evalSummand_same]
    exact evalPair_natural X a b f
  · simp only [evalSummand, dite_eq_right hp, comp_zero, zero_comp]

private def evalChain {m : ℕ} (a : X.obj ⦋m⦌) (ha : cochainDifferential X m a = 0)
    (N : ℕ) : simplexChains.{u} N ⟶ (single (ModuleCat.{u} ℤ) (.down ℕ) m).obj (coeffs X N) :=
  mkHomToSingle (evalCochain X a N) (fun i hi =>
    have he : i = m + 1 := hi.symm
    he ▸ evalCochain_boundary X a ha N)

private abbrev coeffSingle (N m : ℕ) := (single (ModuleCat.{u} ℤ) (.down ℕ) m).obj (coeffs X N)

private def evalProjection (N m n : ℕ) :
    (Tens (coeffSingle X N m) (coeffSingle X N n)).X (m + n) ⟶ coeffs X N :=
  mapBifunctorDesc (fun p q (h : p + q = m + n) => by
    by_cases hp : p = m
    · subst p
      have hq : q = n := Nat.add_left_cancel h
      subst q
      exact tm (singleObjXSelf (.down ℕ) m (coeffs X N)).hom
        (singleObjXSelf (.down ℕ) n (coeffs X N)).hom ≫ multiplication X N
    · exact 0)

private lemma evaluate_factor {m n : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌)
    (ha : cochainDifferential X m a = 0) (hb : cochainDifferential X n b = 0) (N : ℕ) :
    evaluate X a b N =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap
        (evalChain X a ha N) (evalChain X b hb N)).f (m + n) ≫ evalProjection X N m n := by
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = m + n at h
  rw [ι_evaluate, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap,
    Category.assoc, evalProjection, ι_mapBifunctorDesc]
  by_cases hp : p = m
  · subst p
    have hq : q = n := Nat.add_left_cancel h
    subst q
    simp only [evalSummand_same]
    change evalPair X a b N = tm ((evalChain X a ha N).f m) ((evalChain X b hb N).f n) ≫
      tm (singleObjXSelf (.down ℕ) m (coeffs X N)).hom
        (singleObjXSelf (.down ℕ) n (coeffs X N)).hom ≫ multiplication X N
    rw [evalChain, evalChain, mkHomToSingle_f, mkHomToSingle_f, ← Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp]
    simp [evalPair]
  · simp [evalSummand, hp]

private lemma evaluate_boundary {m n : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌)
    (ha : cochainDifferential X m a = 0) (hb : cochainDifferential X n b = 0) (N : ℕ) :
    (Tens (simplexChains N) (simplexChains N)).d (m + n + 1) (m + n) ≫
      evaluate X a b N = 0 := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap
    (evalChain X a ha N) (evalChain X b hb N)
  have hzero : f.f (m + n + 1) = 0 := by
    apply mapBifunctor.hom_ext
    intro p q h
    change p + q = m + n + 1 at h
    rw [comp_zero]
    change ιMapBifunctor _ _ F (.down ℕ) p q _ h ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap
        (evalChain X a ha N) (evalChain X b hb N)).f _ = 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap]
    by_cases hp : p = m
    · have hq : q ≠ n := by omega
      have hz : (evalChain X b hb N).f q = 0 := by simp [evalChain, mkHomToSingle, hq]
      rw [hz, hzRight, zero_comp]
    · have hz : (evalChain X a ha N).f p = 0 := by simp [evalChain, mkHomToSingle, hp]
      rw [hz, hzLeft, zero_comp]
  rw [evaluate_factor X a b ha hb N]
  change _ ≫ f.f (m + n) ≫ _ = _
  rw [← Category.assoc, ← f.comm, hzero, zero_comp, zero_comp]

private lemma evalPair_swap {m n N : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) :
    swapTensor ((simplexChains.{u} N).X n) ((simplexChains N).X m) ≫ evalPair X a b N =
      evalPair X b a N := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_hom_ext
  intro s t
  obtain ⟨g, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective s
  obtain ⟨f, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective t
  change evalPair X a b N (TensorProduct.comm ℤ _ _
    (gen (SSet.stdSimplex.objEquiv.symm g) ⊗ₜ[ℤ] gen (SSet.stdSimplex.objEquiv.symm f))) =
    evalPair X b a N (gen (SSet.stdSimplex.objEquiv.symm g) ⊗ₜ[ℤ]
      gen (SSet.stdSimplex.objEquiv.symm f))
  rw [TensorProduct.comm_tmul, evalPair_gen, evalPair_gen, mul_comm]

private lemma evaluate_swap {m n : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (N k : ℕ) :
    (swapChains (simplexChains N) (simplexChains N)).f k ≫ evaluateAt X a b N k =
      (-1 : ℤ)^(m*n) • evaluateAt X b a N k := by
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = k at h
  rw [← Category.assoc, ι_swapChains, Preadditive.zsmul_comp, Category.assoc,
    ι_evaluate, Preadditive.comp_zsmul, ι_evaluate]
  by_cases hp : p = n
  · subst p
    by_cases hq : q = m
    · subst q
      rw [evalSummand_same, evalSummand_same, evalPair_swap, Nat.mul_comm n m]
    · rw [evalSummand_zero_left X a b hq, evalSummand_zero_right X b a hq,
        comp_zero, smul_zero, smul_zero]
  · rw [evalSummand_zero_right X a b hp, evalSummand_zero_left X b a hp,
      comp_zero, smul_zero, smul_zero]

private lemma awDiagonal_fundamental (N : ℕ) :
    (awDiagonal (Δ[N] : SSet.{u})).f N (fundamental N) =
      ∑ i : Fin (N + 1),
        ιMapBifunctor (simplexChains N) (simplexChains N) F (.down ℕ) i (N - i) N
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDegrees N i)
          (gen (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront N i)) ⊗ₜ[ℤ]
            gen (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack N i))) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp (C (Δ[N] : SSet.{u})) (C Δ[N]) N
    (diagonalAt _ (fundamental N)) = _
  have hdiag : diagonalAt _ (fundamental.{u} N) = fundamental N ⊗ₜ[ℤ] fundamental N :=
    diagonalAt_gen _ _
  rw [hdiag, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront N i
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack N i
  let ι := ιMapBifunctor (simplexChains.{u} N) (simplexChains N) F (.down ℕ) i (N - i) N
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDegrees N i)
  change ι (TensorProduct.map ((C (Δ[N] : SSet.{u})).map f.op).hom
      ((C (Δ[N] : SSet.{u})).map g.op).hom (fundamental N ⊗ₜ[ℤ] fundamental N)) =
    ι (gen (SSet.stdSimplex.objEquiv.symm f) ⊗ₜ[ℤ] gen (SSet.stdSimplex.objEquiv.symm g))
  rw [TensorProduct.map_tmul]
  have heval {p : ℕ} (h : ⦋p⦌ ⟶ ⦋N⦌) :
      ((C (Δ[N] : SSet.{u})).map h.op).hom (fundamental N) =
        gen (SSet.stdSimplex.objEquiv.symm h) := by
    change (L).map ((SSet.stdSimplex.obj ⦋N⦌).map h.op)
      (gen (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋N⦌))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
    congr 1
    change SSet.stdSimplex.objEquiv.symm (h ≫ 𝟙 _) = _
    rw [Category.comp_id]
  rw [heval f, heval g]

private lemma evaluate_aw {m n N : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (h : m+n=N) :
    evaluateAt X a b N N ((awDiagonal (Δ[N] : SSet.{u})).f N (fundamental N)) =
      X.map (frontFace m n ≫ eqToHom (congrArg SimplexCategory.mk h)) a *
      X.map (backFace m n ≫ eqToHom (congrArg SimplexCategory.mk h)) b := by
  rw [awDiagonal_fundamental, map_sum]
  let i₀ : Fin (N + 1) := ⟨m, by omega⟩
  rw [Finset.sum_eq_single i₀]
  · have hp : (i₀ : ℕ) = m := rfl
    have hq : N - (i₀ : ℕ) = n := by omega
    change (ιMapBifunctor (simplexChains N) (simplexChains N) F (.down ℕ) i₀ (N-i₀) N
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDegrees N i₀) ≫ evaluateAt X a b N N)
        (gen (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront N i₀)) ⊗ₜ[ℤ]
          gen (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack N i₀))) = _
    rw [ι_evaluate]
    erw [evalSummand_gen X a b hp hq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront N i₀)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack N i₀)]
    have hf : eqToHom (congrArg SimplexCategory.mk hp.symm) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront N i₀ =
          frontFace m n ≫ eqToHom (congrArg SimplexCategory.mk h) := by
      ext j
      simp [frontFace]
      rfl
    have hg : eqToHom (congrArg SimplexCategory.mk hq.symm) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack N i₀ =
          backFace m n ≫ eqToHom (congrArg SimplexCategory.mk h) := by
      ext j
      simp [backFace, hp]
    rw [hf, hg]
  · intro i _ hi
    have hp : (i : ℕ) ≠ m := fun h => hi (Fin.ext h)
    change (ιMapBifunctor (simplexChains N) (simplexChains N) F (.down ℕ) i (N-i) N
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDegrees N i) ≫ evaluateAt X a b N N)
        (gen (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront N i)) ⊗ₜ[ℤ]
          gen (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack N i))) = 0
    rw [ι_evaluate, evalSummand_zero_left X a b hp]
    rfl
  · simp

private lemma castRingObj {i j : ℕ} (h : i = j) (x : X.obj ⦋i⦌) :
    cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u)) h) x =
      X.map (eqToHom (congrArg SimplexCategory.mk h)) x := by
  subst j
  simp

private lemma evaluate_aw_cup {m n N : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (h : m+n=N) :
    evaluateAt X a b N N ((awDiagonal (Δ[N] : SSet.{u})).f N (fundamental N)) =
      cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u)) h) (cup X a b) := by
  rw [evaluate_aw X a b h, castRingObj X h]
  simp only [cup, map_mul, X.map_comp, CommRingCat.comp_apply]

private lemma evaluate_difference {m n N : ℕ}
    (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌) (h : m+n=N) :
    evaluateAt X a b N N (differenceChain N) =
      cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u)) h) (cup X a b) -
      (-1 : ℤ)^(m*n) • cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u))
        ((Nat.add_comm n m).trans h)) (cup X b a) := by
  let w := (awDiagonal (Δ[N] : SSet.{u})).f N (fundamental N)
  change evaluateAt X a b N N
    (w - (swapChains (simplexChains N) (simplexChains N)).f N w) = _
  rw [map_sub]
  have hs := congrArg (fun f => f w) (evaluate_swap X a b N N)
  change evaluateAt X a b N N ((swapChains (simplexChains N) (simplexChains N)).f N w) =
    (-1 : ℤ)^(m*n) • evaluateAt X b a N N w at hs
  rw [hs]
  exact congrArg₂ (· - ·) (evaluate_aw_cup X a b h)
    (congrArg ((-1 : ℤ)^(m*n) • ·) (evaluate_aw_cup X b a ((Nat.add_comm n m).trans h)))

private lemma cochainCommutator_boundary {m n k : ℕ} (a : X.obj ⦋m⦌) (b : X.obj ⦋n⦌)
    (ha : cochainDifferential X m a = 0) (hb : cochainDifferential X n b = 0)
    (hk : m+n=k+1) :
    ∃ z : X.obj ⦋k⦌, cochainDifferential X k z =
      evaluateAt X a b (k+1) (k+1) (differenceChain (k+1)) := by
  let z := commutativityChain.{u} k
  let e := evaluateAt X a b (k+1) (k+1)
  let e₀ := evaluateAt X a b k (k+1)
  refine ⟨e₀ z, ?_⟩
  have hf : e (tensorFaceSum z) = cochainDifferential X k (e₀ z) := by
    rw [tensorFaceSum_eq, map_sum, cochainDifferential_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul]
    congr 1
    have he := evaluate_natural X a b (SimplexCategory.δ i : ⦋k⦌ ⟶ ⦋k+1⦌)
    change (tensorPush (SimplexCategory.δ i)).f (m+n) ≫ evaluateAt X a b (k+1) (m+n) =
      evaluateAt X a b k (m+n) ≫ coeffMap X (SimplexCategory.δ i) at he
    rw [hk] at he
    exact congrArg (fun f => f z) he
  have hz := evaluate_boundary X a b ha hb (k+1)
  change (Tens (simplexChains (k+1)) (simplexChains (k+1))).d (m+n+1) (m+n) ≫
    evaluateAt X a b (k+1) (m+n) = 0 at hz
  rw [hk] at hz
  have hc := congrArg (fun x => e x) (commutativityChain_boundary.{u} k)
  change ((Tens (simplexChains (k+1)) (simplexChains (k+1))).d (k+2) (k+1) ≫ e)
    (commutativityChain (k+1)) =
      e (differenceChain (k+1) - tensorFaceSum z) at hc
  rw [show (Tens (simplexChains (k+1)) (simplexChains (k+1))).d (k+2) (k+1) ≫ e = 0 from hz,
    map_sub, hf] at hc
  exact (sub_eq_zero.mp hc.symm).symm

private lemma classOfBoundary {i j : ℕ} (h : i+1=j) (z : Cocycles X j)
    (x : X.obj ⦋i⦌)
    (hx : cochainDifferential X i x =
      cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u)) h.symm) z.val) :
    cohomologyClass X j z = 0 := by
  subst j
  let K := ringCochainComplex X
  have hc : cycleRepresentative X (i+1) z = K.toCycles i (i+1) x := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles (i+1))).mp inferInstance
    rw [cycleRepresentative_apply, ← ConcreteCategory.comp_apply, toCycles_i,
      ringCochainComplex_d_apply]
    exact hx.symm
  rw [cohomologyClass_apply, hc, ← ConcreteCategory.comp_apply, toCycles_comp_homologyπ]
  rfl

private lemma castClass {i j : ℕ} (h : i=j) (a : Cocycles X i) :
    cohomologyClass X j (cast (congrArg (fun k => ↥(Cocycles X k)) h) a) =
      cast (congrArg (cohomology X) h) (cohomologyClass X i a) := by
  subst j
  rfl

private lemma castCocycle_val {i j : ℕ} (h : i=j) (a : Cocycles X i) :
    (cast (congrArg (fun k => ↥(Cocycles X k)) h) a).val =
      cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u)) h) a.val := by
  subst j
  rfl

private lemma degreeCast_sub (B : ℕ → Type u) [∀ k, AddCommGroup (B k)]
    {i j : ℕ} (h : i=j) (a b : B i) :
    cast (congrArg B h) (a-b) = cast (congrArg B h) a - cast (congrArg B h) b := by
  subst j
  rfl

private lemma degreeCast_zsmul (B : ℕ → Type u) [∀ k, AddCommGroup (B k)]
    {i j : ℕ} (h : i=j) (s : ℤ) (a : B i) :
    cast (congrArg B h) (s • a) = s • cast (congrArg B h) a := by
  subst j
  rfl

/-- 概要：余単体的可換環のコホモロジー上の Alexander–Whitney 積は次数付き可換。
方針：標準単体の鎖テンソルを収縮して AW 対角の交換差を埋め、余輪体で評価する。
規約：Koszul の符号は二つの次数の積で決まる。
使われ方：Hodge–Tate 比較の積（BS 著者版 Construction 4.9）。 -/
theorem cohomologyCup_comm {m n : ℕ} (a : cohomology X m) (b : cohomology X n) :
    cast (by rw [Nat.add_comm]) (cohomologyCup X a b) = (-1 : ℤ) ^ (m * n) • cohomologyCup X b a := by
  obtain ⟨a, rfl⟩ := cohomologyClass_surjective X m a
  obtain ⟨b, rfl⟩ := cohomologyClass_surjective X n b
  let h := Nat.add_comm n m
  let z := cocycleCup X a b - (-1 : ℤ)^(m*n) • cast (congrArg (fun k => ↥(Cocycles X k)) h) (cocycleCup X b a)
  have hzval : z.val = cup X a.val b.val - (-1 : ℤ)^(m*n) •
      cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u)) h) (cup X b.val a.val) := by
    exact congrArg (fun y : X.obj ⦋m+n⦌ =>
      cup X a.val b.val - (-1 : ℤ)^(m*n) • y)
      (castCocycle_val X h (cocycleCup X b a))
  have hc : cohomologyClass X (m+n) z = 0 := by
    by_cases hzero : m+n=0
    · obtain ⟨hm, hn⟩ := Nat.add_eq_zero_iff.mp hzero
      subst m
      subst n
      have he := evaluate_difference X a.val b.val (N := 0) rfl
      rw [differenceChain_zero, map_zero] at he
      have hz : z = 0 := Subtype.ext (hzval.trans he.symm)
      rw [hz, map_zero]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have ha : cochainDifferential X m a.val = 0 :=
        (ringCochainComplex_d_apply X m a.val).symm.trans a.property
      have hb : cochainDifferential X n b.val = 0 :=
        (ringCochainComplex_d_apply X n b.val).symm.trans b.property
      obtain ⟨x, hx⟩ := cochainCommutator_boundary X a.val b.val ha hb hk
      apply classOfBoundary X hk.symm z x
      rw [hx, evaluate_difference X a.val b.val hk, hzval]
      erw [degreeCast_sub (fun k => (X.obj ⦋k⦌ : Type u)) hk,
        degreeCast_zsmul (fun k => (X.obj ⦋k⦌ : Type u)) hk, cast_cast]
  change cohomologyClass X (m+n)
    (cocycleCup X a b - (-1 : ℤ)^(m*n) • cast (congrArg (fun k => ↥(Cocycles X k)) h) (cocycleCup X b a)) = 0 at hc
  rw [map_sub, map_zsmul, castClass X h] at hc
  rw [cohomologyCup_class, cohomologyCup_class, sub_eq_zero.mp hc,
    degreeCast_zsmul (cohomology X) h.symm, cast_cast]
  rfl

end Evaluation

end SerrePositivity.Cosimplicial
