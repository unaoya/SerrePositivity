module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAlgebra
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionPostcomposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionPrecomposition
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-!
模型。文献の定義との比較は後で
# Convolution 代数の関手性

概要：Berger–Fresse §3.1 の内部 Hom の前合成と後合成を P 代数の射として構成する。
方針：全演算の保存則と底の Hom 関手の恒等・合成則を用いる。
規約：始域は反変、値域は共変とする。
使われ方：余代数区間からの path object とその端点・定数の射を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：代数射の後合成は convolution 代数の射（BF §3.1）。
方針：各 arity の後合成の演算保存を束ねる。
規約：底の射は通常の内部 Hom の後合成。
使われ方：固定した余代数からの convolution 関手の射となる。 -/
def convolutionPost (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra) {B B' : P.Algebra} (f : B ⟶ B') :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAlgebra hP H B ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAlgebra hP H B' where
  hom := homPostcompose H.carrier f.hom
  comm n := by
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n ≫ homPostcompose H.carrier f.hom =
      (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map (homPostcompose H.carrier f.hom) n) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B' n
    simpa only [id_tensorHom] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction_post hP H f n

/-- 概要：固定した余代数からの convolution は代数の自己関手（BF §3.1）。
方針：後合成の恒等・合成則を底の Hom 関手から引き戻す。
規約：代数の作用と射を同時に構成する。
使われ方：区間を固定した functorial path object の本体となる。 -/
def convolutionFunctor (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra) : P.Algebra ⥤ P.Algebra where
  obj B := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAlgebra hP H B
  map f := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionPost hP H f
  map_id B := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext ((homFunctor H.carrier).map_id B.carrier)
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext ((homFunctor H.carrier).map_comp f.hom g.hom)

/-- 概要：余代数射の前合成は convolution 代数の射（BF §3.1）。
方針：各 arity の前合成の演算保存を束ねる。
規約：射の向きは余代数射と反対になる。
使われ方：余代数区間の端点と収縮の前合成を代数射にする。 -/
def convolutionPre (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) {H H' : P.Coalgebra} (f : H' ⟶ H) (B : P.Algebra) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAlgebra hP H B ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAlgebra hP H' B where
  hom := homPrecompose f.hom B.carrier
  comm n := by
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n ≫ homPrecompose f.hom B.carrier =
      (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map (homPrecompose f.hom B.carrier) n) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H' B n
    simpa only [id_tensorHom] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction_pre hP f B n

/-- 概要：余代数射の前合成は値域の代数について自然（BF §3.1）。
方針：底の Hom の前合成と後合成の交換を代数射の等式へ上げる。
規約：自然変換の各成分は構成済みの前合成射。
使われ方：区間の端点・収縮から自然な代数射を得る。 -/
def convolutionPreNat (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) {H H' : P.Coalgebra} (f : H' ⟶ H) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionFunctor hP H ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionFunctor hP H' where
  app B := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionPre hP f B
  naturality {B B'} g := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact homPostcompose_precompose A f.hom g.hom

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
