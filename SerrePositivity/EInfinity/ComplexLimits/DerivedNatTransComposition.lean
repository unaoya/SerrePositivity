module
public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransComponent
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveNatTransFunctor
/-! 概要：元の複体値自然変換の導来像は全合成と正方形を保つ。
方針：混合宇宙の同じ全円柱の合成則を元の D(R) へ送る。
規約：全添字と元の自然変換を保持する。
使われ方：自由単位と元の augmentation・評価の全三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {I : Type (u + 1)} [Category.{u} I]

/-- 概要：同じ二つの通常自然変換の導来像は全関手圏の合成を保つ。
方針：元の混合宇宙円柱の合成を同じ後合成関手で写す。
規約：元の全図式を保持。使われ方：単位の全正方形。 -/
lemma complexOrdinaryDerivedNatTransHom_comp {F G H : I ⥤ Complex A}
    (η : F ⟶ G) (θ : G ⟶ H) :
    complexOrdinaryDerivedNatTransHom A (η ≫ θ) =
      complexOrdinaryDerivedNatTransHom A η ≫ complexOrdinaryDerivedNatTransHom A θ := by
  have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy_hom_comp I (Complex A) η θ
  let T := (hoFunctor.map ((ihom (nerve I)).map (complexOrdinaryDerivedSource A))).toFunctor
  have ht := congrArg T.map h
  rw [Functor.map_comp] at ht
  have hm {V W : I ⥤ Complex A} (a : V ⟶ W) :
      complexOrdinaryDerivedNatTransHom A a = T.map
        (Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy a))) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy a)
      (complexOrdinaryDerivedSource A)
  rw [hm, hm, hm]
  exact ht

/-- 概要：元の通常自然変換の可換正方形は全 D(R) 正方形を与える。
方針：全合成保存に同じ自然変換等式を適用する。
規約：全パラメータを保持。使われ方：元の単位比較の大域式。 -/
lemma complexOrdinaryDerivedNatTransHom_square {F G H J : I ⥤ Complex A}
    (a : F ⟶ G) (b : G ⟶ J) (c : F ⟶ H) (d : H ⟶ J) (h : a ≫ b = c ≫ d) :
    complexOrdinaryDerivedNatTransHom A a ≫ complexOrdinaryDerivedNatTransHom A b =
      complexOrdinaryDerivedNatTransHom A c ≫ complexOrdinaryDerivedNatTransHom A d := by
  rw [← complexOrdinaryDerivedNatTransHom_comp, h, complexOrdinaryDerivedNatTransHom_comp]

end SerrePositivity.EInfinity.ComplexLimits
