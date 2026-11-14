module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePostcompArrow
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeShiftNull
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFunctorCone

/-!
概要：元実 cone の左包含像を同じ realization の全自然な指定入力にする。
方針：元次数 −1 の左包含を同じ dg 関手で写す。
規約：元零化と全符号を保持する。
使われ方：元全実逆回転 cone を実 realization へ運ぶ全比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
  (Q : DGFunctor R (RightModule R D) (RightModule R E))
local notation "CF" => dgModuleNaturalConeFunctor R D F G η

/-- 概要：元左包含の同じ dg 関手による実像。
方針：元全 Hom 写像を次数 −1 の指定元へ適用する。
規約：元斉次元を保持。使われ方：元 cone image の指定微分入力。 -/
def dgModuleNaturalConeImageInput (x : P) :
    (moduleHom R E (Q.obj (F.obj x)) (Q.obj ((CF).obj x))).X (-1) :=
  (Q.map (F.obj x) ((CF).obj x)).f (-1)
    (dgModuleNaturalConeNullHomotopyElement R D F G η x)

/-- 概要：元左包含の実像は全 Hom に符号付き自然。
方針：元全自然性を同じ dg 関手の全斉次合成保存へ渡す。
規約：閉零次数に制限しない。使われ方：実 cone image の全比較。 -/
lemma dgModuleNaturalConeImageInput_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R ((((CF).comp Q).map x y).f n z)
      (dgModuleNaturalConeImageInput R E D F G η Q x) (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R
        (dgModuleNaturalConeImageInput R E D F G η Q y)
        (((F.comp Q).map x y).f n z) (sub_eq_add_neg n 1).symm := by
  exact dgNegativeNaturalityMap Q
    (dgModuleNaturalConeNullHomotopyElement R D F G η x)
    (dgModuleNaturalConeNullHomotopyElement R D F G η y)
    ((F.map x y).f n z) (((CF).map x y).f n z)
    (dgModuleNaturalConeNullHomotopyElement_naturality R D F G η x y n z)
end SerrePositivity.KST.SConstruction
