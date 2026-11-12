module
public import SerrePositivity.KST.SConstruction.CubicalSerreGenerators

/-! # 全 cubical sets 上の元の Serre 対角と増大
概要：全表示関係を保つ元の鎖立方体の対角・増大を、全 cubical sets の鎖射へ延長する。
方針：各生成鎖射の tensor と余極限の普遍性を使い、元の各立方体での値を回収する。
規約：余結合・余単位の全体への移送は後続の Comonoid で扱う。使われ方：Λ の oplax tensor。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Opposite MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の Serre 対角の生成鎖射による像は全表示関係を保つ。 -/
lemma cubicalSerreDiagonal_relation {K : CubicalSet.{u}} {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : c ⟶ d) (φ : cubicalYoneda.obj d ⟶ K) :
    (serreConcreteCubeComplexFunctor A).map f ≫
        (serreConcreteCubeDiagonal A d ≫
          (cubicalSerreGenerator A φ ⊗ₘ cubicalSerreGenerator A φ)) =
      serreConcreteCubeDiagonal A c ≫
        (cubicalSerreGenerator A (cubicalYoneda.map f ≫ φ) ⊗ₘ
          cubicalSerreGenerator A (cubicalYoneda.map f ≫ φ)) := by
  rw [← Category.assoc, serreConcreteCubeComplexFunctor_comul, Category.assoc,
    tensorHom_comp_tensorHom, cubicalSerreGenerator_relation]

/-- 全 cubical sets の元の鎖複体上の Serre 対角。 -/
def cubicalSerreDiagonal (K : CubicalSet.{u}) :
    (cubicalSerreChains A).obj K ⟶
      (cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj K :=
  cubicalSerreDesc A K _
    (fun c φ => serreConcreteCubeDiagonal A c ≫
      (cubicalSerreGenerator A φ ⊗ₘ cubicalSerreGenerator A φ))
    (fun f φ => cubicalSerreDiagonal_relation A f φ)

/-- 全体の Serre 対角は、元の各立方体の対角そのものを回収する。 -/
lemma cubicalSerreDiagonal_generator (K : CubicalSet.{u}) {c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (φ : cubicalYoneda.obj c ⟶ K) :
    cubicalSerreGenerator A φ ≫ cubicalSerreDiagonal A K =
      serreConcreteCubeDiagonal A c ≫
        (cubicalSerreGenerator A φ ⊗ₘ cubicalSerreGenerator A φ) :=
  cubicalSerreDesc_fac A K _
    (fun d ψ => serreConcreteCubeDiagonal A d ≫
      (cubicalSerreGenerator A ψ ⊗ₘ cubicalSerreGenerator A ψ))
    (fun f ψ => cubicalSerreDiagonal_relation A f ψ) c φ

/-- 全 cubical sets の元の鎖複体上の増大。 -/
def cubicalSerreAugmentation (K : CubicalSet.{u}) :
    (cubicalSerreChains A).obj K ⟶ 𝟙_ (Complex A) :=
  cubicalSerreDesc A K _ (fun c _ => serreConcreteCubeAugmentation A c)
    (fun f _ => serreConcreteCubeComplexFunctor_counit A f)

/-- 全体の増大は、元の各立方体の増大そのものを回収する。 -/
lemma cubicalSerreAugmentation_generator (K : CubicalSet.{u}) {c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (φ : cubicalYoneda.obj c ⟶ K) :
    cubicalSerreGenerator A φ ≫ cubicalSerreAugmentation A K =
      serreConcreteCubeAugmentation A c :=
  cubicalSerreDesc_fac A K _ (fun d _ => serreConcreteCubeAugmentation A d)
    (fun f _ => serreConcreteCubeComplexFunctor_counit A f) c φ

/-- 全体の Serre 対角は、元の cubical set の射について自然。 -/
lemma cubicalSerreDiagonal_naturality {K L : CubicalSet.{u}} (f : K ⟶ L) :
    (cubicalSerreChains A).map f ≫ cubicalSerreDiagonal A L =
      cubicalSerreDiagonal A K ≫
        ((cubicalSerreChains A).map f ⊗ₘ (cubicalSerreChains A).map f) := by
  apply cubicalSerreChains_hom_ext A
  intro c x
  change cubicalSerreGenerator A (cubicalCell c x) ≫ _ =
    cubicalSerreGenerator A (cubicalCell c x) ≫ _
  rw [← Category.assoc, cubicalSerreGenerator_naturality,
    cubicalSerreDiagonal_generator, ← Category.assoc, cubicalSerreDiagonal_generator,
    Category.assoc, tensorHom_comp_tensorHom, cubicalSerreGenerator_naturality]

/-- 全体の増大は、元の cubical set の射について自然。 -/
lemma cubicalSerreAugmentation_naturality {K L : CubicalSet.{u}} (f : K ⟶ L) :
    (cubicalSerreChains A).map f ≫ cubicalSerreAugmentation A L =
      cubicalSerreAugmentation A K := by
  apply cubicalSerreChains_hom_ext A
  intro c x
  change cubicalSerreGenerator A (cubicalCell c x) ≫ _ =
    cubicalSerreGenerator A (cubicalCell c x) ≫ _
  rw [← Category.assoc, cubicalSerreGenerator_naturality,
    cubicalSerreAugmentation_generator, cubicalSerreAugmentation_generator]

end SerrePositivity.KST.SConstruction
