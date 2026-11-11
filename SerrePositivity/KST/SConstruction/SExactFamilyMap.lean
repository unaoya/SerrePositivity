module
public import SerrePositivity.KST.SConstruction.SExactFamilyAction

/-! # 全パラメータ S_n 作用の完全関手空間への持ち上げ
概要：元の完全関手族を、S_n 間の完全関手族へ全単体で送る。
方針：実作用を curry し、固定した元の完全射を回収して頂点の完全性を確認する。
規約：全ての自然変換を保持する。使われ方：厳密豊穣 S_n 関手の全 Hom 作用。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma unitHomEquiv_comp {X Y : SSet.{u}} (f : 𝟙_ SSet.{u} ⟶ X) (g : X ⟶ Y) :
    SSet.unitHomEquiv Y (f ≫ g) = g.app (Opposite.op ⦋0⦌) (SSet.unitHomEquiv X f) := rfl

/-- 全完全関手族に対応する、元の S_n 間の実単体的関手族。 -/
def sExactFamilyMap (n : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u}) ⟶
      (ihom (sConstruction n C.obj)).obj (sConstruction n D.obj) :=
  curry (sExactFamilyAction n C D)

/-- 元の完全射に固定した関手族は、同じ元の S_n 完全射の curry。 -/
lemma sExactFamilyMap_fixed (n : ℕ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F ≫ sExactFamilyMap n C D =
      curry' (C := SSet.{u}) (sExactMap n F).hom := by
  rw [sExactFamilyMap, ← curry_natural_left, curry', ← id_tensorHom, sExactFamilyAction_fixed]
  rfl

/-- 全パラメータ作用の元の入力頂点で、同じ S_n 完全射の関手頂点を回収する。 -/
lemma sExactFamilyMap_vertex (n : ℕ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) :
    (sExactFamilyMap n C D).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv C D F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (sExactMap n F).hom := by
  have h := congrArg (SSet.unitHomEquiv _) (sExactFamilyMap_fixed n F)
  rw [unitHomEquiv_comp] at h
  have hp : SSet.unitHomEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv C D F := (SSet.unitHomEquiv _).apply_symm_apply _
  rw [hp] at h
  exact h

/-- 元の全単体的 S_n 関手族の全ての頂点は完全関手。 -/
lemma sExactFamilyMap_isExactVertex (n : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (v : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex (sExactCategory n C) (sExactCategory n D)
      ((sExactFamilyMap n C D).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv C D).surjective v
  rw [sExactFamilyMap_vertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _) (sExactMap n F).hom))
  rw [Equiv.symm_apply_apply]
  exact (sExactMap n F).isExact

/-- 元の S_n 関手族を、全自然変換を持つ完全関手空間へ持ち上げる。 -/
def sExactEnrichedMap (n : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (sExactCategory n C) (sExactCategory n D) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex (sExactCategory n C) (sExactCategory n D))
    (sExactFamilyMap n C D) (sExactFamilyMap_isExactVertex n C D)

/-- 完全関手空間の包含後には、同じ全パラメータ S_n 関手族を回収する。 -/
lemma sExactEnrichedMap_inclusion (n : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    sExactEnrichedMap n C D ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (sExactCategory n C) (sExactCategory n D)).ι =
      sExactFamilyMap n C D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

end SerrePositivity.KST.SConstruction
