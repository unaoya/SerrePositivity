module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingReverse

/-!
概要：区間写像空間の反転の比較射が厳密な同型であること。
方針：任意のパラメーターからの射への作用の全単射性を族の反転の同値で示す。
規約：値域に Kan 性や quasicategory 性を課さない。
使われ方：普遍輸送と比較する反転した coherent Hom のパラメーター。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間写像空間の反転の比較射は同型。
方針：反転の随伴の Hom 同値と区間族の反転の同値を比較し、Yoneda で判定する。
規約：パラメーターは任意の単体集合。
使われ方：反転した区間比較の同値性。 -/
instance intervalMappingReverse_isIso {X : SSet.{u}} (x y : X _⦋0⦌) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingReverse x y) := by
  apply isIso_of_yoneda_map_bijective
  intro A
  let I := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
  let e₀ : (A.op ⟶ I) ≃ (A ⟶ I.op) := SSet.opEquivalence.toAdjunction.homEquiv A I
  let e₁ : (A.op ⟶ I) ≃ (A ⟶ J) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingReverseFamilyEquiv A.op x y).trans
      (Iso.homCongr (SSet.opFunctorCompOpFunctorIso.app A) (Iso.refl J))
  have he (f : A.op ⟶ I) : e₀ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingReverse x y = e₁ f := by
    change ((SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingReverse x y =
      (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingReverseFamily f ≫ 𝟙 J
    rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingReverseFamily_eq, Category.assoc]
  constructor
  · intro h k hk
    obtain ⟨f, rfl⟩ := e₀.surjective h
    obtain ⟨g, rfl⟩ := e₀.surjective k
    apply congrArg e₀
    apply e₁.injective
    rw [← he, ← he]
    exact hk
  · intro h
    obtain ⟨f, hf⟩ := e₁.surjective h
    exact ⟨e₀ f, (he f).trans hf⟩

/-- 概要：区間写像空間の反転は反転した二端点の区間写像空間と同型。
方針：普遍区間族を反転する実際の比較射を同型として束ねる。
規約：順方向の射は intervalMappingReverse のまま。
使われ方：coherent な Hom の反転を普遍輸送のパラメーターに戻す。 -/
def intervalMappingReverseIso {X : SSet.{u}} (x y : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y).op ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) :=
  asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingReverse x y)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
