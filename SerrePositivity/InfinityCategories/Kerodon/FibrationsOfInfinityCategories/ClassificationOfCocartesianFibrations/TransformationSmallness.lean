module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RestrictionsSmallness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningTransformationFamily

/-!
概要：小さい底上の coherent な空間値図式の変換空間の小ささ。
方針：変換の単体を両端固定の prism の図式へ単射で入れ、全頂点の固定から小ささを得る。
規約：底の quasicategory 性や strict な図式であることは要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい変換空間から小さい fibration の相対写像空間への比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：追加パラメーター付き prism の評価は元の関手空間の族を一意に決める。
方針：因子の交換の同型を消去し、uncurry の単射性を使う。
規約：パラメーターと値域の充填性は不要。
使われ方：Kerodon §4.5.1（Tag 01DQ）、変換の単体を coherent な図式へ単射で入れる。 -/
lemma functorParameterizedPrism_injective {K B L X : SSet.{u}} :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (K := K) (B := B) (L := L) (X := X)) := by
  intro f g h
  apply uncurry_injective
  exact (cancel_epi (((β_ K B).hom ▷ L) ≫ (α_ B K L).hom)).mp h

/-- 概要：小さい底上の二つの coherent な空間値図式の変換空間の各次数は小さい。
方針：区間の両端が全頂点を覆う prism の写像の型へ単射で入れる。
規約：変換は両端固定の区間模型を使い、全次数で小ささを述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい Kan 複体としての変換空間の縮小。 -/
instance leftUnstraighteningTransformationSpace_obj_small_of_small_base {B : SSet.{u + 1}}
    [∀ n, Small.{u} (B.obj n)] (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G).obj n) := by
  let L : SSet.{u + 1} := stdSimplex.obj n.unop
  let X := ((Δ[1] : SSet.{u + 1}) ⊗ B) ⊗ L
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (X.obj d) := by
    change Small.{u} (((Δ[1] : SSet.{u + 1}).obj d × B.obj d) × L.obj d)
    infer_instance
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 0 B ▷ L
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 1 B ▷ L
  have hcover : ∀ x : X _⦋0⦌,
      (∃ y, j.app (Opposite.op ⦋0⦌) y = x) ∨
        (∃ z, k.app (Opposite.op ⦋0⦌) z = x) := by
    rintro ⟨⟨t, b⟩, s⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
    fin_cases i
    · exact Or.inl ⟨(b, s), rfl⟩
    · exact Or.inr ⟨(b, s), rfl⟩
  let T := {H : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} //
    j ≫ H = fst B L ≫ F ∧ k ≫ H = fst B L ≫ G}
  have : Small.{u} T := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentMap_fixedRestrictions_small j k
    (fst B L ≫ F) (fst B L ≫ G) hcover
  let code : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G).obj n → T := fun s ↦
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (SSet.yonedaEquiv.symm s)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism_vertex_of_const 1 _ 0 F
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero (SSet.yonedaEquiv.symm s)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism_vertex_of_const 1 _ 1 G
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one (SSet.yonedaEquiv.symm s))⟩
  apply small_of_injective (f := code)
  intro s t h
  apply SSet.yonedaEquiv.symm.injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
  apply functorParameterizedPrism_injective
  exact congrArg Subtype.val h

/-- 概要：宇宙を持ち上げた小さい底の変換空間は各次数で小さい。
方針：次数ごとの小ささを明示して一般化した小ささの定理を適用する。
規約：従来の持ち上げた底の instance の界面を保つ。
使われ方：小さい変換空間を元の宇宙へ縮小する。 -/
instance leftUnstraighteningTransformationSpace_obj_small {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G).obj n) := by
  have : ∀ m, Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj B).obj m) :=
    fun m ↦ inferInstanceAs (Small.{u} (ULift.{u + 1} (B.obj m)))
  exact leftUnstraighteningTransformationSpace_obj_small_of_small_base F G n

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
