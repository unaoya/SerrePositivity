module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.BoundaryPrismOpposite

/-! # 境界充填の左右双対

概要：境界とその充填を単体集合の反転で移す。
方針：標準単体の反転を境界部分複体へ制限する。
規約：始点と終点を交換する。使われ方：相対始対象の充填を相対終対象から導く。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：境界からの射を反転する。
方針：境界の反転同型で前合成する。
規約：境界の次元は変わらない。使われ方：充填条件の双対化。 -/
def reverseBoundaryMap {X : SSet.{u}} (n : ℕ) (b : (boundary n : SSet.{u}) ⟶ X) :
    (boundary n : SSet.{u}) ⟶ X.op :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso n).hom ≫ SSet.opFunctor.map b

/-- 概要：単体の境界への制限と反転は可換。
方針：境界の反転と包含の可換性を使う。
規約：同じ次数で比較する。使われ方：反転した充填を元へ戻す。 -/
lemma reverseBoundaryMap_restrict {X : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X) :
    reverseBoundaryMap n ((boundary n).ι ≫ F) = (boundary n).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex n F := by
  dsimp only [reverseBoundaryMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex]
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso_hom_ι, Category.assoc]

/-- 概要：境界からの射の反転は単射。
方針：前合成の同型と反転関手の忠実性を使う。
規約：quasicategory 性は不要。使われ方：充填の反転からの復帰。 -/
lemma reverseBoundaryMap_injective (X : SSet.{u}) (n : ℕ) :
    Function.Injective (reverseBoundaryMap (X := X) n) := by
  intro a b h
  have : SSet.opFunctor.{u}.Faithful := SSet.opEquivalence.faithful_functor
  apply SSet.opFunctor.map_injective
  exact (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso n).hom).1 h

/-- 概要：境界からの射の反転は標的の後合成と可換。
方針：反転関手の合成則を使う。
規約：標的の射は任意。使われ方：相対的な充填の双対化。 -/
lemma reverseBoundaryMap_comp {X Y : SSet.{u}} (n : ℕ)
    (b : (boundary n : SSet.{u}) ⟶ X) (p : X ⟶ Y) :
    reverseBoundaryMap n (b ≫ p) = reverseBoundaryMap n b ≫ SSet.opFunctor.map p := by
  simp only [reverseBoundaryMap, CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：反転した境界を充填できれば元の境界も充填できる。
方針：充填を反転して二重反転の標準同型で戻す。
規約：指定境界を保つ。使われ方：始対象と終対象の左右双対。 -/
lemma boundaryFiller_of_reverseBoundaryFiller {X : SSet.{u}} (n : ℕ)
    (b : (boundary n : SSet.{u}) ⟶ X) (F : (Δ[n] : SSet.{u}) ⟶ X.op)
    (hF : (boundary n).ι ≫ F = reverseBoundaryMap n b) :
    ∃ G : (Δ[n] : SSet.{u}) ⟶ X, (boundary n).ι ≫ G = b := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex n F ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom, ?_⟩
  apply reverseBoundaryMap_injective X n
  rw [reverseBoundaryMap_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
  exact hF

/-- 概要：境界の反転は頂点の番号を反転する。
方針：包含後に標準単体の反転を計算する。
規約：標準零単体の反転同型も式に含める。使われ方：始点・終点の固定条件。 -/
lemma boundaryReverseIso_vertex (n : ℕ) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso.{u} (n + 1)).hom =
      (stdSimplex.opIso ⦋0⦌).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i.rev) := by
  have : Mono (SSet.opFunctor.{u}.map (boundary.{u} (n + 1)).ι) := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    rw [mono_iff_injective]
    exact Subtype.val_injective
  apply (cancel_mono (SSet.opFunctor.{u}.map (boundary.{u} (n + 1)).ι)).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso_hom_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι,
    Category.assoc, ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro j
  fin_cases j
  rfl

/-- 概要：反転した境界の頂点制限は、反転した番号の元の頂点制限を反転したもの。
方針：境界の反転の頂点での式を後合成する。
規約：任意の頂点で成り立つ。使われ方：相対境界充填の端点。 -/
lemma reverseBoundaryMap_vertex {X : SSet.{u}} (n : ℕ)
    (b : (boundary (n + 1) : SSet.{u}) ⟶ X) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i ≫ reverseBoundaryMap (n + 1) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n i.rev ≫ b) := by
  dsimp only [reverseBoundaryMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex]
  rw [← Category.assoc, boundaryReverseIso_vertex, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
