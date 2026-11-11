module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.LocallySmall
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero

/-!
概要：局所小さい ∞ 圏のホモトピー圏の Hom と対象間同型の型は小さい。
方針：小さい Kan 模型の連結成分を元の pinched Hom の連結成分へ移す。
規約：元の対象と Hom を保持し、局所小ささ自体は全写像空間の比較のままとする。
使われ方：引き戻しの小さい生成候補の対象間同値を小さい型で添字付ける。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：局所小さい ∞ 圏の元の二対象間のホモトピー圏の Hom は小さい。
方針：小さい Kan 模型の連結成分を全同値で移して元の Hom と同定する。
規約：元の Hom を別の模型の Hom に置き換えない。
使われ方：生成候補の貼り合わせデータの小ささ。 -/
lemma IsLocallySmall.hom_small {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall C) (x y : C _⦋0⦌) :
    Small.{u} (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hC x y
  have := hK
  let T := (SSet.uliftFunctor.{u + 1, u}).obj K
  have : Small.{u} (T _⦋0⦌) := inferInstanceAs (Small.{u} (ULift.{u + 1} (K _⦋0⦌)))
  have : Small.{u} (π₀ T) := small_of_surjective (f := π₀.mk) π₀.mk_surjective
  have : Small.{u} (π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)) :=
    small_of_surjective e.isQCatEquivalence.isSimplicialHomotopyEquivalence.mapPiZero_bijective.2
  exact small_of_surjective (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv x y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv x y).surjective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocallySmall (hom_small)


/-- 概要：局所小さい ∞ 圏の元の二対象間の同型全体の型は小さい。
方針：同型の順射による単射を元の小さい Hom へ入れる。
規約：同型の存在命題へ弱めず全同型を数える。
使われ方：引き戻しの小さい生成候補の添字。 -/
lemma IsLocallySmall.vertexIso_small {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall C) (x y : C _⦋0⦌) : Small.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) := by
  have := hC.hom_small x y
  apply small_of_injective (f := fun e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y ↦ e.hom)
  intro e f h
  exact Iso.ext h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocallySmall (vertexIso_small)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
