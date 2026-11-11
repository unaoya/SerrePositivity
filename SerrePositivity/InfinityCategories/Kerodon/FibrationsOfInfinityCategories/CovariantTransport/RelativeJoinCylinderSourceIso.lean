module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinEmpty
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CellularNaturalComparison

/-!
概要：始域の同型による写像円柱比較の同値条件の移送。
方針：Over 圏の同型と比較の自然性を使い、両関手の像の同型を打ち消す。
規約：共通の終域を厳密に保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、空の骨格および有限次元の境界の帰納。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：Over 圏の同型を通じて自然な比較の同値条件を移せる。
方針：二つの関手で写した同型と比較の自然性に二つの合成の同値判定を使う。
規約：関手の単射や余極限の保存は要求しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、骨格の表示の変更。 -/
lemma isPrecompositionEquivalence_over_natComponent_of_iso
    {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (t : F ⟶ G) {A B : Over S} (e : A ≅ B)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app B)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app A) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (F.mapIso e)).comp hB
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map e.hom ≫ t.app B) at h
  rw [t.naturality e.hom] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (G.mapIso e)).cancel_right h

/-- 概要：始域の同型で前合成しても写像円柱比較の同値条件は変わらない。
方針：構造射を保つ Over 圏の同型とその逆を使う。
規約：e は通常の単体集合の同型。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、初期骨格と全体に一致する骨格の移送。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_sourceIso_iff
    {X Y S : SSet.{u}} (e : X ≅ Y) (f : Y ⟶ S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (e.hom ≫ f)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f) := by
  let e₀ : Over.mk (e.hom ≫ f) ≅ Over.mk f := Over.isoMk e rfl
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparisonNat S
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (Over.mk (e.hom ≫ f))) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (Over.mk f))
  constructor
  · intro h
    exact isPrecompositionEquivalence_over_natComponent_of_iso t e₀.symm h
  · intro h
    exact isPrecompositionEquivalence_over_natComponent_of_iso t e₀ h

/-- 概要：有限次元の単体集合では初期対象に相対的な十分大きい骨格の包含は同型。
方針：骨格が全体の部分複体に一致することを使う。
規約：HasDimensionLT d に合わせ、d 未満の次元の骨格を取る。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界の比較を小さい始域の次元から取り出す。 -/
instance relativeJoin_initialSkeleton_ι_isIso (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] :
    IsIso (skeletonOfMono (initial.to X) d).ι := by
  have he : skeletonOfMono (initial.to X) d = ⊤ := by
    change Subcomplex.range (initial.to X) ⊔ X.skeleton d = ⊤
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.skeleton_eq_top_of_hasDimensionLT X d, sup_top_eq]
  rw [he]
  infer_instance

/-- 概要：初期対象を始域とする円柱比較は同値条件を満たす。
方針：各次数の評価が初期対象を保つことから空の始域の比較へ移す。
規約：選ばれた初期対象の表示に依存しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、零骨格の比較の基底。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_isInitialSource
    {X S : SSet.{u}} (f : X ⟶ S) (hX : IsInitial X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f) := by
  let (n : SimplexCategoryᵒᵖ) : IsEmpty (X.obj n) :=
    (Types.initial_iff_empty _).mp
      ⟨IsInitial.isInitialObj ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n) _ hX⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_emptySource f

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
