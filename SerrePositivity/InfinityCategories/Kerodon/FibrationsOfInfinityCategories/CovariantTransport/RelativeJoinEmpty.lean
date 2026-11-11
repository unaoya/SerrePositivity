module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonalEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：空の始域を持つ射の relative join と写像円柱比較の同型性。
方針：空の左因子との join の単位則と、区間付き対角の終端の逆像を使う。
規約：空性は各次数の単体の型の IsEmpty として表す。
使われ方：Kerodon Example 5.2.3.4（Tag 0245）、Proposition 5.2.4.5（Tag 024R） の始域の次元帰納の基底。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：空の左因子との join の右包含は同型。
方針：非零の切断は左の単体を要求するため存在せず、切断零だけが残る。
規約：全次数で左因子の単体が空であると仮定する。
使われ方：Kerodon Example 5.2.3.4（Tag 0245）、relative join の空の左因子の計算。 -/
instance relativeJoin_joinInr_emptySource_isIso (X Y : SSet.{u})
    [∀ n, IsEmpty (X.obj n)] : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  constructor
  · intro x y h
    exact congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h).2)
  · rintro ⟨⟨l, hl⟩, x, y⟩
    cases l with
    | zero => exact ⟨y, by cases x; rfl⟩
    | succ l =>
      change X _⦋l⦌ at x
      exact isEmptyElim x

/-- 概要：空の始域を持つ射の relative join の右包含は同型。
方針：対角の終端の pullback に通常の join の単位同型を適用する。
規約：右因子は底 Y の恒等射。
使われ方：Kerodon Example 5.2.3.4（Tag 0245）、始域の次元帰納の基底の終域。 -/
instance relativeJoinInr_emptySource_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    [∀ n, IsEmpty (X.obj n)] : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 Y)) := by
  have hp : IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPullback_joinDiagonal_inr Y).flip.of_iso (Iso.refl Y)
      (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y)) (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, asIso_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
        Category.id_comp]
    · simp
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 Y) = hp.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst, hp.isoPullback_hom_fst]
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr, pullback.lift_snd, Category.id_comp, hp.isoPullback_hom_snd]
  rw [he]
  infer_instance

/-- 概要：空の係数の prism の端点包含は同型。
方針：始域と終域の各次数が空であることから全単射性を示す。
規約：両端点に適用する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、空の始域の写像円柱の簡約。 -/
instance relativeJoin_prismEndpoint_empty_isIso (i : Fin 2) (X : SSet.{u})
    [∀ n, IsEmpty (X.obj n)] : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i X) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  constructor
  · intro x
    exact isEmptyElim x
  · intro z
    exact isEmptyElim z.2

/-- 概要：空の始域では写像円柱から relative join への比較は同型。
方針：写像円柱の右包含と relative join の右包含の同型性を比較の式に使う。
規約：終域 Y の有限性や quasicategory 性は不要。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、次元マイナス一の帰納の基底。 -/
instance relativeJoinCylinderComparison_emptySource_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    [∀ n, IsEmpty (X.obj n)] : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f) := by
  let j := pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f
  have : IsIso j := by dsimp only [j]; infer_instance
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f = inv j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 Y) := by
    apply (cancel_epi j).1
    rw [IsIso.hom_inv_id_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr f
  rw [he]
  infer_instance

/-- 概要：空の始域で写像円柱比較は全 quasicategory への前合成の同値条件を満たす。
方針：比較が同型であることを一般の前合成の同値判定へ渡す。
規約：始域の単体の空性だけを要求する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セル分解による比較の基底。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_emptySource
    {X Y : SSet.{u}} (f : X ⟶ Y) [∀ n, IsEmpty (X.obj n)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
