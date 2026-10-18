module

public import SerrePositivity.InfinityCategories.F1.JoinDiagonalEndpoint
public import SerrePositivity.InfinityCategories.F1.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：空の始域を持つ射の relative join と写像円柱比較の同型性。
方針：空の左因子との join の単位則と、区間付き対角の終端の逆像を使う。
規約：空性は各次数の単体の型の IsEmpty として表す。
使われ方：Kerodon Example 5.2.3.4、Proposition 5.2.4.5 の始域の次元帰納の基底。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：空の左因子との join の右包含は同型。
方針：非零の切断は左の単体を要求するため存在せず、切断零だけが残る。
規約：全次数で左因子の単体が空であると仮定する。
使われ方：Kerodon Example 5.2.3.4、relative join の空の左因子の計算。 -/
instance relativeJoin_joinInr_emptySource_isIso (X Y : SSet.{u})
    [∀ n, IsEmpty (X.obj n)] : IsIso (joinInr X Y) := by
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
使われ方：Kerodon Example 5.2.3.4、始域の次元帰納の基底の終域。 -/
instance relativeJoinInr_emptySource_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    [∀ n, IsEmpty (X.obj n)] : IsIso (relativeJoinInr f (𝟙 Y)) := by
  have hp : IsPullback (joinInr X Y) (prismEndpoint 1 Y)
      (joinMap f (𝟙 Y)) (joinDiagonal Y) := by
    apply (isPullback_joinDiagonal_inr Y).flip.of_iso (Iso.refl Y)
      (asIso (joinInr X Y)) (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, asIso_hom, joinInr_joinMap,
        Category.id_comp]
    · simp
  have he : relativeJoinInr f (𝟙 Y) = hp.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [relativeJoinInr_fst, hp.isoPullback_hom_fst]
    · rw [relativeJoinInr, pullback.lift_snd, Category.id_comp, hp.isoPullback_hom_snd]
  rw [he]
  infer_instance

/-- 概要：空の係数の prism の端点包含は同型。
方針：始域と終域の各次数が空であることから全単射性を示す。
規約：両端点に適用する。
使われ方：Kerodon Proposition 5.2.4.5、空の始域の写像円柱の簡約。 -/
instance relativeJoin_prismEndpoint_empty_isIso (i : Fin 2) (X : SSet.{u})
    [∀ n, IsEmpty (X.obj n)] : IsIso (prismEndpoint i X) := by
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
使われ方：Kerodon Proposition 5.2.4.5、次元マイナス一の帰納の基底。 -/
instance relativeJoinCylinderComparison_emptySource_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    [∀ n, IsEmpty (X.obj n)] : IsIso (relativeJoinCylinderComparison f) := by
  let j := pushout.inr (prismEndpoint 1 X) f
  have : IsIso j := by dsimp only [j]; infer_instance
  have he : relativeJoinCylinderComparison f = inv j ≫ relativeJoinInr f (𝟙 Y) := by
    apply (cancel_epi j).1
    rw [IsIso.hom_inv_id_assoc]
    exact relativeJoinCylinderComparison_inr f
  rw [he]
  infer_instance

/-- 概要：空の始域で写像円柱比較は全 quasicategory への前合成の同値条件を満たす。
方針：比較が同型であることを一般の前合成の同値判定へ渡す。
規約：始域の単体の空性だけを要求する。
使われ方：Kerodon Proposition 5.2.4.5、セル分解による比較の基底。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_emptySource
    {X Y : SSet.{u}} (f : X ⟶ Y) [∀ n, IsEmpty (X.obj n)] :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f) :=
  isPrecompositionEquivalence_of_iso (asIso (relativeJoinCylinderComparison f))

end SerrePositivity.InfinityCategories
