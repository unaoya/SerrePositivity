module

public import SerrePositivity.InfinityCategories.Core.PinchedUniversal
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：trivial Kan fibration が右 pinched 写像空間上に誘導する射。
方針：部分複体上の族と始点の定値面を join 上で貼り、単射の rlp を使う。
規約：元の単体集合の quasicategory 性は持ち上げには不要。
使われ方：HTT §2.2、Kerodon §4.8.4 の同値の置換への充満忠実性の移行。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：trivial Kan fibration の右写像空間の射は任意の部分複体包含を持ち上げる。
方針：族を join に展開し、始点の定値面と貼り合わせて元の射で持ち上げる。
規約：始点と終点は元の単体集合の頂点に固定する。
使われ方：HTT §2.2、Kerodon §4.8.4 の写像空間の trivial Kan fibration 性。 -/
lemma pinchedHomMap_hasLiftingProperty_of_trivialKanFibration {A X Y : SSet.{u}}
    (p : X ⟶ Y) [TrivialKanFibration p] (x y : X _⦋0⦌) (A₀ : A.Subcomplex) :
    HasLiftingProperty A₀.ι (pinchedHomMap p x y) := by
  constructor
  intro a b sq
  let B₀ : (Δ[0] : SSet.{u}).Subcomplex := ⊥
  let hs := joinUnion_isPushout A₀ B₀
  let G := pinchedHomUncurry a
  let H : join A (B₀ : SSet.{u}) ⟶ X := SSet.const x
  let W := pinchedHomUncurry b
  have hw : joinMap (𝟙 (A₀ : SSet.{u})) B₀.ι ≫ G =
      joinMap A₀.ι (𝟙 (B₀ : SSet.{u})) ≫ H := by
    apply (cancel_epi (joinEmptyIso (A₀ : SSet.{u}) (Δ[0] : SSet.{u})).inv).1
    rw [joinEmptyIso_inv, ← Category.assoc, joinInl_joinMap, Category.id_comp,
      pinchedHomUncurry_inl]
    rw [SSet.comp_const, SSet.comp_const]
  let T := hs.desc G H hw
  have hG : joinUnionLeft A₀ B₀ ≫ T = G := hs.inl_desc _ _ _
  have hH : joinUnionRight A₀ B₀ ≫ T = H := hs.inr_desc _ _ _
  have hW : T ≫ p = (joinUnion A₀ B₀).ι ≫ W := by
    apply hs.hom_ext
    · rw [← Category.assoc, hG, ← Category.assoc, joinUnionLeft_ι]
      have h := congrArg pinchedHomUncurry sq.w
      rw [pinchedHomUncurry_postcomp, pinchedHomUncurry_precomp] at h
      exact h
    · rw [← Category.assoc, hH, ← Category.assoc, joinUnionRight_ι]
      apply (cancel_epi (joinEmptyIso A (Δ[0] : SSet.{u})).inv).1
      rw [joinEmptyIso_inv, SSet.const_comp, SSet.comp_const,
        ← Category.assoc, joinInl_joinMap, Category.id_comp, pinchedHomUncurry_inl]
  have := TrivialKanFibration.mem (p := p) (joinUnion A₀ B₀).ι inferInstance
  let t : CommSq T (joinUnion A₀ B₀).ι p W := ⟨hW⟩
  let L := t.lift
  have hleft : joinMap A₀.ι (𝟙 (Δ[0] : SSet.{u})) ≫ L = G := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft A₀ B₀ ≫ ((joinUnion A₀ B₀).ι ≫ L) = G
    rw [t.fac_left, hG]
  have hright : joinMap (𝟙 A) B₀.ι ≫ L = H := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight A₀ B₀ ≫ ((joinUnion A₀ B₀).ι ≫ L) = H
    rw [t.fac_left, hH]
  have hx : joinInl A Δ[0] ≫ L = SSet.const x := by
    have h := congrArg (fun f ↦ joinInl A (B₀ : SSet.{u}) ≫ f) hright
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp, SSet.comp_const] at h
    exact h
  have hy : joinInr A Δ[0] ≫ L = SSet.yonedaEquiv.symm y := by
    have h := congrArg (fun f ↦ joinInr (A₀ : SSet.{u}) Δ[0] ≫ f) hleft
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp] at h
    exact h.trans (pinchedHomUncurry_inr a)
  refine CommSq.HasLift.mk' { l := pinchedHomCurry L hx hy, fac_left := ?_, fac_right := ?_ }
  · apply pinchedHomUncurry_injective x y
    rw [pinchedHomUncurry_precomp, pinchedHomUncurry_curry]
    exact hleft
  · apply pinchedHomUncurry_injective _ _
    rw [pinchedHomUncurry_postcomp, pinchedHomUncurry_curry]
    exact t.fac_right

/-- 概要：trivial Kan fibration は右 pinched 写像空間上でも trivial Kan fibration。
方針：任意の部分複体包含の持ち上げを境界に適用する。
規約：元の始域・終域の quasicategory 性は不要。
使われ方：HTT §2.2、Kerodon §4.8.4 の充満忠実性。 -/
instance pinchedHomMap_trivialKanFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [TrivialKanFibration p] (x y : X _⦋0⦌) : TrivialKanFibration (pinchedHomMap p x y) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  exact pinchedHomMap_hasLiftingProperty_of_trivialKanFibration p x y (boundary n)

/-- 概要：quasicategory 間の trivial Kan fibration は充満忠実。
方針：右写像空間の射の trivial Kan fibration 性から実際のホモトピー逆を選ぶ。
規約：充満忠実性は A3e の写像空間での定義。
使われ方：Kerodon §4.8.4 の置換への充満忠実性の移行。 -/
lemma isFullyFaithful_of_trivialKanFibration {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) [TrivialKanFibration p] : IsFullyFaithful p := by
  intro x y
  exact (isQCatEquivalence_of_trivialKanFibration (pinchedHomMap p x y)).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
