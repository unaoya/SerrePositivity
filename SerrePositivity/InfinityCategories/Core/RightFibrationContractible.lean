module

public import SerrePositivity.InfinityCategories.Core.PrismFilling

/-!
概要：可縮な fiber を持つ右ファイブレーションの trivial Kan fibration 性。
方針：標準単体へ引き戻し、先頭の fiber と prism の充填を使う。
規約：base の quasicategory 性は仮定しない。
使われ方：Kerodon Proposition 4.4.2.14、Lemma 4.4.2.15。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右ファイブレーションを引き戻した第二射影も右ファイブレーション。
方針：rlp の基底変換に対する閉性を使う。
規約：任意の単体集合の射に沿う引き戻し。
使われ方：Kerodon Lemma 4.4.2.15 の base の標準単体への還元。 -/
instance rightFibration_pullback_snd {E B A : SSet.{u}} (p : E ⟶ B) (f : A ⟶ B)
    [RightFibration p] : RightFibration (pullback.snd p f) :=
  ⟨rightFibrations.pullback_snd p f (RightFibration.mem (p := p))⟩

/-- 概要：引き戻した射の頂点上の fiber は、元の対応する fiber が可縮なら可縮。
方針：元の fiber で境界を充填して定値の第二成分と合わせる。
規約：ファイブレーション性を必要としない。
使われ方：Kerodon Proposition 4.4.2.14 の標準単体への引き戻し。 -/
lemma vertexFiber_pullback_isContractibleKan {E B A : SSet.{u}}
    (p : E ⟶ B) (f : A ⟶ B) (b : A _⦋0⦌)
    (hc : IsContractibleKan (vertexFiber p (f.app (Opposite.op ⦋0⦌) b))) :
    IsContractibleKan (vertexFiber (pullback.snd p f) b) := by
  intro n a
  let q := pullback.snd p f
  let ι := vertexFiberι q b
  have ha : (a ≫ ι ≫ pullback.fst p f) ≫ p =
      SSet.const (f.app (Opposite.op ⦋0⦌) b) := by
    rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc ι, vertexFiberι_comp, SSet.const_comp, SSet.comp_const]
  let a' := vertexFiberLift p (f.app (Opposite.op ⦋0⦌) b)
    (a ≫ ι ≫ pullback.fst p f) ha
  obtain ⟨F, hF⟩ := hc n a'
  let ι' := vertexFiberι p (f.app (Opposite.op ⦋0⦌) b)
  have hw : (F ≫ ι') ≫ p = (SSet.const b : (Δ[n] : SSet.{u}) ⟶ A) ≫ f := by
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
  let L := pullback.lift (F ≫ ι') (SSet.const b) hw
  have hL : L ≫ q = SSet.const b := pullback.lift_snd _ _ _
  refine ⟨vertexFiberLift q b L hL, ?_⟩
  apply vertexFiber_hom_ext q b
  rw [Category.assoc, vertexFiberLift_ι]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hF]
    exact vertexFiberLift_ι _ _ _ _
  · rw [Category.assoc, hL, SSet.comp_const, Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 概要：最初の fiber が可縮な右ファイブレーションは標準単体の境界を持ち上げる。
方針：正次元では prism の証明、零次元では fiber の非空性を使う。
規約：base の射は恒等射。
使われ方：Kerodon Lemma 4.4.2.15 の右ファイブレーション版。 -/
lemma rightFibration_fillBoundary_over_stdSimplex {E : SSet.{u}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{u})) [RightFibration p]
    (hc : IsContractibleKan (vertexFiber p (stdSimplex.obj₀Equiv.symm 0)))
    (a : (boundary n : SSet.{u}) ⟶ E) (ha : a ≫ p = (boundary n).ι) :
    ∃ F : (Δ[n] : SSet.{u}) ⟶ E, (boundary n).ι ≫ F = a ∧ F ≫ p = 𝟙 _ := by
  cases n with
  | zero =>
    obtain ⟨v⟩ := hc.nonempty
    exact ⟨SSet.yonedaEquiv.symm v.val, boundary.hom_ext₀,
      stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  | succ n => exact rightFibration_fillBoundary_over_stdSimplex_succ n p hc a ha

/-- 概要：全ての頂点上の fiber が可縮な右ファイブレーションは trivial Kan fibration。
方針：境界の持ち上げ問題を base の標準単体へ引き戻して解く。
規約：base の quasicategory 性は不要。
使われ方：Kerodon Proposition 4.4.2.14 の右側の逆方向。 -/
lemma rightFibration_trivialKanFibration_of_contractible_fibers {E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (hc : ∀ b : B _⦋0⦌, IsContractibleKan (vertexFiber p b)) :
    TrivialKanFibration p := by
  apply (trivialKanFibration_iff_boundary p).2
  intro n
  constructor
  intro a b sq
  let q := pullback.snd p b
  let a' := pullback.lift a (boundary n).ι sq.w
  have hq : IsContractibleKan (vertexFiber q (stdSimplex.obj₀Equiv.symm 0)) :=
    vertexFiber_pullback_isContractibleKan p b _ (hc _)
  obtain ⟨F, hF, hFp⟩ := rightFibration_fillBoundary_over_stdSimplex n q hq a'
    (pullback.lift_snd _ _ _)
  refine CommSq.HasLift.mk' { l := F ≫ pullback.fst p b, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, hF, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hFp, Category.id_comp]

end SerrePositivity.InfinityCategories
