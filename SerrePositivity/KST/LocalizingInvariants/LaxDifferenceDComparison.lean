module

public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroSourceComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxDAdjunction
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceExact

/-!
概要：元の差の関手と D 包含の合成は、元の q と全関手同型になる。
方針：包含の指定矢印の始域の零性と終域の厳密等式を使う。
規約：元の cofiber 選択と包含を保持。使われ方：ρ の可逆余単位の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma fromD_laxArrow_source_zero (x : D.obj _⦋0⦌) :
    IsZeroSourceArrow (((LaxInclusion.fromD p q) ≫ F2.laxPullbackArrow p.hom q.hom).app
      (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex ((((LaxInclusion.fromD p q) ≫ F2.laxPullbackArrow p.hom q.hom) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) x)
  rw [Category.assoc, F2.laxPullbackArrow_source, ← Category.assoc]
  change IsZeroVertex (((LaxInclusion.fromD p q ≫ (laxFst p q).hom) ≫ p.hom).app _ x)
  rw [LaxInclusion.fromD_fst]
  exact LaxInclusion.zeroC_post p x

lemma fromD_laxArrow_target :
    ((LaxInclusion.fromD p q) ≫ F2.laxPullbackArrow p.hom q.hom) ≫
      ArrowTarget.target E.obj = q.hom := by
  rw [Category.assoc]
  change LaxInclusion.fromD p q ≫
    (F2.laxPullbackArrow p.hom q.hom ≫ evaluateFunctorAt _) = q.hom
  rw [F2.laxPullbackArrow_target, ← Category.assoc]
  change (LaxInclusion.fromD p q ≫ (laxSnd p q).hom) ≫ q.hom = q.hom
  rw [LaxInclusion.fromD_snd, Category.id_comp]

/-- D 包含の後の元の差の関手は q と、全パラメータで同じ関手同型を持つ。 -/
def fromD_differenceIso : FunctorIso (LaxInclusion.fromD p q ≫ laxDifference p q) q.hom := by
  let a := F2.laxPullbackArrow p.hom q.hom
  have h : FunctorIso (LaxInclusion.fromD p q ≫ laxDifference p q)
      ((LaxInclusion.fromD p q ≫ a) ≫ CofiberFamily.cofiber E.obj (𝟙 _)) := by
    simpa only [laxDifference, Category.assoc] using
      FunctorIso.precomp (CofiberFamily.compositionIso E.obj a) (LaxInclusion.fromD p q)
  exact h ≪≫ universalCofiberZeroSourceIso E.obj _ (fromD_laxArrow_source_zero p q) ≪≫
    eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
      (fromD_laxArrow_target p q))

end SerrePositivity.KST.LocalizingInvariants
