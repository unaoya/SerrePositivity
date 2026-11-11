module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement

/-!
概要：底上の二つの比較射の共通の inner anodyne 置換。
方針：共通の始域の射影を因子分解し、二つの inner fibration の持ち上げで比較射を延長する。
規約：共通の始域の quasicategory 性は不要。延長した射には前合成同値性を記録する。
使われ方：Kerodon Theorem 5.3.5.6（Tag 037P）、scaffold の span を底上の quasicategory の比較へ置き換える。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：同じ底上の前合成同値の span は、inner fibration の共通の始域へ延長できる。
方針：射影の inner anodyne 分解に沿って二つの射を延長し、同値性の二対三則を使う。
規約：底が quasicategory なら、新しい共通の始域も quasicategory となる。
使われ方：Kerodon Theorem 5.3.5.6（Tag 037P）、weighted nerve と元の全空間の比較。 -/
lemma exists_innerFibration_comparison_span
    {A X Y S : SSet.{u}} (r : A ⟶ S) (p : X ⟶ S) (q : Y ⟶ S)
    [InnerFibration p] [InnerFibration q]
    (f : A ⟶ X) (g : A ⟶ Y) (hf : f ≫ p = r) (hg : g ≫ q = r)
    (ef : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) (eg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence g) :
    ∃ (Z : SSet.{u}) (i : A ⟶ Z) (t : Z ⟶ S) (a : Z ⟶ X) (b : Z ⟶ Y),
      innerAnodyneExtensions i ∧ InnerFibration t ∧ i ≫ t = r ∧
      i ≫ a = f ∧ i ≫ b = g ∧ a ≫ p = t ∧ b ≫ q = t ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence a ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence b := by
  obtain ⟨Z, i, t, hi, ht, hit⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_innerAnodyne_innerFibration_factorization r
  have := hi p (InnerFibration.mem (q := p))
  have := hi q (InnerFibration.mem (q := q))
  let sx : CommSq f i p t := ⟨hf.trans hit.symm⟩
  let sy : CommSq g i q t := ⟨hg.trans hit.symm⟩
  have ei := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne i hi
  refine ⟨Z, i, t, sx.lift, sy.lift, hi, ht, hit, sx.fac_left, sy.fac_left,
    sx.fac_right, sy.fac_right, ?_, ?_⟩
  · apply ei.cancel_left
    rwa [sx.fac_left]
  · apply ei.cancel_left
    rwa [sy.fac_left]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
