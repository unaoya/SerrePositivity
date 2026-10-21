module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaColimitNonemptyProducts
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafColimitEmptyProducts

/-!
概要：P_Σ の元の sifted 図式の前層余極限頂点が、元の有限積保存条件を満たすと証明する。
方針：空添字と非空有限添字の実際の全錐像の極限性を合わせる。
規約：実際に供給された前層余極限頂点を保持し、局所性を入力へ仮定しない。
使われ方：P_Σ の sifted 余極限閉性と元の前層余極限余錐の制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}} [IsSiftedInfinity B]
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  (q : JoinCocone (r ≫ sigmaPresheafInfinityInclusion C))
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))

include hq in
/-- 元の前層余極限の頂点関手は、元の全ての有限積全錐を保存する。 -/
lemma presheafColimitVertex_preservesFiniteProducts :
    PreservesFiniteProductsFromSmallSource (presheafCoconeVertexFunctor q) := by
  intro J _ p c hc
  classical
  rcases isEmpty_or_nonempty J with he | hn
  · have : IsEmpty J := he
    exact presheafColimitVertex_mapEmptyCone_isLimit r q hq c hc
  · have : Nonempty J := hn
    exact presheafColimitVertex_mapNonemptyCone_isLimit r q hq c hc

include hq in
/-- 元の指定前層余極限頂点は、元の P_Σ の有限積保存条件を満たす。 -/
lemma presheafColimitVertex_isSigmaPresheaf : IsSigmaPresheaf q.vertex :=
  presheafColimitVertex_preservesFiniteProducts r q hq

/-- 実際に供給した前層余極限頂点そのものは、元の P_Σ に属する。 -/
lemma sigmaPresheafAmbientColimit_isSigmaPresheaf :
    IsSigmaPresheaf (presheafCoherentColimitCone (r ≫ sigmaPresheafInfinityInclusion C)).vertex :=
  presheafColimitVertex_isSigmaPresheaf r _
    (presheafCoherentColimitCone_evaluation_isColimit _)

end SerrePositivity.InfinityCategories.HomotopyLimits
