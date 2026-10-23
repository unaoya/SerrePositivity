module
public import SerrePositivity.KST.Fibration.ContractibleRestrictionComparison
public import SerrePositivity.KST.Fibration.ZeroStableHomExtension

/-! # 元の零値完全関手族の、指定部分族上で恒等となる全比較辺 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ指定部分を持つ元の零値関手族を、部分上で厳密に恒等の全可逆辺で結ぶ。 -/
def zeroStableHomFamilyRelativeComparison {C D : StableQCat.{u}} {T U : SSet.{u}}
    (i : T ⟶ U) [Mono i] (H G : U ⟶ (C ⟶[SSet.{u}] D))
    (hH : ∀ v, StableHomZeroVertex C D (H.app (Opposite.op ⦋0⦌) v))
    (hG : ∀ v, StableHomZeroVertex C D (G.app (Opposite.op ⦋0⦌) v))
    (hHG : i ≫ H = i ≫ G) : FixedRestrictionFunctorEdge i H G := by
  let Z := zeroStableHomSpace C D
  have hc := zeroStableHomSpace_isContractibleKan C D
  letI zeroRelativeTargetKan : KanComplex Z := hc.kanComplex
  let F := fullSubcomplexLift (StableHomZeroVertex C D) H hH
  let L := fullSubcomplexLift (StableHomZeroVertex C D) G hG
  let j := (fullSubcomplexOnVertices (C ⟶[SSet.{u}] D) (StableHomZeroVertex C D)).ι
  have hF : F ≫ j = H := fullSubcomplexLift_ι _ _ _
  have hL : L ≫ j = G := fullSubcomplexLift_ι _ _ _
  have hFL : i ≫ F = i ≫ L := by
    apply (cancel_mono j).1
    rw [Category.assoc, hF, Category.assoc, hL]
    exact hHG
  let E := contractibleRestrictionComparison i hc F L hFL
  exact hF ▸ hL ▸ E.postcomp j

end SerrePositivity.KST.Fibration
