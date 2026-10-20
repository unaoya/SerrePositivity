module

public import SerrePositivity.InfinityCategories.F1.FullyFaithfulIsoRecovery
public import SerrePositivity.InfinityCategories.F1.CoherentReconstructionHomRecovery

/-!
概要：全空間へ回収した復元同型は、元の scaffold の標準 Hom の族の同型を保つ。
方針：充満忠実な後合成の回収の往復則を実際の復元同型へ適用する。
規約：同じ始域・標的の同型の存在だけで代用しない。
使われ方：weighted nerve と反転 unstraightening の共同比較の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

local instance {B : SSet.{u}} :
    ∀ X Y : (LeftFibrationObject B)ᵒᵖ, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 回収した全空間の復元同型は、元の scaffold の同じ全標的の Hom の族の同型へ戻る。 -/
lemma leftStrictTransportReconstructionOppositeIso_testFamily
    (C : Type u) [Category.{u} C] :
    (leftStrictTransportReconstructionOppositeIso C).postcomp
      (leftFibrationHomTestFamily (nerve C)) =
      leftStrictTransportReconstructionHomFamilyIso C := by
  unfold leftStrictTransportReconstructionOppositeIso
  exact (leftFibrationHomTestFamily_isFullyFaithful (nerve C)).preimageFunctorIso_postcomp _

end SerrePositivity.InfinityCategories
