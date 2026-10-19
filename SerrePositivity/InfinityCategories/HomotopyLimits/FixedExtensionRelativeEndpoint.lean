module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeFunctorPairRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedFiberSecondMap
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorInitialEvaluation

/-!
概要：初期値を固定する延長の終点制限は、二部分の同時制限の初期値 fiber である。
方針：同時制限の left fibration 性を同じ fiber に移し、一点評価の同型を合成する。
規約：結合した包含の単射性を実証するまで仮定を外さない。使われ方：根辺の終点評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A D C E B : SSet.{u}} (p : E ⟶ B) (β : A ⟶ B)
  (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β) (j : C ⟶ A)

/-- 同じ初期値の全延長を、指定した終端部分へ制限する。 -/
def fixedExtensionRelativeEndpoint : relativeFunctorExtensionSpace p β i v hv ⟶
    relativeFunctorSpace p (j ≫ β) :=
  relativeFunctorExtensionSpaceι p β i v hv ≫ relativeFunctorPre p β j

/-- 初期値と終端部分の包含の余積が単射なら、この制限は left fibration。 -/
instance fixedExtensionRelativeEndpoint_leftFibration [LeftFibration p]
    [Mono (coprod.desc i j)] : LeftFibration (fixedExtensionRelativeEndpoint p β i v hv j) := by
  have : LeftFibration (lift (relativeFunctorPre p β i) (relativeFunctorPre p β j)) :=
    inferInstanceAs (LeftFibration (relativeFunctorPairRestriction p β i j))
  exact inferInstanceAs (LeftFibration (fixedFiberSecondMap
    (relativeFunctorPre p β i) (relativeFunctorPre p β j) (relativeFunctorVertex p (i ≫ β) v hv)))

/-- 制限後も元の全パラメータ族を同じ部分で制限した raw な射を保持する。 -/
lemma fixedExtensionRelativeEndpoint_uncurry {T : SSet.{u}}
    (t : T ⟶ relativeFunctorExtensionSpace p β i v hv) :
    relativeFunctorUncurry (t ≫ fixedExtensionRelativeEndpoint p β i v hv j) =
      (j ▷ T) ≫ relativeFunctorUncurry (t ≫ relativeFunctorExtensionSpaceι p β i v hv) := by
  simpa only [fixedExtensionRelativeEndpoint, Category.assoc] using
    relativeFunctorUncurry_pre (t ≫ relativeFunctorExtensionSpaceι p β i v hv) j

end
end SerrePositivity.InfinityCategories.HomotopyLimits
