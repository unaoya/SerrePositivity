module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecompositionInput

/-!
概要：指定全厳密可換 square の cone 比較入力を保持する。
方針：既存の元左包含の前合成入力を同じ零ホモトピー square に回収する。
規約：四つの元全比較と指定合成等号を保持する。
使われ方：元小模型の評価同型を保つ全実 gluing cone 比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma zeroInput
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    {M N M' N' : ModuleCategory R D}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : ModuleHomotopy R D (f ≫ b) (a ≫ g)) (hz : h.val = 0) :
    moduleConeHomotopyInput R D f g a b h =
      (eHomWhiskerRight (Complex R) a (moduleCone R D g)).f (-1)
        (moduleConeInlElement R D g) := by
  dsimp only [moduleConeHomotopyInput]
  rw [hz]
  change _ + ((eHomWhiskerLeft (Complex R) M (moduleConeInr R D g)).f (-1)).hom 0 = _
  rw [map_zero, add_zero]
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G F' G' : DGFunctor R P (RightModule R D))
  (α : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
  (l : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F F') (r : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G G')
  (hsq : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp α r = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp l β)
include hsq
local notation "f" => dgModuleNaturalConeArrow R D F G α
local notation "g" => dgModuleNaturalConeArrow R D F' G' β
local notation "a" => dgModuleNaturalConeArrow R D F F' l
local notation "b" => dgModuleNaturalConeArrow R D G G' r

/-- 概要：元全厳密 square の閉成分は同じ元実射で可換。
方針：全合成等号へ同じ閉射回収を適用する。
規約：元四辺の厳密等式。使われ方：同じ零ホモトピー square の入力。 -/
lemma dgModuleNaturalConeSquare_closed (x : P) : f x ≫ b x = a x ≫ g x :=
  (dgModuleNaturalConeArrow_comp R D F G G' α r x).symm.trans
    ((congrArg (fun t => dgModuleNaturalConeArrow R D F G' t x) hsq).trans
      (dgModuleNaturalConeArrow_comp R D F F' G' l β x))

/-- 概要：元可換 square の指定零ホモトピー。
方針：同じ閉成分の厳密可換等号を使用する。
規約：元四辺を変更しない。使われ方：全実 cone 比較の指定 square。 -/
def dgModuleNaturalConeSquareHomotopy (x : P) :
    ModuleHomotopy R D (f x ≫ b x) (a x ≫ g x) :=
  ⟨0, by rw [dgModuleNaturalConeSquare_closed R D F G F' G' α β l r hsq]; simp⟩

/-- 概要：既存前合成の指定元は同じ元可換 square の cone 入力そのもの。
方針：元前合成入力の回収と二つの零成分の定義を使用する。
規約：元次数 −1 元を保持。使われ方：全 cone 比較の実成分照合。 -/
lemma dgModuleNaturalConeSquareInput_recovery (x : P) :
    dgModuleNaturalConePrecompositionInput R D F F' G' l β x =
      moduleConeHomotopyInput R D (f x) (g x) (a x) (b x)
        (dgModuleNaturalConeSquareHomotopy R D F G F' G' α β l r hsq x) :=
  (dgModuleNaturalConePrecompositionInput_recovery R D F F' G' l β x).trans
    ((zeroInput R D _ (g x) (a x) (𝟙 _)
      (dgModuleNaturalConePrecompositionSquareHomotopy R D F F' G' l β x) rfl).trans
        (zeroInput R D (f x) (g x) (a x) (b x)
          (dgModuleNaturalConeSquareHomotopy R D F G F' G' α β l r hsq x) rfl).symm)
end SerrePositivity.KST.SConstruction
