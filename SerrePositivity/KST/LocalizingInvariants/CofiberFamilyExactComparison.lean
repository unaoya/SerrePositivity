module

public import SerrePositivity.KST.LocalizingInvariants.CofiberExactNaturality

/-!
概要：任意の元の矢印族の cofiber は、完全関手による後合成と全関手同型で可換。
方針：元の族と普遍 cofiber の比較を、普遍 cofiber の完全自然性の前後に合成する。
規約：元の選択された cofiber を保つ。使われ方：lax 随伴余単位の cofiber の両射影。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable {X Y A : SSet.{u}} [Quasicategory X] [IsStable X]
  [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F]
  (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

def familyExactComparison : FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X a ≫ F)
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber Y (a ≫ (ihom (Δ[1] : SSet.{u})).map F)) := by
  have h := FunctorIso.postcomp (compositionIso X a) F
  have e : FunctorIso ((a ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X (𝟙 _)) ≫ F)
      ((a ≫ (ihom (Δ[1] : SSet.{u})).map F) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber Y (𝟙 _)) := by
    simpa only [Category.assoc] using FunctorIso.precomp (exactNaturality F) a
  exact h ≪≫ e ≪≫ (compositionIso Y (a ≫ (ihom (Δ[1] : SSet.{u})).map F)).symm

end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
