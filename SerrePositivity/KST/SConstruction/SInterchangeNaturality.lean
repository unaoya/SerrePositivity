module
public import SerrePositivity.KST.SConstruction.SDoubleInclusion
public import SerrePositivity.KST.SConstruction.SInterchangeStableIso
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SwapNaturality

/-! # 二重 S 交換の完全関手と添字制限に関する自然性
概要：二重 S の厳密な交換同型は完全関手と両 Ar 添字の面・退化に関して自然。
方針：単射な二重包含により内部 Hom の後合成・前合成の自然性を反映する。
規約：全単体での厳密等号。使われ方：多方向の S₁ の移動を反復実現へ降ろす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

/-- 二重 S の交換は入力の完全関手について厳密に自然。 -/
lemma sInterchangeStableIso_naturality (m n : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (sEndofunctor m).map ((sEndofunctor n).map f) ≫ (sInterchangeStableIso m n Y).hom =
      (sInterchangeStableIso m n X).hom ≫ (sEndofunctor n).map ((sEndofunctor m).map f) := by
  apply Subtype.ext
  change ((sEndofunctor m).map ((sEndofunctor n).map f)).val ≫ sInterchange m n Y.carrier =
    sInterchange m n X.carrier ≫ ((sEndofunctor n).map ((sEndofunctor m).map f)).val
  apply (cancel_mono (sDoubleInclusion n m Y.carrier)).mp
  rw [Category.assoc, sInterchange_doubleInclusion, ← Category.assoc,
    sDoubleInclusion_postcomp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.internalHomSwap_postcomp,
    ← Category.assoc, ← sInterchange_doubleInclusion]
  simpa only [Category.assoc] using (congrArg
    (fun h => sInterchange m n X.carrier ≫ h) (sDoubleInclusion_postcomp n m f)).symm

/-- 二重 S の交換は安定な入力の自己関手として自然同型。 -/
def sInterchangeEndofunctorIso (m n : ℕ) :
    sEndofunctor.{u} n ⋙ sEndofunctor m ≅ sEndofunctor m ⋙ sEndofunctor n :=
  NatIso.ofComponents (sInterchangeStableIso m n) (fun f => sInterchangeStableIso_naturality m n f)

/-- 外側の Ar 添字の制限は交換後の内側の制限と厳密に可換。 -/
lemma sInterchange_outerMap {m m' : ℕ} (n : ℕ) (X : StableModel.{u})
    (θ : Fin (m' + 1) →o Fin (m + 1)) :
    sMap (sConstruction n X.carrier) θ ≫ sInterchange m' n X.carrier =
      sInterchange m n X.carrier ≫ ((sEndofunctor n).map ((sEndofunctorMap θ).app X)).val := by
  apply (cancel_mono (sDoubleInclusion n m' X.carrier)).mp
  rw [Category.assoc, sInterchange_doubleInclusion, ← Category.assoc,
    sDoubleInclusion_outerMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.internalHomSwap_pre_left,
    ← Category.assoc, ← sInterchange_doubleInclusion]
  simpa only [Category.assoc] using (congrArg
    (fun h => sInterchange m n X.carrier ≫ h) (sDoubleInclusion_innerMap n X θ)).symm

/-- 内側の Ar 添字の制限は交換後の外側の制限と厳密に可換。 -/
lemma sInterchange_innerMap (m : ℕ) {n n' : ℕ} (X : StableModel.{u})
    (θ : Fin (n' + 1) →o Fin (n + 1)) :
    ((sEndofunctor m).map ((sEndofunctorMap θ).app X)).val ≫ sInterchange m n' X.carrier =
      sInterchange m n X.carrier ≫ sMap (sConstruction m X.carrier) θ := by
  apply (cancel_mono (sDoubleInclusion n' m X.carrier)).mp
  rw [Category.assoc, sInterchange_doubleInclusion, ← Category.assoc,
    sDoubleInclusion_innerMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre,
    ← Category.assoc, ← sInterchange_doubleInclusion]
  simpa only [Category.assoc] using (congrArg
    (fun h => sInterchange m n X.carrier ≫ h)
    (sDoubleInclusion_outerMap m X.carrier θ)).symm

end SerrePositivity.KST.SConstruction
