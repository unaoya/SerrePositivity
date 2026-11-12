module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories
public import SerrePositivity.KST.SConstruction.FunctorCofiberPreservation

/-!
概要：任意パラメーターの安定な関手圏と、元の後合成・制限・評価の完全関手を公開する。
方針：SConstruction の関手圏の安定性と点ごとの普遍性判定を読み取り専用で再利用する。
規約：有限形状への制限や追加の極限存在仮定は不要。
使われ方：全次元の分母の普遍基底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def stableFunctorCategory (K : SSet.{u}) (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} :=
  ⟨(ihom K).obj A.obj, inferInstance, inferInstance⟩

def exactFunctorMap (K : SSet.{u}) {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (stableFunctorCategory K A) (stableFunctorCategory K B) where
  hom := (ihom K).map F.hom
  isExact := {
    preservesZero := fun _ hz => SConstruction.functor_postcomp_isZeroVertex F.hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F.hom)) hz
    preservesCofiber := fun t ht => SConstruction.functor_postcomp_preserves_cofiber F.hom
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F.hom),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare F.hom⟩ t ht }

def exactFunctorRestriction {K L : SSet.{u}} (i : K ⟶ L) (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (stableFunctorCategory L A) (stableFunctorCategory K A) where
  hom := (pre i).app A.obj
  isExact := {
    preservesZero := fun _ hz => SConstruction.functor_reindex_isZeroVertex i hz
    preservesCofiber := fun t ht => SConstruction.functor_reindex_preserves_cofiber i t ht }

def exactFunctorEvaluation (K : SSet.{u}) (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (stableFunctorCategory K A) A where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k
  isExact := {
    preservesZero := fun _ hz => SConstruction.isZeroVertex_evaluateFunctorAt hz k
    preservesCofiber := fun t ht => (SConstruction.functor_zeroTriangle_pushout_iff t).mp ht k }

end SerrePositivity.KST.LocalizingInvariants
