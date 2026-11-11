module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
public import SerrePositivity.KST.NonConnective.DGKInputCompactNativeLiftedComposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoTensor

/-!
概要：元の全 native 入力の二項合成を、同じ compact 生成元間の全族で比較する。
方針：中間生成同値の単位を全関手空間へ写し、元の厳密全族合成等式へ接続する。
規約：元の全高次入力を保持する。三項以上の整合性や β 自然性の完成は主張しない。
使われ方：K-7 d4 の全 native Hom の合成比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A B C : PerfDGInput.{u, v} R)

/-- 概要：同じ compact 生成元間の全 native 作用の二項合成は、元の全入力合成の作用と関手同型。
方針：中間生成同値の同じ単位を全パラメータへ写し、元の厳密全族合成を使う。
規約：全高次入力の積上の関手同型。点ごとの同型や高次整合性で代用しない。
使われ方：K-7 d4 の元の合成入力と compact 生成元間の作用の照合。 -/
def dgKInputCompactNativeFamilyMap_compIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgKInputCompactNativeFamilyMap R A B ⊗ₘ dgKInputCompactNativeFamilyMap R B C) ≫
        MonoidalClosed.comp _ _ _)
      (dgKInputCompactNativeParameterComp R A B C ≫ dgKInputCompactNativeFamilyMap R A C) := by
  let X := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
    Cardinal.aleph0 (dgKInputIndCompletion R A)
  let Y := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
    (dgKInputStableValue R B).obj
  let Z := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
    Cardinal.aleph0 (dgKInputIndCompletion R C)
  let F := dgKInputCompactNativeLiftedFamilyMap R A B ≫
    (pre (dgKInputCompactGenerationEquivalence R A).inv).app Y
  let G := dgKInputCompactNativeLiftedFamilyMap R B C ≫
    (ihom Y).map (dgKInputCompactGenerationEquivalence R C).hom
  let eB := dgKInputCompactGenerationEquivalence R B
  have eF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ (ihom X).map (eB.hom ≫ eB.inv)) F := by
    simpa only [Functor.map_id, Category.comp_id] using!
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (eB.homInvIso.map_post X) F
  have eFG := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoTensor eF
    (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)))).postcomp (MonoidalClosed.comp X Y Z)
  have hL :
      (dgKInputCompactNativeFamilyMap R A B ⊗ₘ dgKInputCompactNativeFamilyMap R B C) ≫
          MonoidalClosed.comp _ _ _ =
      ((F ≫ (ihom X).map (eB.hom ≫ eB.inv)) ⊗ₘ G) ≫ MonoidalClosed.comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro p
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  have hR : (F ⊗ₘ G) ≫ MonoidalClosed.comp X Y Z =
      dgKInputCompactNativeParameterComp R A B C ≫ dgKInputCompactNativeFamilyMap R A C := by
    unfold dgKInputCompactNativeFamilyMap
    rw [← Category.assoc, ← Category.assoc, ← dgKInputCompactNativeLiftedFamilyMap_comp]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro p
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [hL, ← hR]
  exact eFG


/-- 概要：任意の同じパラメータ族の二つの native 入力に、元の全二項合成比較を制限する。
方針：同じ全族比較を元の二つのパラメータ射の組で前合成する。
規約：比較を点別に選び直さない。
使われ方：K-7 d4 の全入力族と単体的制限への照合。 -/
def dgKInputCompactNativeFamilyMap_compParameterIso
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B))
    (b : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R B C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgKInputCompactNativeFamilyMap_compIso R A B C) (lift a b)

/-- 概要：任意族の二項合成比較の再制限は、元の再制限族の同じ比較そのもの。
方針：正本の前合成合成則と元の組の射の自然性を使う。
規約：同じ関手同型の等式であり、各点での存在に弱めない。
使われ方：K-7 d4 の全二項入力パラメータに対する自然性。 -/
theorem dgKInputCompactNativeFamilyMap_compParameterIso_precomp
    {S T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B))
    (b : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R B C)) (r : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgKInputCompactNativeFamilyMap_compParameterIso R A B C a b) r =
      dgKInputCompactNativeFamilyMap_compParameterIso R A B C (r ≫ a) (r ≫ b) := by
  unfold dgKInputCompactNativeFamilyMap_compParameterIso
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp]
  rfl

end SerrePositivity.KST.NonConnective
