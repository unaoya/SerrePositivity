module
public import SerrePositivity.KST.NonConnective.DGKInputCompactNativeFamily

/-!
概要：元の厳密 dg 射の恒等・合成を、同じ compact 生成同値の単位・余単位へ照合する。
方針：固定 ν の元の通常関手の保存則を使い、生成逆射の中間の往復だけを消去する。
規約：実射は全 native Hom 族の既存の頂点であり、高次の合成整合や β 自然性は主張しない。
使われ方：K-7 d4 の元の dg 射と compact 生成元間の作用の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] {A B C : PerfDGInput.{u, v} R}

/-- 概要：元の恒等 dg 射の compact 作用は、同じ生成同値の余単位で恒等と比較される。
方針：固定 ν 関手の恒等保存を元の生成逆射・順射の往復へ代入する。
規約：作用射を独立に選ばず、既存の全 native Hom 族の頂点を使う。
使われ方：K-7 d4 の恒等入力との照合。 -/
def dgKInputCompactNativeMap_idIso (A : PerfDGInput.{u, v} R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputCompactNativeMap R A A (𝟙 A)) (𝟙 _) := by
  have hν : (dgKInputNuMap R (𝟙 A)).hom = 𝟙 (dgKInputStableValue R A).obj := by
    rw [dgKInputNuMap_eq]
    exact congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R A) (dgKInputStableValue R A) => f.hom)
      ((presentedPerfectDGStableCategoryFunctor R).map_id A)
  unfold dgKInputCompactNativeMap
  rw [hν, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (dgKInputCompactGenerationEquivalence R A).invHomIso

/-- 概要：元の二つの厳密 dg 射の compact 作用の合成は、同じ元の合成射の作用と比較される。
方針：元の ν の厳密合成保存と中間生成同値の単位を前後合成する。
規約：同じ実射と生成同値を使う。全高次合成整合の証明とは区別する。
使われ方：K-7 d4 の元の厳密 dg 入力射での合成比較。 -/
def dgKInputCompactNativeMap_compIso (f : A ⟶ B) (g : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputCompactNativeMap R A B f ≫ dgKInputCompactNativeMap R B C g)
      (dgKInputCompactNativeMap R A C (f ≫ g)) := by
  have hν : (dgKInputNuMap R (f ≫ g)).hom =
      (dgKInputNuMap R f).hom ≫ (dgKInputNuMap R g).hom := by
    rw [dgKInputNuMap_eq, dgKInputNuMap_eq, dgKInputNuMap_eq]
    exact congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R A) (dgKInputStableValue R C) => f.hom)
      ((presentedPerfectDGStableCategoryFunctor R).map_comp f g)
  let F := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (dgKInputNuMap R f).hom
  let G := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (dgKInputNuMap R g).hom
  have e := ((dgKInputCompactGenerationEquivalence R B).homInvIso.precomp
    ((dgKInputCompactGenerationEquivalence R A).inv ≫ F)).postcomp
      (G ≫ (dgKInputCompactGenerationEquivalence R C).hom)
  unfold dgKInputCompactNativeMap
  rw [hν, CategoryTheory.Functor.map_comp]
  simpa only [F, G, Category.assoc, Category.comp_id, Category.id_comp] using e
end SerrePositivity.KST.NonConnective
