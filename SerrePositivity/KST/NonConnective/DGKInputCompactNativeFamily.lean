module
public import SerrePositivity.KST.NonConnective.DGKInputIndCompactGeneration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorSpace

/-!
概要：元の全 native dg Hom 作用を、同じ ν 値の compact 生成同値へ移す。
方針：元の Perf 全関手族を宇宙移送し、固定した生成逆射・順射で前後合成する。
規約：Indω の compact 生成元間の比較であり、D-8 の cone や K 構造辺とは同一視しない。
使われ方：K-7 d4 の全 native Hom と元の Yoneda 包含の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective


variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- 概要：元の全 native Perf 関手族を同じ ν 値の宇宙持ち上げ間へ送る。
方針：F1 正本の関手空間の宇宙移送を元の全族へ適用する。
規約：元の全高次入力を保持し、通常射の族へ離散化しない。
使われ方：同じ compact 生成元間の全 Hom 比較の入力。 -/
def dgKInputCompactNativeLiftedFamilyMap :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B) ⟶
    (ihom ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgKInputStableValue R A).obj)).obj
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (dgKInputStableValue R B).obj) :=
  (SSet.uliftFunctor.map (presentedPerfectDGNativeFamilyMap R A B)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceMap (dgKInputStableValue R A).obj (dgKInputStableValue R B).obj

/-- 概要：元の全 native Hom を同じ Indω の compact 生成元間の全関手族へ移す。
方針：元の ν 全族へ、始域の固定生成逆射と標的の固定生成順射を合成する。
規約：各 dg 射を独立に選び直さない。cone の全入力作用は別途照合する。
使われ方：K-7 d4 の生成同値と元の全高次 dg 作用の比較。 -/
def dgKInputCompactNativeFamilyMap :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B) ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
      Cardinal.aleph0 (dgKInputIndCompletion R A))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
        Cardinal.aleph0 (dgKInputIndCompletion R B)) :=
  dgKInputCompactNativeLiftedFamilyMap R A B ≫
    (pre (dgKInputCompactGenerationEquivalence R A).inv).app _ ≫
    (ihom _).map (dgKInputCompactGenerationEquivalence R B).hom

/-- 概要：同じ全 native 作用の包含後は、元の ν 全族と元の Yoneda の合成に厳密一致。
方針：後合成の関手性と、生成順射の元の包含への厳密回収を使う。
規約：全パラメータの射の等式であり、点別の同型に弱めない。
使われ方：K-7 d4 の元の全入力作用と compact 包含の照合。 -/
theorem dgKInputCompactNativeFamilyMap_inclusion :
    dgKInputCompactNativeFamilyMap R A B ≫
      (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{max (u + 1) v, max (u + 1) v + 1}
        Cardinal.aleph0 (dgKInputIndCompletion R B)) =
    dgKInputCompactNativeLiftedFamilyMap R A B ≫
      (pre (dgKInputCompactGenerationEquivalence R A).inv).app _ ≫
      (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda.{max (u + 1) v} Cardinal.aleph0 (dgKInputStableValue R B).obj) := by
  simp only [dgKInputCompactNativeFamilyMap, Category.assoc,
    ← CategoryTheory.Functor.map_comp, dgKInputCompactGenerationEquivalence_inclusion]

/-- 概要：任意の native 入力族への制限でも、同じ元の包含との全作用を厳密回収する。
方針：同じ全写像空間の等式を入力族へ前合成する。
規約：固定した A・B 間の全 Hom 族であり、構造辺 β の自然性はまだ結論しない。
使われ方：K-7 d4 の全パラメータ比較を実入力族へ適用する。 -/
theorem dgKInputCompactNativeFamilyMap_parameter_inclusion
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (presentedPerfectDGNativeParameter R A B)) :
    (a ≫ dgKInputCompactNativeFamilyMap R A B) ≫
      (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{max (u + 1) v, max (u + 1) v + 1}
        Cardinal.aleph0 (dgKInputIndCompletion R B)) =
    a ≫ dgKInputCompactNativeLiftedFamilyMap R A B ≫
      (pre (dgKInputCompactGenerationEquivalence R A).inv).app _ ≫
      (ihom _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda.{max (u + 1) v} Cardinal.aleph0 (dgKInputStableValue R B).obj) := by
  rw [Category.assoc, dgKInputCompactNativeFamilyMap_inclusion]

/-- 概要：同じ宇宙移送全族の各厳密 dg 点は、元の固定 ν 射を厳密回収する。
方針：元の Perf 全族の頂点公式と F1 の定値関手の宇宙移送を使う。
規約：別の入力射や ν の模型へ置換しない。
使われ方：全 native Hom 作用と元の実 dg 射の照合。 -/
theorem dgKInputCompactNativeLiftedFamilyMap_vertex (f : A ⟶ B) :
    (dgKInputCompactNativeLiftedFamilyMap R A B).app (Opposite.op ⦋0⦌)
      (ULift.up (perfDGInputVertexEquiv R A B f)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgKInputNuMap R f).hom) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp ((presentedPerfectDGNativeFamilyMap R A B).app
    (Opposite.op ⦋0⦌) (perfDGInputVertexEquiv R A B f)) = _
  rw [presentedPerfectDGNativeFamilyMap_vertex, dgKInputNuMap_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp_constant _ 0

/-- 概要：元の厳密 dg 射を、同じ compact 生成同値で両側から読み替える実射。
方針：固定 ν 射の宇宙移送に、元の生成逆射と順射を合成する。
規約：Indω の生成元間の射であり、cone の懸垂構造射とは区別する。
使われ方：K-7 d4 の全族の各元の dg 入力射への制限。 -/
def dgKInputCompactNativeMap (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
      Cardinal.aleph0 (dgKInputIndCompletion R A) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
        Cardinal.aleph0 (dgKInputIndCompletion R B) :=
  (dgKInputCompactGenerationEquivalence R A).inv ≫
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map (dgKInputNuMap R f).hom ≫
      (dgKInputCompactGenerationEquivalence R B).hom

/-- 概要：同じ全 native 入力族の指定点は元の厳密 dg 射の compact 読み替えそのもの。
方針：宇宙移送した全族の頂点回収に同じ前後合成を適用する。
規約：全族と点別射を独立に選ばない。
使われ方：K-7 d4 の元の入力射との厳密照合。 -/
theorem dgKInputCompactNativeFamilyMap_vertex (f : A ⟶ B) :
    (dgKInputCompactNativeFamilyMap R A B).app (Opposite.op ⦋0⦌)
      (ULift.up (perfDGInputVertexEquiv R A B f)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgKInputCompactNativeMap R A B f) := by
  change ((ihom _).map (dgKInputCompactGenerationEquivalence R B).hom).app
    (Opposite.op ⦋0⦌) (((pre (dgKInputCompactGenerationEquivalence R A).inv).app _).app
      (Opposite.op ⦋0⦌) ((dgKInputCompactNativeLiftedFamilyMap R A B).app
        (Opposite.op ⦋0⦌) (ULift.up (perfDGInputVertexEquiv R A B f)))) = _
  rw [dgKInputCompactNativeLiftedFamilyMap_vertex]
  rfl

end SerrePositivity.KST.NonConnective
