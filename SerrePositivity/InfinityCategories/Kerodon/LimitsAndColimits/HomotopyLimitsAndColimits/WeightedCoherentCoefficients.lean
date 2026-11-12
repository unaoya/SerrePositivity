module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.CoherentPathMinimum
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve

/-!
概要：反転した係数の weighted nerve のデータを左 cone の Hom の射へ評価する。
方針：初区間の係数の反転を戻し、最初の正頂点の座標を前合成する。
規約：Kan 性なしでの実際の射と、係数図式の合成作用への整合性を扱う。
使われ方：HTT 4.2.4.1、Kerodon §7.5.4（Tag 03B5） の coherent な錐の比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SimplicialThickening CartesianMonoidalCategory MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：反転した空間に値を持つ simplex の射を反転した標準単体からの射へ戻す。
方針：射を反転して二重反転の標準同型を合成する。
規約：始域は Δ[n] の反転、終域は元の X。
使われ方：HTT 4.2.4.1 の weighted nerve の係数の評価。 -/
def reflectedSimplexMap {X : SSet.{u}} {n : ℕ} (τ : Δ[n] ⟶ X.op) : Δ[n].op ⟶ X :=
  SSet.opFunctor.map τ ≫ SSet.opFunctorCompOpFunctorIso.hom.app X

/-- 概要：係数の反転を戻す操作は標準単体の前合成と可換。
方針：反転関手の合成則を用いる。
規約：前合成の射は任意の単体集合の射。
使われ方：HTT 4.2.4.1 の初区間の制限との整合性。 -/
lemma reflectedSimplexMap_pre {X : SSet.{u}} {m n : ℕ}
    (a : Δ[m] ⟶ Δ[n]) (τ : Δ[n] ⟶ X.op) :
    reflectedSimplexMap (a ≫ τ) = SSet.opFunctor.map a ≫ reflectedSimplexMap τ := by
  simp only [reflectedSimplexMap, CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：係数の反転を戻す操作は元の空間の射への後合成と可換。
方針：二重反転の標準同型の自然性を使う。
規約：X・Y の Kan 性を仮定しない。
使われ方：HTT 4.2.4.1 の係数図式の射の作用。 -/
lemma reflectedSimplexMap_post {X Y : SSet.{u}} {n : ℕ}
    (τ : Δ[n] ⟶ X.op) (f : X ⟶ Y) :
    reflectedSimplexMap (τ ≫ SSet.opFunctor.map f) = reflectedSimplexMap τ ≫ f := by
  simp only [reflectedSimplexMap, CategoryTheory.Functor.map_comp, Category.assoc]
  have h : SSet.opFunctor.map (SSet.opFunctor.map f) ≫
      SSet.opFunctorCompOpFunctorIso.hom.app Y =
      SSet.opFunctorCompOpFunctorIso.hom.app X ≫ f :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality f
  rw [h]

/-- 概要：最小点の座標は正の切断点での path 合成の後半を無視する。
方針：各 simplex の頂点で最小点の合成則を使う。
規約：初区間の包含を反転した標準単体の射を明示する。
使われ方：HTT 4.2.4.1 の左 cone の豊穣合成則。 -/
lemma pathFirstMinimumMap_comp {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    eComp SSet
      (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j =
    fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap i ≫
      SSet.opFunctor.map (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val h)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro k
  change (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j).app d
    ((eComp SSet
      (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)))).down.toOrderHom k =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val h).toOrderHom
      ((SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap i).app d P)).down.toOrderHom k)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap_apply]
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum
    (@CategoryStruct.comp (SimplicialThickening (ULift.{u} (Fin (n + 2)))) _
      ⟨ULift.up 0⟩ ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩
      (P.obj k.rev) (Q.obj k.rev))).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum (P.obj k.rev)).val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum_comp]

variable {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}}
  {n : ℕ} {σ : ComposableArrows I n}

/-- 概要：weighted nerve の反転した係数の自然性を元の係数の射として表す。
方針：自然変換の可換図式の両側を反転し、前後合成の整合性を使う。
規約：初区間 i→j の射を通常の順序射として指定する。
使われ方：HTT 4.2.4.1 の coherent Hom の合成への係数の整合性。 -/
lemma reflectedWeightedCoefficient_naturality
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor)
    (i j : Fin (n + 1)) (h : i ≤ j) :
    reflectedSimplexMap (τ.app i) ≫ H.map (σ.map (homOfLE h)) =
      SSet.opFunctor.map (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val h)) ≫
        reflectedSimplexMap (τ.app j) := by
  have ht := congrArg (fun t : Δ[i.val] ⟶ (H.obj (σ.obj j)).op ↦ reflectedSimplexMap t)
    (τ.naturality (homOfLE h))
  change reflectedSimplexMap
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val h) ≫ τ.app j) =
      reflectedSimplexMap (τ.app i ≫ SSet.opFunctor.map (H.map (σ.map (homOfLE h)))) at ht
  rw [reflectedSimplexMap_pre, reflectedSimplexMap_post] at ht
  exact ht.symm

/-- 概要：weighted nerve の反転した係数を最初の正頂点で評価する射。
方針：最小点の反転初区間への射に、反転を戻した係数を後合成する。
規約：終点 j.succ の Hom は元の H(σj) に値を持つ。
使われ方：HTT 4.2.4.1 の左 cone の非定値 Hom の作用。 -/
noncomputable def weightedCoherentCoefficient
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor) (j : Fin (n + 1)) :
    nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      H.obj (σ.obj j) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫ reflectedSimplexMap (τ.app j)

/-- 概要：評価した係数は path の合成を係数図式の射の作用へ写す。
方針：最小点の合成則の後で、反転を戻した係数の自然性を使う。
規約：Kan 性を仮定せず、単体集合の射の厳密な等式を与える。
使われ方：HTT 4.2.4.1 の coherent な cone の豊穣合成の非定値部分。 -/
lemma weightedCoherentCoefficient_comp
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor)
    (i j : Fin (n + 1)) (h : i ≤ j) :
    eComp SSet
      (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ weightedCoherentCoefficient τ j =
    fst _ _ ≫ weightedCoherentCoefficient τ i ≫ H.map (σ.map (homOfLE h)) := by
  dsimp only [weightedCoherentCoefficient]
  rw [← Category.assoc, pathFirstMinimumMap_comp i j h, Category.assoc,
    Category.assoc, ← reflectedWeightedCoefficient_naturality τ i j h]
  simp only [Category.assoc]


/-- 概要：評価した係数は weighted nerve の全ての添字変換と可換。
方針：最小点の射の自然性と反転を戻す操作の前合成則を使う。
規約：α は面・退化を含む任意の単体圏の射。
使われ方：HTT 4.2.4.1 の coherent な cone の全次数の整合性。 -/
lemma weightedCoherentCoefficient_reindex {m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor) (j : Fin (m + 1)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫
      weightedCoherentCoefficient τ (α.toOrderHom j) =
    weightedCoherentCoefficient (H := H)
      (σ := (SimplexCategory.toCat.map α).toFunctor ⋙ σ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction.{u} α ≫
        CategoryTheory.Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor τ) j := by
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap (α.toOrderHom j) ≫
        reflectedSimplexMap (τ.app (α.toOrderHom j))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫ reflectedSimplexMap
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α j) ≫ τ.app (α.toOrderHom j))
  rw [reflectedSimplexMap_pre, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap_reindex]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
