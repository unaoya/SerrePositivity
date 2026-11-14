module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CarrierScalarExtensionKFlat
public import SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestrictionSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.BaseChange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGNerveH0Naturality

/-!
# 厳密な係数拡大の複体 dg nerve

## 概要
HA §3.2.2 の係数拡大を全複体の dg nerve に施し、閉零射を項別に計算する。

## 方針
閉零射を次数零の余鎖として読み、純粋テンソル上で係数拡大を比較する。

## 規約
可換環準同型に平坦性を仮定しない。

## 使われ方
K 平坦な源で、同じ semifree augmentation を係数拡大した比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory DifferentialGraded CochainComplex HomComplex
open SerrePositivity.InfinityCategories
open SSet
open scoped Simplicial TensorProduct

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 係数拡大をすべての複体に施した dg nerve の写像。 -/
def complexExtensionNerve : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve T (Complex T) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChangeDG f) ≫ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerveRestrictScalarsIso f (Complex T)).hom

private lemma complexBaseChangeDG_map_ofHom {X Y : Complex S} (g : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChangeDG f |>.map X Y).f 0 (Cochain.ofHom g) =
      Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map g) := by
  let := f.toAlgebra
  change (ScalarExtension.homComparison f X Y).f 0 ((1 : T) ⊗ₜ[S] Cochain.ofHom g) =
    Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map g)
  apply Cochain.ext₀
  intro i
  apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((ScalarExtension.homComparison f X Y).f 0 ((1 : T) ⊗ₜ[S] Cochain.ofHom g)).v
      i i (add_zero i) ((1 : T) ⊗ₜ[S] x) =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map g).f i ((1 : T) ⊗ₜ[S] x)
  erw [ScalarExtension.homComparison_apply f X Y 0 i i (add_zero i)]
  rfl

private lemma complexBaseChangeDG_closedNerveHom {X Y : Complex S} (g : X ⟶ Y) (k : ℤ) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChangeDG f).map X Y).f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed S).map g) k) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed T).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map g)) k := by
  by_cases h : k = 0
  · subst k
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero]
    change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChangeDG f).map X Y).f 0
        (cycleFromUnit (homComplex S X Y) ((complexToClosed S).map g)).val =
      (cycleFromUnit (homComplex T ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).obj X) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).obj Y))
        ((complexToClosed T).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map g))).val
    rw [← complexClosedHomEquiv_cochain, ← complexClosedHomEquiv_cochain]
    change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChangeDG f).map X Y).f 0
        (Cochain.ofHom ((closedToComplex S).map ((complexToClosed S).map g))) =
      Cochain.ofHom ((closedToComplex T).map
        ((complexToClosed T).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map g)))
    rw [complexToClosed_map, complexToClosed_map]
    exact complexBaseChangeDG_map_ofHom f g
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ _ h, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ _ h, map_zero]

/-- 閉零射の列の係数拡大は、通常の複体の項別係数拡大に一致する。 -/
lemma complexClosedNerve_extension :
    (nerveMap (complexToClosed S) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion S (Complex S)) ≫
      complexExtensionNerve f =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f) ≫ nerveMap (complexToClosed T) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion T (Complex T) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro Γ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext rfl ?_
  apply heq_of_eq
  funext I a b k hI ha hb hk
  have hab : a ≤ b := by
    rw [ha, hb]
    exact I.min'_le _ (I.max'_mem _)
  let g := Γ.map (homOfLE hab)
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChangeDG f).map (Γ.obj a) (Γ.obj b)).f k
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed S).map g) k) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed T).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map g)) k
  exact complexBaseChangeDG_closedNerveHom f g k

/-- 半自由複体の係数拡大を全複体へ含めた写像は、全複体の写像に一致する。 -/
lemma derivedInfinityBaseChange_inclusion :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := T) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S) ≫ complexExtensionNerve f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rfl

private lemma extensionCochain_heq {X Y X' Y' : Complex S}
    (hX : X = X') (hY : Y = Y')
    {a : Homogeneous X Y 0} {b : Homogeneous X' Y' 0} (h : HEq a b) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChangeDG f).map X Y).f 0 a)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChangeDG f).map X' Y').f 0 b) := by
  subst X'
  subst Y'
  cases h
  rfl

/-- The closed chain map of an extended edge is the ordinary extension of its closed map. -/
lemma complexExtensionNerve_edgeChainMap
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))) x y) :
    (closedToComplex T).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (e.map ((truncation 2).map
      (complexExtensionNerve f)))) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map ((closedToComplex S).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)) := by
  let e' := e.map ((truncation 2).map (complexExtensionNerve f))
  apply Cochain.ofHom_injective
  change Cochain.ofHom (complexClosedHomEquiv T _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e')) =
    Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).map (complexClosedHomEquiv S _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)))
  rw [← complexBaseChangeDG_map_ofHom, complexClosedHomEquiv_cochain,
    complexClosedHomEquiv_cochain]
  change (closedHomEquiv T (Complex T) _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e')).val =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChangeDG f).map (x.obj 0) (y.obj 0)).f 0
      (closedHomEquiv S (Complex S) _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)).val
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle]
  apply eq_of_heq
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq e').trans ((extensionCochain_heq f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_source_obj e).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_target_obj e).symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq e)).symm)

end SerrePositivity.EInfinity.ComplexLimits
