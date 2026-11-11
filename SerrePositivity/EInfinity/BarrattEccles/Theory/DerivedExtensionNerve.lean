module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CarrierScalarExtensionKFlat
public import SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestrictionSource
public import SerrePositivity.InfinityCategories.Derived.BaseChange
public import SerrePositivity.InfinityCategories.Derived.DGNerveH0Naturality

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
open DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial TensorProduct

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 係数拡大をすべての複体に施した dg nerve の写像。 -/
def complexExtensionNerve : dgNerve S (Complex S) ⟶ dgNerve T (Complex T) :=
  dgNerve.map (complexBaseChangeDG f) ≫ (dgNerveRestrictScalarsIso f (Complex T)).hom

private lemma complexBaseChangeDG_map_ofHom {X Y : Complex S} (g : X ⟶ Y) :
    (complexBaseChangeDG f |>.map X Y).f 0 (Cochain.ofHom g) =
      Cochain.ofHom ((complexBaseChange f).map g) := by
  let := f.toAlgebra
  change (ScalarExtension.homComparison f X Y).f 0 ((1 : T) ⊗ₜ[S] Cochain.ofHom g) =
    Cochain.ofHom ((complexBaseChange f).map g)
  apply Cochain.ext₀
  intro i
  apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((ScalarExtension.homComparison f X Y).f 0 ((1 : T) ⊗ₜ[S] Cochain.ofHom g)).v
      i i (add_zero i) ((1 : T) ⊗ₜ[S] x) =
    ((complexBaseChange f).map g).f i ((1 : T) ⊗ₜ[S] x)
  erw [ScalarExtension.homComparison_apply f X Y 0 i i (add_zero i)]
  rfl

private lemma complexBaseChangeDG_closedNerveHom {X Y : Complex S} (g : X ⟶ Y) (k : ℤ) :
    ((complexBaseChangeDG f).map X Y).f k (closedNerveHom ((complexToClosed S).map g) k) =
      closedNerveHom ((complexToClosed T).map ((complexBaseChange f).map g)) k := by
  by_cases h : k = 0
  · subst k
    rw [closedNerveHom_zero, closedNerveHom_zero]
    change ((complexBaseChangeDG f).map X Y).f 0
        (cycleFromUnit (homComplex S X Y) ((complexToClosed S).map g)).val =
      (cycleFromUnit (homComplex T ((complexBaseChange f).obj X) ((complexBaseChange f).obj Y))
        ((complexToClosed T).map ((complexBaseChange f).map g))).val
    rw [← complexClosedHomEquiv_cochain, ← complexClosedHomEquiv_cochain]
    change ((complexBaseChangeDG f).map X Y).f 0
        (Cochain.ofHom ((closedToComplex S).map ((complexToClosed S).map g))) =
      Cochain.ofHom ((closedToComplex T).map
        ((complexToClosed T).map ((complexBaseChange f).map g)))
    rw [complexToClosed_map, complexToClosed_map]
    exact complexBaseChangeDG_map_ofHom f g
  · rw [closedNerveHom_of_ne _ _ h, closedNerveHom_of_ne _ _ h, map_zero]

/-- 閉零射の列の係数拡大は、通常の複体の項別係数拡大に一致する。 -/
lemma complexClosedNerve_extension :
    (nerveMap (complexToClosed S) ≫ closedNerveInclusion S (Complex S)) ≫
      complexExtensionNerve f =
    nerveMap (complexBaseChange f) ≫ nerveMap (complexToClosed T) ≫
      closedNerveInclusion T (Complex T) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro Γ
  apply Simplex.ext
  refine SimplexData.ext rfl ?_
  apply heq_of_eq
  funext I a b k hI ha hb hk
  have hab : a ≤ b := by
    rw [ha, hb]
    exact I.min'_le _ (I.max'_mem _)
  let g := Γ.map (homOfLE hab)
  change ((complexBaseChangeDG f).map (Γ.obj a) (Γ.obj b)).f k
    (closedNerveHom ((complexToClosed S).map g) k) =
      closedNerveHom ((complexToClosed T).map ((complexBaseChange f).map g)) k
  exact complexBaseChangeDG_closedNerveHom f g k

/-- 半自由複体の係数拡大を全複体へ含めた写像は、全複体の写像に一致する。 -/
lemma derivedInfinityBaseChange_inclusion :
    derivedInfinityBaseChange f ≫ derivedInfinityInclusion (S := T) =
      derivedInfinityInclusion (S := S) ≫ complexExtensionNerve f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  apply Simplex.ext
  rfl

private lemma extensionCochain_heq {X Y X' Y' : Complex S}
    (hX : X = X') (hY : Y = Y')
    {a : Homogeneous X Y 0} {b : Homogeneous X' Y' 0} (h : HEq a b) :
    HEq (((complexBaseChangeDG f).map X Y).f 0 a)
      (((complexBaseChangeDG f).map X' Y').f 0 b) := by
  subst X'
  subst Y'
  cases h
  rfl

/-- The closed chain map of an extended edge is the ordinary extension of its closed map. -/
lemma complexExtensionNerve_edgeChainMap
    {x y : (dgNerve S (Complex S)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve S (Complex S))) x y) :
    (closedToComplex T).map (edgeClosed (e.map ((truncation 2).map
      (complexExtensionNerve f)))) =
      (complexBaseChange f).map ((closedToComplex S).map (edgeClosed e)) := by
  let e' := e.map ((truncation 2).map (complexExtensionNerve f))
  apply Cochain.ofHom_injective
  change Cochain.ofHom (complexClosedHomEquiv T _ _ (edgeClosed e')) =
    Cochain.ofHom ((complexBaseChange f).map (complexClosedHomEquiv S _ _ (edgeClosed e)))
  rw [← complexBaseChangeDG_map_ofHom, complexClosedHomEquiv_cochain,
    complexClosedHomEquiv_cochain]
  change (closedHomEquiv T (Complex T) _ _ (edgeClosed e')).val =
    ((complexBaseChangeDG f).map (x.obj 0) (y.obj 0)).f 0
      (closedHomEquiv S (Complex S) _ _ (edgeClosed e)).val
  rw [edgeClosed_cycle, edgeClosed_cycle]
  apply eq_of_heq
  exact (edgeCycle_val_heq e').trans ((extensionCochain_heq f (edge_source_obj e).symm
    (edge_target_obj e).symm (edgeCycle_val_heq e)).symm)

end SerrePositivity.EInfinity.ComplexLimits
