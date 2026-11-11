module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientChains

/-!
# Barratt–Eccles の arity 複体の係数拡大

## 概要
Berger–Fresse §1.1 の arity 複体を任意の環準同型に沿って係数拡大する。

## 方針
半線形な係数写像の随伴像を取り、非退化基底上で逆写像を作る。

## 規約
任意の環準同型について成り立ち、正の余鎖次数は零。

## 使われ方
Barratt–Eccles 代数の厳密な底変更。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomologicalComplex DifferentialGraded
open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 同じ添字の二つの基底を送る半線形写像の随伴像は同型。 -/
lemma adjoint_isIso_of_basis {I : Type u} {X : ModuleCat.{u} S} {Y : ModuleCat.{u} T}
    (b : Module.Basis I S X) (b' : Module.Basis I T Y)
    (k : X ⟶ (ModuleCat.restrictScalars f).obj Y) (hk : ∀ a, k (b a) = b' a) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj f).homEquiv X Y).symm k) := by
  let L := ModuleCat.extendScalars f
  let R := ModuleCat.restrictScalars f
  let A := ModuleCat.extendRestrictScalarsAdj f
  let h := (A.homEquiv X Y).symm k
  let η : X ⟶ R.obj (L.obj X) := A.unit.app X
  let v : I → L.obj X := fun a => η (b a)
  let l : Y ⟶ L.obj X := ModuleCat.ofHom (Y := ↥(L.obj X)) (b'.constr T v)
  have hl (a : I) : l (b' a) = η (b a) := b'.constr_basis T v a
  have hh : η ≫ R.map h = k := (A.homEquiv X Y).apply_symm_apply k
  have hh' (a : I) : h (η (b a)) = b' a :=
    (congrArg (fun g : X ⟶ R.obj Y => g (b a)) hh).trans (hk a)
  refine ⟨⟨l, ?_, ?_⟩⟩
  · apply (A.homEquiv X (L.obj X)).injective
    change η ≫ R.map (h ≫ l) = η ≫ R.map (𝟙 (L.obj X))
    erw [R.map_id, Category.comp_id, R.map_comp, ← Category.assoc, hh]
    apply ModuleCat.hom_ext
    apply b.ext
    intro a
    change l (k (b a)) = η (b a)
    rw [hk, hl]
  · apply ModuleCat.hom_ext
    apply b'.ext
    intro a
    change h (l (b' a)) = b' a
    rw [hl, hh']

/-- arity 複体の係数拡大の比較射。 -/
def coefficientExtensionMap (n : ℕ) :
    (ScalarExtension.extension f).obj (complex S n) ⟶ complex T n :=
  ((ScalarExtension.adjunction f).homEquiv _ _).symm (coefficientComplexMap f n)

/-- 係数拡大の比較は各 arity で同型。 -/
lemma coefficientExtensionMap_isIso (n : ℕ) : IsIso (coefficientExtensionMap f n) := by
  have hcomp (i : ℤ) : IsIso ((coefficientExtensionMap f n).f i) := by
    by_cases hi : 0 < i
    · let L := ModuleCat.extendScalars f
      have hS := L.map_isZero (complex_isZero_positive S n i hi)
      have hT := complex_isZero_positive T n i hi
      let e := hS.iso hT
      have h : (coefficientExtensionMap f n).f i = e.hom := hS.eq_of_src _ _
      rw [h]
      infer_instance
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(q : ℤ) := ⟨(-i).toNat, by omega⟩
    let b := (normalizedBasis S n q).map (complexXIso S n q).symm.toLinearEquiv
    let b' := (normalizedBasis T n q).map (complexXIso T n q).symm.toLinearEquiv
    change IsIso (((ModuleCat.extendRestrictScalarsAdj f).homEquiv
      ((complex S n).X (-(q : ℤ))) ((complex T n).X (-(q : ℤ)))).symm
        ((coefficientComplexMap f n).f (-(q : ℤ))))
    apply adjoint_isIso_of_basis f b b'
    intro a
    change (coefficientComplexMap f n).f (-(q : ℤ))
        ((complexXIso S n q).inv (normalizedBasis S n q a)) =
      (complexXIso T n q).inv (normalizedBasis T n q a)
    cases a with
    | up x =>
      rw [normalizedBasis_apply, normalizedBasis_apply, coefficientComplexMap_generator]
  exact HomologicalComplex.Hom.isIso_of_components _

/-- arity 複体の係数拡大の比較同型。 -/
def coefficientExtensionIso (n : ℕ) :
    (ScalarExtension.extension f).obj (complex S n) ≅ complex T n := by
  have := coefficientExtensionMap_isIso f n
  exact asIso (coefficientExtensionMap f n)

end SerrePositivity.EInfinity.BarrattEccles
