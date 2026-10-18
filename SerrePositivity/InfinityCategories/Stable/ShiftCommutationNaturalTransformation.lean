module
public import SerrePositivity.InfinityCategories.Stable.ShiftCommutationInteger

/-! # シフト交換同型と自然変換の反対次数

概要：自然変換と交換する比較同型の逆次数の比較も自然変換と交換する。
方針：逆比較を挟むシフトの単位・余単位の自然性を使う。
規約：自然変換自体の可逆性は不要。使われ方：S6 の全整数シフトとの両立。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe v u v' u'
open CategoryTheory Functor
namespace SerrePositivity.InfinityCategories

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasShift C ℤ] [HasShift D ℤ]

local instance {F : C ⥤ D} : Group (Σ n : ℤ, StableShiftCommutationIso F n) :=
  stableShiftCommutation_group F

/-- 概要：一回比較から延長した負の一回比較は反対次数の標準比較。
方針：交換同型群の負の一乗を計算する。
規約：厳密な自然同型の等式。使われ方：負方向のシフトの自然性。 -/
lemma stableCommShiftOfOne_neg_one {F : C ⥤ D} (e : StableShiftCommutationIso F 1) :
    letI := stableCommShiftOfOne e
    F.commShiftIso (-1 : ℤ) = stableShiftCommutationNeg e := by
  change stableShiftCommutationPower e (-1) = stableShiftCommutationNeg e
  apply sigma_mk_injective (i := (-1 : ℤ))
  exact (stableShiftCommutationPower_mk e (-1)).trans (zpow_neg_one _)

/-- 概要：次数 a の比較が自然変換と可換なら反対次数の比較も可換。
方針：逆比較の自然性とシフト自己同値の単位・余単位の自然性を順に適用する。
規約：任意の関手・自然変換。使われ方：整数シフトの自然性を負方向へ延長する。 -/
lemma stableShiftCommutationNeg_naturality {F G : C ⥤ D} (τ : F ⟶ G) {a : ℤ}
    (eF : StableShiftCommutationIso F a) (eG : StableShiftCommutationIso G a)
    (h : ∀ X : C, eF.hom.app X ≫ (shiftFunctor D a).map (τ.app X) =
      τ.app ((shiftFunctor C a).obj X) ≫ eG.hom.app X) (X : C) :
    (stableShiftCommutationNeg eF).hom.app X ≫ (shiftFunctor D (-a)).map (τ.app X) =
      τ.app ((shiftFunctor C (-a)).obj X) ≫ (stableShiftCommutationNeg eG).hom.app X := by
  let Z := (shiftFunctor C (-a)).obj X
  let T := shiftFunctor D (-a)
  let u := shiftFunctorCompIsoId D a (-a) (add_neg_cancel a)
  let c := (shiftFunctorCompIsoId C (-a) a (neg_add_cancel a)).hom.app X
  have hi := congrArg (fun f ↦ eF.inv.app Z ≫ f ≫ eG.inv.app Z) (h Z)
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app] at hi
  dsimp only [CategoryTheory.Functor.comp_obj] at hi
  simp only [Category.comp_id] at hi
  have hc := τ.naturality c
  dsimp only [CategoryTheory.Functor.id_obj, CategoryTheory.Functor.comp_obj] at hc
  have hu := u.inv.naturality (τ.app Z)
  dsimp at hu
  calc
    (stableShiftCommutationNeg eF).hom.app X ≫ T.map (τ.app X) =
        u.inv.app (F.obj Z) ≫ T.map (eF.inv.app Z ≫ F.map c ≫ τ.app X) := by
      simp only [stableShiftCommutationNeg_hom_app, T, Z, u, c,
        CategoryTheory.Functor.map_comp, Category.assoc]
    _ = u.inv.app (F.obj Z) ≫ T.map (eF.inv.app Z ≫ τ.app ((shiftFunctor C a).obj Z) ≫
        G.map c) := by rw [hc]
    _ = u.inv.app (F.obj Z) ≫ T.map ((shiftFunctor D a).map (τ.app Z) ≫
        eG.inv.app Z ≫ G.map c) := by rw [← reassoc_of% hi]
    _ = (u.inv.app (F.obj Z) ≫ T.map ((shiftFunctor D a).map (τ.app Z))) ≫
        T.map (eG.inv.app Z) ≫ T.map (G.map c) := by
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (τ.app Z ≫ u.inv.app (G.obj Z)) ≫ T.map (eG.inv.app Z) ≫ T.map (G.map c) := by
      rw [← hu]
    _ = τ.app Z ≫ (stableShiftCommutationNeg eG).hom.app X := by
      simp only [stableShiftCommutationNeg_hom_app, T, Z, u, c, Category.assoc]

/-- 概要：一回比較と可換な自然変換は、そこから延長した全整数の比較と可換。
方針：逆比較の自然性で負の一回を得て、整数の正負両方向の帰納法を適用する。
規約：関手も自然変換も可逆性を仮定しない。使われ方：S6 の三角関手間の自然変換。 -/
lemma stableNatTransCommShiftOfOne {F G : C ⥤ D} (τ : F ⟶ G)
    (eF : StableShiftCommutationIso F 1) (eG : StableShiftCommutationIso G 1)
    (h : ∀ X : C, eF.hom.app X ≫ (shiftFunctor D (1 : ℤ)).map (τ.app X) =
      τ.app ((shiftFunctor C (1 : ℤ)).obj X) ≫ eG.hom.app X) :
    letI := stableCommShiftOfOne eF
    letI := stableCommShiftOfOne eG
    NatTrans.CommShift τ ℤ := by
  letI := stableCommShiftOfOne eF
  letI := stableCommShiftOfOne eG
  have h₁ : NatTrans.CommShiftCore τ (1 : ℤ) := by
    constructor
    apply NatTrans.ext
    funext X
    change (F.commShiftIso (1 : ℤ)).hom.app X ≫ (shiftFunctor D (1 : ℤ)).map (τ.app X) =
      τ.app ((shiftFunctor C (1 : ℤ)).obj X) ≫ (G.commShiftIso (1 : ℤ)).hom.app X
    rw [stableCommShiftOfOne_one, stableCommShiftOfOne_one]
    exact h X
  have hn₁ : NatTrans.CommShiftCore τ (-1 : ℤ) := by
    constructor
    apply NatTrans.ext
    funext X
    change (F.commShiftIso (-1 : ℤ)).hom.app X ≫ (shiftFunctor D (-1 : ℤ)).map (τ.app X) =
      τ.app ((shiftFunctor C (-1 : ℤ)).obj X) ≫ (G.commShiftIso (-1 : ℤ)).hom.app X
    rw [stableCommShiftOfOne_neg_one, stableCommShiftOfOne_neg_one]
    exact stableShiftCommutationNeg_naturality τ eF eG h X
  apply NatTrans.CommShift.of_core
  intro n
  refine Int.induction_on n (NatTrans.CommShiftCore.zero ℤ) (fun i hi ↦ hi.add h₁) ?_
  intro i hi
  simpa only [sub_eq_add_neg] using hi.add hn₁

end SerrePositivity.InfinityCategories
