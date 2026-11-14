module
public import SerrePositivity.DifferentialGraded.Complexes.Cone


/-! # cone の等式輸送と次数零対角作用の二座標

概要：cone の鎖写像の厳密な等式輸送と、次数零の対角作用は指定二座標を保つ。
方針：等式を消去し、既存の cone cochain の射影公式を各次数で評価する。
規約：全整数次数。使われ方：Yoneda の残差を始点の実閉細分へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 同じ始域・終域の鎖写像の等式による cone 輸送は第一座標を保つ。 -/
lemma dgConeEqToHom_fst {M N : Complex A} {f g : M ⟶ N} (h : f = g) (n : ℤ)
    (z : (mappingCone f).X n) :
    (mappingCone.fst g).val.v n (n + 1) rfl
      ((eqToHom (congrArg (fun a : M ⟶ N => mappingCone a) h)).f n z) =
      (mappingCone.fst f).val.v n (n + 1) rfl z := by
  subst g
  rfl

/-- 同じ始域・終域の鎖写像の等式による cone 輸送は第二座標を保つ。 -/
lemma dgConeEqToHom_snd {M N : Complex A} {f g : M ⟶ N} (h : f = g) (n : ℤ)
    (z : (mappingCone f).X n) :
    (mappingCone.snd g).v n n (add_zero n)
      ((eqToHom (congrArg (fun a : M ⟶ N => mappingCone a) h)).f n z) =
      (mappingCone.snd f).v n n (add_zero n) z := by
  subst g
  rfl

/-- 次数零の cone 対角作用の第一座標は、第一成分の作用。 -/
lemma dgConeZeroAction_fst {M N P Q : Complex A} (f : M ⟶ N) (g : P ⟶ Q)
    (a : Cochain M P 0) (b : Cochain N Q 0) (n : ℤ) (z : (mappingCone f).X n) :
    (mappingCone.fst g).val.v n (n + 1) rfl
      ((coneMapCochain f g a b).v n n (add_zero n) z) =
      a.v (n + 1) (n + 1) (add_zero _) ((mappingCone.fst f).val.v n (n + 1) rfl z) := by
  have h := ConcreteCategory.congr_hom (coneMapCochain_fst_v f g a b n n (add_zero n)) z
  simpa only [Int.negOnePow_zero, one_smul, ModuleCat.comp_apply] using h

/-- 次数零の cone 対角作用の第二座標は、第二成分の作用。 -/
lemma dgConeZeroAction_snd {M N P Q : Complex A} (f : M ⟶ N) (g : P ⟶ Q)
    (a : Cochain M P 0) (b : Cochain N Q 0) (n : ℤ) (z : (mappingCone f).X n) :
    (mappingCone.snd g).v n n (add_zero n)
      ((coneMapCochain f g a b).v n n (add_zero n) z) =
      b.v n n (add_zero n) ((mappingCone.snd f).v n n (add_zero n) z) := by
  have h := Cochain.congr_v (coneMapCochain_snd f g a b) n n (add_zero n)
  have he := ConcreteCategory.congr_hom h z
  simpa only [Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n),
    ModuleCat.comp_apply] using he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
