module
public import SerrePositivity.DifferentialGraded.Complexes.Cone

/-! # 比較ホモトピーを保持する cone の全次数作用
概要：左右の斉次射と第三 cochain を、同じ二つの cone の間の実 cochain にする。
方針：標準 fst・snd・inl・inr で三角行列を作り、左 shift の符号を保持する。
規約：微分・合成保存は別工程。使われ方：Hom gluing の実 dg cone 関手。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R] {A B C D : Complex R}

/-- 元の二対角成分と第三比較を保持する、符号付きの実 cone cochain。 -/
def dgGluingConeCochain (f : A ⟶ B) (g : C ⟶ D) {n m : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (h : Homogeneous A D m) (hm : m + 1 = n) :
    Homogeneous (mappingCone f) (mappingCone g) n :=
  mappingCone.liftCochain g
    (n.negOnePow • (mappingCone.fst f).val.comp a (by omega : 1 + n = n + 1))
    ((mappingCone.snd f).comp b (zero_add n) -
      n.negOnePow • (mappingCone.fst f).val.comp h (by omega : 1 + m = n)) rfl

/-- 左射影は同じ左成分と元の shift の符号を回収する。 -/
lemma dgGluingConeCochain_fst (f : A ⟶ B) (g : C ⟶ D) {n m : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (h : Homogeneous A D m) (hm : m + 1 = n) :
    (dgGluingConeCochain f g a b h hm).comp (mappingCone.fst g).val rfl =
      n.negOnePow • (mappingCone.fst f).val.comp a (by omega : 1 + n = n + 1) :=
  mappingCone.liftCochain_fst _ _ _ _

/-- 右射影は右成分と同じ第三比較を回収する。 -/
lemma dgGluingConeCochain_snd (f : A ⟶ B) (g : C ⟶ D) {n m : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (h : Homogeneous A D m) (hm : m + 1 = n) :
    (dgGluingConeCochain f g a b h hm).comp (mappingCone.snd g) (add_zero n) =
      (mappingCone.snd f).comp b (zero_add n) -
        n.negOnePow • (mappingCone.fst f).val.comp h (by omega : 1 + m = n) :=
  mappingCone.liftCochain_snd _ _ _ _

/-- 同じ三成分の cone 作用は加法を保存する。 -/
lemma dgGluingConeCochain_add (f : A ⟶ B) (g : C ⟶ D) {n m : ℤ}
    (a a' : Homogeneous A C n) (b b' : Homogeneous B D n)
    (h h' : Homogeneous A D m) (hm : m + 1 = n) :
    dgGluingConeCochain f g (a + a') (b + b') (h + h') hm =
      dgGluingConeCochain f g a b h hm + dgGluingConeCochain f g a' b' h' hm := by
  simp only [dgGluingConeCochain, mappingCone.liftCochain, Cochain.comp_add,
    Cochain.add_comp, Cochain.sub_comp, Cochain.units_smul_comp, smul_add]
  abel

/-- 同じ三成分の cone 作用は係数環のスカラー倍を保存する。 -/
lemma dgGluingConeCochain_smul (f : A ⟶ B) (g : C ⟶ D) {n m : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (h : Homogeneous A D m) (hm : m + 1 = n)
    (r : R) :
    dgGluingConeCochain f g (r • a) (r • b) (r • h) hm = r • dgGluingConeCochain f g a b h hm := by
  simp only [dgGluingConeCochain, mappingCone.liftCochain, Cochain.comp_smul,
    Cochain.smul_comp, Cochain.sub_comp, Cochain.units_smul_comp]
  simp only [smul_comm n.negOnePow r]
  simp only [smul_sub, smul_add]

/-- 第三成分が零なら、元の対角 cone 作用そのものを回収する。 -/
lemma dgGluingConeCochain_zero_comparison (f : A ⟶ B) (g : C ⟶ D) {n m : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (hm : m + 1 = n) :
    dgGluingConeCochain f g a b (0 : Homogeneous A D m) hm = coneMapCochain f g a b := by
  simp only [dgGluingConeCochain, Cochain.comp_zero, smul_zero, sub_zero, coneMapCochain]

/-- 元の二恒等と第三成分零は、同じ元の cone の恒等を回収する。 -/
lemma dgGluingConeCochain_identity (f : A ⟶ B) :
    dgGluingConeCochain f f (Cochain.ofHom (𝟙 A)) (Cochain.ofHom (𝟙 B))
      (0 : Homogeneous A B (-1)) (by omega) =
      Cochain.ofHom (𝟙 (mappingCone f)) :=
  (dgGluingConeCochain_zero_comparison f f _ _ (by omega : (-1 : ℤ) + 1 = 0)).trans
    (coneMapCochain_identity f)

end SerrePositivity.KST.SConstruction
