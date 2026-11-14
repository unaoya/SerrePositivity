module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberCoconeCoordinates

/-! # Cocone 射影の cone の明示的な縮約

概要：mapping cocone の第一射影の cone は元の終域とホモトピー同値。
方針：cocone の第二包含で逆写像を作り、二つの直和分解から戻りのホモトピーを与える。
規約：安定性を仮定しない全非有界複体の計算。使われ方：D7 の標準 fiber の cofiber 比較。
-/
@[expose] public section
open CategoryTheory Limits SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
variable {S : Type u} [CommRing S] {E D : Complex S}
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- Cocone の第一包含は恒等射と零からの cochain lift。 -/
lemma cocone_inl_eq_lift (f : E ⟶ D) :
    mappingCocone.inl f = mappingCocone.liftCochain f (Cochain.ofHom (𝟙 E))
      (0 : Cochain E D (-1)) (by omega) := by
  simp [mappingCocone.liftCochain, mappingCocone.inl, mappingCone.liftCochain]
/-- Cocone 第一包含の微分。 -/
lemma cocone_delta_inl (f : E ⟶ D) :
    δ 0 1 (mappingCocone.inl f) =
      -((Cochain.ofHom f).comp (mappingCocone.inr f).val (zero_add 1)) := by
  rw [cocone_inl_eq_lift, mappingCocone.δ_liftCochain _ _ _ _ 1 rfl]
  simp
/-- Cocone の二つの座標による恒等 cochain の分解。 -/
lemma cocone_id_cochain (f : E ⟶ D) :
    (Cochain.ofHom (mappingCocone.fst f)).comp (mappingCocone.inl f) (zero_add 0) +
      (mappingCocone.snd f).comp (mappingCocone.inr f).val (by omega) =
        Cochain.ofHom (𝟙 (mappingCocone f)) := by
  apply Cochain.ext₀
  intro p
  calc
    _ = (mappingCocone.fst f).f p ≫ (mappingCocone.inl f).v p p (add_zero p) +
        (mappingCocone.snd f).v p (p - 1) (by omega) ≫
          (mappingCocone.inr f).val.v (p - 1) p (by omega) :=
      congrArg₂ (fun a b => a + b)
        (Cochain.zero_cochain_comp_v _ _ p p (add_zero p))
        (Cochain.comp_v (mappingCocone.snd f) (mappingCocone.inr f).val
          (neg_add_cancel 1) p (p - 1) p (by omega) (by omega))
    _ = _ := mappingCocone.id_X f p (p - 1) (by omega)
/-- Cocone 第一包含と第一射影の合成。 -/
lemma cocone_inl_fst_cochain (f : E ⟶ D) :
    (mappingCocone.inl f).comp (Cochain.ofHom (mappingCocone.fst f)) (add_zero 0) =
      Cochain.ofHom (𝟙 E) := by
  apply Cochain.ext₀
  intro p
  simp [Cochain.comp_zero_cochain_v]
/-- 第二射影の負は第一射影の cone からの降下条件を満たす。 -/
lemma cocone_desc_condition (f : E ⟶ D) :
    δ (-1) 0 (-(mappingCocone.snd f)) = Cochain.ofHom (mappingCocone.fst f ≫ f) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberNullHomotopy_eq_neg_mappingCocone_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy_differential,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberProjection_eq_mappingCocone_fst]
/-- Cocone 第一射影の cone から元の終域への標準射。 -/
def coconeConeDesc (f : E ⟶ D) : mappingCone (mappingCocone.fst f) ⟶ D :=
  mappingCone.desc _ (-(mappingCocone.snd f)) f (cocone_desc_condition f)
/-- 第二包含の負と零は cone への持ち上げ条件を満たす。 -/
lemma cocone_inv_condition (f : E ⟶ D) :
    δ 0 1 (0 : Cochain D E 0) +
      (-(mappingCocone.inr f)).val.comp (Cochain.ofHom (mappingCocone.fst f)) (add_zero 1) = 0 := by
  simp only [δ_zero, zero_add, Cocycle.coe_neg, Cochain.neg_comp]
  apply neg_eq_zero.mpr
  apply Cochain.ext
  intro p q hpq
  simp [Cochain.comp_zero_cochain_v]
/-- 第二包含の負から作った標準射の逆。 -/
def coconeConeInv (f : E ⟶ D) : D ⟶ mappingCone (mappingCocone.fst f) :=
  mappingCone.lift _ (-(mappingCocone.inr f)) 0 (cocone_inv_condition f)
/-- 逆写像の後の標準射は厳密に恒等。 -/
lemma coconeConeInv_desc (f : E ⟶ D) : coconeConeInv f ≫ coconeConeDesc f = 𝟙 D := by
  apply HomologicalComplex.hom_ext
  intro p
  change (coconeConeInv f).f p ≫ (coconeConeDesc f).f p = _
  rw [coconeConeInv, coconeConeDesc,
    mappingCone.lift_desc_f _ _ _ _ _ _ _ p (p + 1) rfl]
  simp

/-- 逆写像の cochain 表示。 -/
lemma coconeConeInv_cochain (f : E ⟶ D) :
    Cochain.ofHom (coconeConeInv f) =
      -((mappingCocone.inr f).val.comp (mappingCone.inl (mappingCocone.fst f)) (by omega)) := by
  simp [coconeConeInv, mappingCone.liftCochain]

/-- 標準射と逆写像の合成を恒等へ結ぶ明示的ホモトピー。 -/
def coconeConeReturnHomotopy (f : E ⟶ D) :
    Homotopy (coconeConeDesc f ≫ coconeConeInv f) (𝟙 _) := by
  apply mappingCone.descHomotopy _ _ _ 0
    (-((mappingCocone.inl f).comp (mappingCone.inl (mappingCocone.fst f)) (zero_add (-1))))
  · simp only [δ_zero, zero_add, Cochain.ofHom_comp]
    rw [← Cochain.comp_assoc_of_second_is_zero_cochain,
      show (mappingCone.inl (mappingCocone.fst f)).comp (Cochain.ofHom (coconeConeDesc f))
        (add_zero (-1)) = -(mappingCocone.snd f) from mappingCone.inl_desc _ _ _ _]
    rw [coconeConeInv_cochain]
    simp only [Cochain.neg_comp, Cochain.comp_neg, neg_neg, Cochain.comp_id]
    have hi := congrArg (fun z : Cochain (mappingCocone f) (mappingCocone f) 0 =>
      z.comp (mappingCone.inl (mappingCocone.fst f)) (zero_add (-1))) (cocone_id_cochain f)
    simp only [Cochain.add_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      Cochain.id_comp] at hi
    rw [Cochain.comp_assoc (mappingCocone.snd f) (mappingCocone.inr f).val
      (mappingCone.inl (mappingCocone.fst f)) (neg_add_cancel 1) (add_neg_cancel 1)
      (zero_add (-1))] at hi
    exact eq_neg_add_iff_add_eq.mpr hi
  · rw [← Category.assoc,
      show mappingCone.inr (mappingCocone.fst f) ≫ coconeConeDesc f = f from
        mappingCone.inr_desc _ _ _ _, Category.comp_id, Cochain.ofHom_comp,
      coconeConeInv_cochain]
    rw [δ_neg, δ_comp _ _ _ 1 0 0 (by omega) rfl (by omega),
      mappingCone.δ_inl, cocone_delta_inl]
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
      Cochain.neg_comp, Cochain.comp_neg, neg_neg, neg_add_rev]
    have hb : (mappingCocone.inl f).comp (Cochain.ofHom
        (mappingCocone.fst f ≫ mappingCone.inr (mappingCocone.fst f))) (zero_add 0) =
        Cochain.ofHom (mappingCone.inr (mappingCocone.fst f)) := by
      rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_first_is_zero_cochain,
        cocone_inl_fst_cochain, Cochain.id_comp]
    rw [hb, neg_add_cancel_right]
    exact congrArg Neg.neg (Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom f) (mappingCocone.inr f).val (mappingCone.inl (mappingCocone.fst f))
      (by omega)).symm

/-- Cocone 第一射影の cone と元の終域のホモトピー同値。 -/
def coconeConeHomotopyEquiv (f : E ⟶ D) :
    HomotopyEquiv (mappingCone (mappingCocone.fst f)) D where
  hom := coconeConeDesc f
  inv := coconeConeInv f
  homotopyHomInvId := coconeConeReturnHomotopy f
  homotopyInvHomId := Homotopy.ofEq (coconeConeInv_desc f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
