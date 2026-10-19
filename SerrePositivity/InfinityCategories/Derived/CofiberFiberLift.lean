module
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberRotation
public import SerrePositivity.InfinityCategories.Derived.FiberCoconeCoordinates

/-! # 標準 cofiber 正方形の明示的な fiber 比較

概要：二脚 f,g と標準ホモトピーから、始域から二包含の差の fiber への鎖写像を作る。
方針：mapping cocone の lift に二脚の対と標準 cone 包含の負を渡す。
規約：普遍性による比較辺との一致は後続で示す。使われ方：D7 の安定性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 標準正方形の二脚の対。 -/
def cofiberPairMap (f : A ⟶ B) (g : A ⟶ C) : A ⟶ B ⊞ C := biprod.lift f g

/-- 二脚の対の後に符号反転をすると cone の入力となる差の射になる。 -/
lemma cofiberPairMap_sign (f : A ⟶ B) (g : A ⟶ C) :
    cofiberPairMap f g ≫ (cofiberBiproductSignIso B C).hom = cofiberDifference f g := by
  apply biprod.hom_ext <;> simp [cofiberPairMap, cofiberDifference,
    cofiberBiproductSignIso, Category.assoc]

/-- 二脚の対と二包含の差の合成は cone の入力と標準包含の合成。 -/
lemma cofiberPairMap_outputDifference (f : A ⟶ B) (g : A ⟶ C) :
    cofiberPairMap f g ≫ fiberDifference (pushoutInclusionB f g) (pushoutInclusionC f g) =
      cofiberDifference f g ≫ mappingCone.inr (cofiberDifference f g) := by
  rw [cofiberOutputDifference_eq, ← Category.assoc, cofiberPairMap_sign]

/-- 標準 cone ホモトピーの負は二脚の対を fiber へ持ち上げる条件を満たす。 -/
lemma cofiberFiberLift_condition (f : A ⟶ B) (g : A ⟶ C) :
    δ (-1) 0 (-(mappingCone.inl (cofiberDifference f g))) +
      Cochain.ofHom (cofiberPairMap f g ≫
        fiberDifference (pushoutInclusionB f g) (pushoutInclusionC f g)) = 0 := by
  rw [δ_neg, mappingCone.δ_inl, cofiberPairMap_outputDifference, neg_add_cancel]

/-- 二脚と標準ホモトピーを保持する明示的な fiber 比較鎖写像。 -/
def cofiberFiberLift (f : A ⟶ B) (g : A ⟶ C) :
    A ⟶ pullbackFiber (pushoutInclusionB f g) (pushoutInclusionC f g) :=
  mappingCocone.lift _ (cofiberPairMap f g) (-(mappingCone.inl (cofiberDifference f g)))
    (cofiberFiberLift_condition f g)

/-- 明示的な比較と fiber 射影の合成は二脚の対そのもの。 -/
lemma cofiberFiberLift_projection (f : A ⟶ B) (g : A ⟶ C) :
    cofiberFiberLift f g ≫ fiberProjection
      (fiberDifference (pushoutInclusionB f g) (pushoutInclusionC f g)) = cofiberPairMap f g := by
  rw [fiberProjection_eq_mappingCocone_fst]
  exact mappingCocone.lift_fst _ _ _ _

/-- 明示的な比較の B 側の射影は f。 -/
lemma cofiberFiberLift_projectionB (f : A ⟶ B) (g : A ⟶ C) :
    cofiberFiberLift f g ≫ pullbackProjectionB (pushoutInclusionB f g)
      (pushoutInclusionC f g) = f := by
  change (cofiberFiberLift f g ≫ fiberProjection _) ≫ biprod.fst = f
  rw [cofiberFiberLift_projection, cofiberPairMap, biprod.lift_fst]

/-- 明示的な比較の C 側の射影は g。 -/
lemma cofiberFiberLift_projectionC (f : A ⟶ B) (g : A ⟶ C) :
    cofiberFiberLift f g ≫ pullbackProjectionC (pushoutInclusionB f g)
      (pushoutInclusionC f g) = g := by
  change (cofiberFiberLift f g ≫ fiberProjection _) ≫ biprod.snd = g
  rw [cofiberFiberLift_projection, cofiberPairMap, biprod.lift_snd]

/-- 明示的な比較は標準四角形の共通の対角も保つ。 -/
lemma cofiberFiberLift_diagonal (f : A ⟶ B) (g : A ⟶ C) :
    cofiberFiberLift f g ≫ pullbackDiagonal (pushoutInclusionB f g)
      (pushoutInclusionC f g) = pushoutDiagonal f g := by
  change (cofiberFiberLift f g ≫ pullbackProjectionC (pushoutInclusionB f g)
    (pushoutInclusionC f g)) ≫ pushoutInclusionC f g = _
  rw [cofiberFiberLift_projectionC]
  rfl

/-- 明示的な比較の負一次成分は標準 cone ホモトピーの負。 -/
lemma cofiberFiberLift_snd (f : A ⟶ B) (g : A ⟶ C) (p q : ℤ) (hpq : p + (-1) = q) :
    (cofiberFiberLift f g).f p ≫
      (mappingCocone.snd
        (fiberDifference (pushoutInclusionB f g) (pushoutInclusionC f g))).v p q hpq =
      -(mappingCone.inl (cofiberDifference f g)).v p q hpq := by
  simpa only [cofiberFiberLift, Cochain.neg_v] using mappingCocone.lift_f_snd_v
    (fiberDifference (pushoutInclusionB f g) (pushoutInclusionC f g))
    (cofiberPairMap f g) (-(mappingCone.inl (cofiberDifference f g)))
    (cofiberFiberLift_condition f g) p q hpq

/-- 比較写像は標準 fiber ホモトピーを元の cofiber ホモトピーそのものへ引き戻す。 -/
lemma cofiberFiberLift_homotopy (f : A ⟶ B) (g : A ⟶ C) :
    (Cochain.ofHom (cofiberFiberLift f g)).comp
      (fiberNullHomotopy (fiberDifference (pushoutInclusionB f g) (pushoutInclusionC f g)))
      (zero_add (-1)) = mappingCone.inl (cofiberDifference f g) := by
  rw [fiberNullHomotopy_eq_neg_mappingCocone_snd, Cochain.comp_neg]
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.neg_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    cofiberFiberLift_snd, neg_neg]

end SerrePositivity.InfinityCategories
