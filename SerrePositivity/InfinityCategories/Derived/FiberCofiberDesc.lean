module
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberLift

/-! # 標準 fiber 正方形の明示的な cofiber 比較

概要：標準 fiber の二射影の cofiber から元の終域への鎖写像を作る。
方針：二射の和と標準 fiber ホモトピーを mapping cone の desc に渡す。
規約：二脚・対角・ホモトピーを厳密に保持する。使われ方：D7 の双対比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex HomComplex
variable {S : Type u} [CommRing S] {B C D : Complex S}

/-- 二射を二項直和からの一射にまとめる。 -/
def fiberSumMap (g : B ⟶ D) (h : C ⟶ D) : B ⊞ C ⟶ D := biprod.desc g h

/-- 二射影の差と二射の和の合成は fiber 射影と元の差の合成。 -/
lemma fiberCofiberDesc_input (g : B ⟶ D) (h : C ⟶ D) :
    cofiberDifference (pullbackProjectionB g h) (pullbackProjectionC g h) ≫ fiberSumMap g h =
      fiberProjection (fiberDifference g h) ≫ fiberDifference g h := by
  simp [cofiberDifference, pullbackProjectionB, pullbackProjectionC, fiberSumMap,
    fiberDifference, biprod.lift_eq, biprod.desc_eq, Category.assoc,
    Preadditive.comp_add, Preadditive.add_comp, Preadditive.neg_comp, Preadditive.comp_neg]

/-- 標準 fiber ホモトピーは cofiber からの降下条件を満たす。 -/
lemma fiberCofiberDesc_condition (g : B ⟶ D) (h : C ⟶ D) :
    δ (-1) 0 (fiberNullHomotopy (fiberDifference g h)) =
      Cochain.ofHom (cofiberDifference (pullbackProjectionB g h) (pullbackProjectionC g h) ≫
        fiberSumMap g h) := by
  rw [fiberCofiberDesc_input, fiberNullHomotopy_differential]

/-- 二射影の標準 cofiber から元の終域への明示的な比較鎖写像。 -/
def fiberCofiberDesc (g : B ⟶ D) (h : C ⟶ D) :
    pushoutCofiber (pullbackProjectionB g h) (pullbackProjectionC g h) ⟶ D :=
  mappingCone.desc _ (fiberNullHomotopy (fiberDifference g h)) (fiberSumMap g h)
    (fiberCofiberDesc_condition g h)

/-- 比較射の B 側の包含との合成は g。 -/
lemma fiberCofiberDesc_inclusionB (g : B ⟶ D) (h : C ⟶ D) :
    pushoutInclusionB (pullbackProjectionB g h) (pullbackProjectionC g h) ≫
      fiberCofiberDesc g h = g := by
  simp [pushoutInclusionB, Category.assoc, fiberCofiberDesc, fiberSumMap]

/-- 比較射の C 側の包含との合成は h。 -/
lemma fiberCofiberDesc_inclusionC (g : B ⟶ D) (h : C ⟶ D) :
    pushoutInclusionC (pullbackProjectionB g h) (pullbackProjectionC g h) ≫
      fiberCofiberDesc g h = h := by
  simp [pushoutInclusionC, Category.assoc, fiberCofiberDesc, fiberSumMap]

/-- 比較射は共通の対角も保つ。 -/
lemma fiberCofiberDesc_diagonal (g : B ⟶ D) (h : C ⟶ D) :
    pushoutDiagonal (pullbackProjectionB g h) (pullbackProjectionC g h) ≫
      fiberCofiberDesc g h = pullbackDiagonal g h := by
  simp only [pushoutDiagonal, Category.assoc, fiberCofiberDesc_inclusionC, pullbackDiagonal]

/-- 比較射は標準 cofiber ホモトピーを元の fiber ホモトピーに移す。 -/
lemma fiberCofiberDesc_homotopy (g : B ⟶ D) (h : C ⟶ D) :
    (mappingCone.inl (cofiberDifference (pullbackProjectionB g h) (pullbackProjectionC g h))).comp
      (Cochain.ofHom (fiberCofiberDesc g h)) (add_zero (-1)) =
      fiberNullHomotopy (fiberDifference g h) :=
  mappingCone.inl_desc _ _ _ _

end SerrePositivity.InfinityCategories
