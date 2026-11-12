module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberSquareComparisonData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingConeZeroTarget

/-! # 標準 cofiber から標準 suspension への鎖写像

概要：span の右下の対象を零に送る cone 写像と、その包含・ホモトピー・接続射の式を作る。
方針：mappingCone.map に始点の恒等と終域の零写像を入れる。
規約：接続射は Mathlib の負の第一射影。使われ方：D7 の実際の cofiber 接続射の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
open scoped ZeroObject
variable {S : Type u} [CommRing S] {A B : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 零への span の写像は cofiber の差の射と可換。 -/
lemma cofiberToSuspension_comm (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f (0 : A ⟶ 0) ≫ (0 : B ⊞ (0 : Complex S) ⟶ 0 ⊞ 0) =
      𝟙 A ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0) := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference, biprod.lift_eq]

/-- 標準 cofiber から標準 suspension の cone への鎖写像。 -/
def cofiberToSuspensionMap (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f (0 : A ⟶ 0) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber (0 : A ⟶ 0) (0 : A ⟶ 0) :=
  mappingCone.map _ _ (𝟙 A) 0 (cofiberToSuspension_comm f)

/-- cone の次数 −1 の包含は cofiber から suspension への写像で保たれる。 -/
lemma cofiberToSuspensionMap_inl (f : A ⟶ B) :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f (0 : A ⟶ 0))).comp
        (Cochain.ofHom (cofiberToSuspensionMap f)) (add_zero (-1)) =
      mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0)) := by
  unfold cofiberToSuspensionMap mappingCone.map
  rw [mappingCone.inl_desc]
  simp

/-- 右下の対象からの包含は零になる。 -/
lemma cofiberToSuspensionMap_inclusionB (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f (0 : A ⟶ 0) ≫ cofiberToSuspensionMap f = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB, cofiberToSuspensionMap, mappingCone.map]

/-- 左上の零対象からの包含は零になる。 -/
lemma cofiberToSuspensionMap_inclusionC (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f (0 : A ⟶ 0) ≫ cofiberToSuspensionMap f = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC, cofiberToSuspensionMap, mappingCone.map]

/-- suspension のシフト同型を合成すると元の cone の接続射になる。 -/
lemma cofiberToSuspensionMap_connecting (f : A ⟶ B) :
    cofiberToSuspensionMap f ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mappingConeZeroTargetIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0))
          ((biprod_isZero_iff (0 : _root_.SerrePositivity.DifferentialGraded.Complex S) 0).mpr ⟨isZero_zero _, isZero_zero _⟩)).hom =
      (mappingCone.triangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f (0 : A ⟶ 0))).mor₃ := by
  have h := (mappingCone.triangleMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f (0 : A ⟶ 0))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0)) (𝟙 A) 0
    (cofiberToSuspension_comm f)).comm₃.symm
  change cofiberToSuspensionMap f ≫
      (mappingCone.triangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0))).mor₃ =
    (mappingCone.triangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f (0 : A ⟶ 0))).mor₃ ≫
      (CategoryTheory.shiftFunctor (_root_.SerrePositivity.DifferentialGraded.Complex S) (1 : ℤ)).map (𝟙 A) at h
  exact h.trans ((congrArg
    (fun z => (mappingCone.triangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f (0 : A ⟶ 0))).mor₃ ≫ z)
    ((CategoryTheory.shiftFunctor (_root_.SerrePositivity.DifferentialGraded.Complex S) (1 : ℤ)).map_id A)).trans (Category.comp_id _))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
