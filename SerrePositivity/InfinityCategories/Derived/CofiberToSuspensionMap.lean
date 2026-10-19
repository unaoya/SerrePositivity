module
public import SerrePositivity.InfinityCategories.Derived.CofiberSquareComparisonData
public import SerrePositivity.InfinityCategories.Derived.MappingConeZeroTarget

/-! # 標準 cofiber から標準 suspension への鎖写像

概要：span の右下の対象を零に送る cone 写像と、その包含・ホモトピー・接続射の式を作る。
方針：mappingCone.map に始点の恒等と終域の零写像を入れる。
規約：接続射は Mathlib の負の第一射影。使われ方：D7 の実際の cofiber 接続射の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex HomComplex
open scoped ZeroObject
variable {S : Type u} [CommRing S] {A B : Complex S}

/-- 零への span の写像は cofiber の差の射と可換。 -/
lemma cofiberToSuspension_comm (f : A ⟶ B) :
    cofiberDifference f (0 : A ⟶ 0) ≫ (0 : B ⊞ (0 : Complex S) ⟶ 0 ⊞ 0) =
      𝟙 A ≫ cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0) := by
  simp [cofiberDifference, biprod.lift_eq]

/-- 標準 cofiber から標準 suspension の cone への鎖写像。 -/
def cofiberToSuspensionMap (f : A ⟶ B) :
    pushoutCofiber f (0 : A ⟶ 0) ⟶ pushoutCofiber (0 : A ⟶ 0) (0 : A ⟶ 0) :=
  mappingCone.map _ _ (𝟙 A) 0 (cofiberToSuspension_comm f)

/-- cone の次数 −1 の包含は cofiber から suspension への写像で保たれる。 -/
lemma cofiberToSuspensionMap_inl (f : A ⟶ B) :
    (mappingCone.inl (cofiberDifference f (0 : A ⟶ 0))).comp
        (Cochain.ofHom (cofiberToSuspensionMap f)) (add_zero (-1)) =
      mappingCone.inl (cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0)) := by
  unfold cofiberToSuspensionMap mappingCone.map
  rw [mappingCone.inl_desc]
  simp

/-- 右下の対象からの包含は零になる。 -/
lemma cofiberToSuspensionMap_inclusionB (f : A ⟶ B) :
    pushoutInclusionB f (0 : A ⟶ 0) ≫ cofiberToSuspensionMap f = 0 := by
  simp [pushoutInclusionB, cofiberToSuspensionMap, mappingCone.map]

/-- 左上の零対象からの包含は零になる。 -/
lemma cofiberToSuspensionMap_inclusionC (f : A ⟶ B) :
    pushoutInclusionC f (0 : A ⟶ 0) ≫ cofiberToSuspensionMap f = 0 := by
  simp [pushoutInclusionC, cofiberToSuspensionMap, mappingCone.map]

/-- suspension のシフト同型を合成すると元の cone の接続射になる。 -/
lemma cofiberToSuspensionMap_connecting (f : A ⟶ B) :
    cofiberToSuspensionMap f ≫
        (mappingConeZeroTargetIso (cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0))
          ((biprod_isZero_iff (0 : Complex S) 0).mpr ⟨isZero_zero _, isZero_zero _⟩)).hom =
      (mappingCone.triangle (cofiberDifference f (0 : A ⟶ 0))).mor₃ := by
  have h := (mappingCone.triangleMap (cofiberDifference f (0 : A ⟶ 0))
    (cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0)) (𝟙 A) 0
    (cofiberToSuspension_comm f)).comm₃.symm
  change cofiberToSuspensionMap f ≫
      (mappingCone.triangle (cofiberDifference (0 : A ⟶ 0) (0 : A ⟶ 0))).mor₃ =
    (mappingCone.triangle (cofiberDifference f (0 : A ⟶ 0))).mor₃ ≫
      (CategoryTheory.shiftFunctor (Complex S) (1 : ℤ)).map (𝟙 A) at h
  exact h.trans ((congrArg
    (fun z => (mappingCone.triangle (cofiberDifference f (0 : A ⟶ 0))).mor₃ ≫ z)
    ((CategoryTheory.shiftFunctor (Complex S) (1 : ℤ)).map_id A)).trans (Category.comp_id _))

end SerrePositivity.InfinityCategories
