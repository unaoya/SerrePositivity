module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.DoubleMappingCylinder

/-!
# span の射が誘導する二重写像円筒の比較

概要：可換な span の射から実際の二重写像円筒の比較写像を構成する。
方針：中央の円筒の射と左右の射を pushout の普遍性で貼り合わせる。
規約：Segal 1974 Lemma 1.7 の Y→X の比較射。
使われ方：各頂点との homotopy-cartesian な四角形を述べるための実写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open scoped _root_.Simplicial

/--
概要：span の可換な射が誘導する二重写像円筒の比較射。
方針：中央では Δ[1] との直積、左右では与えられた射を使い、端点の式で貼り合わせる。
規約：Segal 1974 Lemma 1.7。可換性の条件は仮定として明示する。
使われ方：二重写像円筒の貼り合わせ定理の比較対象。
-/
def doubleMappingCylinderMap {C A B C' A' B' : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (f' : C' ⟶ A') (g' : C' ⟶ B')
    (c : C ⟶ C') (a : A ⟶ A') (b : B ⟶ B')
    (hf : c ≫ f' = f ≫ a) (hg : c ≫ g' = g ≫ b) :
    doubleMappingCylinder f g ⟶ doubleMappingCylinder f' g' :=
  pushout.desc ((c ▷ Δ[1]) ≫ doubleMappingCylinder_middle f' g')
    (coprod.desc (a ≫ doubleMappingCylinder_left f' g') (b ≫ doubleMappingCylinder_right f' g'))
    (by
      apply coprod.hom_ext
      · simp only [cylinderEndpoints, coprod.inl_desc_assoc, coprod.inl_map_assoc,
          coprod.inl_desc]
        rw [SSet.ι₀_comp_assoc, doubleMappingCylinder_zero, ← Category.assoc, hf, Category.assoc]
      · simp only [cylinderEndpoints, coprod.inr_desc_assoc, coprod.inr_map_assoc,
          coprod.inr_desc]
        rw [SSet.ι₁_comp_assoc, doubleMappingCylinder_one, ← Category.assoc, hg, Category.assoc])

/--
概要：比較写像と中央の円筒の包含との合成則。
方針：pushout.desc の第一の包含との合成則を使う。
規約：中央の射は c と Δ[1] の直積である。
使われ方：二重写像円筒の中央の比較正方形。
-/
@[reassoc] theorem doubleMappingCylinder_middle_map {C A B C' A' B' : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (f' : C' ⟶ A') (g' : C' ⟶ B')
    (c : C ⟶ C') (a : A ⟶ A') (b : B ⟶ B')
    (hf : c ≫ f' = f ≫ a) (hg : c ≫ g' = g ≫ b) :
    doubleMappingCylinder_middle f g ≫ doubleMappingCylinderMap f g f' g' c a b hf hg =
      (c ▷ Δ[1]) ≫ doubleMappingCylinder_middle f' g' := by
  exact pushout.inl_desc _ _ _

/--
概要：比較写像と左の対象の包含との合成則。
方針：pushout.desc の第二の包含と余積の包含の合成則を使う。
規約：Segal Lemma 1.7 の左の頂点の四角形。
使われ方：左の homotopy-cartesian 性を述べる比較の等式。
-/
@[reassoc] theorem doubleMappingCylinder_left_map {C A B C' A' B' : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (f' : C' ⟶ A') (g' : C' ⟶ B')
    (c : C ⟶ C') (a : A ⟶ A') (b : B ⟶ B')
    (hf : c ≫ f' = f ≫ a) (hg : c ≫ g' = g ≫ b) :
    doubleMappingCylinder_left f g ≫ doubleMappingCylinderMap f g f' g' c a b hf hg =
      a ≫ doubleMappingCylinder_left f' g' := by
  simp only [doubleMappingCylinder_left, doubleMappingCylinderMap, Category.assoc,
    pushout.inr_desc, coprod.inl_desc]

/--
概要：比較写像と右の対象の包含との合成則。
方針：pushout.desc の第二の包含と余積の包含の合成則を使う。
規約：Segal Lemma 1.7 の右の頂点の四角形。
使われ方：右の homotopy-cartesian 性を述べる比較の等式。
-/
@[reassoc] theorem doubleMappingCylinder_right_map {C A B C' A' B' : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (f' : C' ⟶ A') (g' : C' ⟶ B')
    (c : C ⟶ C') (a : A ⟶ A') (b : B ⟶ B')
    (hf : c ≫ f' = f ≫ a) (hg : c ≫ g' = g ≫ b) :
    doubleMappingCylinder_right f g ≫ doubleMappingCylinderMap f g f' g' c a b hf hg =
      b ≫ doubleMappingCylinder_right f' g' := by
  simp only [doubleMappingCylinder_right, doubleMappingCylinderMap, Category.assoc,
    pushout.inr_desc, coprod.inr_desc]

/--
概要：二重写像円筒からの射は中央の円筒と左右の対象上で一致すれば等しい。
方針：pushout と余積の二つの普遍性を使う。
規約：二重写像円筒の実際の射の外延性。
使われ方：誘導写像の恒等射・合成の保存。
-/
theorem _root_.SerrePositivity.InfinityCategories.Kan.DoubleMappingCylinderMap.doubleMappingCylinder_hom_ext {C A B Z : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B)
    {u v : doubleMappingCylinder f g ⟶ Z}
    (hm : doubleMappingCylinder_middle f g ≫ u = doubleMappingCylinder_middle f g ≫ v)
    (hl : doubleMappingCylinder_left f g ≫ u = doubleMappingCylinder_left f g ≫ v)
    (hr : doubleMappingCylinder_right f g ≫ u = doubleMappingCylinder_right f g ≫ v) : u = v := by
  apply pushout.hom_ext
  · exact hm
  · apply coprod.hom_ext
    · simpa only [doubleMappingCylinder_left, Category.assoc] using hl
    · simpa only [doubleMappingCylinder_right, Category.assoc] using hr

/--
概要：span の恒等射が誘導する二重写像円筒の射は恒等射である。
方針：中央と左右の包含上で合成則を確認し、外延性を使う。
規約：二重写像円筒の関手性の恒等射の部分。
使われ方：貼り合わせの図式とその模型の比較。
-/
@[simp] theorem doubleMappingCylinderMap_id {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    doubleMappingCylinderMap f g f g (𝟙 C) (𝟙 A) (𝟙 B)
      (by simp) (by simp) = 𝟙 (doubleMappingCylinder f g) := by
  apply _root_.SerrePositivity.InfinityCategories.Kan.DoubleMappingCylinderMap.doubleMappingCylinder_hom_ext f g
  · rw [doubleMappingCylinder_middle_map]
    simp only [id_whiskerRight, Category.id_comp, Category.comp_id]
  · rw [doubleMappingCylinder_left_map]
    simp only [Category.id_comp, Category.comp_id]
  · rw [doubleMappingCylinder_right_map]
    simp only [Category.id_comp, Category.comp_id]

/--
概要：span の射の合成が誘導する比較射は、二つの誘導写像の合成に等しい。
方針：中央と左右の包含で合成則を使い、中央では円筒との直積が合成を保つことを使う。
規約：二重写像円筒の関手性の合成の部分。
使われ方：Segal の骨格の貼り合わせの比較の合成。
-/
theorem doubleMappingCylinderMap_comp {C A B C' A' B' C'' A'' B'' : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (f' : C' ⟶ A') (g' : C' ⟶ B')
    (f'' : C'' ⟶ A'') (g'' : C'' ⟶ B'')
    (c : C ⟶ C') (a : A ⟶ A') (b : B ⟶ B')
    (c' : C' ⟶ C'') (a' : A' ⟶ A'') (b' : B' ⟶ B'')
    (hf : c ≫ f' = f ≫ a) (hg : c ≫ g' = g ≫ b)
    (hf' : c' ≫ f'' = f' ≫ a') (hg' : c' ≫ g'' = g' ≫ b') :
    doubleMappingCylinderMap f g f' g' c a b hf hg ≫
      doubleMappingCylinderMap f' g' f'' g'' c' a' b' hf' hg' =
    doubleMappingCylinderMap f g f'' g'' (c ≫ c') (a ≫ a') (b ≫ b')
      (by rw [Category.assoc, hf', ← Category.assoc, hf, Category.assoc])
      (by rw [Category.assoc, hg', ← Category.assoc, hg, Category.assoc]) := by
  apply _root_.SerrePositivity.InfinityCategories.Kan.DoubleMappingCylinderMap.doubleMappingCylinder_hom_ext f g
  · rw [doubleMappingCylinder_middle_map_assoc, doubleMappingCylinder_middle_map,
      doubleMappingCylinder_middle_map]
    simp only [comp_whiskerRight, Category.assoc]
  · rw [doubleMappingCylinder_left_map_assoc, doubleMappingCylinder_left_map,
      doubleMappingCylinder_left_map]
    exact (Category.assoc _ _ _).symm
  · rw [doubleMappingCylinder_right_map_assoc, doubleMappingCylinder_right_map,
      doubleMappingCylinder_right_map]
    exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinderMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderMap := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinderMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderMap_comp := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinderMap_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderMap_id := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinderMap_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_left_map := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinder_left_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_left_map_assoc := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinder_left_map_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_middle_map := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinder_middle_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_middle_map_assoc := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinder_middle_map_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_right_map := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinder_right_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_right_map_assoc := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinder_right_map_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinderMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderMap.congr_simp := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinderMap.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderMap.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinderMap.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderMap_comp._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinderMap_comp._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderMap_id._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.doubleMappingCylinderMap_id._proof_1
