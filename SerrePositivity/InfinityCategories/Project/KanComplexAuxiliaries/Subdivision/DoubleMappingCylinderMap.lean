module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.DoubleMappingCylinder

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
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Comparison
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
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f' g' :=
  pushout.desc ((c ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f' g')
    (coprod.desc (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f' g') (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f' g'))
    (by
      apply coprod.hom_ext
      · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inl_desc_assoc, coprod.inl_map_assoc,
          coprod.inl_desc]
        rw [SSet.ι₀_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_zero, ← Category.assoc, hf, Category.assoc]
      · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inr_desc_assoc, coprod.inr_map_assoc,
          coprod.inr_desc]
        rw [SSet.ι₁_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_one, ← Category.assoc, hg, Category.assoc])

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
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf hg =
      (c ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f' g' := by
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
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf hg =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f' g' := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap, Category.assoc,
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
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf hg =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f' g' := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap, Category.assoc,
    pushout.inr_desc, coprod.inr_desc]

/--
概要：二重写像円筒からの射は中央の円筒と左右の対象上で一致すれば等しい。
方針：pushout と余積の二つの普遍性を使う。
規約：二重写像円筒の実際の射の外延性。
使われ方：誘導写像の恒等射・合成の保存。
-/
theorem _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderMap.doubleMappingCylinder_hom_ext {C A B Z : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B)
    {u v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g ⟶ Z}
    (hm : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g ≫ u = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g ≫ v)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g ≫ u = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g ≫ v)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g ≫ u = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g ≫ v) : u = v := by
  apply pushout.hom_ext
  · exact hm
  · apply coprod.hom_ext
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left, Category.assoc] using hl
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right, Category.assoc] using hr

/--
概要：span の恒等射が誘導する二重写像円筒の射は恒等射である。
方針：中央と左右の包含上で合成則を確認し、外延性を使う。
規約：二重写像円筒の関手性の恒等射の部分。
使われ方：貼り合わせの図式とその模型の比較。
-/
@[simp] theorem doubleMappingCylinderMap_id {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f g (𝟙 C) (𝟙 A) (𝟙 B)
      (by simp) (by simp) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderMap.doubleMappingCylinder_hom_ext f g
  · rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_map]
    simp only [id_whiskerRight, Category.id_comp, Category.comp_id]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_map]
    simp only [Category.id_comp, Category.comp_id]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_map]
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
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf hg ≫
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f' g' f'' g'' c' a' b' hf' hg' =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f'' g'' (c ≫ c') (a ≫ a') (b ≫ b')
      (by rw [Category.assoc, hf', ← Category.assoc, hf, Category.assoc])
      (by rw [Category.assoc, hg', ← Category.assoc, hg, Category.assoc]) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderMap.doubleMappingCylinder_hom_ext f g
  · rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_map_assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_map,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_map]
    simp only [comp_whiskerRight, Category.assoc]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_map_assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_map,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_map]
    exact (Category.assoc _ _ _).symm
  · rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_map_assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_map,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_map]
    exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
