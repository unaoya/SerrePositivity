module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorRightFace

/-! # 元の右側自由座標付き生成元標準面の実鎖射の再帰
概要：元の零・一端点の追加と辺保持を、元の指定次元の実鎖面で回収する。
方針：元の余モノイド射の再帰を underlying 鎖射へ送り、元の面座標を保持する。
規約：元の全生成元と実鎖射を保持。使われ方：読み替え部分集合の両面式との帰納。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の零端点の追加の実鎖射は、座標 t の同じ元の零面との合成。 -/
lemma serreCubeGeneratorRightFace_point_zero_hom (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (t : ℕ) :
    (serreCubeGeneratorRightFace A (n + 1) (i, 0) t).hom =
      (serreCubeGeneratorRightFace A n i t).hom ≫
        serreCubeChainFace A false (n + t) ((n + 1) + t) (by omega) ⟨t, by omega⟩ := by
  have h := congrArg (fun f => f.hom) (serreCubeGeneratorRightFace_point_zero A n i t)
  simp only [Comon.comp_hom'] at h
  exact h.trans (congrArg (fun g => (serreCubeGeneratorRightFace A n i t).hom ≫ g)
    (serreCubeRightFace_hom A false n t))

/-- 元の一端点の追加の実鎖射は、座標 t の同じ元の一面との合成。 -/
lemma serreCubeGeneratorRightFace_point_one_hom (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (t : ℕ) :
    (serreCubeGeneratorRightFace A (n + 1) (i, 1) t).hom =
      (serreCubeGeneratorRightFace A n i t).hom ≫
        serreCubeChainFace A true (n + t) ((n + 1) + t) (by omega) ⟨t, by omega⟩ := by
  have h := congrArg (fun f => f.hom) (serreCubeGeneratorRightFace_point_one A n i t)
  simp only [Comon.comp_hom'] at h
  exact h.trans (congrArg (fun g => (serreCubeGeneratorRightFace A n i t).hom ≫ g)
    (serreCubeRightFace_hom A true n t))

/-- 元の辺の追加の実鎖射は、右側自由座標の一段追加の実鎖射と異種等号で一致。 -/
lemma serreCubeGeneratorRightFace_edge_hom (n : ℕ) (i : SerreCubeGeneratorIndex n) (t : ℕ) :
    HEq (serreCubeGeneratorRightFace A (n + 1) (i, 2) t).hom
      (serreCubeGeneratorRightFace A n i (t + 1)).hom :=
  serreCubeComonoidHom_heq_hom A (by simp only [serreCubeGeneratorFreeDimension]; omega)
    (by omega) _ _ (serreCubeGeneratorRightFace_edge A n i t)

end SerrePositivity.KST.SConstruction
