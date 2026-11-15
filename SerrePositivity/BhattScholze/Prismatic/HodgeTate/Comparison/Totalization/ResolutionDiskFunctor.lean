module

public import SerrePositivity.HomologicalAlgebra.UnboundedSemifreeModel

/-!
# 既存の全斉次生成元の自由 disk 被覆の関手性

## 概要
本体の同じ自由 disk 被覆について、像の生成元へ送る元の写像の恒等・合成を確認する。

## 方針
生成元の添字を実際の射で送り、既存の自由 disk の全射の自然性を使う。

## 規約
別の分解や選んだ持ち上げは導入しない。この関手の加法性は主張しない。

## 使われ方
BS 著者版 Lemma 4.22 の厳密な余単体的入力に、既存の同じ分解候補を適用する準備。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 本体の全生成元の添字を、実際の射で送る。 -/
def diskIndexMap {M N : ModuleCategory R D} (g : M ⟶ N)
    (j : ModuleDiskCoverIndex R D M) : ModuleDiskCoverIndex R D N :=
  ⟨j.1, j.2.1, ((moduleEvaluation R D j.1).map g).f j.2.1 j.2.2⟩

/-- 本体の評価関手の恒等射の法則を元で評価する。 -/
theorem evalMap_id (M : ModuleCategory R D) (x : D) (n : ℤ)
    (z : ((moduleEvaluation R D x).obj M).X n) :
    ((moduleEvaluation R D x).map (𝟙 M)).f n z = z := by
  have h := congrArg (fun g => g.f n z) ((moduleEvaluation R D x).map_id M)
  simpa only [HomologicalComplex.id_f, ModuleCat.id_apply] using h

/-- 本体の評価関手の合成の法則を元で評価する。 -/
theorem evalMap_comp {M N P : ModuleCategory R D} (g : M ⟶ N) (h : N ⟶ P)
    (x : D) (n : ℤ) (z : ((moduleEvaluation R D x).obj M).X n) :
    ((moduleEvaluation R D x).map (g ≫ h)).f n z =
      ((moduleEvaluation R D x).map h).f n (((moduleEvaluation R D x).map g).f n z) := by
  have e := congrArg (fun k => k.f n z) ((moduleEvaluation R D x).map_comp g h)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply] using e

/-- 添字の恒等射の法則。 -/
@[simp] theorem diskIndexMap_id (M : ModuleCategory R D) (j : ModuleDiskCoverIndex R D M) :
    diskIndexMap R D (𝟙 M) j = j := by
  rcases j with ⟨x, n, z⟩
  exact congrArg (fun t => (⟨x, n, t⟩ : ModuleDiskCoverIndex R D M)) (evalMap_id R D M x n z)

/-- 添字の合成の法則。 -/
@[simp] theorem diskIndexMap_comp {M N P : ModuleCategory R D} (g : M ⟶ N) (h : N ⟶ P)
    (j : ModuleDiskCoverIndex R D M) :
    diskIndexMap R D (g ≫ h) j = diskIndexMap R D h (diskIndexMap R D g j) := by
  rcases j with ⟨x, n, z⟩
  exact congrArg (fun t => (⟨x, n, t⟩ : ModuleDiskCoverIndex R D P)) (evalMap_comp R D g h x n z)

/-- 同じ自由 disk 被覆の、像の生成元へ送る射。 -/
def diskCoverMap {M N : ModuleCategory R D} (g : M ⟶ N) :
    moduleDiskCover R D M ⟶ moduleDiskCover R D N :=
  Sigma.desc (fun j => moduleDiskCoverι R D N (diskIndexMap R D g j))

/-- 元の各生成元上の指定公式。 -/
@[reassoc] theorem diskCoverι_map {M N : ModuleCategory R D} (g : M ⟶ N)
    (j : ModuleDiskCoverIndex R D M) :
    moduleDiskCoverι R D M j ≫ diskCoverMap R D g =
      moduleDiskCoverι R D N (diskIndexMap R D g j) := Sigma.ι_comp_desc _ _

/-- 添字の等式に沿う包含の従属合同。 -/
theorem diskCoverι_heq (M : ModuleCategory R D) {i j : ModuleDiskCoverIndex R D M} (h : i=j) :
    HEq (moduleDiskCoverι R D M i) (moduleDiskCoverι R D M j) := by
  cases h
  rfl

set_option maxHeartbeats 800000 in
-- 小さい余積の添字に依存する包含の型の照合に上限を確保する。
/-- 自由 disk 被覆の恒等射の法則。 -/
@[simp] theorem diskCoverMap_id (M : ModuleCategory R D) :
    diskCoverMap R D (𝟙 M) = 𝟙 (moduleDiskCover R D M) := by
  apply Sigma.hom_ext
  intro j
  change moduleDiskCoverι R D M j ≫ diskCoverMap R D (𝟙 M) = _
  rw [diskCoverι_map]
  exact (eq_of_heq (diskCoverι_heq R D M (i := diskIndexMap R D (𝟙 M) j) (j := j) (diskIndexMap_id R D M j))).trans
    (Category.comp_id (moduleDiskCoverι R D M j)).symm

set_option maxHeartbeats 800000 in
-- 小さい余積の添字に依存する包含の型の照合に上限を確保する。
/-- 自由 disk 被覆の合成の法則。 -/
@[simp] theorem diskCoverMap_comp {M N P : ModuleCategory R D} (g : M ⟶ N) (h : N ⟶ P) :
    diskCoverMap R D (g ≫ h) = diskCoverMap R D g ≫ diskCoverMap R D h := by
  apply Sigma.hom_ext
  intro j
  change moduleDiskCoverι R D M j ≫ diskCoverMap R D (g ≫ h) =
    moduleDiskCoverι R D M j ≫ (diskCoverMap R D g ≫ diskCoverMap R D h)
  simp only [← Category.assoc, diskCoverι_map]
  exact eq_of_heq (diskCoverι_heq R D P (i := diskIndexMap R D (g ≫ h) j)
    (j := diskIndexMap R D h (diskIndexMap R D g j)) (diskIndexMap_comp R D g h j))

set_option maxHeartbeats 800000 in
-- 元の自由 disk の随伴と小さい余積の型の照合に上限を確保する。
/-- 同じ自由 disk の元の生成元指定の自然性。 -/
theorem diskGenerator_naturality {M N : ModuleCategory R D} (g : M ⟶ N)
    (x : D) (n : ℤ) (z : ((moduleEvaluation R D x).obj M).X n) :
    (freeDiskHomEquiv R D x n N).symm (((moduleEvaluation R D x).map g).f n z) =
      (freeDiskHomEquiv R D x n M).symm z ≫ g := by
  apply (freeDiskHomEquiv R D x n N).injective
  rw [Equiv.apply_symm_apply, freeDiskHomEquiv_naturality, Equiv.apply_symm_apply]

/-- 本体の同じ全射は、生成元の像へ送る射に関して自然である。 -/
@[reassoc] theorem diskCoverMap_π {M N : ModuleCategory R D} (g : M ⟶ N) :
    diskCoverMap R D g ≫ moduleDiskCoverπ R D N = moduleDiskCoverπ R D M ≫ g := by
  apply Sigma.hom_ext
  rintro ⟨x, n, z⟩
  change moduleDiskCoverι R D M ⟨x, n, z⟩ ≫ (diskCoverMap R D g ≫ moduleDiskCoverπ R D N) =
    moduleDiskCoverι R D M ⟨x, n, z⟩ ≫ (moduleDiskCoverπ R D M ≫ g)
  simp only [← Category.assoc, diskCoverι_map, moduleDiskCoverι_π]
  exact diskGenerator_naturality R D g x n z

/-- 同じ既存の被覆を恒等・合成を保つ関手としてまとめる。 -/
def diskCoverFunctor : ModuleCategory R D ⥤ ModuleCategory R D where
  obj M := moduleDiskCover R D M
  map g := diskCoverMap R D g
  map_id M := diskCoverMap_id R D M
  map_comp g h := diskCoverMap_comp R D g h

/-- 同じ既存の被覆射を自然変換としてまとめる。 -/
def diskCoverAugmentation : diskCoverFunctor R D ⟶ 𝟭 (ModuleCategory R D) where
  app M := moduleDiskCoverπ R D M
  naturality _ _ g := diskCoverMap_π R D g

end SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
