module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ResolutionDiskFunctor
public import SerrePositivity.DifferentialGraded.Resolution.Basic
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
# 既存の全 kernel cycle の添付の関手性

## 概要
本体の同じ kernel cell の添字と写像を、実際の可換四角形について写す。

## 方針
cycle の像を添字へ送り、既存の自由 sphere の生成元の自然性を使う。

## 規約
元の kernel cell 構成を変えない。選んだ持ち上げの恒等・合成を仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の既存の半自由分解候補の厳密な関手性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 固定した対象・次数における元の kernel cycle の像。 -/
def kernelCycleMap {F G : Arrow (ModuleCategory R D)} (s : F ⟶ G) (x : D) (n : ℤ)
    (z : {z : complexCycles R ((moduleEvaluation R D x).obj F.left) (n+1) //
      ((moduleEvaluation R D x).map F.hom).f (n+1) z.val = 0}) :
    {z : complexCycles R ((moduleEvaluation R D x).obj G.left) (n+1) //
      ((moduleEvaluation R D x).map G.hom).f (n+1) z.val = 0} :=
  ⟨complexMapCycle R ((moduleEvaluation R D x).map s.left) (n+1) z.val, by
    have h := congrArg (fun g => ((moduleEvaluation R D x).map g).f (n+1) z.val.val) s.w
    rw [evalMap_comp, evalMap_comp, z.property, map_zero] at h
    exact h⟩

/-- kernel cycle の恒等射の法則。 -/
@[simp] theorem kernelCycleMap_id (F : Arrow (ModuleCategory R D)) (x : D) (n : ℤ) (z) :
    kernelCycleMap R D (𝟙 F) x n z = z := by
  apply Subtype.ext
  apply Subtype.ext
  exact evalMap_id R D F.left x (n+1) z.val.val

/-- kernel cycle の合成の法則。 -/
@[simp] theorem kernelCycleMap_comp {F G H : Arrow (ModuleCategory R D)}
    (s : F ⟶ G) (t : G ⟶ H) (x : D) (n : ℤ) (z) :
    kernelCycleMap R D (s ≫ t) x n z =
      kernelCycleMap R D t x n (kernelCycleMap R D s x n z) := by
  apply Subtype.ext
  apply Subtype.ext
  exact evalMap_comp R D s.left t.left x (n+1) z.val.val

/-- 同じ対象と添付次数を保つ、元の kernel 添字の像。 -/
def kernelIndexMap {F G : Arrow (ModuleCategory R D)} (s : F ⟶ G)
    (j : ModuleKernelCellIndex R D F.hom) : ModuleKernelCellIndex R D G.hom :=
  ⟨j.1, j.2.1, kernelCycleMap R D s j.1 j.2.1 j.2.2⟩

/-- kernel 添字の恒等射の法則。 -/
@[simp] theorem kernelIndexMap_id (F : Arrow (ModuleCategory R D)) (j : ModuleKernelCellIndex R D F.hom) :
    kernelIndexMap R D (𝟙 F) j = j := by
  rcases j with ⟨x, n, z⟩
  exact congrArg (fun z' => (⟨x, n, z'⟩ : ModuleKernelCellIndex R D F.hom))
    (kernelCycleMap_id R D F x n z)

/-- kernel 添字の合成の法則。 -/
@[simp] theorem kernelIndexMap_comp {F G H : Arrow (ModuleCategory R D)} (s : F ⟶ G) (t : G ⟶ H)
    (j : ModuleKernelCellIndex R D F.hom) :
    kernelIndexMap R D (s ≫ t) j = kernelIndexMap R D t (kernelIndexMap R D s j) := by
  rcases j with ⟨x, n, z⟩
  exact congrArg (fun z' => (⟨x, n, z'⟩ : ModuleKernelCellIndex R D H.hom))
    (kernelCycleMap_comp R D s t x n z)

/-- 元の sphere の包含。型には添字の対象と次数だけを残す。 -/
def kernelSourceι (F : Arrow (ModuleCategory R D)) (j : ModuleKernelCellIndex R D F.hom) :
    freeSphere R D j.1 (j.2.1 + 1) ⟶ moduleKernelCellSource R D F.hom :=
  Sigma.ι (moduleKernelCellFamily R D F.hom) j

/-- 元の kernel sphere の余積を、像の添字へ写す射。 -/
def kernelSourceMap {F G : Arrow (ModuleCategory R D)} (s : F ⟶ G) :
    moduleKernelCellSource R D F.hom ⟶ moduleKernelCellSource R D G.hom :=
  Sigma.desc (fun j => kernelSourceι R D G (kernelIndexMap R D s j))

/-- 元の各 sphere 上の指定公式。 -/
@[reassoc] theorem kernelSourceι_map {F G : Arrow (ModuleCategory R D)} (s : F ⟶ G)
    (j : ModuleKernelCellIndex R D F.hom) :
    kernelSourceι R D F j ≫ kernelSourceMap R D s =
      kernelSourceι R D G (kernelIndexMap R D s j) := Sigma.ι_comp_desc _ _

/-- kernel 添字の等式に沿う包含の従属合同。 -/
theorem kernelSourceι_heq (F : Arrow (ModuleCategory R D)) {i j : ModuleKernelCellIndex R D F.hom}
    (h : i=j) : HEq (kernelSourceι R D F i)
      (kernelSourceι R D F j) := by
  cases h
  rfl

/-- 対象と次数を固定した kernel cycle の元の包含。 -/
def kernelCycleι (F : Arrow (ModuleCategory R D)) (x : D) (n : ℤ)
    (z : {z : complexCycles R ((moduleEvaluation R D x).obj F.left) (n+1) //
      ((moduleEvaluation R D x).map F.hom).f (n+1) z.val = 0}) :
    freeSphere R D x (n+1) ⟶ moduleKernelCellSource R D F.hom :=
  Sigma.ι (moduleKernelCellFamily R D F.hom) ⟨x, n, z⟩

/-- 固定した対象と次数の生成元での、元の余積の射の公式。 -/
@[reassoc] theorem kernelCycleι_map {F G : Arrow (ModuleCategory R D)} (s : F ⟶ G)
    (x : D) (n : ℤ) (z) :
    kernelCycleι R D F x n z ≫ kernelSourceMap R D s =
      kernelCycleι R D G x n (kernelCycleMap R D s x n z) := Sigma.ι_comp_desc _ _

/-- 同じ対象と次数の元の包含は恒等写像で変わらない。 -/
theorem kernelCycleι_id (F : Arrow (ModuleCategory R D)) (x : D) (n : ℤ) (z) :
    kernelCycleι R D F x n (kernelCycleMap R D (𝟙 F) x n z) =
      kernelCycleι R D F x n z :=
  congrArg (kernelCycleι R D F x n) (kernelCycleMap_id R D F x n z)

/-- kernel sphere の余積の恒等射の法則。 -/
@[simp] theorem kernelSourceMap_id (F : Arrow (ModuleCategory R D)) :
    kernelSourceMap R D (𝟙 F) = 𝟙 (moduleKernelCellSource R D F.hom) := by
  apply Sigma.hom_ext
  rintro ⟨x, n, z⟩
  exact (kernelCycleι_map R D (𝟙 F) x n z).trans
    ((kernelCycleι_id R D F x n z).trans (Category.comp_id (kernelCycleι R D F x n z)).symm)

set_option maxHeartbeats 800000 in
-- 小さい余積の添字に依存する包含の型の照合に上限を確保する。
/-- kernel sphere の余積の合成の法則。 -/
@[simp] theorem kernelSourceMap_comp {F G H : Arrow (ModuleCategory R D)} (s : F ⟶ G) (t : G ⟶ H) :
    kernelSourceMap R D (s ≫ t) = kernelSourceMap R D s ≫ kernelSourceMap R D t := by
  apply Sigma.hom_ext
  intro j
  change kernelSourceι R D F j ≫ kernelSourceMap R D (s ≫ t) =
    kernelSourceι R D F j ≫ (kernelSourceMap R D s ≫ kernelSourceMap R D t)
  simp only [← Category.assoc, kernelSourceι_map]
  exact eq_of_heq (kernelSourceι_heq R D H (i := kernelIndexMap R D (s ≫ t) j)
    (j := kernelIndexMap R D t (kernelIndexMap R D s j)) (kernelIndexMap_comp R D s t j))

set_option maxHeartbeats 800000 in
-- 元の自由 sphere の随伴と小さい余積の型の照合に上限を確保する。
/-- 元の自由 sphere の cycle 指定は、実際の射について自然である。 -/
theorem sphereGenerator_naturality {M N : ModuleCategory R D} (g : M ⟶ N)
    (x : D) (n : ℤ) (z : complexCycles R ((moduleEvaluation R D x).obj M) n) :
    (freeSphereHomEquiv R D x n N).symm (complexMapCycle R ((moduleEvaluation R D x).map g) n z) =
      (freeSphereHomEquiv R D x n M).symm z ≫ g := by
  apply (freeSphereHomEquiv R D x n N).injective
  apply Subtype.ext
  rw [Equiv.apply_symm_apply, freeSphereHomEquiv_naturality_val]
  have h := congrArg Subtype.val ((freeSphereHomEquiv R D x n M).apply_symm_apply z)
  rw [h] <;> rfl

/-- 元の kernel 添付写像は、可換四角形について自然である。 -/
@[reassoc] theorem kernelSourceMap_cell {F G : Arrow (ModuleCategory R D)} (s : F ⟶ G) :
    kernelSourceMap R D s ≫ moduleKernelCellMap R D G.hom =
      moduleKernelCellMap R D F.hom ≫ s.left := by
  apply Sigma.hom_ext
  rintro ⟨x, n, z⟩
  calc
    _ = kernelCycleι R D G x n (kernelCycleMap R D s x n z) ≫
        moduleKernelCellMap R D G.hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ moduleKernelCellMap R D G.hom) (kernelCycleι_map R D s x n z))
    _ = (freeSphereHomEquiv R D x (n+1) G.left).symm
        (complexMapCycle R ((moduleEvaluation R D x).map s.left) (n+1) z.val) :=
      moduleKernelCellι_map R D G.hom _
    _ = (freeSphereHomEquiv R D x (n+1) F.left).symm z.val ≫ s.left :=
      sphereGenerator_naturality R D s.left x (n+1) z.val
    _ = _ := by rw [← Category.assoc, moduleKernelCellι_map]

/-- 同じ既存の kernel sphere の余積を関手としてまとめる。 -/
def kernelSourceFunctor : Arrow (ModuleCategory R D) ⥤ ModuleCategory R D where
  obj F := moduleKernelCellSource R D F.hom
  map s := kernelSourceMap R D s
  map_id F := kernelSourceMap_id R D F
  map_comp s t := kernelSourceMap_comp R D s t

/-- 同じ既存の kernel 添付写像を自然変換としてまとめる。 -/
def kernelCellTransformation : kernelSourceFunctor R D ⟶ Arrow.leftFunc where
  app F := moduleKernelCellMap R D F.hom
  naturality _ _ s := kernelSourceMap_cell R D s

/-- 同じ既存の kernel 添付写像を arrow 圏へまとめる。 -/
def kernelArrowFunctor : Arrow (ModuleCategory R D) ⥤ Arrow (ModuleCategory R D) where
  obj F := Arrow.mk (moduleKernelCellMap R D F.hom)
  map s := Arrow.homMk (kernelSourceMap R D s) s.left (kernelSourceMap_cell R D s)
  map_id F := by
    apply Arrow.hom_ext
    · exact kernelSourceMap_id R D F
    · rfl
  map_comp s t := by
    apply Arrow.hom_ext
    · exact kernelSourceMap_comp R D s t
    · rfl

end SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
